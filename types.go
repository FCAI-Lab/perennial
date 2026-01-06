package goose

import (
	"fmt"
	"go/ast"
	"go/types"
	"math/big"
	"strconv"
	"strings"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/glang"
	"github.com/goose-lang/goose/util"
)

// this file has the translations for types themselves
func (ctx *Ctx) typeDecl(spec *ast.TypeSpec) (decls []glang.Decl) {
	declName := spec.Name.Name
	if _, ok := ctx.typeOf(spec.Name).(*types.Named); ok {
		declName = spec.Name.Name + "ⁱᵐᵖˡ"
	}

	ctx.dep.SetCurrentName(declName)
	defer ctx.dep.UnsetCurrentName()
	switch ctx.filter.GetAction(spec.Name.Name) {
	case declfilter.Axiomatize:
		decls = append(decls, glang.AxiomDecl{
			DeclName: declName,
			Type:     glang.VerbatimExpr("go.type"),
		})
		return
	case declfilter.Trust:
		if namedType, ok := ctx.typeOf(spec.Name).(*types.Named); ok {
			ctx.namedTypes = append(ctx.namedTypes, namedType)
			decls = append(decls, ctx.namedTypePropClassDecl(namedType)...)
		}
	case declfilter.Translate:
		ty := ctx.typeOf(spec.Type)
		decl := glang.TypeDecl{
			Name:       declName,
			Body:       ctx.glangType(spec, ty),
			TypeParams: ctx.typeParamList(spec.TypeParams),
		}
		decls = append(decls, decl)
		if namedType, ok := ctx.typeOf(spec.Name).(*types.Named); ok {
			ctx.namedTypes = append(ctx.namedTypes, namedType)
			// Add a go.type declaration
			var typeParams []string
			var typeParamsList glang.ListExpr
			if tps := namedType.TypeParams(); tps != nil {
				for i := range tps.Len() {
					typeParams = append(typeParams, tps.At(i).Obj().Name())
					typeParamsList = append(typeParamsList, glang.GallinaIdent(tps.At(i).Obj().Name()))
				}
			}
			decls = append(decls, glang.TypeDecl{
				Name: namedType.Obj().Name(),
				Body: glang.NewCallExpr(glang.VerbatimExpr("go.Named"),
					glang.StringLiteral{Value: namedType.Obj().Pkg().Path() + "." + namedType.Obj().Name()},
					typeParamsList,
				),
				TypeParams: typeParams,
			})

			// Add all the declarations associated with a new struct type
			decls = append(decls, ctx.namedRocqTypeDecl(spec)...)
			decls = append(decls, ctx.namedTypePropClassDecl(namedType)...)
		}
	}

	return
}

func (ctx *Ctx) namedRocqTypeDecl(spec *ast.TypeSpec) (decls []glang.Decl) {
	w := new(strings.Builder)
	fmt.Fprintf(w, "Module %s.\n", spec.Name.Name)
	fmt.Fprintf(w, "Section def.\nContext {ext : ffi_syntax} {go_gctx : GoGlobalContext}.\n")
	typeParams := ""
	namedType := ctx.typeOf(spec.Name).(*types.Named)
	if tps := namedType.TypeParams(); tps != nil {
		fmt.Fprintf(w, "Context {")
		for i := range tps.Len() {
			fmt.Fprintf(w, "%s ", tps.At(i).Obj().Name())
		}
		fmt.Fprint(w, ": Type}.\n")
	}

	switch t := ctx.typeOf(spec.Type).(type) {
	case *types.Struct:
		fmt.Fprintf(w, "Record t :=\nmk {\n")
		for i := range t.NumFields() {
			f := t.Field(i)
			err, ft := util.ToCoqType(f.Type())
			if err != nil {
				ctx.unsupported(spec, "%s", err.Error())
			}
			fmt.Fprintf(w, "  %s : %s;\n", f.Name(), ft)
		}
		fmt.Fprintf(w, "}.\n")

		// ZeroVal instance
		fmt.Fprintf(w, "#[global] Instance zero_val")
		if tps := namedType.TypeParams(); tps != nil {
			for i := range tps.Len() {
				fmt.Fprintf(w, "`{!ZeroVal %s} ", tps.At(i).Obj().Name())
			}
		}
		fmt.Fprintf(w, " : ZeroVal t := {| zero_val := mk")
		for range t.NumFields() {
			fmt.Fprint(w, " (zero_val _)")
		}
		fmt.Fprint(w, "|}.")

		// RecordSet instance
		fmt.Fprintf(w, "\n#[global] Instance settable : Settable t :=\n")
		fmt.Fprintf(w, "  settable! mk <")
		sep := ""
		for i := range t.NumFields() {
			fmt.Fprintf(w, "%s%s", sep, t.Field(i).Name())
			sep = "; "
		}
		fmt.Fprintf(w, ">.")

		fmt.Fprintf(w, "\nEnd def.\n")

		fmt.Fprint(w, "\n#[global] Arguments mk : clear implicits.")
		fmt.Fprint(w, "\n#[global] Arguments t : clear implicits.")

		fmt.Fprintf(w, "\nEnd %s.", spec.Name.Name)
	default:
		fmt.Fprintf(w, "Definition t %s : Type := ", typeParams)
		err, rocqType := util.ToCoqType(t)
		if err != nil {
			ctx.unsupported(spec, "%s", err.Error())
		}
		fmt.Fprintf(w, "%s.", rocqType)
		fmt.Fprint(w, "\nEnd def.")
		fmt.Fprintf(w, "\nEnd %s.", spec.Name.Name)
	}

	recordDecl := glang.VerbatimDecl{
		Name:    spec.Name.Name + ".t",
		Content: w.String(),
	}
	decls = append(decls, recordDecl)
	return decls
}

func (ctx *Ctx) namedTypePropClassDecl(t *types.Named) []glang.Decl {
	typeName := t.Obj().Name()

	typeParams := ""
	if t.TypeParams() != nil {
		for i := range t.TypeParams().Len() {
			name := t.TypeParams().At(i).Obj().Name()
			typeParams += " " + name
		}
	}

	ty := "(" + typeName + typeParams + ")"
	ptrTy := "(go.PointerType " + ty + ")"

	w := new(strings.Builder)
	fmt.Fprintln(w, "Class "+typeName+"_Assumptions "+
		"{ext : ffi_syntax} `{!GoGlobalContext} `{!GoLocalContext} `{!GoSemanticsFunctions} : Prop :=")
	fmt.Fprintln(w, "{")

	// zero val instance
	fmt.Fprintf(w, "  #[global] %s_zero_val ", typeName)
	if t.TypeParams() != nil {
		for i := range t.TypeParams().Len() {
			fmt.Fprintf(w, "%s %[1]s' `{!ZeroVal %[1]s'} `{!go.GoZeroValEq %[1]s %[1]s'}", t.TypeParams().At(i).Obj().Name())
		}
	}
	fmt.Fprintf(w, " :: go.GoZeroValEq ")
	if t.TypeParams() != nil {
		fmt.Fprintf(w, "(%s", typeName)
		for i := range t.TypeParams().Len() {
			fmt.Fprintf(w, " %s", t.TypeParams().At(i).Obj().Name())
		}
		fmt.Fprintf(w, ") (%s.t", typeName)

		for i := range t.TypeParams().Len() {
			fmt.Fprintf(w, " %s'", t.TypeParams().At(i).Obj().Name())
		}
		fmt.Fprintf(w, ");\n")
	} else {
		fmt.Fprintf(w, "%s %s.t;\n", typeName, typeName)
	}

	// underlying instance
	fmt.Fprintf(w, "  #[global] %[1]s_underlying%[2]s :: go.Underlying (%[1]s%[2]s) (%[1]sⁱᵐᵖˡ%[2]s);\n", typeName, typeParams)

	// StructFieldSet and StructFieldGet instances
	if ctx.filter.GetAction(t.Obj().Name()) == declfilter.Translate {
		if st, ok := t.Underlying().(*types.Struct); ok {
			for i := range st.NumFields() {
				fieldName := st.Field(i).Name()
				rocqTypeParams := ""
				if t.TypeParams() != nil {
					for i := range t.TypeParams().Len() {
						rocqTypeParams += " " + t.TypeParams().At(i).Obj().Name() + "'"
					}
				}

				fmt.Fprintf(w, "  #[global] %s_get_%s", typeName, fieldName)
				fmt.Fprintf(w, "%[3]s%[2]s (x : %[1]s.t%[2]s) :: "+
					"go.IsGoStepPureDet (StructFieldGet (%[1]s%[3]s) \"%[4]s\") #x #x.(%[1]s.%[4]s);\n",
					typeName, rocqTypeParams, typeParams, fieldName)

				fmt.Fprintf(w, "  #[global] %s_set_%s", typeName, fieldName)
				fmt.Fprintf(w, "%[3]s%[2]s (x : %[1]s.t%[2]s) y :: "+
					"go.IsGoStepPureDet (StructFieldSet (%[1]s%[3]s) \"%[4]s\") (#x, #y) #(x <|%[1]s.%[4]s := y|>);\n",
					typeName, rocqTypeParams, typeParams, fieldName)
			}
		}
	}

	// for every method in `t`
	goMset := types.NewMethodSet(t)
	for i := range goMset.Len() {
		selection := goMset.At(i)
		methodName, index := selection.Obj().Name(), selection.Index()
		if ctx.filter.GetAction(typeName+"."+methodName) == declfilter.Axiomatize {
			continue
		}
		var impl string
		if len(index) == 0 {
			ctx.nope(t.Obj(), "expected non-empty index in methodSet translation")
		} else if len(index) == 1 {
			ctx.dep.Add(glang.TypeMethod(typeName, methodName))
			impl = "(" + glang.TypeMethod(typeName, methodName) + typeParams + ")"
		} else {
			structType, ok := t.Underlying().(*types.Struct)
			if !ok {
				ctx.nope(t.Obj(), "type with embedded method should be a struct")
			}
			field := structType.Field(index[0])
			impl = `(λ: "$r", MethodResolve ` + ctx.glangType(field, field.Type()).Coq(true) + " " +
				methodName + " #() (StructFieldGet " + ty + ` "` + field.Name() + `" "$r" ))%V`
		}
		fmt.Fprintln(w, "  #[global] "+typeName+"'ptr_"+methodName+"_unfold"+typeParams+
			" :: MethodUnfold "+ty+` "`+methodName+`" `+impl+";")
	}

	goPtrMset := types.NewMethodSet(types.NewPointer(t))
	for i := range goPtrMset.Len() {
		selection := goPtrMset.At(i)
		methodName, index := selection.Obj().Name(), selection.Index()
		if ctx.filter.GetAction(typeName+"."+methodName) == declfilter.Axiomatize {
			continue
		}
		var impl string
		if len(index) == 0 {
			ctx.nope(t.Obj(), "expected non-empty index in methodSet translation")
		} else if len(index) == 1 {
			ctx.dep.Add(glang.TypeMethod(typeName, methodName))
			recvType := t.Method(index[0]).Signature().Recv().Type()
			if _, recvIsPointer := recvType.(*types.Pointer); recvIsPointer {
				ctx.dep.Add(glang.TypeMethod(typeName, methodName))
				impl = "(" + glang.TypeMethod(typeName, methodName) + typeParams + ")"
			} else {
				impl = `(λ: "$r", MethodResolve ` + ty + " " +
					methodName + " #() (![" + ty + `] "$r")`
			}
		} else {
			structType, ok := t.Underlying().(*types.Struct)
			if !ok {
				ctx.nope(t.Obj(), "type with embedded method should be a struct")
			}
			field := structType.Field(index[0])
			var fieldType types.Type = types.NewPointer(field.Type())
			var fieldExpr glang.Expr = glang.NewCallExpr(
				glang.VerbatimExpr("StructFieldRef"),
				ctx.glangType(t.Obj(), t),
				glang.NewStringVal(field.Name()),
				glang.IdentExpr("$r"),
			)

			// if `&(x.f)` would be a `**T`, dereference it to get `*T`
			if _, fieldIsPointer := field.Type().(*types.Pointer); fieldIsPointer {
				fieldExpr = glang.DerefExpr{
					X:  fieldExpr,
					Ty: ctx.glangType(field, field.Type()),
				}
				fieldType = field.Type()
			}
			impl = `(λ: "$r", MethodResolve ` + ctx.glangType(field, fieldType).Coq(true) + " " +
				methodName + " #() " + fieldExpr.Coq(true) + ")"
		}
		fmt.Fprintln(w, "  #[global] "+typeName+"'ptr_"+methodName+"_unfold"+typeParams+
			" :: MethodUnfold "+ptrTy+` "`+methodName+`" `+impl+";")
	}
	fmt.Fprint(w, "}.")

	decl := glang.VerbatimDecl{
		Name:    t.Obj().Name() + "_Assumptions",
		Content: w.String(),
	}

	return []glang.Decl{decl}
}

func (ctx *Ctx) typeOf(e ast.Expr) types.Type {
	return ctx.info.TypeOf(e)
}

func (ctx *Ctx) structType(t *types.Struct) glang.Expr {
	ty := glang.StructType{}
	for i := range t.NumFields() {
		fieldType := t.Field(i).Type()
		fieldName := t.Field(i).Name()
		if fieldName == "_" {
			fieldName = "_" + strconv.Itoa(i)
		}

		ty.Fields = append(ty.Fields, glang.FieldDecl{
			Name: fieldName,
			Type: ctx.glangType(t.Field(i), fieldType),
		})
	}
	return ty
}

func (ctx *Ctx) basicType(n locatable, t *types.Basic) glang.Expr {
	switch t.Name() {
	case "untyped string":
		return glang.GallinaIdent("go.string")
	case "Pointer":
		return glang.GallinaIdent("unsafe.Pointer")
	}
	return glang.GallinaIdent("go." + t.Name())
}

func (ctx *Ctx) signature(n locatable, t *types.Signature) glang.Expr {
	var argTypes glang.ListExpr
	var variadic glang.Expr
	var resultTypes glang.ListExpr

	// Ignore Recv; this might be a signature in an interface.

	if t.Params() != nil {
		for i := range t.Params().Len() {
			argTypes = append(argTypes, ctx.glangType(n, t.Params().At(i).Type()))
		}
	}
	variadic = glang.BoolLiteral(t.Variadic())
	if t.Results() != nil {
		for i := range t.Results().Len() {
			resultTypes = append(resultTypes, ctx.glangType(n, t.Results().At(i).Type()))
		}
	}
	return glang.NewCallExpr(glang.GallinaIdent("go.Signature"),
		argTypes,
		variadic,
		resultTypes,
	)
}

func (ctx *Ctx) interfaceType(n locatable, t *types.Interface) glang.Expr {
	var elems glang.ListExpr
	for i := range t.NumExplicitMethods() {
		elems = append(elems,
			glang.NewCallExpr(glang.GallinaIdent("go.MethodElem"),
				glang.NewStringVal(t.ExplicitMethod(i).Name()),
				ctx.signature(n, t.ExplicitMethod(i).Signature())),
		)
	}
	for i := range t.NumEmbeddeds() {
		em := t.EmbeddedType(i)
		var terms glang.ListExpr
		if uem, ok := em.(*types.Union); ok {
			for j := range uem.Len() {
				typeTermCons := "go.TypeTerm"
				if uem.Term(j).Tilde() {
					typeTermCons = typeTermCons + "Underlying"
				}
				terms = append(terms, glang.NewCallExpr(
					glang.GallinaIdent(typeTermCons),
					ctx.glangType(n, uem.Term(j).Type())),
				)
			}
		} else {
			terms = append(terms, glang.NewCallExpr(
				glang.GallinaIdent("go.TypeTerm"),
				ctx.glangType(n, em)),
			)
		}
		elems = append(elems,
			glang.NewCallExpr(glang.GallinaIdent("go.TypeElem"), terms))
	}

	return glang.NewCallExpr(glang.GallinaIdent("go.InterfaceType"), elems)
}

func (ctx *Ctx) glangType(n locatable, t types.Type) glang.Expr {
	t = types.Unalias(t)
	switch t := t.(type) {
	case *types.Struct:
		return ctx.structType(t)
	case *types.TypeParam:
		return glang.GallinaIdent(t.Obj().Name())
	case *types.Basic:
		return ctx.basicType(n, t)
	case *types.Pointer:
		return glang.NewCallExpr(glang.VerbatimExpr("go.PointerType"), ctx.glangType(n, t.Elem()))
	case *types.Named:
		if t.Obj().Pkg() == nil {
			switch t.Obj().Name() {
			case "error":
				return glang.GallinaIdent("go.error")
			case "any":
				return glang.GallinaIdent("go.any")
			}
			ctx.nope(n, "unexpected built-in type %v", t.Obj())
		}
		ctx.dep.Add(ctx.qualifiedName(t.Obj()))
		if t.TypeArgs().Len() != 0 {
			return glang.CallExpr{
				MethodName: glang.GallinaIdent(ctx.qualifiedName(t.Obj())),
				Args:       ctx.convertTypeArgsToGlang(n, t.TypeArgs()),
			}
		} else {
			return glang.GallinaIdent(ctx.qualifiedName(t.Obj()))
		}

	case *types.Map:
		return glang.NewCallExpr(glang.GallinaIdent("go.MapType"),
			ctx.glangType(n, t.Key()), ctx.glangType(n, t.Elem()))
	case *types.Chan:
		chanDir := ""
		switch t.Dir() {
		case types.SendRecv:
			chanDir = "go.sendrecv"
		case types.SendOnly:
			chanDir = "go.sendonly"
		case types.RecvOnly:
			chanDir = "go.recvonly"
		}
		return glang.NewCallExpr(glang.GallinaIdent("go.ChannelType"),
			glang.GallinaIdent(chanDir), ctx.glangType(n, t.Elem()),
		)
	case *types.Array:
		return glang.NewCallExpr(glang.VerbatimExpr("go.ArrayType"),
			glang.ZLiteral{Value: big.NewInt(t.Len())}, ctx.glangType(n, t.Elem()))
	case *types.Signature:
		return glang.NewCallExpr(glang.GallinaIdent("go.FunctionType"), ctx.signature(n, t))
	case *types.Interface:
		return ctx.interfaceType(n, t)
	case *types.Slice:
		return glang.NewCallExpr(glang.GallinaIdent("go.SliceType"), ctx.glangType(n, t.Elem()))
	}
	ctx.unsupported(n, "unknown type %v", t)
	return nil // unreachable
}

func sliceElem(t types.Type) types.Type {
	if t, ok := underlyingType(t).(*types.Slice); ok {
		return t.Elem()
	}
	panic(fmt.Errorf("expected slice type, got %v", t))
}

func ptrElem(t types.Type) types.Type {
	if t, ok := underlyingType(t).(*types.Pointer); ok {
		return t.Elem()
	}
	panic(fmt.Errorf("expected pointer type, got %v", t))
}

func chanElem(t types.Type) types.Type {
	if t, ok := underlyingType(t).(*types.Chan); ok {
		return t.Elem()
	}
	panic(fmt.Errorf("expected channel type, got %v", t))
}

func isByteSlice(t types.Type) bool {
	if t, ok := t.(*types.Slice); ok {
		if elTy, ok := t.Elem().Underlying().(*types.Basic); ok {
			return elTy.Kind() == types.Byte
		}
	}
	return false
}

func isString(t types.Type) bool {
	if t, ok := t.(*types.Basic); ok {
		return t.Kind() == types.String
	}
	return false
}

func (ctx *Ctx) convertTypeArgsToGlang(l locatable, typeList *types.TypeList) (glangTypeArgs []glang.Expr) {
	glangTypeArgs = make([]glang.Expr, typeList.Len())
	for i := range glangTypeArgs {
		glangTypeArgs[i] = ctx.glangType(l, typeList.At(i))
	}
	return
}

type structTypeInfo struct {
	name           string
	throughPointer bool
	namedType      *types.Named
	structType     *types.Struct
	typeArgs       *types.TypeList
}

func (ctx *Ctx) structInfoToGlangType(info structTypeInfo) glang.Expr {
	ctx.dep.Add(info.name)
	return glang.GallinaIdent(info.name)
}

func (ctx *Ctx) getStructInfo(t types.Type) (structTypeInfo, bool) {
	throughPointer := false
	if pt, ok := t.(*types.Pointer); ok {
		throughPointer = true
		t = pt.Elem()
	}
	if t, ok := t.(*types.Named); ok {
		name := ctx.qualifiedName(t.Obj())
		if structType, ok := t.Underlying().(*types.Struct); ok {
			return structTypeInfo{
				name:           name,
				typeArgs:       t.TypeArgs(),
				namedType:      t,
				throughPointer: throughPointer,
				structType:     structType,
			}, true
		}
	}
	return structTypeInfo{}, false
}

type interfaceTypeInfo struct {
	name           string
	interfaceType  *types.Interface
	throughPointer bool
}

func (ctx *Ctx) getInterfaceInfo(t types.Type) (interfaceTypeInfo, bool) {
	throughPointer := false
	if pt, ok := t.(*types.Pointer); ok {
		throughPointer = true
		t = pt.Elem()
	}
	if t, ok := t.(*types.Named); ok {
		name := ctx.qualifiedName(t.Obj())
		if interfaceType, ok := t.Underlying().(*types.Interface); ok {
			return interfaceTypeInfo{
				name:           name,
				interfaceType:  interfaceType,
				throughPointer: throughPointer,
			}, true
		}
	}
	return interfaceTypeInfo{}, false
}
