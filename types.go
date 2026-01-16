package goose

import (
	"fmt"
	"go/ast"
	"go/types"
	"math/big"
	"slices"
	"strconv"
	"strings"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/glang"
)

// this file has the translations for types themselves
func (ctx *Ctx) typeDecl(spec *ast.TypeSpec) {
	typeName := spec.Name.Name

	if namedType, ok := ctx.typeOf(spec.Name).(*types.Named); ok {
		ctx.namedTypeSpecs = append(ctx.namedTypeSpecs, spec)

		var typeParams []string
		var typeParamsList glang.ListExpr
		if tps := namedType.TypeParams(); tps != nil {
			for i := range tps.Len() {
				typeParams = append(typeParams, tps.At(i).Obj().Name())
				typeParamsList = append(typeParamsList, glang.GallinaIdent(tps.At(i).Obj().Name()))
			}
		}
		ctx.out.typeNamedDecls = append(ctx.out.typeNamedDecls, glang.TypeDecl{
			Name: typeName,
			Body: glang.NewCallExpr(glang.VerbatimExpr("go.Named"),
				glang.StringLiteral{Value: namedType.Obj().Pkg().Path() + "." + namedType.Obj().Name()},
				typeParamsList,
			),
			TypeParams: typeParams,
		})
	}

	switch ctx.filter.GetAction(spec.Name.Name) {
	case declfilter.Axiomatize:
		if _, ok := ctx.typeOf(spec.Name).(*types.Alias); ok {
			ctx.out.typeAliasDecls = append(ctx.out.typeAliasDecls, glang.AxiomDecl{
				DeclName: typeName,
				Type:     glang.VerbatimExpr("go.type"),
			})
		}
		return
	case declfilter.Translate:
		if aliasedType, ok := ctx.typeOf(spec.Name).(*types.Alias); ok {
			var typeParams []string
			if tps := aliasedType.TypeParams(); tps != nil {
				for i := range tps.Len() {
					typeParams = append(typeParams, tps.At(i).Obj().Name())
				}
			}
			ctx.out.typeAliasDecls = append(ctx.out.typeAliasDecls, glang.TypeDecl{
				Name:       typeName,
				Body:       ctx.glangType(spec.Type, types.Unalias(aliasedType)),
				TypeParams: typeParams,
			})
		}
	case declfilter.Trust:
	}
}

func (ctx *Ctx) namedTypeSemanticsDecl(spec *ast.TypeSpec) []glang.Decl {
	return slices.Concat(ctx.namedRocqTypeDecl(spec), ctx.namedTypeImplDecl(spec),
		ctx.namedTypePropClassDecl(spec))
}

// Adding a "'" to avoid conflicting with Coq keywords and definitions that
// would already be in context (like `t`). Could do this only when there is a
// conflict, but it's lower entropy to do it always rather than pick and
// choosing when.
func recordProjection(i int, s string) string {
	if s == "_" {
		return s + fmt.Sprint(i) + "'"
	}
	return s + "'"
}

func (ctx *Ctx) namedRocqTypeDecl(spec *ast.TypeSpec) (decls []glang.Decl) {
	w := new(strings.Builder)
	fmt.Fprintf(w, "Module %s.\n", spec.Name.Name)
	fmt.Fprintf(w, "Section def.\nContext {ext : ffi_syntax} {go_gctx : GoGlobalContext}.\n")
	namedType := ctx.typeOf(spec.Name).(*types.Named)

	switch ctx.filter.GetAction(spec.Name.Name) {
	case declfilter.Trust:
		return
	case declfilter.Axiomatize:
		fmt.Fprintf(w, "Axiom t : ")
		if tps := namedType.TypeParams(); tps != nil {
			fmt.Fprintf(w, "∀ {")
			for i := range tps.Len() {
				fmt.Fprintf(w, "%s ", tps.At(i).Obj().Name())
			}
			fmt.Fprint(w, ": Type}, ")
		}
		fmt.Fprintf(w, "Type.")
		// ZeroVal instance
		fmt.Fprintf(w, "\nAxiom zero_val : ")
		if tps := namedType.TypeParams(); tps != nil {
			fmt.Fprintf(w, "∀")
			for i := range tps.Len() {
				fmt.Fprintf(w, " `{!ZeroVal %s}", tps.At(i).Obj().Name())
			}
			fmt.Fprintf(w, ", ")
		}
		fmt.Fprintf(w, "ZeroVal t.")
		fmt.Fprintf(w, "\n#[global] Existing Instance zero_val.")

		fmt.Fprint(w, "\nEnd def.")
		fmt.Fprintf(w, "\nEnd %s.", spec.Name.Name)
	case declfilter.Translate:
		switch t := ctx.typeOf(spec.Type).(type) {
		case *types.Struct:
			fmt.Fprintf(w, "Record t")

			if tps := namedType.TypeParams(); tps != nil {
				fmt.Fprintf(w, " {")
				for i := range tps.Len() {
					fmt.Fprintf(w, "%s ", tps.At(i).Obj().Name())
				}
				fmt.Fprint(w, ": Type}")
			}
			fmt.Fprintf(w, " :=\nmk {\n")

			for i := range t.NumFields() {
				f := t.Field(i)
				ft := ctx.toGallinaType(spec, f.Type())
				fmt.Fprintf(w, "  %s : %s;\n", recordProjection(i, f.Name()), ft)
			}
			fmt.Fprintf(w, "}.\n")

			// ZeroVal instance
			fmt.Fprintf(w, "\n#[global] Instance zero_val")
			if tps := namedType.TypeParams(); tps != nil {
				for i := range tps.Len() {
					fmt.Fprintf(w, " `{!ZeroVal %s}", tps.At(i).Obj().Name())
				}
			}
			fmt.Fprintf(w, " : ZeroVal t := {| zero_val := mk")

			if tps := namedType.TypeParams(); tps != nil {
				for i := range tps.Len() {
					fmt.Fprintf(w, " %s", tps.At(i).Obj().Name())
				}
			}
			for range t.NumFields() {
				fmt.Fprint(w, " (zero_val _)")
			}
			fmt.Fprint(w, "|}.")

			fmt.Fprint(w, "\n#[global] Arguments mk : clear implicits.")
			fmt.Fprint(w, "\n#[global] Arguments t : clear implicits.")

			fmt.Fprintf(w, "\nEnd def.\n")

			fmt.Fprintf(w, "\nEnd %s.", spec.Name.Name)
		default:
			fmt.Fprintf(w, "Definition t")

			if tps := namedType.TypeParams(); tps != nil {
				fmt.Fprintf(w, " {")
				for i := range tps.Len() {
					fmt.Fprintf(w, "%s ", tps.At(i).Obj().Name())
				}
				fmt.Fprint(w, ": Type}")
			}
			fmt.Fprintf(w, " : Type := ")

			rocqType := ctx.toGallinaType(spec, t)
			fmt.Fprintf(w, "%s.", rocqType)
			fmt.Fprint(w, "\nEnd def.")
			fmt.Fprintf(w, "\nEnd %s.", spec.Name.Name)
		}
	}

	recordDecl := glang.VerbatimDecl{
		Name:    spec.Name.Name + ".t",
		Content: w.String(),
	}
	decls = append(decls, recordDecl)
	return decls
}

func (ctx *Ctx) namedTypeImplDecl(spec *ast.TypeSpec) []glang.Decl {
	if ctx.filter.GetAction(spec.Name.Name) != declfilter.Translate {
		return nil
	}
	typeName := spec.Name.Name
	decl := glang.TypeDecl{
		Name:       typeName + "ⁱᵐᵖˡ",
		Body:       ctx.glangType(spec, ctx.typeOf(spec.Type)),
		TypeParams: ctx.typeParamList(spec.TypeParams),
	}
	return []glang.Decl{decl}
}

// FIXME: this should take the TypeSpec
func (ctx *Ctx) namedTypePropClassDecl(spec *ast.TypeSpec) []glang.Decl {
	typeName := spec.Name.Name
	t := ctx.typeOf(spec.Name).(*types.Named)
	tunder := ctx.typeOf(spec.Type)

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

	// type repr instance
	fmt.Fprintf(w, "  #[global] %s_type_repr ", typeName)
	if t.TypeParams() != nil {
		for i := range t.TypeParams().Len() {
			fmt.Fprintf(w, "%s %[1]s' `{!ZeroVal %[1]s'} `{!go.TypeRepr %[1]s %[1]s'}", t.TypeParams().At(i).Obj().Name())
		}
	}
	fmt.Fprintf(w, " :: go.TypeRepr ")
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
	if ctx.filter.GetAction(typeName) != declfilter.Axiomatize {
		fmt.Fprintf(w, "  #[global] %[1]s_underlying%[2]s :: go.Underlying (%[1]s%[2]s) (%[1]sⁱᵐᵖˡ%[2]s);\n", typeName, typeParams)
	}

	// maybe emit StructFieldSet and StructFieldGet instances
	if ctx.filter.GetAction(t.Obj().Name()) == declfilter.Translate {
		if st, ok := tunder.(*types.Struct); ok {
			rocqTypeParams := ""
			if t.TypeParams() != nil {
				for i := range t.TypeParams().Len() {
					rocqTypeParams += " " + t.TypeParams().At(i).Obj().Name() + "'"
				}
			}

			for i := range st.NumFields() {
				fieldName := st.Field(i).Name()
				projName := recordProjection(i, st.Field(i).Name())

				fmt.Fprintf(w, "  #[global] %s_get_%s", typeName, fieldName)
				fmt.Fprintf(w, "%[3]s%[2]s (x : %[1]s.t%[2]s) :: "+
					"go.IsGoStepPureDet (StructFieldGet (%[1]s%[3]s) \"%[4]s\") #x #x.(%[1]s.%[5]s);\n",
					typeName, rocqTypeParams, typeParams, fieldName, projName)

				fmt.Fprintf(w, "  #[global] %s_set_%s", typeName, fieldName)
				fmt.Fprintf(w, "%[3]s%[2]s (x : %[1]s.t%[2]s) y :: "+
					"go.IsGoStepPureDet (StructFieldSet (%[1]s%[3]s) \"%[4]s\") (#x, #y) #(x <|%[1]s.%[5]s := y|>);\n",
					typeName, rocqTypeParams, typeParams, fieldName, projName)
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
		fmt.Fprintln(w, "  #[global] "+typeName+"_"+methodName+"_unfold"+typeParams+
			" :: MethodUnfold "+ty+` "`+methodName+`" `+impl+";")
	}

	// for every method in `*t`
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
			recvType := t.Method(index[0]).Signature().Recv().Type()
			if _, recvIsPointer := recvType.(*types.Pointer); recvIsPointer {
				impl = "(" + glang.TypeMethod(typeName, methodName) + typeParams + ")"
			} else {
				impl = `(λ: "$r", MethodResolve ` + ty + ` "` +
					methodName + `" #() (![` + ty + `] "$r"))`
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

func (ctx *Ctx) basicType(t *types.Basic) glang.Expr {
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
				glang.StringLiteral{Value: t.ExplicitMethod(i).Name()},
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
		return ctx.basicType(t)
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

func (ctx *Ctx) basicTypeToGallina(n locatable, t *types.Basic) string {
	switch t.Name() {
	case "uint64", "int64":
		return "w64"
	case "uint32", "int32":
		return "w32"
	case "uint16", "int16":
		return "w16"
	case "uint8", "int8", "byte":
		return "w8"
	case "uint", "int":
		return "w64"
	case "float64":
		return "w64"
	case "bool":
		return "bool"
	case "string", "untyped string":
		return "go_string"
	case "Pointer", "uintptr":
		return "loc"
	}
	ctx.unsupported(n, "Unknown basic type %s,", t.Name())
	return ""
}

func (ctx *Ctx) namedTypeToGallina(l locatable, t *types.Named) string {
	var baseName string
	pkg := t.Obj().Pkg()
	if pkg != nil {
		baseName = pkg.Name() + "." + t.Obj().Name() + ".t"
	} else {
		baseName = t.Obj().Name() + ".t"
	}
	// if TypeParams() is not nil, there are type parameters in the base named type
	if t.TypeParams() != nil {
		var params []string
		for i := 0; i < t.TypeArgs().Len(); i++ {
			params = append(params, ctx.toGallinaType(l, t.TypeArgs().At(i)))
		}
		return fmt.Sprintf("(%s %s)", baseName, strings.Join(params, " "))
	}
	return baseName
}

// ToCoqType converts a type to a Gallina type modeling that type
func (ctx *Ctx) toGallinaType(l locatable, t types.Type) string {
	switch t := types.Unalias(t).(type) {
	case *types.Basic:
		return ctx.basicTypeToGallina(l, t)
	case *types.Slice:
		return "slice.t"
	case *types.Array:
		return fmt.Sprintf("(array.t %s %d)", ctx.toGallinaType(l, t.Elem()), t.Len())
	case *types.Pointer:
		return "loc"
	case *types.Signature:
		return "func.t"
	case *types.Interface:
		return "interface.t"
	case *types.Map, *types.Chan:
		return "loc"
	case *types.Named:
		return ctx.namedTypeToGallina(l, t)
	case *types.TypeParam:
		return t.String()
	case *types.Struct:
		if t.NumFields() == 0 {
			return "unit"
		}
		ctx.unsupported(l, "Anonymous structs with fields are not supported %s", t.String())
	}
	ctx.unsupported(l, "Unknown type %s (of type %T)", t, t)
	return ""
}
