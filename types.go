package goose

import (
	"fmt"
	"go/ast"
	"go/types"
	"math/big"
	"strconv"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/glang"
)

// this file has the translations for types themselves
func (ctx *Ctx) typeDecl(spec *ast.TypeSpec) (decls []glang.Decl) {
	declName := spec.Name.Name
	if t, ok := ctx.typeOf(spec.Name).(*types.Named); ok {
		ctx.namedTypes = append(ctx.namedTypes, t)
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
	case declfilter.Trust:
	case declfilter.Translate:
		ty := ctx.typeOf(spec.Type)
		decl := glang.TypeDecl{
			Name:       declName,
			Body:       ctx.glangType(spec, ty),
			TypeParams: ctx.typeParamList(spec.TypeParams),
		}
		decls = append(decls, decl)
	}

	if namedType, ok := ctx.typeOf(spec.Name).(*types.Named); ok {
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
	}

	return
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
