package goose

import (
	"fmt"
	"go/ast"
	"go/types"
	"strconv"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/glang"
)

// this file has the translations for types themselves
func (ctx *Ctx) typeDecl(spec *ast.TypeSpec) (decls []glang.Decl) {
	switch ctx.filter.GetAction(spec.Name.Name) {
	case declfilter.Axiomatize:
		if t, ok := ctx.typeOf(spec.Name).(*types.Named); ok {
			if _, isInterface := t.Underlying().(*types.Interface); !isInterface {
				ctx.namedTypes = append(ctx.namedTypes, t)
			}
		}
		decls = append(decls, glang.AxiomDecl{
			DeclName: spec.Name.Name,
			Type:     glang.GallinaVerbatim("go.type"),
		})
		return
	case declfilter.Trust:
		if t, ok := ctx.typeOf(spec.Name).(*types.Named); ok {
			if _, ok := t.Underlying().(*types.Interface); !ok {
				ctx.namedTypes = append(ctx.namedTypes, t)
			}
		}
	case declfilter.Translate:
		ctx.dep.SetCurrentName(spec.Name.Name)
		defer ctx.dep.UnsetCurrentName()

		if t, ok := ctx.typeOf(spec.Name).(*types.Named); ok {
			if _, ok := t.Underlying().(*types.Interface); !ok {
				ctx.namedTypes = append(ctx.namedTypes, t)
			}
		}
		ty := ctx.typeOf(spec.Type)
		decl := glang.TypeDecl{
			Name:       spec.Name.Name,
			Body:       ctx.glangType(spec, ty),
			TypeParams: ctx.typeParamList(spec.TypeParams),
		}

		decls = append(decls, decl)
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

// SimpleType translates t if it is a "simple type" (typically a simple
// identifier, with no structs or generics), returning nil if the type is not
// supported.
func SimpleType(t types.Type) glang.Expr {
	t = types.Unalias(t)
	if isProphId(t) {
		return glang.GallinaIdent("ProphIdT")
	}
	switch t := t.(type) {
	case *types.Struct:
		return nil
	case *types.TypeParam:
		// might need special handling
		return nil
	case *types.Basic:
		switch t.Name() {
		case "uint64", "uint32", "uint16", "uint8", "int64", "int32", "int16", "int8", "byte", "int", "uint", "bool", "string", "float64", "float32":
			return glang.GallinaIdent(fmt.Sprintf("%sT", t.Name()))
		case "untyped string":
			return glang.GallinaIdent("stringT")
		case "Pointer":
			return glang.PtrType{}
		}
		return nil
	case *types.Pointer:
		return glang.PtrType{}
	case *types.Named:
		if t.Obj().Pkg() == nil {
			if t.Obj().Name() == "error" {
				return glang.GallinaIdent("error")
			}
			return nil // unexpected
		}
		if t.Obj().Pkg().Name() == "filesys" && t.Obj().Name() == "File" {
			return glang.GallinaIdent("fileT")
		}
		if t.Obj().Pkg().Name() == "disk" && t.Obj().Name() == "Disk" {
			return glang.GallinaIdent("disk.Disk")
		}
		return nil // structs, type arguments, reference to a type
	case *types.Slice:
		// TODO: Value is not actually used
		return glang.SliceType{Value: nil}
	case *types.Map:
		keyT := SimpleType(t.Key())
		valueT := SimpleType(t.Elem())
		if keyT != nil && valueT != nil {
			return glang.MapType{Key: keyT, Value: valueT}
		}
	case *types.Signature:
		return glang.FuncType{}
	case *types.Interface:
		return glang.InterfaceType{}
	case *types.Chan:
		elemT := SimpleType(t.Elem())
		if elemT != nil {
			return glang.ChanType{Elem: elemT}
		}
	case *types.Array:
		elemT := SimpleType(t.Elem())
		if elemT != nil {
			return glang.ArrayType{Len: uint64(t.Len()), Elem: elemT}
		}
	}
	return nil
}

func (ctx *Ctx) glangType(n locatable, t types.Type) glang.Expr {
	t = types.Unalias(t)
	if tr := SimpleType(t); tr != nil {
		return tr
	}
	switch t := t.(type) {
	case *types.Struct:
		return ctx.structType(t)
	case *types.TypeParam:
		return glang.GallinaIdent(t.Obj().Name())
	case *types.Basic:
		// if not handled by SimpleType, unsupported
		ctx.unsupported(n, "basic type %s", t.Name())
	case *types.Pointer:
		return glang.PtrType{}
	case *types.Named:
		if t.Obj().Pkg() == nil {
			ctx.unsupported(n, "unexpected built-in type %v", t.Obj())
		}
		if info, ok := ctx.getStructInfo(t); ok {
			return ctx.structInfoToGlangType(info)
		}
		ctx.dep.Add(ctx.qualifiedName(t.Obj()))
		if t.TypeArgs().Len() != 0 {
			return glang.CallExpr{
				MethodName: glang.GallinaIdent(ctx.qualifiedName(t.Obj())),
				Args:       ctx.convertTypeArgsToGlang(nil, t.TypeArgs()),
			}
		}
		return glang.GallinaIdent(ctx.qualifiedName(t.Obj()))
	case *types.Map:
		return glang.MapType{Key: ctx.glangType(n, t.Key()), Value: ctx.glangType(n, t.Elem())}
	case *types.Chan:
		return glang.ChanType{Elem: ctx.glangType(n, t.Elem())}
	case *types.Array:
		return glang.ArrayType{Len: uint64(t.Len()), Elem: ctx.glangType(n, t.Elem())}
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

func isProphId(t types.Type) bool {
	if t, ok := t.(*types.Pointer); ok {
		if t, ok := t.Elem().(*types.Named); ok {
			name := t.Obj()
			return name.Pkg() != nil &&
				name.Pkg().Name() == "machine" &&
				name.Name() == "prophId"
		}
	}
	return false
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

// glang.Expr is an interface that is a subset of glang.Expr, but Go has
// requires a conversion (perhaps because there are different runtime
// representations)
func typesToExprs(ts []glang.Expr) []glang.Expr {
	var es []glang.Expr
	for _, t := range ts {
		es = append(es, t)
	}
	return es
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
