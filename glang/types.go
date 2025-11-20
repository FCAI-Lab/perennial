package glang

// This file has the structs to represent types

import (
	"fmt"
)

// FieldDecl is a name:type declaration in a struct definition
type FieldDecl struct {
	Name string
	Type Expr
}

type StructType struct {
	Fields []FieldDecl
}

var _ Expr = StructType{}

// Coq is the GooseLang type
func (d StructType) Coq(needs_paren bool) string {
	var pp buffer
	pp.Add("type.structT [")
	pp.Indent(2)
	for i, fd := range d.Fields {
		sep := ";"
		if i == len(d.Fields)-1 {
			sep = ""
		}
		pp.Add("(%s, %s)%s", StringLiteral{fd.Name}.Coq(false), fd.Type.Coq(false), sep)
	}
	pp.Indent(-2)
	pp.AddLine("]")
	return addParens(needs_paren, pp.Build())
}

// GallinaTypeDecl represents the same information as a TypeDecl, but translates
// as a go.type.
type TypeDecl struct {
	Name       string
	Body       Expr
	TypeParams []string
}

func (d TypeDecl) CoqDecl() string {
	var pp buffer

	typeParams := ""
	for _, t := range d.TypeParams {
		typeParams += fmt.Sprintf("(%s : go.type) ", t)
	}

	pp.Add("Definition %s %s: go.type := %s.", GallinaIdent(d.Name).Coq(false), typeParams, d.Body.Coq(false))
	pp.Add("#[global] Typeclasses Opaque %s.", GallinaIdent(d.Name).Coq(false))
	pp.Add("#[global] Opaque %s.", GallinaIdent(d.Name).Coq(false))
	return pp.Build()
}

func (d TypeDecl) DefName() (bool, string) {
	return true, d.Name
}

type MapType struct {
	Key   Expr
	Value Expr
}

var _ Expr = MapType{}

// Coq is the GooseLang type
func (t MapType) Coq(needs_paren bool) string {
	return NewCallExpr(GallinaVerbatim("type.mapT"), t.Key, t.Value).Coq(needs_paren)
}

type ChanType struct {
	Elem Expr
}

// Coq is the GooseLang type
func (t ChanType) Coq(needs_paren bool) string {
	return NewCallExpr(GallinaVerbatim("type.chanT"), t.Elem).Coq(needs_paren)
}

type FuncType struct{}

var _ Expr = FuncType{}

func (t FuncType) Coq(needs_paren bool) string {
	return "#funcT"
}

type InterfaceType struct{}

var _ Expr = InterfaceType{}

func (t InterfaceType) Coq(needs_paren bool) string {
	return "#interfaceT"
}

type SliceType struct {
	Value Expr
}

var _ Expr = SliceType{}

func (t SliceType) Coq(needs_paren bool) string {
	return "#sliceT"
}

type ArrayType struct {
	Len  uint64
	Elem Expr
}

var _ Expr = ArrayType{}

// Coq is the GooseLang type
func (t ArrayType) Coq(needs_paren bool) string {
	len_e := Int64Val{IntToZ(int64(t.Len))}
	return NewCallExpr(GallinaVerbatim("type.arrayT"), len_e, t.Elem).Coq(needs_paren)
}

type PtrType struct{}

var _ Expr = PtrType{}

// Coq is the GooseLang type
func (t PtrType) Coq(needs_paren bool) string {
	return "#ptrT"
}
