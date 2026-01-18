package proofgen

import (
	"go/ast"
	"go/token"
	"go/types"
	"iter"
	"log"
	"slices"
	"strconv"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/glang"
	"github.com/goose-lang/goose/proofgen/tmpl"
	"github.com/goose-lang/goose/util/toposort"
	"golang.org/x/tools/go/packages"
)

type typesTranslator struct {
	pkg *packages.Package

	specs          []*ast.TypeSpec
	nameToTypeSpec map[string]*ast.TypeSpec

	filter declfilter.DeclFilter
}

func (tr typesTranslator) ReadablePos(p token.Pos) string {
	return tr.pkg.Fset.Position(p).String()
}

func (tr *typesTranslator) translateStructType(spec *ast.TypeSpec, s *types.Struct) []tmpl.TypeDecl {
	decl := tmpl.TypeDecl{
		PkgName:    tr.pkg.Name,
		Name:       glang.GallinaIdent(spec.Name.Name).Coq(false),
		TypeParams: nil, // populated below
		Fields:     nil, // populated below
	}
	if spec.TypeParams != nil {
		for _, tp := range spec.TypeParams.List {
			for _, name := range tp.Names {
				decl.TypeParams = append(decl.TypeParams, name.Name)
			}
		}
	}
	for i := 0; i < s.NumFields(); i++ {
		fieldName := s.Field(i).Name()
		if fieldName == "_" {
			fieldName = "_" + strconv.Itoa(i)
		}
		decl.Fields = append(decl.Fields, fieldName)
	}
	return []tmpl.TypeDecl{decl}
}

func (tr *typesTranslator) translateType(spec *ast.TypeSpec) []tmpl.TypeDecl {
	switch s := tr.pkg.TypesInfo.TypeOf(spec.Type).(type) {
	case *types.Struct:
		return tr.translateStructType(spec, s)
	}
	return nil
}

func (tr *typesTranslator) Decl(d ast.Decl) {
	switch d := d.(type) {
	case *ast.FuncDecl:
	case *ast.GenDecl:
		switch d.Tok {
		case token.TYPE:
			for _, spec := range d.Specs {
				spec := spec.(*ast.TypeSpec)
				switch tr.filter.GetAction(spec.Name.Name) {
				case declfilter.Translate:
					tr.specs = append(tr.specs, spec)
					tr.nameToTypeSpec[spec.Name.Name] = spec
				case declfilter.Axiomatize:
					continue
				case declfilter.Trust:
					continue
				}
			}
		}
	case *ast.BadDecl:
	default:
	}
}

func translateTypes(pkg *packages.Package, filter declfilter.DeclFilter) []tmpl.TypeDecl {
	tr := &typesTranslator{
		pkg:    pkg,
		filter: filter,
		nameToTypeSpec: make(map[string]*ast.TypeSpec),
	}
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			tr.Decl(d)
		}
	}

	var decls []tmpl.TypeDecl

	for t := range toposort.ToposortSeq(slices.Values(tr.specs),
		func(s *ast.TypeSpec) iter.Seq[*ast.TypeSpec] {
			return func(yield func(s *ast.TypeSpec) bool) {
				if tr.filter.GetAction(s.Name.Name) == declfilter.Axiomatize {
					return
				}
				ast.Inspect(s.Type, func(n ast.Node) bool {
					switch n := n.(type) {
					case *ast.SelectorExpr, *ast.StarExpr:
						return false
					case *ast.ArrayType:
						return n.Len != nil
					case *ast.Ident:
						if t, ok := tr.nameToTypeSpec[n.Name]; ok {
							return yield(t)
						}
					}
					return true
				})
			}
		},
		func(cycle []*ast.TypeSpec) {
			s := "cycle: "
			sep := ""
			for _, t := range cycle {
				s += sep + t.Name.Name
				sep = "-> "
			}
			log.Fatal(cycle[0], "%s", s)
		}) {
		decls = append(decls, tr.translateType(t)...)
	}
	return decls
}
