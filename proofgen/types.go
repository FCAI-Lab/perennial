package proofgen

import (
	"go/ast"
	"go/token"
	"go/types"
	"log"
	"strconv"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/deptracker"
	"github.com/goose-lang/goose/glang"
	"github.com/goose-lang/goose/proofgen/tmpl"
	"golang.org/x/tools/go/packages"
)

type typesTranslator struct {
	pkg *packages.Package

	filter declfilter.DeclFilter

	deps *deptracker.Deps
	defs map[string]tmpl.TypeDecl
	// tracks the order definitions were seen in
	defNames []string
}

func (tr typesTranslator) ReadablePos(p token.Pos) string {
	return tr.pkg.Fset.Position(p).String()
}

func (tr *typesTranslator) newDecl(spec *ast.TypeSpec, info tmpl.TypeInfo) tmpl.TypeDecl {
	return tmpl.TypeDecl{
		PkgName:  tr.pkg.Name,
		Name:     glang.GallinaIdent(spec.Name.Name).Coq(false),
		TypeInfo: info,
	}
}

func (tr *typesTranslator) axiomatizeType(spec *ast.TypeSpec) {
	name := spec.Name.Name
	defName := name + ".t"
	tr.deps.SetCurrentName(defName)
	defer tr.deps.UnsetCurrentName()

	decl := tr.newDecl(spec, tmpl.TypeAxiom{})
	tr.defNames = append(tr.defNames, defName)
	tr.defs[defName] = decl
}

func (tr *typesTranslator) translateStructType(spec *ast.TypeSpec, s *types.Struct) {
	name := spec.Name.Name
	defName := name + ".t"
	tr.deps.SetCurrentName(defName)
	defer tr.deps.UnsetCurrentName()

	info := tmpl.TypeStruct{
		TypeParams: nil, // populated below
		Fields:     nil, // populated below
	}
	if spec.TypeParams != nil {
		for _, tp := range spec.TypeParams.List {
			for _, name := range tp.Names {
				info.TypeParams = append(info.TypeParams, name.Name)
			}
		}
	}
	for i := 0; i < s.NumFields(); i++ {
		fieldName := s.Field(i).Name()
		if fieldName == "_" {
			fieldName = "_" + strconv.Itoa(i)
		}
		field := tmpl.TypeField{
			Name: fieldName,
			// Type: tr.toCoqTypeWithDeps(s.Field(i).Type()),
		}
		info.Fields = append(info.Fields, field)
	}
	decl := tr.newDecl(spec, info)
	tr.defNames = append(tr.defNames, defName)
	tr.defs[defName] = decl
}

func (tr *typesTranslator) translateType(spec *ast.TypeSpec) {
	switch s := tr.pkg.TypesInfo.TypeOf(spec.Type).(type) {
	case *types.Struct:
		tr.translateStructType(spec, s)
	default:
	}
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
					tr.translateType(spec)
				case declfilter.Axiomatize:
					tr.axiomatizeType(spec)
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
		deps:   deptracker.New(),
		defs:   make(map[string]tmpl.TypeDecl),
		pkg:    pkg,
		filter: filter,
	}
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			tr.Decl(d)
		}
	}

	var printingOrdered []string
	printing := make(map[string]bool)
	printed := make(map[string]bool)
	var printDefAndDeps func(string)

	var decls []tmpl.TypeDecl
	printDefAndDeps = func(n string) {
		if printed[n] {
			return
		} else if printing[n] {
			log.Fatal("Found a cyclic dependency: ", printingOrdered)
		}

		printingOrdered = append(printingOrdered, n)
		printing[n] = true
		defer func() {
			printingOrdered = printingOrdered[:len(printingOrdered)-1]
			delete(printing, n)
		}()

		for depName := range tr.deps.GetDeps(n) {
			printDefAndDeps(depName)
		}
		decl, ok := tr.defs[n]
		if ok {
			decls = append(decls, decl)
		}
		printed[n] = true
	}
	for _, d := range tr.defNames {
		printDefAndDeps(d)
	}
	return decls
}
