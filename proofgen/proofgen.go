package proofgen

import (
	"io"
	"sort"
	"strings"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/glang"
	"github.com/goose-lang/goose/proofgen/tmpl"
	"golang.org/x/tools/go/packages"
)

func Package(w io.Writer, pkg *packages.Package, ffi string, bootstrap bool, filter declfilter.DeclFilter) {
	coqPath := strings.ReplaceAll(glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(pkg.PkgPath), "/", ".")

	pf := tmpl.PackageProof{
		Ffi:        ffi,
		Bootstrap:  bootstrap,
		Name:       pkg.Name,
		HasTrusted: filter.HasTrusted(),
		ImportPath: coqPath,
	}

	var imports []string
	for path := range pkg.Imports {
		if filter.ShouldImport(path) {
			imports = append(imports, path)
		}
	}
	sort.Strings(imports)

	for _, path := range imports {
		coqPath := strings.ReplaceAll(glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(path), "/", ".")
		pf.Imports = append(pf.Imports, tmpl.Import{
			Path: coqPath,
		})
	}

	pf.Types = translateTypes(pkg, filter)

	if err := pf.Write(w); err != nil {
		panic(err)
	}
}
