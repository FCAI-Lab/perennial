package goose

import (
	"github.com/goose-lang/goose/glang"
	"go/token"
)

var gooseLangOps = map[token.Token]glang.OpId{
	token.EQL: glang.OpEquals,
	token.NEQ: glang.OpNotEquals,
	token.ADD: glang.OpPlus,
	token.LSS: glang.OpLessThan,
	token.GTR: glang.OpGreaterThan,
	token.SUB: glang.OpMinus,
	token.MUL: glang.OpMul,
	token.QUO: glang.OpQuot,
	token.REM: glang.OpRem,
	token.LEQ: glang.OpLessEq,
	token.GEQ: glang.OpGreaterEq,
	token.SHL: glang.OpShl,
	token.SHR: glang.OpShr,

	token.LAND:    glang.OpLAnd,
	token.LOR:     glang.OpLOr,
	token.AND:     glang.OpAnd,
	token.AND_NOT: glang.OpAndNot,
	token.OR:      glang.OpOr,
	token.XOR:     glang.OpXor,
}

var untypedIntOps = map[token.Token]glang.OpId{
	token.ADD: glang.OpPlus,
	token.LSS: glang.OpLessThanZ,
	token.GTR: glang.OpGreaterThanZ,
	token.SUB: glang.OpMinus,
	token.EQL: glang.OpEqualsZ,
	token.NEQ: glang.OpNotEqualsZ,
	token.MUL: glang.OpMul,
	token.QUO: glang.OpQuot,
	token.REM: glang.OpRem,
	token.LEQ: glang.OpLessEqZ,
	token.GEQ: glang.OpGreaterEqZ,
}

var untypedStringOps = map[token.Token]glang.OpId{
	token.ADD: glang.OpGallinaAppend,
	token.EQL: glang.OpEquals,
	token.NEQ: glang.OpNotEquals,
}
