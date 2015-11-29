(******************************************************************************
 * Project: pscala
 * By: Théophile Bastian <contact@tobast.fr>
 *
 * This project implements a compiler for "Petit Scala", as defined in
 * <https://www.lri.fr/~filliatr/ens/compil/projet/sujet1-v1.pdf>
 * It is developped as a school project for J-C. Filliâtre's Compilation course
 * at the Ecole Normale Superieure, Paris.
 ******************************************************************************
 * File: ast.mli
 *
 * Defines the AST type for Petit Scala
 *****************************************************************************)

(* Really dirty to declare it here, but couldn't manage to declare it in the
parser files *)
exception Parsing_error of string

type ident = string

type unaryOp = UnaryNot | UnaryMinus
type binOp = KwEqual | KwNEqual | Equal | NEqual | Less | Leq | Greater | Geq |
	Plus | Minus | Times | Div | Mod | Land | Lor

type classInclRelation = SubclassOf | SuperclassOf | NoClassRel

type access = 
| AccIdent of ident
| AccMember of expr * ident

and expr =
| Eint of int
| Estr of string
| Ebool of bool
| Eunit
| Ethis
| Enull
| Eaccess of access
| Eassign of access * expr
| Ecall of access * argType * expr list
| Einstantiate of ident * argType * expr list
| Eunaryop of unaryOp * expr
| Ebinop of binOp * expr * expr
| Eif of expr * expr * expr 
| Ewhile of expr * expr
| Ereturn of expr
| Eprint of expr
| Eblock of block

and blockVal = Bexpr of expr | Bvar of var
and block = blockVal list

and var =
| Vvar of ident * optType * expr
| Vval of ident * optType * expr

and typ = ident * argType
and optType = Type of typ | NoType
and argType = EmptyAType | ArgType of typ list

and meth = {
	mname : ident ;
	parTypes : paramType list ;
	mparams : parameter list ;
	retType : typ ;
	mbody : block ;
	override : bool
}
and classExtends = {
	extType : typ ;
	param : expr list }
and classDef = {
	cname : ident ;
	classTypes : paramTypeClass list ;
	cparams : parameter list ;
	extends : classExtends option; 
	cbody : decl list
}

and decl = Dvar of var | Dmeth of meth

and parameter = ident * typ
and paramType = {
	name : ident ;
	rel : classInclRelation ;
	oth : typ
}

and paramTypeModifier = TMplus | TMminus | TMneutral
and paramTypeClass = paramType * paramTypeModifier

type prgm = {
	classes : classDef list ;
	main : classDef
}

