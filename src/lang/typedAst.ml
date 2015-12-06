(******************************************************************************
 * Project: pscala
 * By: Théophile Bastian <contact@tobast.fr>
 *
 * This project implements a compiler for "Petit Scala", as defined in
 * <https://www.lri.fr/~filliatr/ens/compil/projet/sujet1-v1.pdf>
 * It is developped as a school project for J-C. Filliâtre's Compilation course
 * at the Ecole Normale Superieure, Paris.
 ******************************************************************************
 * File: typedAst.ml
 *
 * Defines the AST for Petit Scala, after expressions typing.
 *****************************************************************************)

open Ast (* We don't want to redefine *everything*, a lot is still working. *)

type typAccess =
| TAccIdent of ident
| TAccMember of typExpr * ident

and typExpr = { tex : typExprVal ; etyp : typ }

and typExprVal =
| TEint of int
| TEstr of string
| TEbool of bool
| TEunit
| TEthis
| TEnull
| TEaccess of typAccess
| TEassign of typAccess * typExpr
| TEcall of typAccess * argType * typExpr list
| TEinstantiate of ident * argType * typExpr list
| TEunaryop of unaryOp * typExpr
| TEbinop of binOp * typExpr * typExpr
| TEif of typExpr * typExpr * typExpr 
| TEwhile of typExpr * typExpr
| TEreturn of typExpr
| TEprint of typExpr
| TEblock of typBlock

and typBlockVal = TBexpr of typExpr | TBvar of typVar
and typBlock = typBlockVal list

and varType = bool (* Mutable? *) * typ

and typVar = {
	vname : ident ;
	vtyp : varType ;
	vexpr : typExpr
}

and typMeth = {
	tmname : ident;
	tparTypes : paramType list ;
	tmparams : parameter list ;
	tretTyp : typ ;
	tmbody : typExpr ;
	toverride : bool
}

and typClassExtends = {
	textType : typ ;
	tparam : typExpr list
}
and typedClass = {
	tcname: ident ;
	tclassTypes : paramTypeClass list ;
	tcparams : parameter list ;
	textends : typClassExtends option ;
	tcbody : typDecl list ;
	tcvars : varType SMap.t ;
	tcmeth : typMeth SMap.t ;
	tcvariance : paramTypeModifier
}
and typDecl = TDvar of typVar | TDmeth of typMeth

and typPrgm = {
	tclasses : typedClass list ;
	tmain : typedClass ;
	tenvironment : typingEnvironment
}

and typingEnvironment = {
	suptypeDecl : (typ list) SMap.t ;
	classes : typedClass SMap.t ;
	vars : varType SMap.t
}
