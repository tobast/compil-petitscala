(******************************************************************************
 * Project: pscala
 * By: Théophile Bastian <contact@tobast.fr>
 *
 * This project implements a compiler for "Petit Scala", as defined in
 * <https://www.lri.fr/~filliatr/ens/compil/projet/sujet1-v1.pdf>
 * It is developped as a school project for J-C. Filliâtre's Compilation course
 * at the Ecole Normale Superieure, Paris.
 ******************************************************************************
 * File: astPrinter.ml
 *
 * Pretty printing of an AST
 *****************************************************************************)

open Ast
open Format
open Lexing

let printPos ppf pos =
	fprintf ppf "%d:%d" (pos.pos_lnum) (pos.pos_cnum)

let strOfUnaryOp = function
| UnaryNot -> "!"
| UnaryMinus -> "-"

let strOfBinOp = function
| KwEqual -> "eq"
| KwNEqual -> "ne"
| Equal -> "=="
| NEqual -> "!="
| Less -> "<"
| Leq -> "<="
| Greater -> ">"
| Geq -> ">="
| Plus -> "+"
| Minus -> "-"
| Times -> "*"
| Div -> "/"
| Mod -> "%"
| Land -> "&&"
| Lor -> "||"

let rec print_expr ppf  exp= 
	let doPrint = function
	| Eint(n) -> fprintf ppf "%d" n
	| Estr(s) -> fprintf ppf "%s" s
	| Ebool(b) -> fprintf ppf "%s" (if b then "true" else "false")
	| Eunit -> fprintf ppf "()"
	| Enull -> fprintf ppf "null"
	| Ethis -> fprintf ppf "this"
	| Eaccess(acc) -> print_access ppf acc
	| Eassign(acc,exp) ->
		fprintf ppf "%a = %a" print_access acc print_expr exp
	| Ecall(acc,argt,elist) ->
		fprintf ppf "%a [%a](%a)" print_access acc print_argt argt
			printExpList elist
	| Einstantiate(idt,argt,elist) -> 
		fprintf ppf "new %s [%a](%a)" idt print_argt argt printExpList elist
	| Eunaryop(uop,exp) ->
		fprintf ppf "%s%a" (strOfUnaryOp uop) print_expr exp
	| Ebinop(bop,ex1,ex2) ->
		fprintf ppf "%a %s %a" print_expr ex1 (strOfBinOp bop) print_expr ex2
	| Eif(ex1,ex2,ex3) ->
		fprintf ppf "if%a %a else %a" print_expr ex1 print_expr ex2
			print_expr ex3
	| Ewhile(ex1,ex2) ->
		fprintf ppf "while %a %a" print_expr ex1 print_expr ex2
	| Ereturn(exp) -> 
		fprintf ppf "return %a" print_expr exp
	| Eprint(exp) -> 
		fprintf ppf "print %a" print_expr exp
	| Eblock(blk) -> 
		fprintf ppf "{ %a }" print_block blk
	in

	fprintf ppf "[%a](" printPos exp.eloc.loc_beg;
	doPrint exp.ex ;
	fprintf ppf ")[%a]" printPos exp.eloc.loc_end

and printExpList ppf = function
| [] -> ()
| [hd] -> print_expr ppf hd
| hd::tl -> fprintf ppf "%a, %a" print_expr hd printExpList tl

and print_access ppf = function
| AccIdent(idt) -> fprintf ppf "%s" idt
| AccMember(exp,idt) -> fprintf ppf "%a.%s" print_expr exp idt

and print_block ppf = function
| [] -> ()
| [hd] -> print_blockVal ppf hd
| hd::tl -> fprintf ppf "%a ; %a" print_blockVal hd print_block tl

and print_blockVal ppf = function
| Bexpr(exp) -> print_expr ppf exp
| Bvar(v) -> print_var ppf v

and print_var ppf v = match v.v with
| Vvar(idt,ot,exp) ->
	fprintf ppf "var %s%a = %a" idt print_optType ot print_expr exp
| Vval(idt,ot,exp) -> 
	fprintf ppf "val %s%a = %a" idt print_optType ot print_expr exp

and print_optType ppf = function
| Type(t) -> fprintf ppf "[%a]" print_type t
| NoType -> ()

and print_type ppf (idt,argt) =
	fprintf ppf "%s%a" idt print_argt argt

and print_argt ppf = function
| EmptyAType -> ()
| ArgType(lst) ->
	let rec doPrint = function
	| [] -> ()
	| [hd] -> print_type ppf hd
	| hd::tl -> fprintf ppf "%a, " print_type hd ; doPrint tl
	in
	fprintf ppf "["; doPrint lst ; fprintf ppf "]"
