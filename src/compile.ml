
(******************************************************************************
 * Project: pscala
 * By: Théophile Bastian <contact@tobast.fr>
 *
 * This project implements a compiler for "Petit Scala", as defined in
 * <https://www.lri.fr/~filliatr/ens/compil/projet/sujet1-v1.pdf>
 * It is developped as a school project for J-C. Filliâtre's Compilation course
 * at the Ecole Normale Superieure, Paris.
 ******************************************************************************
 * File: compile.ml
 * Compiles a typed AST.
 *****************************************************************************)

open TypedAst
open Ast
exception InternalError of string

open X86_64

(***
 * Returns a fresh new unused ID for a string label in the data block
 ***)
let nextStringId =
	let nextStringId = ref (-1) in
	(fun () ->
		nextStringId := !nextStringId + 1 ;
		("string"^(string_of_int !nextStringId)))

(***
 * Inserts a string into the program data, return both its label and the
 * assembly code.
 ***)
let addDataString s =
	let dataLabel = nextStringId () in
	(dataLabel, (label dataLabel) ++ (string s))

(***
 * Returns a program with only a text field with value t
 ***)
let prgmText t =
	{
		data = nop;
		text = t
	}

(***
 * Compiles a typed expression.
 * Until a better option is found (1st pass to assign registers to
 * intermediary calculations?), the result of an expression is stored
 * into %rdi at the end of the code returned by compileExpr.
 ***)
let rec compileExpr argExp = match argExp.tex with
| TEint n ->
	prgmText (movq (ilab (string_of_int n)) (reg rdi))
| TEstr s ->
	let dataLabel,dataContent = addDataString s in
	{
		data = dataContent ;
		text = (movq (ilab dataLabel) (reg rdi))
	}

| TEbool b ->
	prgmText (movq (ilab (if b then "1" else "0")) (reg rdi))
| TEunit
| TEnull ->
	prgmText (movq (ilab "0") (reg rdi))
| TEunaryop(UnaryNot, exp) ->
	let exprComp = compileExpr exp in
	{ exprComp with
		text = exprComp.text ++ (xorq (ilab "1") (reg rdi)) }
| TEunaryop(UnaryMinus, exp) ->	
	let exprComp = compileExpr exp in
	{ exprComp with
		text = exprComp.text ++ (subq (ilab "0") (reg rdi)) }
| TEbinop(op,exp1, exp2) ->
	let exprComp1 = compileExpr exp1
	and exprComp2 = compileExpr exp2 in
	let preOp = {
		text = exprComp1.text ++
			pushq (reg rdi) ++
			exprComp2.text ++ (* Result of exp2 is in rdi *)
			popq rax (* Result of exp1 is on rax *)
			;
		data = exprComp1.data ++ exprComp2.data
	} in

	let opAction = (match op with
		(* Arithmetic *)
		| Plus -> addq (reg rax) (reg rdi)
		| Minus -> subq (reg rax) (reg rdi)
		| Times -> imulq (reg rax) (reg rdi)
		| Div ->
			(movq (ilab "0") (reg rdx)) ++ (idivq (reg rdi)) ++
			(movq (reg rax) (reg rdi))
		| Mod ->
			(movq (ilab "0") (reg rdx)) ++ (idivq (reg rdi)) ++
			(movq (reg rdx) (reg rdi))
		(* Logical *)
		| KwEqual -> (*TODO*) assert false
		| KwNEqual -> (*TODO*) assert false
		| Equal -> (*TODO*) assert false
		| NEqual -> (*TODO*) assert false
		| Less -> (*TODO*) assert false
		| Leq -> (*TODO*) assert false
		| Greater -> (*TODO*) assert false
		| Geq -> (*TODO*) assert false
		| Land -> (*TODO*) assert false
		| Lor -> (*TODO*) assert false
	) in

	{ preOp with text = preOp.text ++ opAction }

| TEprint exp ->
	(match fst exp.etyp with
	| "String" ->
		let explicitStr = (match exp.tex with
			| TEstr(s) -> s
			| _ -> raise (InternalError "Expected a litteral string.")) in

		let dataLabel,dataContent = addDataString explicitStr in
		(* Add it to the data segment, print it. *)
		{ data = dataContent ;
		  text = (movq (ilab dataLabel) (reg rdi)) ++
		         (movq (ilab "0") (reg rax)) ++
				 (call "printf") }
	| "Int" ->
		let exprComp = compileExpr exp in
		{ exprComp with
			text = exprComp.text ++
				(movq (reg rdi) (reg rsi)) ++
				(movq (ilab "0") (reg rax)) ++
				(movq (ilab "printfIntFormat") (reg rdi)) ++
				(call "printf")
		}
	| _ ->
		raise (InternalError "Request print of a non-String and non-Integer \
			typed value")
	)
| TEblock block ->
	List.fold_left (fun input cur -> match cur with
		| TBexpr exp ->
			let cPrgm = compileExpr exp in
			{ text = input.text ++ cPrgm.text ;
			  data = input.data ++ cPrgm.data }
		| TBvar var -> assert false
		)
		{text = nop ; data = nop } block
| _ ->
	assert false


(***
 * Wraps the given program, to add some base code to it
 ***)
let wrapPrgm prgm =
	{
		text=(glabel "main") ++ prgm.text ++ 
			(movq (ilab "0") (reg rax)) ++ ret;
		data=(label "printfIntFormat") ++ (string "%d") ++ prgm.data
	}

(***
 * Compiles a typed program
 ***)
let compileTypPrgm prgm =
	(* For now, only compiles the main method (TODO)*)
	let compiled = compileExpr ((Ast.SMap.find "main" prgm.tmain.tcmeth).tmbody)
	in

	wrapPrgm compiled

