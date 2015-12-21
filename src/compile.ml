
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
 * Compiles a typed expression.
 ***)
let rec compileExpr argExp = match argExp.tex with
| TEprint exp ->
	(match fst exp.etyp with
	| "String" ->
		let dataLabel = nextStringId () in
		let explicitStr = (match exp.tex with
			| TEstr(s) -> s
			| _ -> raise (InternalError "Expected a litteral string.")) in
		(* Add it to the data segment, print it. *)
		{ data = (label dataLabel) ++ (string explicitStr) ;
		  text = (movq (ilab dataLabel) (reg rdi)) ++
		         (movq (ilab "0") (reg rax)) ++
				 (call "printf") }
	| _ ->
		assert false)
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
 * Compiles a typed program
 ***)
let compileTypPrgm prgm =
	(* For now, only compiles the main method (TODO)*)
	let compiled = compileExpr ((Ast.SMap.find "main" prgm.tmain.tcmeth).tmbody)
	in

	{ compiled with text = (glabel "main") ++ compiled.text }
