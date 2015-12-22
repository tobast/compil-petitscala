
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

let nextIfId =
	let next = ref (-1) in
	(fun () -> next := !next+1 ; "L"^(string_of_int !next)^"_")
let nextWhileId =
	let next = ref (-1) in
	(fun () -> next := !next+1 ; "L"^(string_of_int !next)^"_while")

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
let rec compileExpr argExp env stackDepth = match argExp.tex with
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
| TEaccess acc ->
	(match acc with
	| TAccIdent idt ->
		let offset = (try SMap.find idt env
			with Not_found -> raise (InternalError ("Variable '"^idt^"' not \
				found in the current context."))
			) in
		{
			text = (movq (ind ~ofs:offset rbp) (reg rdi));
			data = nop
		}
	| TAccMember(expr,idt) -> assert false
	)
| TEassign(acc, exp) ->
	let exprComp = compileExpr exp env stackDepth in
	(match acc with
	| TAccIdent idt ->
		let offset = (try SMap.find idt env
			with Not_found -> raise (InternalError ("Variable '"^idt^"' not \
				found in the current context."))
			) in
		{
			text = exprComp.text ++ (movq (reg rdi) (ind ~ofs:offset rbp)) ;
			data = exprComp.data
		}
	| TAccMember(accExp,idt) ->
		assert false
	)
| TEunaryop(UnaryNot, exp) ->
	let exprComp = compileExpr exp env stackDepth in
	{ exprComp with
		text = exprComp.text ++ (xorq (ilab "1") (reg rdi)) }
| TEunaryop(UnaryMinus, exp) ->	
	let exprComp = compileExpr exp env stackDepth in
	{ exprComp with
		text = exprComp.text ++ (subq (ilab "0") (reg rdi)) }
| TEbinop(op,exp1, exp2) ->
	let exprComp1 = compileExpr exp1 env stackDepth
	and exprComp2 = compileExpr exp2 env stackDepth in
	let preOp = {
		text = exprComp1.text ++
			pushq (reg rdi) ++
			exprComp2.text ++ (* Result of exp2 is in rdi *)
			popq rax (* Result of exp1 is on rax *)
			;
		data = exprComp1.data ++ exprComp2.data
	} in

	let setQReg setter = (setter (reg al)) ++ (movzbq (reg al) rdi) in

	let opAction = (match op with
		(* Arithmetic *)
		| Plus -> addq (reg rax) (reg rdi)
		| Minus -> (subq (reg rdi) (reg rax)) ++ (movq (reg rax) (reg rdi))
		| Times -> imulq (reg rax) (reg rdi)
		| Div ->
			(movq (ilab "0") (reg rdx)) ++ (idivq (reg rdi)) ++
			(movq (reg rax) (reg rdi))
		| Mod ->
			(movq (ilab "0") (reg rdx)) ++ (idivq (reg rdi)) ++
			(movq (reg rdx) (reg rdi))
		(* Logical *)
		(* Use the setcc functions! *)
		| KwEqual -> (*TODO*) assert false
		| KwNEqual -> (*TODO*) assert false
		| Equal -> (cmpq (reg rdi) (reg rax)) ++ (setQReg sete)
		| NEqual -> (cmpq (reg rdi) (reg rax)) ++ (setQReg setne)
		| Less -> (cmpq (reg rdi) (reg rax)) ++ (setQReg setl)
		| Leq -> (cmpq (reg rdi) (reg rax)) ++ (setQReg setle)
		| Greater -> (cmpq (reg rdi) (reg rax)) ++ (setQReg seta)
		| Geq -> (cmpq (reg rdi) (reg rax)) ++ (setQReg setae)
		| Land -> andq (reg rax) (reg rdi)
		| Lor -> orq (reg rax) (reg rdi)
	) in

	{ preOp with text = preOp.text ++ opAction }

| TEif(cond,expIf,expElse) ->
	let labelStr = nextIfId () in
	let condComp = compileExpr cond env stackDepth in
	let ifComp = compileExpr expIf env stackDepth
	and elseComp = compileExpr expElse env stackDepth in
	let ifTxt = ifComp.text ++ (jmp (labelStr^"end"))
	and elseTxt = (label (labelStr^"else")) ++ elseComp.text in

	{
		text = condComp.text ++ (cmpq (ilab "0") (reg rdi)) ++ 
			(jz (labelStr^"else")) ++
			ifTxt ++ elseTxt ++ (label (labelStr^"end")) ;
		data = condComp.data ++ ifComp.data ++ elseComp.data
	}

| TEwhile(cond,code) ->
	let labelStr = nextWhileId () in
	let condComp = compileExpr cond env stackDepth
	and codeComp = compileExpr code env stackDepth in
	
	{
		text = (label (labelStr^"while")) ++ (condComp.text) ++
			(cmpq (ilab "0") (reg rdi)) ++ (jz (labelStr^"end")) ++
			codeComp.text ++ (jmp (labelStr^"while")) ++
			(label (labelStr^"end")) ;
		data = condComp.data ++ codeComp.data
	}
	
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
		let exprComp = compileExpr exp env stackDepth in
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
	let nStackDepth = ref stackDepth in
	let nEnv = ref env in
	let folded = List.fold_left (fun input cur -> match cur with
		| TBexpr exp ->
			let cPrgm = compileExpr exp !nEnv !nStackDepth in
			{
				text = input.text ++ cPrgm.text ;
				data = input.data ++ cPrgm.data
			}
		| TBvar var ->
			let valComp = compileExpr var.vexpr !nEnv !nStackDepth in
			nStackDepth := !nStackDepth + 8;
			nEnv := SMap.add (var.vname) (-(!nStackDepth)) !nEnv;
			{
				text = input.text ++ valComp.text ++
					(subq (imm 8) (reg rsp)) ++
					(movq (reg rdi) (ind ~ofs:(-(!nStackDepth)) rbp)) ;
				data = input.data ++ valComp.data
			}
				
		)
		{text = nop ; data = nop } block
	in
	{ folded with
		text = folded.text ++
			(addq (imm (!nStackDepth-stackDepth)) (reg rsp)) (* Restore rsp *)
	}
| _ ->
	assert false


(***
 * Wraps the given program, to add some base code to it
 ***)
let wrapPrgm prgm =
	{
		text=(glabel "main") ++ (movq (reg rsp) (reg rbp)) ++ prgm.text ++ 
			(movq (ilab "0") (reg rax)) ++ ret;
		data=(label "printfIntFormat") ++ (string "%d") ++ prgm.data
	}

(***
 * Compiles a typed program
 ***)
let compileTypPrgm prgm =
	(* For now, only compiles the main method (TODO)*)
	let compiled = compileExpr
		((Ast.SMap.find "main" prgm.tmain.tcmeth).tmbody)
		SMap.empty
		0
	in

	wrapPrgm compiled

