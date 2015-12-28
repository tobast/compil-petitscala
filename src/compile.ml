
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

type dataLocation =
	| Here							(* Right where we are pointing *)
	| FollowPtr of dataLocation		(* Follow the address of the pointer *)
	| Offset of int * dataLocation	(* Add an offset *)

type classMetaDescriptor = {
	memLoc : label ; (* Location in memory *)
	methods : int SMap.t ;
		(* maps a method name to its offset in the descriptor *)
	vals : int SMap.t ;
		(* maps a field name to its offset in an allocated object on the heap*)
	clType : typedClass
}

let metaDescriptors = ref SMap.empty

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
let nextMethLabel =
	let next = ref (-1) in
	(fun () -> next := !next+1 ; (string_of_int !next))

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
 * Returns a code following a location from the address in %rdx and putting it
 * in %rdx.
 ***)
let rec followLocation = function
| Here -> nop
| FollowPtr(next) -> movq (ind rdx) (reg rdx) ++ (followLocation next)
| Offset (offset, next) -> addq (imm offset) (reg rdx) ++ (followLocation next)

(***
 * Returns assembly code that allocates a data block for an instantiation of
 * clName on the heap using sbrk. After this code is executed, the segment
 * start is found in %rax
 ***)
let allocateBlock clName =
	let cl = SMap.find clName !metaDescriptors in
	let segSize = (SMap.cardinal cl.vals + 1) * 8 in

	(movq (imm segSize) (reg rdi)) ++ (call "sbrk") ++
		(movq (ilab cl.memLoc) (ind rax))

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
	let alloc = allocateBlock "String" in
	{
		data = dataContent ;
		text = alloc ++ (movq (ilab dataLabel) (reg rcx)) ++
			(movq (reg rcx) (ind ~ofs:8 rax)) ++ (movq (reg rax) (reg rdi))
	}

| TEbool b ->
	prgmText (movq (ilab (if b then "1" else "0")) (reg rdi))
| TEunit
| TEnull ->
	prgmText (movq (ilab "0") (reg rdi))
| TEthis ->
	let ofs = SMap.find "this" env in
	prgmText ((movq (reg rbp) (reg rdx)) ++ (followLocation ofs) ++
		(movq (ind rdx) (reg rdi)))
| TEaccess acc ->
	(match acc with
	| TAccIdent idt ->
		let offset = (try SMap.find idt env
			with Not_found -> raise (InternalError ("Variable '"^idt^"' not \
				found in the current context."))
			) in
		{
			text = (movq (reg rbp) (reg rdx)) ++ (followLocation offset) ++
				(movq (ind rdx) (reg rdi));
			data = nop
		}
	| TAccMember(expr,idt) ->
		let metaDescr = SMap.find (fst expr.etyp) !metaDescriptors in
		let ofs = Offset(SMap.find idt metaDescr.vals, Here) in
		let compExpr = compileExpr expr env stackDepth in
		{
			text = compExpr.text ++ (movq (reg rdi) (reg rdx)) ++
				(followLocation ofs) ++ (movq (ind rdx) (reg rdi)) ;
			data = compExpr.data
		}
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
			text = exprComp.text ++ (movq (reg rbp) (reg rdx)) ++
				(followLocation offset) ++ (movq (reg rdi) (ind rdx)) ++
				(movq (imm 0) (reg rdi));
			data = exprComp.data
		}
	| TAccMember(accExp,idt) ->
		let metaDescr = SMap.find (fst accExp.etyp) !metaDescriptors in
		let ofs = Offset(SMap.find idt metaDescr.vals, Here) in
		let compAcc = compileExpr accExp env stackDepth in
		{
			text = exprComp.text ++ (pushq (reg rdi)) ++
				compAcc.text ++ (movq (reg rdi) (reg rdx)) ++
				(followLocation ofs) ++ (popq rdi) ++
				(movq (reg rdi) (ind rdx)) ++ (movq (imm 0) (reg rdi)) ;
			data = exprComp.data ++ compAcc.data
		}
	)
| TEcall(acc, argt, params) ->
	let thisAddr, callComp, expData = (match acc with
		| TAccIdent(idt) ->
			(raise (InternalError "Call to a TAccIdent, which is supposed to \
				be impossible."))
		| TAccMember(exp,idt) ->
			let expComp = compileExpr exp env stackDepth in
			let typ = SMap.find (fst exp.etyp) !metaDescriptors in
			let methOffset = SMap.find idt (typ.methods) in
			(expComp.text ++ (pushq (reg rdi)),
				(movq (ind rdx) (reg rdx)) ++
				(addq (imm methOffset) (reg rdx)) ++ (call_star (ind rdx)),
				expComp.data)
		) in
	
	let nbPar = List.length params in
	let stackParams,dataParams = List.fold_left (fun (curSt, curDat) ex ->
			let exComp = compileExpr ex env stackDepth in
			curSt ++ exComp.text ++ (pushq (reg rdi)), curDat ++ exComp.data)
		(nop,nop) params in
	
	let unstackParams = (addq (imm (8*(List.length params + 1))) (reg rsp)) in

	{
		text = thisAddr ++ stackParams ++
			(movq (ind ~ofs:(8*nbPar) rsp) (reg rdx)) ++
			callComp ++ unstackParams ++ (movq (reg rdi) (reg rax));
		data = expData ++ dataParams
	}

| TEinstantiate(idt, _, params) ->
	let metaDescr = SMap.find idt !metaDescriptors in
	let rec makeEvalParams cur = function
	| [],[] -> cur
	| fHead::fTail, curParam::ptail ->
			let compParam = compileExpr curParam env stackDepth in
			let offset = SMap.find (fst fHead) metaDescr.vals in
			makeEvalParams {
					text = cur.text ++ compParam.text ++ (popq rdx) ++
						(movq (reg rdi) (ind ~ofs:offset rdx)) ++
						(pushq (reg rdx)) ;
					data = cur.data ++ compParam.data
				} (fTail, ptail)
	| _,_ -> raise (InternalError ("Wrong number of parameters. What the hell \
		did the typer?!"))
	in
		
	let alloc = (allocateBlock idt) in
	let evalParams = makeEvalParams {text=nop;data=nop}
		(metaDescr.clType.tcparams, params) in

	(* To make the program behave as if `this' was the class we're building
	 in order to fill the objects' fields, we fake a function start on the
	 stack, then reference `this' as rbp-8 *)
	let chThis = (pushq (reg rbp)) ++ (movq (reg rsp) (reg rbp))
	and unchThis = (popq rbp) in
	let clEnv = SMap.singleton "this" (Offset(-8,Here)) in

	let fieldsInit = List.fold_left (fun curPrgm decl -> match decl with
			| TDmeth(_) -> curPrgm
			| TDvar(var) ->
				let compExpr = compileExpr var.vexpr clEnv stackDepth in
				let offset = SMap.find var.vname metaDescr.vals in
				{
					text = curPrgm.text ++ compExpr.text ++ (pushq (reg rdi)) ++
						(movq (ind ~ofs:(-8) rbp) (reg rdx)) ++
						(popq rdi) ++ (movq (reg rdi) (ind ~ofs:offset rdx)) ;
					data = curPrgm.data ++ compExpr.data
				}
		)
		{text = nop ; data = nop}
		metaDescr.clType.tcbody in (* Keeping the order might be necessary *)
	{
		text = alloc ++ (* Allocate *)
			(* Evaluate parameters *)
			(pushq (reg rax)) ++ evalParams.text ++ (popq rax) ++
			(* Initialize class fields *)
			chThis ++ (pushq (reg rax)) ++ fieldsInit.text ++
			(popq rax) ++ unchThis ++ (movq (reg rax) (reg rdi));
		data = evalParams.data ++ fieldsInit.data
	}

| TEunaryop(UnaryNot, exp) ->
	let exprComp = compileExpr exp env stackDepth in
	{ exprComp with
		text = exprComp.text ++ (xorq (ilab "1") (reg rdi)) }
| TEunaryop(UnaryMinus, exp) ->	
	let exprComp = compileExpr exp env stackDepth in
	{ exprComp with
		text = exprComp.text ++ (imulq (imm (-1)) (reg rdi)) }
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
		| KwEqual -> (cmpq (reg rdi) (reg rax)) ++ (setQReg sete)
		| KwNEqual -> (cmpq (reg rdi) (reg rax)) ++ (setQReg setne)
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
			(label (labelStr^"end")) ++
			(movq (imm 0) (reg rdi));
		data = condComp.data ++ codeComp.data
	}

| TEreturn exp ->
	let codeComp = compileExpr exp env stackDepth in
	{
		text =
			(* Evaluate return value *)
			codeComp.text ++ (movq (reg rdi) (reg rax)) ++
			(* Restore stack *)
			(addq (imm stackDepth) (reg rsp)) ++ (popq rbp) ++
			(* Return *)
			ret ;
		data = codeComp.data
	}
	
| TEprint exp ->
	(match fst exp.etyp with
	| "String" ->
		let regAssign,dataAssign = (match exp.tex with
			| TEstr(s) ->
				let dataLabel,dataContent = addDataString s in
				(movq (ilab dataLabel) (reg rdi)), dataContent
			| _ ->
				let compExpr = compileExpr exp env stackDepth in
				(compExpr.text ++ (movq (ind ~ofs:8 rdi) (reg rdi))),
				compExpr.data
			) in

		(* Add it to the data segment, print it. *)
		{ data = dataAssign ;
		  text = regAssign ++
		         (movq (imm 0) (reg rax)) ++
				 (call "printf") ++
				 (movq (imm 0) (reg rdi)) }
	| "Int" ->
		let exprComp = compileExpr exp env stackDepth in
		{ exprComp with
			text = exprComp.text ++
				(movq (reg rdi) (reg rsi)) ++
				(movq (imm 0) (reg rax)) ++
				(movq (ilab "printfIntFormat") (reg rdi)) ++
				(call "printf") ++
				(movq (imm 0) (reg rdi))
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
			nEnv := SMap.add (var.vname)
				(Offset ( (-(!nStackDepth)), Here)) !nEnv;
			{
				text = input.text ++ valComp.text ++
					(pushq (reg rdi)) ++
					(movq (imm 0) (reg rdi));
				data = input.data ++ valComp.data
			}
				
		)
		{text = nop ; data = nop } block
	in
	{ folded with
		text = folded.text ++
			(addq (imm (!nStackDepth-stackDepth)) (reg rsp)) (* Restore rsp *)
	}


let buildMethod meth methLab env =
	let env = ref SMap.empty in
	List.iteri (fun i par -> env := SMap.add par (Offset (16+8*i, Here)) !env)
		(List.rev ("this"::(List.map fst meth.tmparams))) ;
	let codeComp = compileExpr meth.tmbody !env 0 in
	let nText = (label methLab) ++ (pushq (reg rbp)) ++
		(movq (reg rsp) (reg rbp)) ++ codeComp.text ++ (popq rbp) ++
		(movq (reg rdi) (reg rax)) ++ ret in
	{ codeComp with text = nText }


let buildClassDescriptor cl =
	let env = SMap.empty in
	let varsLocs = let next = ref 0 in SMap.fold (fun name var prev ->
			(* Add fields as vars *)
			next := !next + 8 ;
			SMap.add name !next prev
		) cl.tcvars
		(List.fold_left (fun prev cur -> (* Add class parameters as vars *)
				next := !next + 8 ;
				SMap.add (fst cur) !next prev)
			SMap.empty cl.tcparams) in
	let methLocs,methLabels,locs,_ = SMap.fold
		(fun name _ (prevLocs,prevLbl,prevLocsLst,i) ->
			let methLab = ("M"^(nextMethLabel ())^"_"^cl.tcname^"_"^name) in
			(SMap.add name i prevLocs,
			SMap.add name methLab prevLbl,
			methLab::prevLocsLst,
			i+8)
		) cl.tcmeth (SMap.empty, SMap.empty, [], 8) in
			
	let descriptorLabel = "D_"^cl.tcname in
	let dataAdd = (label descriptorLabel) ++ (dquad [0]) ++ (*FIXME temp*)
		(address (List.rev locs))
	in

	metaDescriptors := SMap.add cl.tcname {
			memLoc = descriptorLabel ;
			methods = methLocs ;
			vals = varsLocs ;
			clType = cl
		} !metaDescriptors ;

	(* TODO inherit and preserve order *)
	let compiled = SMap.fold (fun name code prevComp ->
			let methLabel = SMap.find name methLabels in
			let methComp = buildMethod code methLabel env in
			{
				text = prevComp.text ++ methComp.text;
				data = prevComp.data ++ methComp.data
			}
		)
		cl.tcmeth ({text=nop; data=nop}) in
	
	{ compiled with data = compiled.data ++ dataAdd }

(***
 * Compiles a typed program
 ***)
let compileTypPrgm prgm =
	(* Adds the base classes the way we want them to be *)
	let mkBaseClass fields name extends =
		let dummyVar = false,("",EmptyAType) in
		{
			tcname = name ;
			tclassTypes = [];
			tcparams = [];
			textends = Some {textType = extends,EmptyAType ; tparam=[]};
			tcbody = [];
			tcvars = List.fold_left (fun cur n ->
				SMap.add n dummyVar cur) SMap.empty fields ;
			tcmeth = SMap.empty ;
			tcvariance = TMneutral
		} in
	let mkBaseClassNF = mkBaseClass [] in
	let buildClasses = [
			mkBaseClass ["data"] "String" "AnyRef"
		] @ (prgm.tclasses) @ [prgm.tmain] in

	let descriptorsComp = List.fold_left (fun prev cur ->
			let comp = buildClassDescriptor cur in
			{ text = prev.text ++ comp.text ;
			  data = prev.data ++ comp.data })
		{text=nop;data=nop} buildClasses in

	let callMainComp = compileExpr
		{ etyp=("Unit",EmptyAType) ;
		  tex = TEcall(
		  	  TAccMember(
			  { etyp=("Main",EmptyAType) ;
			    tex = TEinstantiate("Main",EmptyAType,[]) },
			  "main"),
			EmptyAType,
			[ { etyp=("",EmptyAType) ; tex=(TEint 0) } ] )
		}
		SMap.empty
		0 in

	{
		text = (glabel "main") ++
			callMainComp.text ++
			(xorq (reg rax) (reg rax)) ++ ret ++
			descriptorsComp.text;
		data = (label "printfIntFormat") ++ (string "%d") ++
			callMainComp.data ++
			descriptorsComp.data
	}

