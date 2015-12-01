(******************************************************************************
 * Project: pscala
 * By: Théophile Bastian <contact@tobast.fr>
 *
 * This project implements a compiler for "Petit Scala", as defined in
 * <https://www.lri.fr/~filliatr/ens/compil/projet/sujet1-v1.pdf>
 * It is developped as a school project for J-C. Filliâtre's Compilation course
 * at the Ecole Normale Superieure, Paris.
 ******************************************************************************
 * File: typer.ml
 *
 * Deduces and checks types consistency
 *****************************************************************************)

open Ast
open Typedefs

exception InternalError of string
exception TyperError of codeLoc * string

let findClass cl env =
	try SMap.find cl env.classes
	with Not_found -> raise (InternalError ("Class "^cl^" was not found in "^
		"the environment, yet the program was previously checked."))

let rec dispType ty =
	(fst ty)^
	(match snd ty with
	| ArgType(hd::tl) ->
		"["^(List.fold_left (fun cur ty -> cur^","^(dispType ty))
			(dispType hd) tl)^"]"
	| _ -> "")

(***
 * Raises a TyperError exception indicating that expType was expected instead
 * of actType at location loc
 ***)
let wrongTypeError loc actTyp expTyp =
	raise (TyperError (loc,("This expression has type "^(dispType actTyp)^
		", but type "^(dispType expTyp)^" was expected.")))

(***
* Checks that the class cl1 is "an arrow of" the class cl2, ie. that cl2
* extends (even indirectly) cl1
***)
let rec isArrow env cl1 cl2 =
	let baseClasses = [ "Nothing"; "Unit"; "Int"; "Boolean"; "Null";
		"String"; "AnyVal"; "AnyRef"; "Any" ] in
	let baseArrows = [
		("Unit", "AnyVal") ;
		("Int", "AnyVal") ;
		("Boolean", "AnyVal") ;
		("String", "AnyRef" ) ;
		("AnyVal", "Any") ;
		("AnyRef", "Any")
	]  in

	let userDefined cl = List.mem cl baseClasses in
	let arrowOf cl =
		if userDefined cl then
			let clDef = findClass cl env in
			(match clDef.extends with
			| None -> "AnyRef"
			| Some cl -> fst cl.extType)

		else
			let elem =  (try List.find (fun k -> fst k = cl) baseArrows
				with Not_found -> assert false (* Unreachable? *))
			in snd elem
	in

	if cl1 = cl2 then (* The arrow relation is reflexive *)
		true
	else if userDefined cl1 then begin (* cl1 is NOT user-defined *)
		if cl1 = "Nothing" then
			true
		else if cl1 = "Any" then
			false (* We have already checked that cl1 != cl2 *)
		else if cl1 = "Null" then
			cl2 = "String" || (userDefined cl2)
		else
			(List.mem (cl1,cl2) baseArrows) || (isArrow env (arrowOf cl1) cl2)
	end else (* cl1 IS user-defined *)
		let arr = arrowOf cl1 in
		(arr = cl2) || (isArrow env arr cl2)

(***
 * Checks that ty1 is a subtype of ty2 in the environment env
 ***)
let rec isSubtype env ty1 ty2 =
	if fst ty1 = "Nothing" then (* Nothing -> every other class *)
		true
	else if (fst ty1 = "Null") && (isArrow env "Null" (fst ty2)) then
		(* When the class is supertype of null, substituting its parameters
		keeps it supertype of null *)
		true
	else if fst ty1 = fst ty2 then
		(* If we compare identical types, we only have to check that ty1
		parameters are sub/supertypes of ty2 parameters according to the
		variance *)
		let rec chkVariance formal lt1 lt2 = match formal,lt1,lt2 with
		| [],[],[] -> true
		| [],_,_ | _,[],_ | _,_,[] ->
			raise (InternalError ("Encountered types with not enough/too much"^
				" argument types."))
		| fhd::ftl, pty1::l1tl, pty2::l2tl  ->
			let cParam = (match snd fhd with
			| TMplus -> isSubtype env pty1 pty2
			| TMminus -> isSubtype env pty2 pty1
			| TMneutral -> pty1 = pty2
			) in
			if cParam
				then chkVariance ftl l1tl l2tl
				else false
		in
		(match (snd ty1, snd ty2) with
		| EmptyAType, EmptyAType -> true
		| EmptyAType,ArgType _ | ArgType _, EmptyAType -> 
			raise (InternalError ("Encountered types with not enough/too much"^
				" argument types."))
		| ArgType tl1, ArgType tl2 ->
			chkVariance (findClass (fst ty1) env).classTypes tl1 tl2
		)
	else if (not (isArrow env (fst ty1) (fst ty2))) then
		(* If C1 -/-> C2 *)
		try
			let suptyps = SMap.find (fst ty2) env.suptypeDecl in
			let _ = List.find (fun ty -> isSubtype env ty1 ty) suptyps in
			true
		with Not_found ->
			false
	else (* If C1 extends C[..], C -> C2 *)
		let extCl = (match (findClass (fst ty1) env).extends with
			| None -> { extType = ("AnyRef",EmptyAType) ; param = [] }
			| Some t -> t) in
		let extName = fst (extCl.extType) in
		if isArrow env extName (fst ty2) then begin
			match (snd extCl.extType) with
			| EmptyAType -> isSubtype env extCl.extType ty2
			| ArgType(at1) ->
				let typlist = List.rev (List.fold_left
					(fun cur ex -> (exprType env ex)::cur) [] extCl.param) in
				let nty1 = (extName, ArgType typlist) in
				isSubtype env nty1 ty2
		end else
			false

and exprType env exp = match exp.ex with
| Eint _ -> "Int",EmptyAType
| Estr _ -> "String",EmptyAType
| Ebool _ -> "Boolean",EmptyAType
| Eunit -> "Unit",EmptyAType
| Enull  -> "Null",EmptyAType
| Ethis ->
	let _,_,t = (try List.find (fun k -> match k with
			| AccIdent("this"),false,_ -> true
			| _ -> false) env.vars
		with Not_found -> raise (InternalError ("Value `this' was not "^
			"declared in this context."))) in
	t
| Eaccess(AccIdent(id)) ->
	let _,_,t = (try List.find (fun k -> match k with
			| id,_,_ -> true
			| _ -> false) env.vars
		with Not_found -> (* TODO
			(AccIdent("dummy"),false,
				exprType env (Eaccess(AccMember(Ethis, id))))*)
			assert false ) in
	t
| Eaccess(AccMember(exp,id)) ->
	let subTyp = exprType env exp in
	assert false (*TODO implement*)
	(*
		with Not_found -> raise (TyperError exp.eloc ("Variable `"^id^"' was "^
			"not declared in this scope."))) in
	t*)
| Eunaryop(UnaryNot, ex) ->
	let exTyp = exprType env ex in
	if fst exTyp = "Boolean" then
		exTyp
	else
		wrongTypeError exp.eloc exTyp ("Boolean",EmptyAType)
| Eunaryop(UnaryMinus, ex) ->
	let exTyp = exprType env ex in
	if fst exTyp = "Int" then
		exTyp
	else
		wrongTypeError exp.eloc exTyp ("Int",EmptyAType)
| Ebinop(op,ex1,ex2) ->
	let tex1 = exprType env ex1 and tex2 = exprType env ex2 in
	(match op with
	| KwEqual | KwNEqual ->
		if not (isSubtype env tex1 ("AnyRef",EmptyAType)) then
			wrongTypeError ex1.eloc tex1 ("AnyRef",EmptyAType)
		else if not (isSubtype env tex2 ("AnyRef",EmptyAType)) then
			wrongTypeError ex2.eloc tex2 ("AnyRef",EmptyAType)
		else
			("Boolean", EmptyAType)
	| Equal | NEqual | Greater | Geq | Less | Leq ->
		if not (fst tex1 = "Int") then
			wrongTypeError ex1.eloc tex1 ("Int", EmptyAType)
		else if not (fst tex2 = "Int") then
			wrongTypeError ex2.eloc tex2 ("Int", EmptyAType)
		else
			("Boolean", EmptyAType)
	| Plus | Minus | Times | Div | Mod ->
		if not (fst tex1 = "Int") then
			wrongTypeError ex1.eloc tex1 ("Int", EmptyAType)
		else if not (fst tex2 = "Int") then
			wrongTypeError ex2.eloc tex2 ("Int", EmptyAType)
		else
			("Int", EmptyAType)
	| Land | Lor ->
		if not (fst tex1 = "Boolean") then
			wrongTypeError ex1.eloc tex1 ("Boolean", EmptyAType)
		else if not (fst tex2 = "Boolean") then
			wrongTypeError ex2.eloc tex2 ("Boolean", EmptyAType)
		else
			("Boolean", EmptyAType)
	)
| Eprint(ex) ->
	let tex = exprType env ex in
	if (fst tex <> "String") && (fst tex <> "Int") then
		wrongTypeError ex.eloc tex ("String or Int",EmptyAType) (* Bweark. *)
	else
		("Unit", EmptyAType)
| Eif(cnd,exIf,exElse) ->
	let tCnd = exprType env cnd and tIf = exprType env exIf
	and tElse = exprType env exElse in
	if fst tCnd <> "Boolean" then
		wrongTypeError cnd.eloc tCnd ("Boolean", EmptyAType)
	else if isSubtype env tIf tElse then
		tElse
	else if isSubtype env tElse tIf then
		tIf
	else
		raise (TyperError (exp.eloc,("If statement has type "^(dispType tIf)^
			", but else statement has type "^(dispType tElse)^". Cannot unify"^
			" this as one of those types.")))
| Ewhile(cnd,code) ->
	let tCnd = exprType env cnd and tCode = exprType env code in
	if fst tCnd <> "Boolean" then
		wrongTypeError cnd.eloc tCnd ("Boolean", EmptyAType)
	else
		("Unit",EmptyAType)

