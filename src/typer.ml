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
open TypedAst
open Lexing

exception InternalError of string
exception TyperError of codeLoc * string

let classExists env clName refLoc =
	if not (SMap.mem clName env.classes) then
		raise (TyperError (refLoc, "The class `"^clName^"' referenced here "^
			"is not defined."))

let findClass cl env reqLoc =
	try SMap.find cl env.classes
	with Not_found -> raise (TyperError (reqLoc, "Class "^cl^", requested "^
		"from here, was not found in the environment."))

let rec dispType ty =
	(fst ty)^
	(match snd ty with
	| ArgType(hd::tl) ->
		"["^(List.fold_left (fun cur ty -> cur^","^(dispType ty))
			(dispType hd) tl)^"]"
	| _ -> "")

let dummyLoc =
	let l=({pos_fname=""; pos_lnum=0; pos_bol=0; pos_cnum=0} : Lexing.position)
	in {loc_beg=l ; loc_end=l}

(***
 * Used to ensure that types/parameters/... have distinct names.
 * Returns false iff each element is distinct from the others in l
 ***)
let rec hasDoubleElem l =
	let rec appearsAhead e = function
	| [] -> false
	| hd::tl -> if hd = e then true else appearsAhead e tl
	in

	match l with
	| [] -> false
	| hd::tl -> if appearsAhead hd tl then true else hasDoubleElem tl
	

(***
 * Raises a TyperError exception indicating that expType was expected instead
 * of actType at location loc
 ***)
let wrongTypeError loc actTyp expTyp =
	raise (TyperError (loc,("This expression has type "^(dispType actTyp)^
		", but type "^(dispType expTyp)^" was expected.")))

(***
 * Replaces the type `genericType', which may contain parameter types from
 * the class `fst clTyp', with the real type obtained by substituting every
 * local type by its type passed as argument of `clTyp'
 ***)
let rec substClassTypes env clTyp loc genericType =
	match snd clTyp with
	| EmptyAType -> genericType
	| ArgType(clParams) ->
		let classDef = findClass (fst clTyp) env loc in
		let rec doSubst clTy par = match (clTy,par) with
		| [],[] ->
			(* If it was not a class type, substitute deeper *)
			let selfSubst = substClassTypes env clTyp loc in
			(fst genericType, (match (snd genericType) with
					| EmptyAType -> EmptyAType
					| ArgType(t) -> ArgType(List.map selfSubst t)))
		| [],_ | _,[] -> raise (TyperError (loc, "Class "^(fst clTyp)^" was "^
			"passed more/less types than expected."))
		| (fpar::_, rpar::_) when (fst genericType = (fst fpar).name) -> rpar
		| _::ftl, _::rtl -> doSubst ftl rtl
		in
		doSubst classDef.tclassTypes clParams

(***
 * Replaces the type `genericType', which may contain parameter types from
 * the method `meth', with the real type obtained by substituting every
 * local type by its type passed as argument of `meth' in `argTy'
 ***)
let rec substMethTypes env meth argTy loc genericType =
	match argTy with
	| EmptyAType -> genericType
	| ArgType(methPar) ->
		let rec doSubst methPa par = match (methPa,par) with
		| [],[] ->
			(* If it was not a class type, substitute deeper *)
			let selfSubst = substMethTypes env meth argTy loc in
			(fst genericType, (match (snd genericType) with
					| EmptyAType -> EmptyAType
					| ArgType(t) -> ArgType(List.map selfSubst t)))
		| [],_|_,[] -> raise (TyperError (loc, "Method "^(meth.tmname)^" was "^
			"passed more/less types than expected."))
		| (fpar::_,rpar::_) when (fst genericType = fpar.name) -> rpar
		| _::ftl,_::rtl -> doSubst ftl rtl
		in
		doSubst meth.tparTypes methPar

let addSuptypeDecl env tname ty =
	let cList = (try SMap.find tname env.suptypeDecl with Not_found -> []) in
	let nMap = SMap.add tname (ty::cList) env.suptypeDecl in
	{env with suptypeDecl = nMap }
let addClass env clName cl =
	let nCls = SMap.add clName cl (env.classes) in
	{env with classes = nCls}
let addVar env vName var =
	let nVars = SMap.add vName var env.vars in
	{env with vars = nVars }
let classAddVar cl vName var =
	let nVars = SMap.add vName var cl.tcvars in
	{ cl with tcvars = nVars }
let addMeth cl mName mVal =
	let nMeth = SMap.add mName mVal cl.tcmeth in
	{ cl with tcmeth = nMeth }


(***
 * Given a position type (positive/negative), checks that the given type
 * is legal at the given code position. Throws an exception otherwise.
 ***)
let rec checkVariance env ty posType loc =
	let getTypeVariance ty =
		let cl = findClass (fst ty) env loc in
		cl.tcvariance
	in
	let invVariance = function
	| TMplus -> TMminus
	| TMminus -> TMplus
	| TMneutral -> TMneutral
	in
	let rec recurseVariance real formal = match (real,formal) with
	| [],[] -> ()
	| [],_|_,[] -> raise (TyperError (loc, "Got more/less type parameters "^
						"than expected for class "^(fst ty)^"."))
	| rhd::rtl, fhd::ftl ->
		(match (snd fhd) with
		| TMneutral -> checkVariance env rhd TMneutral loc
		| TMplus -> checkVariance env rhd posType loc
		| TMminus -> checkVariance env rhd (invVariance posType) loc) ;
		recurseVariance rtl ftl
	in

	let tyVariance = getTypeVariance ty in

	if tyVariance <> TMneutral then (
		if tyVariance <> posType then (
			let posTypStr = (match posType with
				| TMplus -> "positive"
				| TMminus -> "negative"
				| TMneutral -> "neutral") in
			let tyVarStr = (match tyVariance with
				| TMplus -> "covariant"
				| TMminus -> "contravariant"
				| TMneutral -> assert false (*unreachable*) ) in
			raise (TyperError (loc, "This expression has type "^(dispType ty)^
				" and is in a "^posTypStr^" position, yet it is "
				^tyVarStr^"."))
			)

		);

	(match snd ty with
	| EmptyAType -> ()
	| ArgType(t) -> 
		let cl = findClass (fst ty) env loc in
		recurseVariance t cl.tclassTypes)

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

	let userDefined cl = not( List.mem cl baseClasses) in
	let arrowOf cl =
		if userDefined cl then
			let clDef = (try findClass cl env dummyLoc
				with TyperError(_) -> 
					raise (InternalError ("Requested arrow of nonexistent "^
						"class "^cl^"."))) in
			(match clDef.textends with
			| None -> "AnyRef"
			| Some cl -> fst cl.textType)

		else
			let elem =  (try List.find (fun k -> fst k = cl) baseArrows
				with Not_found ->
					raise (InternalError ("Couldn't find "^cl^
						" in base arrows.")))
			in snd elem
	in

	if cl1 = cl2 then (* The arrow relation is reflexive *)
		true
	else if not (userDefined cl1) then begin (* cl1 is NOT user-defined *)
		if cl1 = "Nothing" then
			true
		else if cl1 = "Any" then
			false (* We have already checked that cl1 != cl2 *)
		else if cl1 = "Null" then
			cl2 = "String" || (userDefined cl2) || (isArrow env "AnyRef" cl2)
		else
			(List.mem (cl1,cl2) baseArrows) || (isArrow env (arrowOf cl1) cl2)
	end else (* cl1 IS user-defined *)
		let arr = arrowOf cl1 in
		(arr = cl2) || (isArrow env arr cl2)

(***
 * Checks that ty1 is a subtype of ty2 in the environment env
 ***)
let rec isSubtype env ty1 loc1 ty2 =
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
			let pty1=dispType ty1 and pty2 = dispType ty2 in
			raise (InternalError ("Encountered types with not enough/too much"^
				" argument types: "^pty1^" ; "^pty2^"."))
		| fhd::ftl, pty1::l1tl, pty2::l2tl  ->
			let cParam = (match snd fhd with
			| TMplus -> isSubtype env pty1 loc1 pty2
			| TMminus -> isSubtype env pty2 loc1 pty1
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
			chkVariance (findClass (fst ty1) env loc1).tclassTypes tl1 tl2
		)
	else (* If C1 extends C[..], C -> C2 *) (
		let extCl = (match (findClass (fst ty1) env loc1).textends with
			| None -> { textType = ("AnyRef",EmptyAType) ; tparam = [] }
			| Some t -> t) in
		let extName = fst (extCl.textType) in
		if isArrow env extName (fst ty2) then begin
			(*
			match (snd extCl.extType) with
			| EmptyAType -> dbgRec 3 ;isSubtype env extCl.extType loc1 ty2
			| ArgType(at1) ->
				let typlist = List.rev (List.fold_left
					(fun cur ex -> (exprType env ex)::cur) [] extCl.param) in
				let nty1 = (extName, ArgType typlist) in
				dbgRec 4 ; isSubtype env nty1 loc1 ty2
			*)
			let nty1 = (extName, (match snd extCl.textType with
				| EmptyAType -> EmptyAType
				| ArgType(at) -> ArgType(
					List.map (substClassTypes env ty1 loc1) at)))
			in
			isSubtype env nty1 loc1 ty2
		end
		else if (not (isArrow env (fst ty1) (fst ty2))) then (
			(* If C1 -/-> C2 *)
			try
				let suptyps = SMap.find (fst ty2) env.suptypeDecl in
				ignore
					(List.find (fun ty -> isSubtype env ty1 loc1 ty) suptyps);
				true
			with Not_found ->
				false)
		else
			false)


(***
 * Checks that the substitution of type parameters formal -> real is
 * well formed.
 ***)
and checkSubstWellFormed env formal real entity loc substFct =
	match formal,real with
	| [],[] -> ()
	| [],_|_,[] -> raise (TyperError (loc,entity^" is passed "^
		"more/less type parameters than expected."))
	| fhd::ftl, rhd::rtl ->
		(match fhd.rel with
		| SubclassOf -> if not (isSubtype env rhd loc (substFct fhd.oth)) then
			raise (TyperError (loc, "Ill-formed substitution: type "^
				(dispType rhd)^" was expected to be subtype of "^
				(dispType (substFct fhd.oth))^" in type parameters."))
			
		| SuperclassOf -> if not (isSubtype env (substFct fhd.oth) loc rhd) then
			raise (TyperError (loc, "Ill-formed substitution: type "^
				(dispType rhd)^" was expected to be supertype of "^
				(dispType (substFct fhd.oth))^" in type parameters."))
		| NoClassRel -> ()
		);
		checkSubstWellFormed env ftl rtl entity loc substFct

(***
 * Checks that the type `ty' is well formed in the environment `env'. If not,
 * raises a TyperError at location `loc'.
 ***)
and checkWellFormed env ty loc =
	let cl = findClass (fst ty) env loc in
	(match (snd ty) with
	| EmptyAType -> ()
	| ArgType(t) ->
		(* Check types recursively *)
		List.iter (fun ti -> checkWellFormed env ti loc) t ;

		(* Check bounds *)
		checkSubstWellFormed env (List.map fst cl.tclassTypes) t cl.tcname loc
			(substClassTypes env ty loc)
	)
(***
 * Returns the varType of a Ast.var in order to allow easy insertion into the
 * environment map
 ***)
and varValue env varStmt =
	let mutbl = (match varStmt.v with
		| Vvar(_) -> true
		| Vval(_) -> false) in
	match varStmt.v with
	| Vvar(id,Type(ty),defExp) | Vval(id,Type(ty),defExp) ->
		let expTypEx = (exprType env defExp) in
		let expTyp = expTypEx.etyp in
		checkWellFormed env ty varStmt.vloc;
		if isSubtype env expTyp (defExp.eloc) ty then
			(mutbl, ty), expTypEx
		else
			raise (TyperError (defExp.eloc, ("This expression was declared a "^
				"subtype of "^(dispType ty)^", but is of type "^
				(dispType expTyp)^".")))
	| Vvar(id,NoType,defExp)   | Vval(id,NoType,defExp)   ->
		let expTypEx = (exprType env defExp) in
		(mutbl, expTypEx.etyp), expTypEx

(***
 * Checks that a variable declaration is correct (variance, types, ...)
 ***)
and checkVarWellDef env varDef =
	let _,optTyp,vExp = (match varDef.v with
		Vvar(x,y,z) | Vval(x,y,z) -> x,y,z) in

	let varTyp = (exprType env vExp).etyp in
	checkWellFormed env varTyp vExp.eloc;

	(match optTyp with
	| NoType -> ()
	| Type(suppTyp) ->
		if not (isSubtype env varTyp vExp.eloc suppTyp) then
			wrongTypeError vExp.eloc varTyp suppTyp
	) ;
	
	let posVariance =
		(match varDef.v with Vvar(_) -> TMneutral | Vval(_) -> TMplus) in
	checkVariance env varTyp posVariance vExp.eloc;
	(match optTyp with
	| NoType -> ()
	| Type(suppTyp) ->
		checkVariance env suppTyp posVariance varDef.vloc)

	
and isMutable env acc loc = match acc with
| AccIdent(id) ->
	(try fst (SMap.find id env.vars)
	with Not_found -> isMutable env (AccMember({ex=Ethis;eloc=loc},id)) loc)
| AccMember(exp,id) ->
	let expTyp = (exprType env exp).etyp in
	let cl = findClass (fst expTyp) env (exp.eloc) in
	(try fst (SMap.find id (cl.tcvars))
	with Not_found -> raise (TyperError (exp.eloc, ("Variable `"^id^"' was "^
		"not declared in this scope."))))

and exprType env exp : typExpr = match exp.ex with
| Eint v -> { tex=TEint(v) ; etyp="Int",EmptyAType}
| Estr v -> { tex=TEstr(v) ; etyp="String",EmptyAType}
| Ebool v ->{ tex=TEbool(v); etyp="Boolean",EmptyAType}
| Eunit ->  { tex=TEunit ;   etyp="Unit",EmptyAType}
| Enull ->  { tex=TEnull ;   etyp="Null",EmptyAType}
| Ethis ->
	(try
		{ tex=TEthis ; etyp=snd (SMap.find "this" env.vars) }
	with Not_found -> raise (InternalError ("Value `this' was not "^
		"declared in this scope.")))
| Eaccess(AccIdent(id)) ->
	{ tex = TEaccess(TAccIdent(id)) ;
	  etyp=
		(try
			snd (SMap.find id env.vars)
		with Not_found ->
			(exprType env {ex=Eaccess(AccMember(
							{ex=Ethis;eloc=exp.eloc},id)) ;
						  eloc=exp.eloc }).etyp)
	}
| Eaccess(AccMember(aexp,id)) ->
	let subTypExp = exprType env aexp in
	let subTyp = subTypExp.etyp in
	classExists env (fst subTyp) aexp.eloc;
	let cl = findClass (fst subTyp) env (aexp.eloc) in
	let ty =
		(try substClassTypes env subTyp aexp.eloc (snd (SMap.find id cl.tcvars))
		with Not_found ->
			raise (TyperError (exp.eloc,("Variable `"^(fst subTyp)^"."^id^
				"' was not declared in this scope."))))
	in
	{ tex = TEaccess(TAccMember(subTypExp,id)) ; etyp = ty }
| Eassign(acc, assignExp) ->
	if not (isMutable env acc (exp.eloc)) then
		raise (TyperError (exp.eloc, ("Illegaly assigning the read-only "^
			"value "^(match acc with AccIdent(x)|AccMember(_,x) -> x)^".")));
	let vTyEx = exprType env {ex=Eaccess(acc) ; eloc=exp.eloc} in
	let vTyAcc = (match vTyEx.tex with TEaccess(t) -> t | _ -> assert false) in
	let vTy = vTyEx.etyp in
	let eTyEx = exprType env assignExp in
	let eTy = eTyEx.etyp in
	if isSubtype env eTy (assignExp.eloc) vTy then
		{ tex = TEassign(vTyAcc,eTyEx) ; etyp = ("Unit", EmptyAType) }
	else
		raise (TyperError (assignExp.eloc, ("This expression has type "^
			(dispType eTy)^", but was expected to be a subtype of "^
			(dispType vTy)^".")))

| Einstantiate(id,argt,params) ->
	checkWellFormed env (id,argt) exp.eloc ;
	let cl = findClass id env exp.eloc in
	let rec checkPar formal par out = match (formal,par) with
	| [],[] -> List.rev out
	| _,[]|[],_ -> raise (TyperError (exp.eloc, ("Got more/less parameters "^
		"than expected while constructing "^id^".")))
	| fHd::fTl, pHd::pTl ->
		let tpHdEx = exprType env pHd in
		let tpHd = tpHdEx.etyp in
		if isSubtype env tpHd (pHd).eloc fHd then
			checkPar fTl pTl (tpHdEx::out)
		else
			wrongTypeError (pHd.eloc) fHd tpHd
	in
	let outPars = 
		checkPar (List.map (substClassTypes env (id,argt) exp.eloc)
			(List.map snd cl.tcparams)) params [] in
	{ tex = TEinstantiate(id,argt,outPars) ; etyp=id,argt}

| Ecall(acc, argt, params) ->
	(match argt with
	| EmptyAType -> () 
	| ArgType(at) -> List.iter (fun k -> checkWellFormed env k exp.eloc) at);
	
	let classType, tyAcc, methName, accLoc = (match acc with
		| AccIdent(id) ->
			((exprType env {ex=Ethis;eloc=exp.eloc}).etyp, TAccIdent(id),
			id, exp.eloc)
		| AccMember(clExp,id) ->
			let clExpTyp = exprType env clExp in
			(clExpTyp.etyp, TAccMember(clExpTyp,id), id, clExp.eloc)
		) in

	if not (SMap.mem (fst classType) (env.classes)) then
		raise (TyperError (exp.eloc, "No class "^(fst classType)^
			"was previously defined in method call."));
	
	let cl = findClass (fst classType) env accLoc in
	
	let meth = (try SMap.find methName cl.tcmeth
		with Not_found ->
			raise (TyperError (exp.eloc, "Class "^(cl.tcname)^" has no such "^
				"method "^methName^"."))) in
	
	let substTypes ty = 
		substClassTypes env classType exp.eloc
			(substMethTypes env meth argt exp.eloc ty) in

	(* Well-formed check *)
	(match argt with
	| EmptyAType -> ()
	| ArgType(t) -> 
		checkSubstWellFormed env meth.tparTypes t meth.tmname exp.eloc
			substTypes) ;

	let rec checkArgs formal pars out = match (formal,pars) with
	| [],[] -> List.rev out
	| _,[]|[],_ -> raise (TyperError (exp.eloc, ("Got more/less parameters "^
		"than expected while calling method.")))
	| fHd::fTl, pHd::pTl ->
		let parTypEx = exprType env pHd in
		let parTyp = parTypEx.etyp in
		let fmethTyp = substTypes (snd fHd) in
		if not (isSubtype env parTyp exp.eloc fmethTyp) then
			wrongTypeError pHd.eloc parTyp fmethTyp
		else
			checkArgs fTl pTl (parTypEx::out)
	in
	let outArgs = checkArgs meth.tmparams params [] in
		
	{ tex = TEcall(tyAcc,argt,outArgs) ; etyp = (substTypes meth.tretTyp) }

| Eunaryop(UnaryNot, ex) ->
	let exTyp = exprType env ex in
	if fst exTyp.etyp = "Boolean" then
		{ tex = TEunaryop(UnaryNot, exTyp) ; etyp = exTyp.etyp }
	else
		wrongTypeError exp.eloc exTyp.etyp ("Boolean",EmptyAType)
| Eunaryop(UnaryMinus, ex) ->
	let exTyp = exprType env ex in
	if fst exTyp.etyp = "Int" then
		{ tex = TEunaryop(UnaryMinus, exTyp) ; etyp = exTyp.etyp }
	else
		wrongTypeError exp.eloc exTyp.etyp ("Int",EmptyAType)
| Ebinop(op,ex1,ex2) ->
	let tex1ex = exprType env ex1 and tex2ex = exprType env ex2 in
	let tex1 = tex1ex.etyp and tex2 = tex2ex.etyp in
	let typVal =
		(match op with
		| KwEqual | KwNEqual ->
			if not (isSubtype env tex1 ex1.eloc ("AnyRef",EmptyAType)) then
				wrongTypeError ex1.eloc tex1 ("AnyRef",EmptyAType)
			else if not (isSubtype env tex2 ex2.eloc ("AnyRef",EmptyAType)) then
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
	in
	{ tex = TEbinop(op,tex1ex,tex2ex) ; etyp = typVal }
| Eprint(ex) ->
	let texex = exprType env ex in
	let tex = texex.etyp in
	if (fst tex <> "String") && (fst tex <> "Int") then
		wrongTypeError ex.eloc tex ("String or Int",EmptyAType) (* Bweark. *)
	else
		{ tex = TEprint(texex) ; etyp = ("Unit", EmptyAType) }
| Eif(cnd,exIf,exElse) ->
	let tCndEx = exprType env cnd and tIfEx = exprType env exIf
	and tElseEx = exprType env exElse in
	let tCnd = tCndEx.etyp and tIf = tIfEx.etyp and tElse = tElseEx.etyp in
	if fst tCnd <> "Boolean" then
		wrongTypeError cnd.eloc tCnd ("Boolean", EmptyAType)
	else if isSubtype env tIf exIf.eloc tElse then
		{tex = TEif(tCndEx,tIfEx,tElseEx) ; etyp = tElse }
	else if isSubtype env tElse exElse.eloc tIf then
		{tex = TEif(tCndEx,tIfEx,tElseEx) ; etyp = tIf }
	else
		raise (TyperError (exp.eloc,("If statement has type "^(dispType tIf)^
			", but else statement has type "^(dispType tElse)^". Cannot unify"^
			" this as one of those types.")))
| Ewhile(cnd,code) ->
	let tCndEx = exprType env cnd and tCodeEx = exprType env code in
	let tCnd = tCndEx.etyp in
	if fst tCnd <> "Boolean" then
		wrongTypeError cnd.eloc tCnd ("Boolean", EmptyAType)
	else
		{ tex = TEwhile(tCndEx,tCodeEx) ; etyp = ("Unit",EmptyAType) }
| Ereturn(ex) ->
	let tExEx = exprType env ex in
	let tEx = tExEx.etyp in
	let retTyp = (try snd (SMap.find "_return" env.vars)
		with Not_found -> raise (TyperError (exp.eloc, "Return statement "^
			"outside of a method's body."))) in
	if isSubtype env tEx ex.eloc retTyp then
		{ tex = TEreturn(tExEx) ; etyp = ("Nothing", EmptyAType) }
	else
		wrongTypeError ex.eloc retTyp tEx
| Eblock(bl) ->
	(* Check that variables are declared only once. *)
	if hasDoubleElem (List.fold_left (fun cur decl -> match decl with
			| Bvar(var) ->
				let name = (match var.v with Vvar(x,_,_)|Vval(x,_,_) -> x) in
				name::cur
			| _ -> cur) [] bl) then
		raise (TyperError (exp.eloc, "A field with the same name was declared"^
			" twice in block."));

	let rec blockType env l outBl = match l with
	| [] -> { tex = TEblock(List.rev outBl) ; etyp = ("Unit", EmptyAType) }
	| Bexpr(ex)::[] ->
		let exty = exprType env ex in
		{ tex = TEblock(List.rev (TBexpr(exty)::outBl)) ; etyp = exty.etyp }
	| hd::tl -> (match hd with
		| Bvar(vv) ->
			let v = vv.v in
			let vName = (match v with Vvar(x,_,_) | Vval(x,_,_) -> x) in

			checkVarWellDef env vv ; 

			let varVal,typEx = varValue env vv in
			let nEnv = addVar env vName varVal in
			let nVar = { vname = vName ; vtyp = varVal ; vexpr = typEx } in
			blockType nEnv tl (TBvar(nVar) :: outBl)
		| Bexpr(bex) ->
			let typEx = exprType env bex in
			blockType env tl (TBexpr(typEx) :: outBl)
		)
	in
	blockType env bl []

(***
 * Types a full class in the given environment, and returns the same
 * environment, to which the freshly typed class was added.
 ***)
let doClassTyping env (cl : Ast.classDef) : typedClass * typingEnvironment =
	let nEnv = ref env in

	let inheritFromClass env (cl : typedClass) supertype clLoc =
		let super = (try SMap.find (fst supertype) env.classes
			with Not_found ->
				raise (TyperError (clLoc, "The class `"^(fst supertype)^
					", inherited by "^(cl.tcname)^", was not declared in "^
					"this scope."))) in

		let outCl = ref cl in
		let substTyp = substClassTypes env supertype clLoc in
		SMap.iter (fun key field ->
				outCl := classAddVar !outCl key (fst field,
					(substTyp (snd field))))
			super.tcvars;

		let substParTypes pts =
			List.map (fun pt -> { pt with oth = substTyp pt.oth }) pts
		in
		SMap.iter (fun key meth ->
				outCl := addMeth !outCl key { meth with
					tparTypes = substParTypes meth.tparTypes ;
					tmparams = List.map (fun p -> (fst p,
							substTyp (snd p))) meth.tmparams ;
					tretTyp = substTyp meth.tretTyp })
			super.tcmeth ;
		(*NOTE WARNING we do not substitute types in the body of the method,
			which becomes thus invalid. We are *NOT* supposed to use it
			anymore! *)

		{ !outCl with textends=Some {
			textType = supertype ;
			(* Up to the user to set tparam. Causes bugs if done here. *)
			tparam = [] }
		}
	in
	
	let addParamType parTyps envRef alterEnv bestLoc isClass =
										(*FIXME imprecise loc*)
		List.iter (fun parTyCl ->
				let parTy = fst parTyCl in
				if parTy.rel <> NoClassRel then (
					let nTy = parTy.oth in
					checkWellFormed (alterEnv !envRef) nTy bestLoc );

				let nClass = { tcname = (parTy.name) ;
							   tclassTypes = [] ;
							   tcparams = [] ;
							   textends = None ;
							   tcbody = [] ;
							   tcmeth = SMap.empty ;
							   tcvars = SMap.empty ;
							   tcvariance = snd parTyCl}
				in
				let nClass = 
					(match parTy.rel with
					| SubclassOf ->
						checkVariance (alterEnv !envRef) parTy.oth
							(if isClass then TMplus else TMminus)
							bestLoc;
						inheritFromClass (alterEnv !envRef) nClass parTy.oth
							bestLoc
					| SuperclassOf ->
						checkVariance (alterEnv !envRef) parTy.oth
							(if isClass then TMminus else TMplus)
							bestLoc;
						envRef := addSuptypeDecl !envRef parTy.name parTy.oth ;
						nClass
					| _ -> nClass)
				in
				envRef := addClass !envRef parTy.name nClass)
			parTyps
	in

	(* Check that the class was not previously defined. *)
	if SMap.mem cl.cname env.classes then
		raise (TyperError (cl.cLoc, "A class named "^cl.cname^" is "^
			"already defined."));

	(* Adding the T from [+/-/() T] to the environment *)
	if hasDoubleElem (List.map (fun k -> (fst k).name) cl.classTypes) then
		raise (TyperError (cl.cLoc, "The same name was used twice in the "^
			"type parameters of this class."));
	addParamType cl.classTypes nEnv (fun k -> k ) cl.cLoc true;

	(* Inheritance *)
	let nClass =
		{tcname = cl.cname ;
		 tclassTypes = cl.classTypes ;
		 tcparams = cl.cparams ;
		 textends = None ; (* Done later *)
		 tcbody = [] ;
		 tcmeth = SMap.empty ;
		 tcvars = SMap.empty ;
		 tcvariance = TMneutral
		} in
	let nClass = ref
		(match cl.extends with
		| None -> nClass
		| Some t ->
			checkVariance !nEnv t.extType TMplus cl.cLoc ;
			if List.mem (fst t.extType) ["Any";"AnyVal";"Unit";"Int";
					"Boolean";"String";"Null";"Nothing"] then
				raise (TyperError (cl.cLoc, "This class cannot inherit from "^
					(fst t.extType)^", as it is a base type."))
			else if not (SMap.mem (fst t.extType) env.classes) then
				raise (TyperError (cl.cLoc, "This class cannot inherit from "^
					(fst t.extType)^", as it is not defined."));

			checkWellFormed !nEnv t.extType cl.cLoc; (*FIXME imprecise loc*)
			inheritFromClass !nEnv nClass t.extType cl.cLoc
		) in
	let curEnv cenv =
		addClass cenv (cl.cname) !nClass
	in
	
	(* Parameters checking and adding *)
	if hasDoubleElem (List.map fst cl.cparams) then
		raise (TyperError (cl.cLoc, "The same name was used twice "^
			"in the parameters of this class."));
	List.iter (fun (idt,ty) ->
			checkWellFormed (curEnv !nEnv) ty cl.cLoc (*FIXME imprecise loc*);
			(* Implicit val declaration: we have to check variance *)
			checkVariance (curEnv !nEnv) ty TMplus cl.cLoc ;
			nClass := classAddVar !nClass idt (false,ty))
		cl.cparams;
	(* `This' adding *)
	let thisArgt = (match cl.classTypes with
		| [] -> EmptyAType
		| l -> ArgType (List.map (fun ptc -> ((fst ptc).name, EmptyAType)) l))
	in
	nEnv := addVar (curEnv !nEnv) "this" (false, (cl.cname, thisArgt));

	(* Check that we can construct the inherited class *)
	let makeTypeExtends = function
	| None -> None
	| Some ext ->
		Some { textType = ext.extType ;
			tparam = List.map (exprType !nEnv) ext.param }
	in
	nClass := { !nClass with textends = makeTypeExtends cl.extends };
	(match cl.extends with
		| None -> ()
		| Some t ->
			let inheritedTyp = (exprType (curEnv !nEnv)
				{ ex = Einstantiate( (fst t.extType),(snd t.extType), t.param);
				  eloc = cl.cLoc (*FIXME imprecise loc*)
				}).etyp
			in
			if inheritedTyp <> t.extType then
				raise (TyperError (cl.cLoc, ("Illegal call to the superclass "^
					"constructor while declaring class "^cl.cname^".")))
	);

	(*** Body ***)
	(* Check that methods are uniquely defined *)
	if hasDoubleElem (List.fold_left (fun cur v -> match v with
			| Dmeth(meth) -> (meth.mname)::cur
			| _ -> cur) [] cl.cbody) then
		raise (TyperError (cl.cLoc, "The same name was used twice in the "^
			"methods names of "^cl.cname^"."));
				
	List.iter (fun declare -> match declare with
		| Dvar(varDecl) ->
			let name = (match varDecl.v with Vvar(x,_,_) | Vval(x,_,_) -> x) in
			let vt,vexp = varValue (curEnv !nEnv) varDecl in
			checkVarWellDef (curEnv !nEnv) varDecl ;
			if SMap.mem name !nClass.tcvars then
				raise (TyperError (varDecl.vloc, "A field named "^
					name^" was already declared in this class."));
			nClass := { !nClass with tcvars=(SMap.add name vt !nClass.tcvars) ;
							tcbody=TDvar({
										vname=name;
										vtyp=vt;
										vexpr=vexp}
										)::(!nClass.tcbody)}
		| Dmeth(methDecl) ->
			let locEnv = ref !nEnv in

			(* Type parameters *)
			if hasDoubleElem (List.map (fun k->k.name) methDecl.parTypes) then
				raise (TyperError (methDecl.mLoc, "The same name was used "^
					"twice in the type parameters of this method."));
			addParamType (List.map (fun k -> (k,TMneutral)) methDecl.parTypes)
				locEnv curEnv methDecl.mLoc false;

			let curEnvLoc e =
				(*Cur class with the currently typed method with a dummy body*)
				addClass e cl.cname
					(addMeth !nClass methDecl.mname {
						tmname = methDecl.mname ;
						tparTypes = methDecl.parTypes ;
						tmparams = methDecl.mparams ;
						tretTyp = methDecl.retType ;
						tmbody = {tex = TEblock([]) ;etyp = methDecl.retType};
						toverride = methDecl.override
						})
			in

			(* Parameters *)
			if hasDoubleElem (List.map fst methDecl.mparams) then
				raise (TyperError (methDecl.mLoc, "The same name was used "^
					"twice in the parameters of this method."));
			List.iter (fun (idt,ty) ->
					(*FIXME imprecise loc*)
					checkWellFormed (curEnvLoc !locEnv) ty methDecl.mLoc;
					checkVariance (curEnvLoc !locEnv) ty TMminus methDecl.mLoc;
					locEnv := addVar !locEnv idt (false,ty))
				methDecl.mparams;
			locEnv := addVar !locEnv "_return" (false,methDecl.retType) ;

			(* Override correction *)
			(try
				let supermeth = SMap.find methDecl.mname !nClass.tcmeth in
				if not methDecl.override then
					raise (TyperError (methDecl.mLoc,("This method was "^
						"previously declared.")));

				(* As we are comparing from the inherited method (and not the
				   method of the superclass itself), we only have to substitute
				   type parameters' names *)
				let substParamTypeName tName =
					let rec doSubst curPT superPT = match (curPT,superPT) with
					| [],[] -> tName
					| [],_|_,[] -> 
						raise (TyperError (methDecl.mLoc, ("This overriding "^
							"method doesn't have the same number of "^
							"parameters than the method it is overriding.")))
					| chd::ctl, shd::stl ->
						if shd.name = tName then
							chd.name
						else
							doSubst ctl stl
					in
					doSubst methDecl.parTypes supermeth.tparTypes
				in
				let rec substParamType ty =
					(substParamTypeName (fst ty), (match snd ty with
						| EmptyAType -> EmptyAType
						| ArgType(tt) -> ArgType (List.map substParamType tt)
						))
				in

				let rec compareParTypes nPar supPar parId =
					match nPar,supPar with
				| [],[] -> ()
				| [],_ | _,[] ->
					raise (TyperError (methDecl.mLoc, ("This overriding "^
						"method doesn't have the same number of parameters "^
						"than the method it is overriding.")))
				| (_,newHd)::newTl, (_,supHd)::supTl ->
					if newHd <> (substParamType supHd) then
						raise (TyperError (methDecl.mLoc, ("Parameter "^
							(string_of_int parId)^" has type "^
							(dispType newHd)^", yet it is overriding a "^
							"parameter of type "^
							(dispType (substParamType supHd))^".")));
					compareParTypes newTl supTl (parId+1)
				in
				compareParTypes methDecl.mparams supermeth.tmparams 1;

				(* return type *)
				if not (isSubtype (curEnvLoc !locEnv)
						methDecl.retType methDecl.mLoc
						(substParamType supermeth.tretTyp)) then
					raise (TyperError (methDecl.mLoc, ("This overriding "^
						"method's return type "^(dispType methDecl.retType)^
						" is not a subtype of "^(dispType supermeth.tretTyp)^
						", the return type of the method it is overriding.")))
			
				(* All clear here! *)

			with Not_found ->
				if methDecl.override then
					raise (TyperError (methDecl.mLoc, ("This method is "^
						"declared as overriding, yet there is no such method "^
						"to override in the superclass.")))
			);

			(* Check type and variance *)
			checkVariance (curEnvLoc !locEnv) methDecl.retType TMplus
				methDecl.mLoc;
			let bodyTypEx = exprType (curEnvLoc !locEnv) methDecl.mbody in
			let bodyTyp = bodyTypEx.etyp in
			if not (isSubtype (curEnvLoc !locEnv) bodyTyp
					methDecl.mbody.eloc methDecl.retType) then
				wrongTypeError methDecl.mbody.eloc bodyTyp methDecl.retType ;

			(* Effectively adding the method, all done*)
			let nMeth = {
				tmname = methDecl.mname ;
				tparTypes = methDecl.parTypes ;
				tmparams = methDecl.mparams ;
				tretTyp = methDecl.retType ;
				tmbody = bodyTypEx ;
				toverride = methDecl.override
			} in
			nClass := addMeth !nClass methDecl.mname nMeth
		)
		cl.cbody;
	nClass := { !nClass with tcbody = List.rev (!nClass.tcbody) } ;
	!nClass, (curEnv env)

let doPrgmTyping (prgm : Ast.prgm) =
	let smap_of_list l =
		List.fold_left (fun cur (id,v) -> SMap.add id v cur) SMap.empty l in
	let mkBaseClass (name,inher) =
		(name, { tcname=name ; tclassTypes=[] ; tcparams=[] ;
				 textends=
				 	if inher <> "" then Some
						{ textType=(inher,EmptyAType) ; tparam=[] }
					else None ;
				 tcbody=[] ; tcvars=SMap.empty ; tcmeth=SMap.empty ;
				 tcvariance = TMneutral} )
	in
	let baseClasses = smap_of_list (List.map mkBaseClass [
			"Nothing",	"";
			"Null",		"";
			"Unit",		"AnyVal";
			"Int",		"AnyVal";
			"Boolean",	"AnyVal";
			"String",	"AnyRef";
			"AnyVal",	"Any";
			"AnyRef",	"Any";
			"Any",		""
		]) in
	(* Add Array. We consider it to be user-defined, would be a hell of a mess
	  otherwise. *)
	let baseClasses = SMap.add "Array"
		{ (snd (mkBaseClass ("Array","AnyRef"))) with
			tclassTypes = [( {name="ty";rel=NoClassRel;oth=("",EmptyAType)},
					TMneutral )]
		} baseClasses in
	let env = ref { suptypeDecl = SMap.empty ;
		classes = baseClasses ;
		vars = SMap.empty } in

	let typedClassesList = List.rev (List.fold_left
		(fun cur cl ->
			let nCl,nEn = doClassTyping !env cl in
			env := nEn ;
			nCl::cur)
		[] prgm.classes ) in

	let tcmain, nEn = doClassTyping !env (prgm.main) in
	env := nEn ;

	if prgm.main.cname <> "Main" then
		raise (TyperError (prgm.main.cLoc, ("This class is supposed to be the"^
			" main class, yet it is not named `Main'."))) ;
(*	let tcmain = (try SMap.find "Main" !env.classes 
		with Not_found ->
			raise (InternalError "Main class was not found, yet exists.")) in
*)
	let mainMeth = (try SMap.find "main" tcmain.tcmeth
		with Not_found ->
			raise (TyperError (prgm.main.cLoc, ("Method `main' is not "^
				"defined in `Main' class.")))) in
	let rec findMainLoc = function
	| [] -> raise Not_found
	| Dmeth(me)::tl -> if me.mname = "main" then me.mLoc else findMainLoc tl
	| _::tl -> findMainLoc tl
	in
	let mainLoc = (try findMainLoc prgm.main.cbody
		with Not_found -> raise (TyperError (prgm.main.cLoc, "The method "^
			"main was not declared in the Main class."))) in

	(* Main.main checking *)
	(if mainMeth.tparTypes <> [] then
		raise (TyperError (mainLoc, "Main.main may not have "^
			"type parameters."))
	else if mainMeth.tretTyp <> ("Unit", EmptyAType) then
		raise (TyperError (mainLoc, "Main.main must return Unit."))
	else if List.length mainMeth.tmparams <> 1 ||
				snd (List.hd mainMeth.tmparams) <>
					("Array",ArgType(["String",EmptyAType])) then
		raise (TyperError (mainLoc, "Main.main must have a single "^
			"parameter of type Array[String]"))
	else if tcmain.tclassTypes <> [] then
		raise (TyperError (prgm.main.cLoc, "Class `Main' may not have"^
			" type parameters."))
	else if tcmain.tcparams <> [] then
		raise (TyperError (prgm.main.cLoc, "Class `main' may not take "^
			"parameters.")));

	let outPrgm = {
			tclasses = typedClassesList ;
			tmain = tcmain ;
			tenvironment = !env
		} in
	outPrgm
