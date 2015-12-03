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
open Lexing
open Typedefs

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


let getInheritedType cl = match cl.textends with
| None -> { extType = "AnyRef",EmptyAType ; param = [] }
| Some t -> t

(***
 * Replaces the type `genericType', which may contain parameter types from
 * the class `fst clTyp', with the real type obtained by substituting every
 * local type by its type passed as argument of `clTyp'
 ***)
let substClassTypes env clTyp loc genericType =
	match snd clTyp with
	| EmptyAType -> genericType
	| ArgType(clParams) ->
		let classDef = findClass (fst clTyp) env loc in
		let rec doSubst clTy par = match (clTy,par) with
		| [],[] -> genericType
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
let substMethTypes env meth argTy loc genericType =
	match argTy with
	| EmptyAType -> genericType
	| ArgType(methPar) ->
		let rec doSubst methPa par = match (methPa,par) with
		| [],[] -> genericType
		| [],_|_,[] -> raise (TyperError (loc, "Method "^(meth.mname)^" was "^
			"passed more/less types than expected."))
		| (fpar::_,rpar::_) when (fst genericType = fpar.name) -> rpar
		| _::ftl,_::rtl -> doSubst ftl rtl
		in
		doSubst meth.parTypes methPar

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
			| Some cl -> fst cl.extType)

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
			cl2 = "String" || (userDefined cl2)
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
			raise (InternalError ("Encountered types with not enough/too much"^
				" argument types."))
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
	else if (not (isArrow env (fst ty1) (fst ty2))) then
		(* If C1 -/-> C2 *)
		try
			let suptyps = SMap.find (fst ty2) env.suptypeDecl in
			let _ = List.find (fun ty -> isSubtype env ty1 loc1 ty) suptyps in
			true
		with Not_found ->
			false
	else (* If C1 extends C[..], C -> C2 *)
		let extCl = (match (findClass (fst ty1) env loc1).textends with
			| None -> { extType = ("AnyRef",EmptyAType) ; param = [] }
			| Some t -> t) in
		let extName = fst (extCl.extType) in
		if isArrow env extName (fst ty2) then begin
			match (snd extCl.extType) with
			| EmptyAType -> isSubtype env extCl.extType loc1 ty2
			| ArgType(at1) ->
				let typlist = List.rev (List.fold_left
					(fun cur ex -> (exprType env ex)::cur) [] extCl.param) in
				let nty1 = (extName, ArgType typlist) in
				isSubtype env nty1 loc1 ty2
		end else
			false

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
		let expTyp = exprType env defExp in
		checkWellFormed env ty varStmt.vloc;
		if isSubtype env expTyp (defExp.eloc) ty then
			(mutbl, ty)
		else
			raise (TyperError (defExp.eloc, ("This expression was declared a "^
				"subtype of "^(dispType ty)^", but is of type "^
				(dispType expTyp)^".")))
	| Vvar(id,NoType,defExp)   | Vval(id,NoType,defExp)   ->
		let expTyp = exprType env defExp in
		(mutbl, expTyp)
	
and isMutable env acc loc = match acc with
| AccIdent(id) ->
	(try fst (SMap.find id env.vars)
	with Not_found -> isMutable env (AccMember({ex=Ethis;eloc=loc},id)) loc)
| AccMember(exp,id) ->
	let expTyp = exprType env exp in
	let cl = findClass (fst expTyp) env (exp.eloc) in
	(try fst (SMap.find id (cl.tcvars))
	with Not_found -> raise (TyperError (exp.eloc, ("Variable `"^id^"' was "^
		"not declared in this scope."))))

and exprType env exp = match exp.ex with
| Eint _ -> "Int",EmptyAType
| Estr _ -> "String",EmptyAType
| Ebool _ -> "Boolean",EmptyAType
| Eunit -> "Unit",EmptyAType
| Enull  -> "Null",EmptyAType
| Ethis ->
	(try snd (SMap.find "this" env.vars)
	with Not_found -> raise (InternalError ("Value `this' was not "^
		"declared in this scope.")))
| Eaccess(AccIdent(id)) ->
	(try snd (SMap.find id env.vars)
	with Not_found ->
		exprType env {ex=Eaccess(AccMember(
						{ex=Ethis;eloc=exp.eloc},id)) ;
					  eloc=exp.eloc })
| Eaccess(AccMember(aexp,id)) ->
	let subTyp = exprType env aexp in
	(*
	let rec findMemberType clTyp =
		let cl = findClass (fst clTyp) env in
		(try 
			(substClassTypes env clTyp (snd (SMap.find id (env.vars))))
		with Not_found ->
			let inherTyp = getInheritedType cl in
			if (fst inherTyp.extType) = "AnyRef" then
				raise (TyperError (exp.eloc,("Variable `"^id^"' was "^
					"not declared in this scope.")))
			else if inherTyp.param = [] then
				findMemberType (fst inherTyp.extType, EmptyAType)
			else
				findMemberType (fst inherTyp.extType,
					ArgType ((List.map (fun sExp -> substClassTypes env clTyp
						(exprType env sExp)) (inherTyp.param))))
		)
	in
	findMemberType subTyp *)

	classExists env (fst subTyp) aexp.eloc;
	let cl = findClass (fst subTyp) env (aexp.eloc) in
	(try substClassTypes env subTyp aexp.eloc (snd (SMap.find id cl.tcvars))
	with Not_found ->
		raise (TyperError (exp.eloc,("Variable `"^(fst subTyp)^"."^id^"' was "^
			"not declared in this scope."))))
| Eassign(acc, assignExp) ->
	if not (isMutable env acc (exp.eloc)) then
		raise (TyperError (exp.eloc, ("Illegaly assigning the read-only "^
			"value "^(match acc with AccIdent(x)|AccMember(_,x) -> x)^".")));
	let vTy = exprType env {ex=Eaccess(acc) ; eloc=exp.eloc} in
	let eTy = exprType env assignExp in
	if isSubtype env eTy (assignExp.eloc) vTy then
		("Unit", EmptyAType)
	else
		raise (TyperError (assignExp.eloc, ("This expression has type "^
			(dispType eTy)^", but was expected to be a subtype of "^
			(dispType vTy)^".")))

| Einstantiate(id,argt,params) ->
	checkWellFormed env (id,argt) exp.eloc ;
	let cl = findClass id env exp.eloc in
	let rec checkPar formal par = match (formal,par) with
	| [],[] -> ()
	| _,[]|[],_ -> raise (TyperError (exp.eloc, ("Got more/less parameters "^
		"than expected while constructing "^id^".")))
	| fHd::fTl, pHd::pTl ->
		let tpHd = exprType env pHd in
		if isSubtype env tpHd (pHd).eloc fHd then
			checkPar fTl pTl
		else
			wrongTypeError (pHd.eloc) fHd tpHd
	in
	checkPar (List.map (substClassTypes env (id,argt) exp.eloc)
		(List.map snd cl.tcparams)) params ;
	(id,argt)

| Ecall(acc, argt, params) ->
	(match argt with
	| EmptyAType -> () 
	| ArgType(at) -> List.iter (fun k -> checkWellFormed env k exp.eloc) at);
	
	let classType, methName, accLoc = (match acc with
		| AccIdent(id) -> (exprType env {ex=Ethis;eloc=exp.eloc}, id, exp.eloc)
		| AccMember(clExp,id) -> (exprType env clExp, id, clExp.eloc)
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
	(*TODO check sigma o sigma' well formed *)

	let rec checkArgs formal pars = match (formal,pars) with
	| [],[] -> ()
	| _,[]|[],_ -> raise (TyperError (exp.eloc, ("Got more/less parameters "^
		"than expected while calling method.")))
	| fHd::fTl, pHd::pTl ->
		let parTyp = exprType env pHd in
		let fmethTyp = substTypes (snd fHd) in

		if not (isSubtype env parTyp exp.eloc fmethTyp) then
			wrongTypeError pHd.eloc parTyp fmethTyp
	in
	checkArgs meth.mparams params ;
	
	substTypes meth.retType
(*substMethTypes env meth argt (substClassTypes env classType meth.retType)*)
			
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
	else if isSubtype env tIf exIf.eloc tElse then
		tElse
	else if isSubtype env tElse exElse.eloc tIf then
		tIf
	else
		raise (TyperError (exp.eloc,("If statement has type "^(dispType tIf)^
			", but else statement has type "^(dispType tElse)^". Cannot unify"^
			" this as one of those types.")))
| Ewhile(cnd,code) ->
	let tCnd = exprType env cnd and (*tCode*)_ = exprType env code in
	if fst tCnd <> "Boolean" then
		wrongTypeError cnd.eloc tCnd ("Boolean", EmptyAType)
	else
		("Unit",EmptyAType)
| Ereturn(ex) ->
	let tEx = exprType env ex in
	let retTyp = (try snd (SMap.find "_return" env.vars)
		with Not_found -> raise (TyperError (exp.eloc, "Return statement "^
			"outside of a method's body."))) in
	if isSubtype env tEx ex.eloc retTyp then
		("Nothing", EmptyAType)
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

	let rec blockType env = function
	| [] -> ("Unit", EmptyAType)
	| Bexpr(ex)::[] ->
		exprType env ex
	| hd::tl -> (match hd with
		| Bvar(vv) ->
			let v = vv.v in
			let vName = (match v with Vvar(x,_,_) | Vval(x,_,_) -> x) in
			let nEnv = addVar env vName (varValue env vv) in
			blockType nEnv tl
		| Bexpr(bex) ->
			let _ = exprType env bex in
			blockType env tl
		)
	in
	blockType env bl

(***
 * Types a full class in the given environment, and returns the same
 * environment, to which the freshly typed class was added.
 ***)
let doClassTyping env cl =
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
					parTypes = substParTypes meth.parTypes ;
					mparams = List.map (fun p -> (fst p,
							substTyp (snd p))) meth.mparams ;
					retType = substTyp meth.retType })
			super.tcmeth ;
		(*NOTE WARNING we do not substitute types in the body of the method,
			which becomes thus invalid. We are *NOT* supposed to use it
			anymore! *)

		!outCl
	in
	
	let addParamType parTyps envRef bestLoc (*FIXME imprecise loc*) =
		List.iter (fun parTy ->
				if parTy.rel <> NoClassRel then
					let nTy = parTy.oth in
					checkWellFormed env nTy bestLoc ;

				let nClass = { tcname = (parTy.name) ;
							   tclassTypes = [] ;
							   tcparams = [] ;
							   textends = None ;
							   tcbody = [] ;
							   tcmeth = SMap.empty ;
							   tcvars = SMap.empty }
				in
				let nClass = 
					(match parTy.rel with
					| SubclassOf ->
						inheritFromClass !envRef nClass parTy.oth bestLoc
					| SuperclassOf ->
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
	addParamType (List.map fst cl.classTypes) nEnv cl.cLoc;
	
	(* Inheritance *)
	let nClass =
		{tcname = cl.cname ;
		 tclassTypes = cl.classTypes ;
		 tcparams = cl.cparams ;
		 textends = cl.extends ;
		 tcbody = [] ;
		 tcmeth = SMap.empty ;
		 tcvars = SMap.empty
		} in
	let nClass = ref
		(match cl.extends with
		| None -> nClass
		| Some t ->
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
			nClass := classAddVar !nClass idt (false,ty))
		cl.cparams;
	(* `This' adding *)
	let thisArgt = (match cl.classTypes with
		| [] -> EmptyAType
		| l -> ArgType (List.map (fun ptc -> ((fst ptc).name, EmptyAType)) l))
	in
	nEnv := addVar !nEnv "this" (false, (cl.cname, thisArgt));

	(* Check that we can construct the inherited class *)
	(match cl.extends with
		| None -> ()
		| Some t ->
			let inheritedTyp = (exprType (curEnv !nEnv)
				{ ex = Einstantiate( (fst t.extType),(snd t.extType), t.param);
				  eloc = cl.cLoc (*FIXME imprecise loc*)
				})
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
			let vt = varValue (curEnv !nEnv) varDecl in
			if SMap.mem name !nClass.tcvars then
				raise (TyperError (varDecl.vloc, "A field named "^
					name^" was already declared in this class."));
			nClass := { !nClass with tcvars=(SMap.add name vt !nClass.tcvars)}
		| Dmeth(methDecl) ->
			let locEnv = ref !nEnv in

			(* Type parameters *)
			if hasDoubleElem (List.map (fun k -> k.name) methDecl.parTypes) then
				raise (TyperError (methDecl.mLoc, "The same name was used "^
					"twice in the type parameters of this method."));
			addParamType methDecl.parTypes locEnv methDecl.mLoc ;

			(* Parameters *)
			if hasDoubleElem (List.map fst methDecl.mparams) then
				raise (TyperError (methDecl.mLoc, "The same name was used "^
					"twice in the parameters of this method."));
			List.iter (fun (idt,ty) ->
					(*FIXME imprecise loc*)
					checkWellFormed (curEnv !locEnv) ty methDecl.mLoc;
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
				   method of the superclass itself), we do not have to bother
				   with type substitution *)
				let rec compareParTypes nPar supPar parId =
					match nPar,supPar with
				| [],[] -> ()
				| [],_ | _,[] ->
					raise (TyperError (methDecl.mLoc, ("This overriding "^
						"method doesn't have the same number of parameters "^
						"than the method it is overriding.")))
				| (_,newHd)::newTl, (_,supHd)::supTl ->
					if newHd <> supHd then
						raise (TyperError (methDecl.mLoc, ("Parameter "^
							(string_of_int parId)^" has type "^
							(dispType newHd)^", yet it is overriding a "^
							"parameter of type "^(dispType supHd)^".")));
					compareParTypes newTl supTl (parId+1)
				in
				compareParTypes methDecl.mparams supermeth.mparams 1;

				(* return type *)
				if not (isSubtype (curEnv !nEnv)
						methDecl.retType methDecl.mLoc supermeth.retType) then
					raise (TyperError (methDecl.mLoc, ("This overriding "^
						"method's return type "^(dispType methDecl.retType)^
						" is not a subtype of "^(dispType supermeth.retType)^
						", the return type of the method it is overriding.")))
			
				(* All clear here! *)

			with Not_found ->
				if methDecl.override then
					raise (TyperError (methDecl.mLoc, ("This method is "^
						"declared as overriding, yet there is no such method "^
						"to override in the superclass.")))
			);
			(* Effectively adding the method, check type *)
			nClass := addMeth !nClass methDecl.mname methDecl ;
			let bodyTyp = exprType (curEnv !locEnv) methDecl.mbody in
			if not (isSubtype (curEnv !nEnv) bodyTyp
					methDecl.mbody.eloc methDecl.retType) then
				wrongTypeError methDecl.mbody.eloc bodyTyp methDecl.retType
		)
		cl.cbody;
	(curEnv !nEnv)

let doPrgmTyping (prgm : Ast.prgm) =
	let smap_of_list l =
		List.fold_left (fun cur (id,v) -> SMap.add id v cur) SMap.empty l in
	let mkBaseClass (name,inher) =
		(name, { tcname=name ; tclassTypes=[] ; tcparams=[] ;
				 textends=
				 	if inher <> "" then Some
						{ extType=(inher,EmptyAType) ; param=[] }
					else None ;
				 tcbody=[] ; tcvars=SMap.empty ; tcmeth=SMap.empty } )
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

	List.iter
		(fun cl -> env := doClassTyping !env cl)
		prgm.classes ;

	env := doClassTyping !env (prgm.main) ;
	if prgm.main.cname <> "Main" then
		raise (TyperError (prgm.main.cLoc, ("This class is supposed to be the"^
			" main class, yet it is not named `Main'."))) ;
	let tcmain = (try SMap.find "Main" !env.classes 
		with Not_found ->
			raise (InternalError "Main class was not found, yet exists.")) in
	let mainMeth = (try SMap.find "main" tcmain.tcmeth
		with Not_found ->
			raise (TyperError (prgm.main.cLoc, ("Method `main' is not "^
				"defined in `Main' class.")))) in

	(* Main.main checking *)
	if mainMeth.parTypes <> [] then
		raise (TyperError (mainMeth.mLoc, "Main.main may not have "^
			"type parameters."))
	else if mainMeth.retType <> ("Unit", EmptyAType) then
		raise (TyperError (mainMeth.mLoc, "Main.main must return Unit."))
	else if List.length mainMeth.mparams <> 1 ||
				snd (List.hd mainMeth.mparams) <>
					("Array",ArgType(["String",EmptyAType])) then
		raise (TyperError (mainMeth.mLoc, "Main.main must have a single "^
			"parameter of type Array[String]"))
	else if tcmain.tclassTypes <> [] then
		raise (TyperError (prgm.main.cLoc, "Class `Main' may not have"^
			" type parameters."))
	else if tcmain.tcparams <> [] then
		raise (TyperError (prgm.main.cLoc, "Class `main' may not take "^
			"parameters."))
