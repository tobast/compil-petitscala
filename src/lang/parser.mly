%{
	open Ast

	let parse_error str =
		raise (Parsing_error str)

	let dummyLoc ex pos = { ex = ex ; eloc = {
							loc_beg = pos ; loc_end = pos } }

	let chkMain cl =
		let valid = (cl.cname = "Main") && (cl.classTypes = []) &&
		(cl.cparams = []) && (cl.extends = None) in
		if not valid then
			raise (Ast.Parsing_error "Expected main class.")
	let processInt str isNeg =
		let size = String.length str in
		let maxint = (if isNeg then (1 lsl 31) else ((1 lsl 30)-1+(1 lsl 30)))
		in
		let rec process pos cur =
			if(pos = size) then
				(if isNeg then -cur else cur)
			else
				let digit = int_of_string (String.make 1 str.[pos]) in
				if (maxint - digit)/10 >= cur then
					process (pos+1) (10*cur + digit)
				else
					raise (Parsing_error ("Overflow in constant integer value "^
						str^"."))
		in
		process 0 0
	
	let emptyType = "Unit",EmptyAType

	let mapOfClassList l =
		List.fold_left (fun cur elem -> SMap.add elem.cname elem cur)
			SMap.empty l
%}

%token KW_CLASS KW_DEF KW_ELSE KW_EQ KW_EXTENDS KW_FALSE KW_IF KW_NE
%token KW_NEW KW_NULL KW_OBJECT KW_OVERRIDE KW_PRINT KW_RETURN KW_THIS
%token KW_TRUE KW_VAL KW_VAR KW_WHILE
%token Tcomma Tlpar Trpar Tsupertype Tsubtype Tdbeq Tneq Tleq Tgeq
%token Tless Tgreater Tequal Tbang Tlbra Trbra Tcolon Tsemicolon
%token Tlbracket Trbracket
%token Tplus Tminus Ttimes Tdiv Tmod Tland Tlor Tdot Teof
%token <string> Tint
%token <string> Tstring
%token <Ast.ident> Tident

/* =============== PRIORITIES ========================= */

%nonassoc KW_IF
%nonassoc KW_ELSE
%nonassoc KW_WHILE KW_RETURN
%right Tequal
%left Tlor
%left Tland
%left KW_EQ KW_NE Tdbeq Tneq
%left Tgreater Tless Tgeq Tleq
%left Tplus Tminus
%left Ttimes Tdiv Tmod
%right Tuminus Tbang 
%left Tdot

%start prgm
%type <Ast.prgm> prgm

%%


prgm:
| cl=classDef* ; mcl=classMain ; Teof		{ { classes = (*mapOfClassList*)cl;
												main = mcl}}
;

classMain:
	KW_OBJECT ; id=Tident ; Tlbra ;
	dec = separated_list(Tsemicolon, decl) ; Trbra
		{ if id = "Main" then { cname = id ; classTypes=[]; cparams=[];
								extends = None ; cbody = dec ;
								cLoc = {loc_beg=$startpos ; loc_end=$endpos} }
		  else raise (Parsing_error ("Expected object named Main, got "^id^"."))
		}
			
;

classExtends:
	KW_EXTENDS ; t=typ ;
	par = loption(delimited(
		Tlpar,separated_list(Tcomma, expr),
		Trpar))
											{{ extType = t ; param = par }}
;

classDef:
	KW_CLASS ; name=Tident;
	parTC=loption(delimited(
		Tlbracket,
		separated_nonempty_list(Tcomma, param_type_class),
		Trbracket)) ;
	param=loption(delimited(
		Tlpar,
		separated_list(Tcomma, param),
		Trpar)) ;
	ext = option(classExtends) ;
	Tlbra ;
	dec = separated_list(Tsemicolon, decl) ;
	Trbra
											{ {
												cname = name ;
												classTypes = parTC ;
												cparams = param ;
												extends = ext ;
												cbody = dec ;
												cLoc = { loc_beg=$startpos ;
														loc_end=$endpos }
											} }
;

decl:
| v = var											{ Dvar(v) }
| m = methodDef										{ Dmeth(m) }
;

method_proto:
| ovrd=boption(KW_OVERRIDE) ; KW_DEF ; id=Tident ;
	pt=loption(delimited(Tlbracket,
		separated_nonempty_list(Tcomma,param_type),
		Trbracket)) ;
	Tlpar ; par=separated_list(Tcomma, param) ; Trpar
									{ {mname = id ; parTypes = pt ;
										mparams = par ;
										retType=emptyType ; 
										mbody= { ex=Eblock([]) ;
											eloc={loc_beg=$startpos;
												loc_end=$endpos} } ;
										override=ovrd ;
										mLoc = { loc_beg=$startpos ;
												loc_end=$startpos } } }
;

methodDef:
| mth=method_proto ; bl=expr				{ match bl.ex with
												| Eblock(b) -> 
													{ mth with mbody=bl ;
													 mLoc = {loc_beg=$startpos;
														loc_end = $endpos } }
												| _ -> raise (Parsing_error
													"Block expected.")
											}
| mth=method_proto ; Tcolon ; t=typ ;
	Tequal ; exp=expr						{{ mth with retType=t;
												mbody= exp ;
												mLoc = {loc_beg=$startpos;
														loc_end=$endpos}}}
;

expr:
| t = exprVal						{ { ex = t ; eloc = {
													loc_beg = $startpos; 
													loc_end = $endpos} } }
;

exprVal:
/*
| Tminus ; n = Tint			%prec Tuminus			{ Eint(processInt n true)}
*/
| n=Tint											{ Eint(processInt n false)}
| s=Tstring											{ Estr(s) }
| KW_TRUE											{ Ebool(true) }
| KW_FALSE											{ Ebool(false) }
| Tlpar ; Trpar										{ Eunit }
| KW_THIS											{ Ethis }
| KW_NULL											{ Enull }
| Tlpar ; e = exprVal ; Trpar							{ e }
| ac = access ; Tequal ; e = expr					{ Eassign(ac,e) }
| ac = access										{ Eaccess(ac) }
| ac = access ; a = argTypes ; Tlpar ;
	arg=separated_list(Tcomma, expr) ; Trpar		{ Ecall(ac,a,arg) }
| KW_NEW ; id = Tident ; a = argTypes ; Tlpar ;
	arg=separated_list(Tcomma, expr) ; Trpar		{ Einstantiate(id,a,arg) }
| Tbang ; e = expr									{ Eunaryop(UnaryNot, e) }
| Tminus ; e = expr			%prec Tuminus			{ Eunaryop(UnaryMinus, e) }
| e1 = expr; op = binop ; e2 = expr					{ Ebinop(op, e1,e2) }
| KW_IF ; Tlpar ; cnd = expr ; Trpar ;
	ibody = expr ; KW_ELSE ; ebody = expr
							%prec KW_IF				{ Eif(cnd,ibody,ebody) }
| KW_IF ; Tlpar ; cnd = expr ; Trpar ;
	ibody = expr			%prec KW_IF				{Eif(cnd,ibody, dummyLoc
														(Eblock([])) $endpos)}
| KW_WHILE ; Tlpar ; cnd = expr ; Trpar ;
	body = expr				%prec KW_WHILE			{ Ewhile(cnd, body) }
| KW_RETURN ; e = expr								{ Ereturn(e) }
| KW_RETURN											{ Ereturn(dummyLoc
															Eunit $endpos) }
| KW_PRINT ; Tlpar ; e = expr ; Trpar				{ Eprint(e) }
| Tlbra ;
	e = separated_list(Tsemicolon, blockval) ;
	Trbra											{ Eblock(e) }
;

access:
| i = Tident											{ AccIdent(i) }
| e = expr ; Tdot ; i = Tident						{ AccMember(e,i) }
;

argTypes:
|													{ EmptyAType }
| Tlbracket ;
	t=separated_nonempty_list(Tcomma,typ) ;
	Trbracket										{ ArgType t }
;

typ:
| i = Tident ; argt = argTypes						{ (i,argt) }

%inline binop:
| KW_EQ			{ KwEqual }
| KW_NE			{ KwNEqual }
| Tdbeq			{ Equal }
| Tneq			{ NEqual }
| Tless			{ Less }
| Tgreater		{ Greater }
| Tleq			{ Leq }
| Tgeq			{ Geq }
| Tplus			{ Plus }
| Tminus		{ Minus }
| Ttimes		{ Times }
| Tdiv			{ Div }
| Tmod			{ Mod }
| Tland			{ Land }
| Tlor			{ Lor }
;

param:
| id=Tident ; Tcolon ; t=typ			{ (id,t) }
;

param_type:
| id=Tident ; Tsubtype ; t=typ			{ { name=id; rel=SubclassOf; oth=t} }
| id=Tident ; Tsupertype; t=typ			{ { name=id; rel=SuperclassOf; oth=t} }
| id=Tident								{ { name=id; rel=NoClassRel;
											oth=emptyType} }
;

param_type_class:
| Tplus ; pt=param_type					{ (pt,TMplus) }
| Tminus; pt=param_type					{ (pt,TMminus) }
| pt=param_type							{ (pt,TMneutral) }
;

blockval:
| e = expr		{ Bexpr e }
| v = var		{ Bvar v }
;

var:
| KW_VAR ; i = Tident ; Tequal ; e = expr			{ { v = Vvar(i,NoType,e);
														vloc =
														 {loc_beg=$startpos ;
														  loc_end=$endpos } } }
| KW_VAR ; i = Tident ; Tcolon ; t = typ ;
	Tequal ; e = expr								{ { v = Vvar(i,Type(t),e) ;
														vloc =
														 {loc_beg=$startpos ;
														  loc_end=$endpos } } }
| KW_VAL ; i = Tident ; Tequal ; e = expr			{ { v = Vval(i,NoType,e) ;
														vloc =
														 {loc_beg=$startpos ;
														  loc_end=$endpos } } }
| KW_VAL ; i = Tident ; Tcolon ; t = typ ;
	Tequal ; e = expr								{ { v = Vval(i,Type(t),e) ;
														vloc =
														 {loc_beg=$startpos ;
														  loc_end=$endpos } } }
;

