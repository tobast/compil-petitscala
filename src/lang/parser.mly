%{
	open Ast

	let chkMain cl =
		let valid = (cl.cname = "Main") && (cl.classTypes = []) &&
		(cl.cparams = []) && (fst (cl.extends.extType) = "Any") in
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
//%type <Ast.prgm> prgm
%type <Ast.expr> prgm

%%


prgm: /* TEMP */
| e = expr ; Teof							{ e }
/*
prog:
| cl=class* ; mcl=classMain ; Teof			{ { classes = cl ; main = mcl}}
;

classMain:
	KW_OBJECT ; id=Tident ; Tlbra ;
	dec = separated_list(Tsemicolon, decl) ; Trbra
		{ if id = "Main" then { name = id ; classTypes=[]; params=[];
								extends = [] ; body = dec }
		  else raise (ParsingError ("Expected object named Main, got "^id^"."))
		}
			
;

class:
	KW_CLASS ; name=Tident; parTC = separated_list(Tcomma, paramTypeClass) ;


decl:;
*/

expr:
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
	ibody = expr			%prec KW_IF				{Eif(cnd,ibody,Eblock([]))}
| KW_WHILE ; Tlpar ; cnd = expr ; Trpar ;
	body = expr				%prec KW_WHILE			{ Ewhile(cnd, body) }
| KW_RETURN ; e = expr								{ Ereturn(e) }
| KW_RETURN											{ Ereturn(Eunit) }
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

blockval:
| e = expr		{ Bexpr e }
| v = var		{ Bvar v }
;

var:
| KW_VAR ; i = Tident ; Tequal ; e = expr			{ Vvar(i,NoType,e) }
| KW_VAR ; i = Tident ; Tcolon ; t = typ ;
	Tequal ; e = expr								{ Vvar(i,Type(t),e) }
| KW_VAL ; i = Tident ; Tequal ; e = expr			{ Vval(i,NoType,e) }
| KW_VAL ; i = Tident ; Tcolon ; t = typ ;
	Tequal ; e = expr								{ Vval(i,Type(t),e) }
;

