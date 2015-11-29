(*****************************************
*** DEBUG FILE - DUMPS ALL TOKENS ********
*****************************************)

%{
	open Ast

	let dump x =
		Printf.printf "%s\n" x
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

%start prgm
%type <unit> prgm

%%

prgm:
| dump*;Teof			{dump "We were here" }
;

dump:
| KW_CLASS		{ dump "KW_CLASS" }
| KW_DEF		{ dump "KW_DEF" }
| KW_ELSE		{ dump "KW_ELSE" }
| KW_EQ		{ dump "KW_EQ" }
| KW_EXTENDS		{ dump "KW_EXTENDS" }
| KW_FALSE		{ dump "KW_FALSE" }
| KW_IF		{ dump "KW_IF" }
| KW_NE		{ dump "KW_NE" }
| KW_NEW		{ dump "KW_NEW" }
| KW_NULL		{ dump "KW_NULL" }
| KW_OBJECT		{ dump "KW_OBJECT" }
| KW_OVERRIDE		{ dump "KW_OVERRIDE" }
| KW_PRINT		{ dump "KW_PRINT" }
| KW_RETURN		{ dump "KW_RETURN" }
| KW_THIS		{ dump "KW_THIS" }
| KW_TRUE		{ dump "KW_TRUE" }
| KW_VAL		{ dump "KW_VAL" }
| KW_VAR		{ dump "KW_VAR" }
| KW_WHILE		{ dump "KW_WHILE" }
| Tcomma		{ dump "Tcomma" }
| Tlpar		{ dump "Tlpar" }
| Trpar		{ dump "Trpar" }
| Tsupertype		{ dump "Tsupertype" }
| Tsubtype		{ dump "Tsubtype" }
| Tdbeq		{ dump "Tdbeq" }
| Tneq		{ dump "Tneq" }
| Tleq		{ dump "Tleq" }
| Tgeq		{ dump "Tgeq" }
| Tless		{ dump "Tless" }
| Tgreater		{ dump "Tgreater" }
| Tequal		{ dump "Tequal" }
| Tbang		{ dump "Tbang" }
| Tlbra		{ dump "Tlbra" }
| Trbra		{ dump "Trbra" }
| Tcolon		{ dump "Tcolon" }
| Tsemicolon		{ dump "Tsemicolon" }
| Tlbracket		{ dump "Tlbracket" }
| Trbracket		{ dump "Trbracket" }
| Tplus		{ dump "Tplus" }
| Tminus		{ dump "Tminus" }
| Ttimes		{ dump "Ttimes" }
| Tdiv		{ dump "Tdiv" }
| Tmod		{ dump "Tmod" }
| Tland		{ dump "Tland" }
| Tlor		{ dump "Tlor" }
| Tdot		{ dump "Tdot" }
| s=Tint		{ Printf.printf "Tint=%s" s }
| s=Tstring		{ Printf.printf "Tstring=%s" s }
| s=Tident		{ Printf.printf "Tident=%s" s }
;
