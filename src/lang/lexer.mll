
{
open Lexing
open Parser

exception Lexical_error of string

let lexicalError errStr =
	raise (Lexical_error errStr)

let keyword_list = [
	"class",	KW_CLASS;
	"def",		KW_DEF;
	"else",		KW_ELSE;
	"eq",		KW_EQ;
	"extends",	KW_EXTENDS;
	"false",	KW_FALSE;
	"if",		KW_IF;
	"ne",		KW_NE;
	"new",		KW_NEW;
	"null",		KW_NULL;
	"object",	KW_OBJECT;
	"override",	KW_OVERRIDE;
	"print",	KW_PRINT;
	"return",	KW_RETURN;
	"this",		KW_THIS;
	"true",		KW_TRUE;
	"val",		KW_VAL;
	"var",		KW_VAR;
	"while",	KW_WHILE;
	]
let keywordsHT = Hashtbl.create 25
let () = List.iter (fun (x,y) -> Hashtbl.add keywordsHT x y) keyword_list

let string_of_list l =
	let len = List.length l in
	let out = Bytes.create len in
	List.iteri (fun pos c -> Bytes.set out (len-pos-1) c) l;
	out

let escapedCharToReg = function
| '\\'	-> '\\'
| 'n'	-> '\n'
| 't'	-> '\t'
| '"'	-> '"'
| _ 	-> assert false (* This portion of code should never be called *)

let newline lexbuf =                                                        
	let pos = lexbuf.lex_curr_p in
	lexbuf.lex_curr_p <-                                                      
		{ pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }
		
}

let escChar = '\\' ([ 'n' 't' '"' '\\' ] as escaped)
let regChar = ['\032'-'\033' '\035'-'\091' '\093'-'\126']
let alpha = [ 'a'-'z' 'A'-'Z' ]
let digit = [ '0'-'9' ]

(******************************************************************************
*************** TOKENS (ENTRY POINT) *****************************************)

let whitespace = [' ' '\t']

rule token = parse
| '\n'				{ newline lexbuf ; token lexbuf }
| whitespace+		{ token lexbuf }
| ','				{ Tcomma }
| '('				{ Tlpar }
| ')'				{ Trpar }
| '['				{ Tlbracket }
| ']'				{ Trbracket }
| ">:"				{ Tsupertype }
| "<:"				{ Tsubtype }
| "=="				{ Tdbeq}
| "!="				{ Tneq}
| "<="				{ Tleq }
| ">="				{ Tgeq }
| '<'				{ Tless }
| '>'				{ Tgreater }
| '='				{ Tequal }
| '!'				{ Tbang }
| '{'				{ Tlbra }
| '}'				{ Trbra }
| ':'				{ Tcolon }
| ';'				{ Tsemicolon }
| '+'				{ Tplus }
| '-'				{ Tminus }
| '/'				{ Tdiv }
| '*'				{ Ttimes }
| '%'				{ Tmod }
| "&&"				{ Tland }
| "||"				{ Tlor }
| '.'				{ Tdot }
| "//" [^'\n']*		{ token lexbuf }
| "/*"				{ comment lexbuf }
| ('0' | ['1'-'9'] digit*) as nums				{ Tint (nums) }
	(* Keep it as a string: the parser will be able to check if neg or pos *)
| "0"				{ lexicalError "Unexpected leading zero(es)."}
| '"'				{ cstring [] lexbuf }
| (alpha (alpha | digit | '_')*) as ident		{ 
					try Hashtbl.find keywordsHT ident
					with Not_found -> Tident(ident) }
| eof 				{ Teof}
| _ as c			{lexicalError ("Illegal character: '"^
							(String.make 1 c)^"'.")}


(******************************************************************************
*************** STRINGS ******************************************************)

and cstring curChars = parse
| '"'				{ Tstring (string_of_list curChars) }
| regChar as c		{ cstring (c::curChars) lexbuf }
| escChar			{ cstring ((escapedCharToReg escaped)::curChars) lexbuf }
| eof				{ lexicalError "Missing terminating \" character." }

(******************************************************************************
*************** COMMENTS *****************************************************)

and comment = parse
| "*/"				{ token lexbuf }
| [^'\n']			{ comment lexbuf }
| '\n'				{ newline lexbuf ; comment lexbuf }
| "/*"				{ lexicalError "Unexpected symbol '/*' in a commentary." }
| eof				{ lexicalError "Missing terminating */ symbol." }
