
{

exception Lexical_error of Lexing.position * string

let lexicalError errStr lexbuf =
	raise (Lexical_error (lexbuf.lex_curr_p, errStr))

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

}

let escChar = '\\' ([ 'n' 't' '"' '\\' ] as escaped)
let regChar = ['\032'-'\033' '\035'-'\091' '\093'-'\126']
let alpha = [ 'a'-'z' 'A'-'Z' ]
let digit = [ '0'-'9' ]

(******************************************************************************
*************** TOKENS (ENTRY POINT) *****************************************)

let whitespace = [' ' '\t' '\n']

rule token = parse
| whitespace+		{ file lexbuf }
| "//"_*'\n'		{ file lexbuf }
| "/*"				{ comment lexbuf }
| ','				{ Tcomma }
| '('				{ Tlbracket }
| ')'				{ Trbracket }
| ">:"				{ Trightdafuq }
| "<:"				{ Tleftdafuq }
| "=="				{ Tdbequal }
| "!="				{ Tnequal }
| "<="				{ Tleq }
| ">="				{ Tgeq }
| '<'				{ Tless }
| '>'				{ Tgreater }
| '='				{ Tequal }
| '!'				{ Tbang }
| '{'				{ Tlbrace }
| '}'				{ Trbrace }
| ':'				{ Tcolon }
| ';'				{ Tsemicolon }
| "&&"				{ Tland }
| "||"				{ Tlor }
| '.'				{ Tdot }
| ('0' | ['1'-'9'] digit*) as nums				{ Tint (int_of_string nums) }

| "00"				{ lexicalError "Unexpected leading zeroes." lexbuf }
| (alpha (alpha | digit | '_')*) as ident		{ 
					try Hashtbl.find keywordsHT ident
					with Not_found -> Tident(ident) }

| eof 				{ Teof}


(******************************************************************************
*************** STRINGS ******************************************************)

and cstring curChars = parse
| '"'				{ Tstring (string_of_list curChars) }
| regChar as c		{ cstring (c::curChar) lexbuf }
| escChar			{ cstring ((escapedCharToReg escaped)::curChars) lexbuf }
| eof				{ lexicalError "Missing terminating \" character." lexbuf }

(******************************************************************************
*************** COMMENTS *****************************************************)

and comment = parse
| "*/"				{ token lexbuf }
| _					{ comment lexbuf }
| "/*"				{ lexicalError 
						"Unexpected symbol '/*' in a commentary." lexbuf }
| eof				{ lexicalError "Missing terminating */ symbol." lexbuf }
