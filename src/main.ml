open Format
open Lexing


let locateError pos file =
	let l = pos.pos_lnum in                                                       
	let c = pos.pos_cnum - pos.pos_bol + 1 in                                     
	sprintf "File \"%s\", line %d, characters %d-%d:\n" file l (c-1) c


(*************************** MAIN ********************************************)
let () =
	let parseOnly = ref false in
	let sourceFilePath = ref "" in
	let argParams = [("--parse-only", Arg.Unit (fun () -> parseOnly := true),
						"Stop after parsing the source file")] in
	let argAnonFct = (fun str -> sourceFilePath := str) in
	let argUsage = "Usage: pscala [options] sourceFile.scala" in

	Arg.parse argParams argAnonFct argUsage;
	
	if !sourceFilePath = "" then begin
		eprintf "Nothing to compile.\n@?";
		exit 2
	end;

	if not (Filename.check_suffix !sourceFilePath ".scala") then begin
		eprintf "A scala source file must end with \".scala\".\n@?";
		Arg.usage argParams argUsage;
		exit 2
	end;

	let sourceHandle = (try open_in !sourceFilePath
		with Sys_error s -> eprintf "Error: %s\n@?" s; exit 2)
	in
	let lexbuf = Lexing.from_channel sourceHandle in
	
	let ast = (try
		Parser.prgm Lexer.token lexbuf
	with
	| Lexer.Lexical_error c ->
		let loc = locateError (Lexing.lexeme_start_p lexbuf) !sourceFilePath in
		eprintf "%sLexical error: %s\n@?" loc c;
		exit 1
	| Ast.Parsing_error c ->
		let loc = locateError (Lexing.lexeme_start_p lexbuf) !sourceFilePath in
		eprintf "%sParsing error: %s\n@?" loc c;
		exit 1
	| Parser.Error ->
		let loc = locateError (Lexing.lexeme_start_p lexbuf) !sourceFilePath in
		eprintf "%sSyntax error.\n@?" loc;
		exit 1
	) in
	close_in sourceHandle (* ;
	AstPrinter.print_expr Format.std_formatter ast;
	print_newline () *)

