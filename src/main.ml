open Ast
open Format
open Lexing

let formatErrorLoc begLoc endLoc file =
	let line = begLoc.pos_lnum in
	let begC = begLoc.pos_cnum - begLoc.pos_bol + 1 in
	let endC = endLoc.pos_cnum - endLoc.pos_bol + 1 in
	sprintf "File \"%s\", line %d, characters %d-%d:\n" file line (begC-1) endC

let locateError pos file =
	let l = pos.pos_lnum in 
	let c = pos.pos_cnum - pos.pos_bol + 1 in
	sprintf "File \"%s\", line %d, characters %d-%d:\n" file l (c-1) c

let keepBacktrace = ref false
let printBacktrace bt =
	if !keepBacktrace then
		eprintf "Backtrace:\n%s@?" bt

let formatterOfFile s =
	try Format.formatter_of_out_channel (open_out s)
	with
	| exc ->
		eprintf "Could not open file \"%s\" for writing: %s\n"
			s (Printexc.to_string exc);
		exit 2

(*************************** MAIN ********************************************)
let () =
	let parseOnly = ref false in
	let typeOnly = ref false in
	let outFile = ref "" in
	let sourceFilePath = ref "" in
	let argParams = [("--parse-only", Arg.Unit (fun () -> parseOnly := true),
						"Stop after parsing the source file") ;
					 ("--type-only", Arg.Unit (fun () -> typeOnly := true),
					 	"Stop after typing the source file") ;
					 ("-o", Arg.String (fun s -> outFile := s),
					 	"Sets the output file. '-' for stdout.") ;
					 ("--backtrace", Arg.Unit
					 	(fun () -> keepBacktrace := true ;
							Printexc.record_backtrace true),
					 	"Keeps and prints the backtrace in case of error.")] in
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
	| Failure c ->
		let loc = locateError (Lexing.lexeme_start_p lexbuf) !sourceFilePath in
		eprintf "%sError: %s\n@?" loc c;
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
	close_in sourceHandle ;

	if !parseOnly then
		exit 0;
	
	let typAst = 
		(try Typer.doPrgmTyping ast
		with
		| Typer.TyperError (pos, msg) ->
			let bt = Printexc.get_backtrace () in
			let loc = formatErrorLoc pos.loc_beg pos.loc_end !sourceFilePath in
			eprintf "%sConsistency error: %s\n@?" loc msg;
			printBacktrace bt ;
			exit 1
		| Typer.InternalError msg ->
			let bt = Printexc.get_backtrace () in
			eprintf "Typer internal error: %s\n@?" msg ;
			printBacktrace bt ;
			exit 2
		| ex ->
			let bt = Printexc.get_backtrace () in
			eprintf "Unknown internal error during typing: %s\n@?"
				(Printexc.to_string ex) ;
			printBacktrace bt ;
			exit 2)
	in

	if !typeOnly then
		exit 0;
	
	let outFormatter = (match !outFile with
		| "-" -> Format.std_formatter
		| "" -> formatterOfFile
			((Filename.chop_suffix !sourceFilePath ".scala")^".s")
		| s -> formatterOfFile s) in

	(*** NOW COMPILE! ***)
	let compiled =
		(try Compile.compileTypPrgm typAst
		with
		| Compile.InternalError msg ->
			let bt = Printexc.get_backtrace () in
			eprintf "Compiler internal error: %s\n@?" msg ;
			printBacktrace bt ;
			exit 2
		)
	in

	fprintf outFormatter "%a@?" X86_64.print_program compiled

