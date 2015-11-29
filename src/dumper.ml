(*****************************************
*** DEBUG FILE - DUMPS ALL TOKENS ********
*****************************************)

open Lexing
open Format

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

	let sourceHandle = open_in !sourceFilePath in
	let lexbuf = Lexing.from_channel sourceHandle in
	
	DumpingParser.prgm Lexer.token lexbuf ; 
	close_in sourceHandle (* ;
	AstPrinter.print_expr Format.std_formatter ast;
	print_newline () *)

