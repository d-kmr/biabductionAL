(*------------------------------*)
(* Biabduction                  *)
(* usage: biabdAL -f input.bi   *)
(*------------------------------*)
open Tools;;
open Slsyntax;;
open Biabd;;
open BiabdData;;

module Parser = Slsyntax_parser_entl;;
module Lexer = Slsyntax_lexer_entl;;

(* read from file *)
let inputstr_stdin () =
  let x = ref "" in
  try
    while true do
      x := !x ^ (input_line stdin) ^ "\n"
    done ;
    "" (* dummy *)
  with End_of_file -> !x ;;

let inputstr_file filename =
  let x = ref "" in
  let ic = open_in filename in
  try
	while true do
	  x := !x ^ (input_line ic) ^ "\n"
	done ;
	"" (* dummy *)
  with End_of_file -> close_in ic;!x
;;

(* Options *)
let _fname = ref "";;
let f_help () = print_endline "help";;
let set_filename fname = _fname := fname;;
let set_tag tag = Ftools.p_opt := tag :: !Ftools.p_opt;;
let setDebug () = set_tag "BIABD_debug";;
let setDebug2 () = set_tag "BIABD_debug";set_tag "BIABD_debug2";;
let _balimit = ref maxLoop;;
let set_balimit n = _balimit := min n maxLoop;;
let _outputFlag = ref true;;
let unset_output () = _outputFlag := false;;
let _timeFlag = ref false;;
let set_time () = _timeFlag := true;;

let msgUsage = "USAGE: biabdAL -f <filename>.bi [-balimit <num>|-debug|-nooutput|-time|..]\n";;

let speclist = [
    ("-debug", Arg.Unit setDebug, "Debugging mode (Same as -deb BIABD_debug)");
    ("-debug2", Arg.Unit setDebug2, "Deeper Debugging mode (Same as -deb BIABD_debug -deb BIABD_debug2)");    
    ("-deb", Arg.String set_tag, "show with tag: BIABD_debug, BIABD_time");
    ("-f", Arg.String set_filename, "Input file");
    ("-nosimpl", Arg.Unit unset_simpl, "Disable simplification of formulas");
    ("-balimit", Arg.Int set_balimit, "set limit of biabduction answers");
    ("-nooutput",Arg.Unit unset_output, "Do not output solutions");
    ("-time",Arg.Unit set_time, "Time checking mode");        
];;

(* parser *)
let parse filename =  
  let lexbuf = Lexing.from_string (inputstr_file filename) in
  Lexing.set_filename lexbuf filename;
  try
    Parser.main Lexer.token lexbuf
  with
    ParseError (errstart,errend,errline) ->
    Format.printf "@[Parse error \"%s\", line %d:@."
      (lexbuf.lex_start_p.pos_fname)
      errline;
    let (st,pos,len) = text_getaround 20 lexbuf.lex_buffer errstart in
    let errmes = "Unexpected Input: " in
    Format.printf "@[%s%s@." errmes (Bytes.sub_string lexbuf.lex_buffer st len);
    exit 0
;;

let myMain() =
  let display_message () = print_endline msgUsage in
  
  Arg.parse speclist print_endline msgUsage;
  if !_fname = "" then display_message () else
    let (sh1,sh2L) =  parse !_fname in
    let (p1,ss1) = sh1 in
    let (_,ss2) = List.hd sh2L in
    ANSITerminal.(printf [Background Magenta; Foreground White; Bold]) "Biabduction Query";
    print_endline "";
    Format.printf "@[P: %a@." P.pp p1;
    Format.printf "@[A: %a@." SS.pp ss1;
    Format.printf "@[B: %a@." SS.pp ss2;
    print_newline ();
    
    ANSITerminal.(printf [Background Magenta; Foreground White; Bold]) "Biabduction Query (simplified)";
    print_endline "";
    Format.printf "@[P: %a@." P.pp (P.syntactical_simpl p1);
    Format.printf "@[A: %a@." SS.pp (SS.syntactical_simpl ss1);
    Format.printf "@[B: %a@." SS.pp (SS.syntactical_simpl ss2);
    print_newline ();
    
    match biabduction !_balimit [] p1 ss1 ss2 with
    | ([],pp) ->
       print_newline ();
       ANSITerminal.(printf [Background Red; Foreground White; Bold]) "No Answer";
       print_endline ""
    | ba_out ->
       let num = List.length (fst ba_out) in
       let showNum n =
         print_endline "";
         ANSITerminal.(printf [Background Magenta; Bold; Foreground White] "Number of Answers: %d") n;
         print_endline""
       in
       if !_outputFlag
       then
         begin           
           ANSITerminal.(printf [Background Magenta; Foreground White]) "Biabduction Answer(s)";
           print_endline "";
           BAoutput.println ba_out;
           showNum num
         end
       else
         showNum num
;;

let () =
  let start = Unix.gettimeofday () in
  myMain ();
  let stop = Unix.gettimeofday () in
  if !_timeFlag then Format.printf "Execution time: %fs\n\n%!" (stop -. start) else ()
;;
