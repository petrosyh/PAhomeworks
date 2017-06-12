(*
 * SNU 4541.664A Program Analysis
 * Main program driver
 *)

open Program

let src = ref ""
let opt_pp = ref false
let opt_hell = ref false
let opt_davinci = ref false

let main () = 
  Arg.parse
    [ ("-pp", Arg.Unit (fun _ -> opt_pp := true), "print pgm");
      ("-hell", Arg.Unit (fun _ -> opt_hell := true), "swHell analysis");
      ("-davinci", Arg.Unit (fun _ -> opt_davinci := true), "davinci analysis")]
    (fun x -> src := x)
    ("Usage : " ^ (Filename.basename Sys.argv.(0)) ^ " [-option] [filename] ");
  let lexbuf = Lexing.from_channel (if !src = "" then stdin else open_in !src) in
  let pgm = (Parser.program Lexer.start lexbuf) in
  if !opt_pp then (
	  let _ =print_endline "=== Printing Input Program ===" in
	  pp pgm
  )
  else if !opt_hell then (
    let result = SwHell.hellAnalyzer pgm in
    print_endline (SwHell.result_to_str result)
  )
  else if !opt_davinci then (
    let result = Davinci.davinciAnalyzer pgm in
    print_endline (Davinci.result_to_str result)
  )
  else
    print_endline "Please provide one of options! (-pp, -hell, -davinci)"
  
let _ = main ()
