(*
 * SNU 4541.664A Program Analysis 2017 Spring
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 *)


(*
 * program
 *)
  
type id = string
type exp =
  | NUM of int
  | VAR of id
  | DEREF of id
  | AT of id
  | ADD of exp * exp
  | MINUS of exp
  | TRUE
  | FALSE
  | READ
  | NOT of exp
  | ANDALSO of exp * exp
  | ORELSE of exp * exp
  | LESS of exp * exp
  
type cmd =
  | SKIP
  | SEQ of cmd * cmd        (* sequence *)
  | IF of exp * cmd * cmd   (* if-then-else *)
  | WHILE of exp * cmd      (* while *)
  | ASSIGN of id * exp      (* assgin to variable *)
  | PTRASSIGN of id * exp

type program = cmd

let rec exp_to_str = function
  | NUM i -> string_of_int i
  | VAR x -> x
  | DEREF x -> "*" ^ x
  | AT x -> "&" ^ x
  | ADD (e1, e2) -> "(" ^ exp_to_str e1 ^ " + " ^ (exp_to_str e2) ^ ")"
  | MINUS e -> "-(" ^ exp_to_str e ^ ")"
  | TRUE -> "true"
  | FALSE -> "false"
  | READ -> "read()"
  | NOT e -> "not" ^ exp_to_str e
  | ANDALSO (e1, e2) ->  "(" ^ exp_to_str e1 ^ " && " ^ (exp_to_str e2) ^ ")"
  | ORELSE (e1, e2) -> "(" ^ exp_to_str e1 ^ " || " ^ (exp_to_str e2) ^ ")"
  | LESS (e1, e2) -> "(" ^ exp_to_str e1 ^ " < " ^ (exp_to_str e2) ^ ")"

let rec cmd_to_str = function
  | SKIP -> "skip"
  | ASSIGN (x, e) -> x ^ " := " ^ exp_to_str e
  | PTRASSIGN (x, e) -> "*" ^ x ^ " := "^ exp_to_str e
  | SEQ (c1, c2) -> cmd_to_str c1 ^ ";\n" ^ cmd_to_str c2
  | IF (e, c1, c2) -> 
    "if (" ^ exp_to_str e ^ ")" ^ cmd_to_str c1 ^ "\n" ^ cmd_to_str c2
  | WHILE (e, c) -> 
    "while (" ^ exp_to_str e ^ ") do (" ^ cmd_to_str c ^ ")"



    let q x = ["\"" ^ x ^ "\""]
    let pfx = "  "
    let indent l = List.map (fun s -> pfx ^ s) l
    let rec comma = function [] -> []
      | [h] -> [h ^ ","]
      | (h :: t) -> h :: (comma t)
	let rec qs xs = match xs with
		[] -> []
		| [hd] -> (q hd)
		| hd::tl -> (comma (q hd))@(qs tl)
    let ps s l = 
		match l with 
		  [] -> [s]
		| (h :: t) -> 
			(s ^ "(")
          		:: (List.fold_left (fun l x -> (comma l) @ (indent x)) (indent h) t)
          		@ [(")")]
	let rec id_e (id,e) = (q id)@(pe e)
    and pe e =
        match e with
          NUM i -> ps "NUM" [[string_of_int i]]
        | VAR x -> ps "VAR" [q x]
        | DEREF x -> ps "DEREF" [q x]
		| AT x -> ps "AT" [q x]
		| ADD (e1, e2) -> ps "ADD" [pe e1; pe e2]
        | MINUS e1 -> ps "MINUS" [pe e1]
		| TRUE -> ps "TRUE" []
		| FALSE -> ps "FALSE" []
		| READ -> ps "READ" []
		| NOT e -> ps "NOT" [pe e]
		| ANDALSO (e1, e2) -> ps "ANDALSO" [pe e1; pe e2]
		| ORELSE (e1, e2) -> ps "ORELSE" [pe e1; pe e2]
		| LESS (e1, e2) -> ps "LESS" [pe e1; pe e2]

	and pc c =
		match c with
		  SKIP -> []
		| SEQ (c1, c2) -> ps "SEQ" [pc c1; pc c2]
        | IF (e, c1, c2) -> ps "IF" [pe e; pc c1; pc c2]
        | ASSIGN (i, e) -> ps "ASSIGN" [q i; pe e]
		| PTRASSIGN (i, e) -> ps "PTRASSIGN" [q i; pe e]
		| WHILE (e, c1) -> ps "WHILE" [pe e; pc c1]
 
    let pp c =  List.iter print_endline (pc c)


