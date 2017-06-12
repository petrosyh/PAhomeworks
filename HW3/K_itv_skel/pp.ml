(*
 * SNU 4190.310 Programming Languages 
 *
 * K- Interpreter
 *)

open K.K

module type KMINUS_PP =
  sig
    val pp: cmd -> unit
  end

module Kminus_PP : KMINUS_PP =
  struct
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
        | ADD (e1, e2) -> ps "ADD" [pe e1; pe e2]
        | MINUS e1 -> ps "MINUS" [pe e1]
		| TRUE -> ps "TRUE" []
		| FALSE -> ps "FALSE" []
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
		| WHILE (e, c1) -> ps "WHILE" [pe e; pc c1]
 
    let pp c =  List.iter print_endline (pc c)
  end
