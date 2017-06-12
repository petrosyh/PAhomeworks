(*
 * SNU 4541.664A Program Analysis 2017 Spring
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 *)


(*
 * davinvi analyzer
 *)

open Program 
open DomFunctor

exception Error of string

(* define Domain here *) 
(* module Var = *)
(*   struct *)
(*     type t = string *)
(*     let compare = compare *)
(*   end *)

(* module Loc = Var *)
(* module LocSet = PrimitiveSet(Loc) *)
(* module LocPowSet = PowerSetDomain (LocSet) *)

let loop_num = ref 0                     
(* abstract domain type *)
type z_hat =  ZSET of (int * int) list | TOP_Z | RINT
type bool_hat = TOP_BOOL | T | F | BOT_BOOL 
type loc_hat = LSET of string list 
                              
let botZhat = (ZSET []) 
(* abstract memory *)
type value = RVAL of (z_hat * bool_hat * loc_hat) | UNREACH  
type memory = id -> value
let resmem_list = ref []

(* bottom values *)
let botValue = RVAL (botZhat, BOT_BOOL, LSET [])
let botMemory = fun x -> botValue
let unreachMemory = fun x -> UNREACH
let failedValue = RVAL (TOP_Z, TOP_BOOL, LSET [])
let failedMemory = fun x -> failedValue
(* memory Operation *)
let store mem id v = fun x -> if (x = id) then v else mem(x)

let rec list_trim l =
  match l with
  | [] -> []
  | hd::tl -> if (List.mem hd tl) then list_trim tl else hd::(list_trim tl)

let rec used_vars_exp exp =
  (match exp with
   | NUM i -> []
   | VAR id | DEREF id | AT id -> id::[]
   | ADD (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
   | MINUS e -> used_vars_exp e
   | TRUE -> []
   | FALSE -> []
   | NOT e -> used_vars_exp e
   | ANDALSO (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
   | ORELSE (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
   | LESS (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
   | READ -> []
  )
    
let rec used_vars cmd =
  match cmd with
  | SKIP -> []
  | SEQ (cmd1, cmd2) -> (used_vars cmd1) @ (used_vars cmd2)
  | IF (e, cmd1, cmd2) -> (used_vars_exp e) @ (used_vars cmd1) @ (used_vars cmd2)
  | WHILE (e, cmd) -> (used_vars_exp e) @ (used_vars cmd)
  | ASSIGN (id, e) -> id::(used_vars_exp e)
  | PTRASSIGN (id, e) -> id::(used_vars_exp e)

let used_varlist cmd = list_trim (used_vars cmd)

(* memory pretty print : "do not" change here *)

let print_ipair : (int * int) -> unit = fun (a, b) ->
  let _ = print_string("(") in
  let _ = print_int(a) in
  let _ = print_string(", ") in
  let _ = print_int(b) in
  print_string(")")
              
              
let rec pp_zhat : z_hat -> unit = fun zhat ->
  match zhat with
  | RINT -> print_string("readint")
  | TOP_Z -> print_string("topZ")
  | ZSET [] -> print_string("botZ")
  | ZSET (hd::tl) ->
     let _ = print_ipair(hd) in
     let _ = print_string(", ") in
     begin
       match tl with
       | [] -> print_string(" ") 
       | _ -> (pp_zhat (ZSET tl))
     end
       
let pp_bool : bool_hat -> unit = fun b ->
  match b with
  | BOT_BOOL -> print_string("bottom") 
  | T -> print_string("T")
  | F -> print_string("F")
  | TOP_BOOL -> print_string("T, F")

let pp_value : value -> unit = fun v ->
  match v with
  | UNREACH ->
     begin
       let _ = print_string("(q, r) = UNREACH") in
       print_newline() 
     end                             
  | RVAL (itv, b, l) ->
     begin
       let _ = print_string("(q, r) = ") in
       let _ = pp_zhat(itv) in
       let _ = print_string(" bool : ") in
       let _ = pp_bool(b) in
       print_newline() 
     end    

let rec pp_memory : memory -> id list -> unit = fun mem -> (fun varlist ->
    match varlist with
    | [] -> ()
    | hd::tl ->
       begin
         match (mem(hd)) with
         | UNREACH ->
            begin
              let _ = print_string(hd ^ " -> (q, r) = UNREACH") in
              let _ = print_newline() in
              pp_memory mem tl
            end                             
         | RVAL (itv, b, l) ->
            begin
              let _ = print_string(hd ^ " -> (q, r) = ") in
              let _ = pp_zhat(itv) in
              let _ = print_string(" bool : ") in
              let _ = pp_bool(b) in
              let _ = print_newline() in
              pp_memory mem tl
            end
       end
  )

                                                             
let rec compare_mem m1 m2 varlist =
  match varlist with
  | [] -> true
  | hd::tl -> (m1(hd) = m2(hd)) && (compare_mem m1 m2 tl)

(* Join and Meet *)
let rec list_intersection l1 l2 =
  match l1 with
  | [] -> []
  | hd::tl -> if (List.mem hd l2) then hd::(list_intersection tl l2) else (list_intersection tl l2)

let zhat_join z1 z2 =
  match z1, z2 with
  | RINT, _ -> RINT
  | _, RINT -> RINT
  | TOP_Z, _ -> TOP_Z
  | _, TOP_Z -> TOP_Z
  | ZSET l1, ZSET l2 -> ZSET (list_trim (l1 @ l2)) 

let zhat_meet z1 z2 =
  match z1, z2 with
  | RINT, _ -> z2
  | _, RINT -> z1
  | TOP_Z, _ -> z2
  | _, TOP_Z -> z1
  | ZSET l1, ZSET l2 -> ZSET (list_intersection l1 l2)
                             
let bool_join b1 b2 =
  match b1, b2 with
  | BOT_BOOL, _ -> b2
  | _, BOT_BOOL -> b1
  | T, F -> TOP_BOOL
  | F, T -> TOP_BOOL
  | T, T -> T
  | F, F -> F
  | _, TOP_BOOL -> TOP_BOOL
  | TOP_BOOL, _ -> TOP_BOOL

let bool_meet b1 b2 =
  match b1, b2 with
  | BOT_BOOL, _ -> BOT_BOOL
  | _, BOT_BOOL -> BOT_BOOL
  | T, F -> BOT_BOOL
  | F, T -> BOT_BOOL
  | T, T -> T
  | F, F -> F
  | _, TOP_BOOL -> b1
  | TOP_BOOL, _ -> b2

let loc_join l1 l2 =
  match l1, l2 with
  | LSET loc1, LSET loc2 -> LSET (list_trim (loc1 @ loc2))


let loc_meet l1 l2 =
  match l1, l2 with
  | LSET loc1, LSET loc2 -> LSET (list_intersection loc1 loc2)

let join v1 v2 =
  match v1, v2 with
  | UNREACH, _ -> v2
  | _, UNREACH -> v1
  | RVAL (z1, b1, l1), RVAL (z2, b2, l2) -> RVAL (zhat_join z1 z2, bool_join b1 b2, loc_join l1 l2)


let meet v1 v2 =
  match v1, v2 with
  | UNREACH, _ -> UNREACH
  | _, UNREACH -> UNREACH
  | RVAL (z1, b1, l1), RVAL (z2, b2, l2) -> RVAL (zhat_meet z1 z2, bool_meet b1 b2, loc_meet l1 l2)

let rec memory_join m1 m2 = fun x -> (join (m1(x)) (m2(x)))
let rec memory_meet m1 m2 = fun x -> (meet (m1(x)) (m2(x)))


(* widen & narrow *)

let rec partial_botMemory mem varlist =
  match varlist with
  | [] -> mem
  | hd::tl -> (store (partial_botMemory mem tl) hd botValue)

let fix botm f varlist =
  let rec fix_rec m varlist =
    let m' = f m in
    (* let _ = print_string("in fix m :") in *)
    (* let _ = pp_memory m varlist in *)
    (* let _ = print_string("in fix m' :") in *)
    (* let _ = pp_memory m' varlist in  *)
    if (!loop_num > 200)
    then m'
    else (
      if (compare_mem m m' varlist)
      then m
      else (fix_rec m' varlist))
  in
  (fix_rec botm varlist)
    
(* TODO : implement davinchi aux func - maybe i should fix it*)

let max_nlist : (int * int) list -> (int * int) = fun l ->
  match l with
  | [] -> raise (Error ("it can't be empty"))
  | hd :: tl -> let rec max_nlist_aux n l' =
                  match l' with
                  | [] -> n
                  | hd' :: tl' -> if (hd' < n) then (max_nlist_aux n tl') else (max_nlist_aux hd' tl')
                in (max_nlist_aux hd tl)

let min_nlist : (int * int) list -> (int * int) = fun l ->
  match l with
  | [] -> raise (Error ("it can't be empty"))
  | hd :: tl -> let rec min_nlist_aux n l' =
                  match l' with
                  | [] -> n
                  | hd' :: tl' -> if (hd' < n) then (min_nlist_aux hd' tl') else (min_nlist_aux n tl')
                in (min_nlist_aux hd tl)
                     
let dav_mod : int -> (int * int) = fun i ->
  if i >= 0 then (i / 1867, i mod 1867) else ((i / 1867) - 1, 1867 + (i mod 1867))
                                               
let mod_sum : ((int * int) * (int * int)) -> (int * int) = fun (e1, e2) ->
  let (q1, r1) = e1 in
  let (q2, r2) = e2 in
  let a1 = q1 * 1867 + r1 in
  let a2 = q2 * 1867 + r2 in
  dav_mod (a1 + a2)

let mod_minus : (int * int) -> (int * int) = fun e ->
  let (q, r) = e in
  let a = q * 1867 + r in
  (dav_mod (- a))
    
let mod_less : ((int * int) * (int * int)) -> bool = fun (e1, e2) ->
  let (q1, r1) = e1 in
  let (q2, r2) = e2 in
  let a1 = q1 * 1867 + r1 in
  let a2 = q2 * 1867 + r2 in
  (a1 < a2)
    
let dav_sum : (z_hat * z_hat) -> z_hat = fun (e1, e2) ->
  match e1, e2 with
  | ZSET [], _ -> botZhat
  | _, ZSET [] -> botZhat
  | RINT, _ -> RINT
  | _, RINT -> RINT
  | TOP_Z, _ -> TOP_Z
  | _, TOP_Z -> TOP_Z
  | ZSET z1, ZSET z2 -> ZSET
                          (List.fold_left
                             (fun z2join z1elt ->
                               let z2' = (List.map (fun z2elt -> (mod_sum (z1elt, z2elt))) z2) in
                               (list_trim (z2join @ z2')))
                             []
                             z1)
                          
let dav_minus : z_hat -> z_hat = fun e ->
  match e with
  | RINT -> RINT
  | ZSET [] -> botZhat
  | TOP_Z -> TOP_Z
  | ZSET z -> ZSET (List.map mod_minus z)

                   
(* let dav_deref : *)
                   
let rec eval : (memory * Program.exp) -> value = fun (mem, e) ->
  match e with
  | NUM i -> RVAL (ZSET [(dav_mod i)], BOT_BOOL, LSET [])
  | VAR x -> mem(x)
  | ADD (e1, e2) ->
     begin
       match (eval (mem, e1)), (eval (mem, e2)) with
       | UNREACH, _ -> botValue
       | _, UNREACH -> botValue
       | RVAL (z1, _, _), RVAL (z2, _, _) -> RVAL (dav_sum (z1, z2), BOT_BOOL, LSET [])
     end
  | MINUS e ->
     begin
       match (eval (mem, e)) with
       | UNREACH -> botValue
       | RVAL (z, _, _) -> RVAL (dav_minus z, BOT_BOOL, LSET [])
     end
  | DEREF id ->
     begin
       match mem(id) with
       | UNREACH -> botValue
       | RVAL (z, b, l) ->
          begin
            match l with
            | LSET l' ->
               begin
                 let rec join_all_loc mem l =
                   match l with
                   | [] -> botValue
                   | hd::tl -> (join (mem(hd)) (join_all_loc mem tl))
                 in (join_all_loc mem l')
               end
          end
     end
  | AT id ->
     begin
       RVAL (botZhat, BOT_BOOL, LSET [id])
     end
  | TRUE -> RVAL (botZhat, T, LSET [])
  | FALSE -> RVAL (botZhat, F, LSET [])
  | NOT e ->
     begin
       match (eval (mem, e)) with
       | UNREACH -> botValue
       | RVAL (_, b, _) -> 
          begin
            match b with
            | BOT_BOOL -> botValue
            | T -> RVAL (botZhat, F, LSET [])
            | F -> RVAL (botZhat, T, LSET [])
            | TOP_BOOL -> RVAL (botZhat, TOP_BOOL, LSET [])
          end
     end
  | ANDALSO (e1, e2) ->
     begin
       match (eval (mem, e1)), (eval (mem, e2)) with
       | UNREACH, _ -> botValue
       | _, UNREACH -> botValue
       | RVAL (_, b1, _), RVAL (_, b2, _) ->
          begin
            match b1, b2 with
            | BOT_BOOL, _ -> botValue
            | _, BOT_BOOL -> botValue
            | F, _ -> RVAL (botZhat, F, LSET [])
            | _, F -> RVAL (botZhat, F, LSET [])
            | T, T -> RVAL (botZhat, T, LSET [])
            | T, TOP_BOOL -> RVAL (botZhat, TOP_BOOL, LSET [])
            | TOP_BOOL, T -> RVAL (botZhat, TOP_BOOL, LSET [])
            | TOP_BOOL, TOP_BOOL -> RVAL (botZhat, TOP_BOOL, LSET [])
          end
     end
  | ORELSE (e1, e2) ->
     begin
       match (eval (mem, e1)), (eval (mem, e2)) with
       | UNREACH, _ -> botValue
       | _, UNREACH -> botValue
       | RVAL (_, b1, _), RVAL (_, b2, _)  ->
          begin
            match b1, b2 with
            | BOT_BOOL, _ -> botValue
            | _, BOT_BOOL -> botValue
            | T, _ -> RVAL (botZhat, T, LSET [])
            | _, T -> RVAL (botZhat, T, LSET [])
            | F, F -> RVAL (botZhat, F, LSET [])
            | F, TOP_BOOL -> RVAL (botZhat, TOP_BOOL, LSET [])
            | TOP_BOOL, F -> RVAL (botZhat, TOP_BOOL, LSET [])
            | TOP_BOOL, TOP_BOOL-> RVAL (botZhat, TOP_BOOL, LSET [])
          end
     end
  | LESS (e1, e2) ->
     begin
       match (eval (mem, e1)), (eval (mem, e2)) with
       | UNREACH, _ -> botValue
       | _, UNREACH -> botValue
       | RVAL (z1, _, _), RVAL (z2, _, _)  ->
          begin
            match z1, z2 with
            | RINT, _ -> RVAL (ZSET [], TOP_BOOL, LSET [])
            | _, RINT -> RVAL (ZSET [], TOP_BOOL, LSET [])
            | ZSET [], _ -> botValue
            | _, ZSET [] -> botValue
            | TOP_Z, _ -> RVAL (ZSET [], TOP_BOOL, LSET [])
            | _, TOP_Z -> RVAL (ZSET [], TOP_BOOL, LSET [])
            | ZSET l1, ZSET l2 ->
               begin
                 match ((max_nlist l1) < (min_nlist l2)) with
                 | true -> RVAL (botZhat, T, LSET [])
                 | false -> RVAL (botZhat, F, LSET [])
               end
          end
     end
  | READ -> RVAL (RINT, BOT_BOOL, LSET []) (* maybe I should count number of READ *)

(* IMPLEMENT assume/not assume with unreachable *)
let rec assume : (memory * exp) -> memory = fun (mem, e) ->
  match e with
  | NUM i -> botMemory
  | VAR id ->
     begin
       match mem(id) with
       | RVAL (z, b, l) ->
          begin
            match b with
            | F -> unreachMemory
            | BOT_BOOL -> botMemory
            | T -> mem
            | TOP_BOOL -> store mem id (RVAL (z, T, l))
          end
       | UNREACH -> botMemory
     end
  | DEREF x ->
     begin
       match (eval (mem, DEREF x)) with
       | RVAL (_, F, _) -> unreachMemory
       | UNREACH -> botMemory
       | _ -> mem
     end
  (* implement more precisely if i can*)
  | TRUE -> mem
  | FALSE -> unreachMemory
  | ADD (e1, e2) -> botMemory
  | MINUS e -> botMemory
  | NOT e -> assumeNot (mem, e)
  | ORELSE (e1, e2) -> (memory_join (assume (mem, e1)) (assume (mem, e2)))
  | ANDALSO (e1, e2) -> (memory_meet (assume (mem, e1)) (assume (mem, e2)))
  | LESS (e1, e2) ->
     begin
       match (eval (mem, (LESS (e1, e2)))) with
       | RVAL (_, T, _) -> mem
       | RVAL (_, TOP_BOOL, _) -> mem
       | RVAL (_, F, _) -> unreachMemory
       | RVAL (_, BOT_BOOL,_) -> botMemory
       | UNREACH -> botMemory
     end
  | _ -> mem
and assumeNot : (memory * exp) -> memory = fun (mem, e) ->
  match e with
  | NUM i -> botMemory
  | VAR id ->
     begin
       match mem(id) with
       | RVAL (z, b, l) ->
          begin
            match b with
            | T -> unreachMemory
            | BOT_BOOL -> botMemory
            | F -> mem
            | TOP_BOOL -> store mem id (RVAL (z, F, l))
          end
       | UNREACH -> botMemory
     end
  | DEREF x ->
     begin
       match (eval (mem, DEREF x)) with
       | RVAL (_, T, _) -> unreachMemory
       | UNREACH -> botMemory
       | _ -> mem
     end
  (* implement more precisely if i can*) 
  | TRUE -> unreachMemory
  | FALSE -> mem
  | ADD (e1, e2) -> botMemory
  | MINUS e -> botMemory
  | NOT e -> assume (mem, e)
  | ORELSE (e1, e2) -> (memory_meet (assumeNot (mem, e1)) (assumeNot (mem, e2)))
  | ANDALSO (e1, e2) -> (memory_join (assumeNot (mem, e1)) (assumeNot (mem, e2)))
  | LESS (e1, e2) ->
     begin
       match (eval (mem, (LESS (e1, e2)))) with
       | RVAL (_, F, _) -> mem
       | RVAL (_, TOP_BOOL, _) -> mem
       | RVAL (_, T, _) -> unreachMemory
       | RVAL (_, BOT_BOOL, _) -> botMemory
       | UNREACH -> botMemory
     end
  | _ -> mem
           
           
type result =
  | YES
  | NO
  | DONTKNOW

let result_to_str : result -> string = fun a -> match a with
                                                | YES -> "Yes, it is davinci code"
                                                | NO -> "No, it is not davinci code"
                                                | DONTKNOW -> "I don't know"

let rec is_unreachmem mem vlist =
  match vlist with
  | [] -> false
  | hd :: tl -> match (mem(hd)) with
                | UNREACH -> true
                | _ -> (is_unreachmem mem tl)
(* add davinchi list *)
let rec analyzer : (memory * program) -> memory = fun (mem, pgm) ->
  let varlist = used_varlist pgm in
  match (is_unreachmem mem varlist) with
  | true -> unreachMemory
  | false ->
     begin
       match pgm with
       | SKIP ->
          let resmem = mem in
          (* let _ = print_string("******* mem in point *******") in *)
          (* let _ = print_newline() in *)
          (* let _ = pp_memory resmem varlist in *)
          resmem_list := resmem::(!resmem_list);
          resmem
       | SEQ(cmd1, cmd2) -> let mem1 = analyzer (mem, cmd1) in
                            let resmem = analyzer (mem1, cmd2) in
                            resmem_list := resmem::(!resmem_list);
                            resmem
       | IF(e, cmd1, cmd2) ->
          let mem1 = assume (mem, e) in
          (* let _ = print_string("hi1 :") in *)
          (* let _ = pp_memory mem1 varlist in *)
          let mem2 = assumeNot (mem, e) in
          (* let _ = print_string("hi2 :") in *)
          (* let _ = pp_memory mem2 varlist in  *)
          let resmem = (memory_join (analyzer (mem1, cmd1)) (analyzer (mem2, cmd2))) in
          (* let _ = print_string("******* mem in point *******") in *)
          (* let _ = print_newline() in *)
          (* let _ = pp_memory resmem varlist in *)
          resmem_list := resmem::(!resmem_list);
          resmem
       | WHILE(e, cmd) ->
          begin
            let f =
              begin
                fun m' ->
                loop_num := !loop_num + 1;
                let truemem = assume (m', e) in
                (* let _ = print_string("***true mem :") in *)
                (* let _ = pp_memory truemem varlist in *)
                (* let _ = pp_memory m' varlist in *)
                match (is_unreachmem truemem varlist) with
                | true ->
                   begin
                     m'
                   end
                | false ->
                   begin
                     let cmem = analyzer (truemem, cmd) in
                     (* let _ = print_string("***cmd mem :") in *)
                     (* let _ = pp_memory cmem varlist in *)
                     let fmem = (memory_join mem cmem) in
                     fmem
                   end
              end
            in
            let botm = (partial_botMemory mem varlist) in
            let fixresult = (fix botm f varlist) in
            (* let _ = pp_memory fixresult varlist  in *)
            (* let _ = print_string("******* mem in point *******") in *)
            (* let _ = print_newline() in *)
            (* let _ = pp_memory fixresult varlist in *)
            resmem_list := fixresult::(!resmem_list); fixresult
          end
       | ASSIGN(id, e) ->
          let v = eval (mem, e) in
          let resmem = store mem id v in
          (* let _ = print_string("******* mem in point *******") in *)
          (* let _ = print_newline() in *)
          (* let _ = pp_memory resmem varlist in *)
          resmem_list := resmem::(!resmem_list); resmem
       | PTRASSIGN(id, e) ->
          let v = eval (mem, e) in
          match (mem(id)) with
          | UNREACH ->  resmem_list := botMemory::(!resmem_list); botMemory (* sure?? *)
          | RVAL (z, b, l) ->
             begin
               match l with
               | LSET l' ->
                  begin
                    match l' with
                    | [] ->
                       begin
                         let resmem = partial_botMemory mem varlist in
                         (* let _ = print_string("******* mem in point *******") in *)
                         (* let _ = print_newline() in *)
                         (* let _ = pp_memory resmem varlist in *)
                         resmem_list := resmem::(!resmem_list); resmem
                       end
                    | [x] ->
                       begin
                         let resmem = store mem x v in
                         (* let _ = print_string("******* mem in point *******") in *)
                         (* let _ = print_newline() in *)
                         (* let _ = pp_memory resmem varlist in *)
                         resmem_list := resmem::(!resmem_list); resmem                         
                       end 
                    | hd::tl ->
                       begin
                         let rec ptrassign_aux mem l' v =
                           match l' with
                           | [] -> mem
                           | hd::tl -> (store (ptrassign_aux mem tl v) hd (join (mem(hd)) v))
                         in
                         begin
                           let resmem = (ptrassign_aux mem l' v) in
                           (* let _ = print_string("******* mem in point *******") in *)
                           (* let _ = print_newline() in *)
                           (* let _ = pp_memory resmem varlist in *)
                           resmem_list := resmem::(!resmem_list); resmem   
                         end
                       end
                  end
             end
     end

let rec resmem_printer resl varlist=
  match resl with
  | [] -> print_newline()
  | hd::tl ->
     let _ = print_string("******* mem in point *******") in
     let _ = print_newline() in
     let _ = pp_memory hd varlist in
     resmem_printer tl varlist

let dav_value z =
  match z with
  | RINT -> false
  | TOP_Z -> false
  | ZSET s -> List.for_all (fun x -> ((snd x) = 415)) s
                           

let maydav_value z =
  match z with
  | RINT -> false
  | TOP_Z -> true
  | ZSET s -> List.exists (fun x -> ((snd x) = 415)) s

let check_dav_z z =
  ((if (dav_value z)
    then YES
    else (if (maydav_value z)
          then DONTKNOW
          else NO)))

let rec check_dav_rlist l =
  match l with
  | [] -> []
  | hd::tl -> (check_dav_z(hd))::(check_dav_rlist tl)

let check_is_dav l =
  if (List.mem NO l)
  then NO
  else (if (List.mem DONTKNOW l)
        then DONTKNOW
        else YES)

let calculate_dav l =
  if (List.mem YES l)
  then YES
  else (if (List.mem DONTKNOW l) then DONTKNOW else NO)
         
let rec remove_bot l =
  match l with
  | [] -> []
  | hd::tl -> if hd = (ZSET []) then remove_bot tl else hd::(remove_bot tl)

                                                              
(* TODO : should handle zset [] *)
(* TODO : davinci analysis *)
let rec davinciAnalyzer : program -> result = fun pgm ->
  let varlist = used_varlist pgm in
  let result = analyzer(botMemory, pgm) in
  (* let _ = resmem_printer !resmem_list varlist in *)
  (* let _ = print_string("*************************") in *)
  (* let _ = print_newline() in *)
  (* let _ = List.iter (print_string) varlist in *)
  let rec get_values mlist vlist =
    match vlist with
    | [] -> []
    | hd::tl ->
       begin
         (* let _ = print_newline() in *)

         (* let _ = print_string(hd) in *)

         let rlist = List.map (fun x ->
                         begin
                           match (x(hd)) with
                           | UNREACH -> raise (Error ("not impled"))
                           | RVAL (z, b, l) ->
                              match z with 
                              | RINT -> RINT
                              | TOP_Z -> TOP_Z
                              | ZSET s -> ZSET (list_trim s)                                              
                         end
                       ) mlist in
         (* let _ = print_newline() in *)
         let result_list = (check_dav_rlist (remove_bot (list_trim rlist))) in
         (* let _ = List.iter (print_string) result_list in *)
         let dav_of_list = check_is_dav result_list in
         (* let _ = print_string(result_to_str(dav_of_list)) in *)
         (* let _ = print_newline() in *)
         (* let _ = List.iter (check_dav)  *)
         dav_of_list::(get_values mlist tl)
       end
  in
  let dav_values = (get_values (!resmem_list) varlist) in
  (* let _ = print_newline() in *)
  (* let _ = List.iter (print_string) (List.map result_to_str dav_values) in *)
  (* let _ = print_newline() in *)
  (calculate_dav dav_values)
    
    (* let _ = pp_memory result varlist in *)
    (* YES *)

    (* raise (Error ("not impled")) *)

    
