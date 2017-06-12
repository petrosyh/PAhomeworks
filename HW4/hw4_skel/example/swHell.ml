(*
 * SNU 4541.664A Program Analysis 2017 Spring
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 *)


(*
 * hell analyzer
 *)
 
open Program 

exception Error of string

(* abstract domain *)
type bound = MIN | Z of int | MAX
type itv = ITV of bound * bound | BOT_ITV
type bool_hat = TOP_BOOL | T | F | BOT_BOOL
type loc_hat = LSET of string list

(* abstract memory, value *)
type value = RVAL of (itv * bool_hat * loc_hat) | UNREACH
type memory = id -> value 

(* bottom and unreachable values and memory *)
let botValue = RVAL (BOT_ITV, BOT_BOOL, LSET [])
let botMemory = fun x -> botValue
let unreachMemory = fun x -> UNREACH

let read_flag = ref 0
(* memory pretty print : "do not" change here *)
let pp_bound : bound -> unit = fun bnd ->
  match bnd with
  | MIN -> print_string("MIN")
  | Z i -> print_int(i)
  | MAX -> print_string("MAX")

let pp_itv : itv -> unit = fun itv ->
  match itv with
  | BOT_ITV -> print_string("bottom")
  | ITV (bnd1, bnd2) -> 
     let _ = print_string("[") in
     let _ = pp_bound(bnd1) in
     let _ = print_string(", ") in
     let _ = pp_bound(bnd2) in
     print_string("]")
	         

let pp_bool : bool_hat -> unit = fun b ->
  match b with
  | BOT_BOOL -> print_string("bottom") 
  | T -> print_string("T")
  | F -> print_string("F")
  | TOP_BOOL -> print_string("T, F")

let rec pp_memory : memory -> id list -> unit = fun mem -> (fun varlist ->
    match varlist with
    | [] -> ()
    | hd::tl ->
       begin
       match (mem(hd)) with
       | UNREACH ->
          begin
            let _ = print_string(hd ^ " -> interval : UNREACH") in
            let _ = print_newline() in
            pp_memory mem tl
          end                             
       | RVAL (itv, b, l) ->
          begin
            let _ = print_string(hd ^ " -> interval : ") in
            let _ = pp_itv(itv) in
            let _ = print_string(" bool : ") in
            let _ = pp_bool(b) in
            let _ = print_newline() in
            pp_memory mem tl
          end
       end
  )

(* memory operation *)
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

let rec used_cnts_exp exp =
  (match exp with
   | NUM i -> 0
   | VAR id | DEREF id | AT id -> 0
   | ADD (e1, e2) -> (used_cnts_exp e1) + (used_cnts_exp e2)
   | MINUS e -> used_cnts_exp e
   | TRUE -> 0
   | FALSE -> 0
   | NOT e -> used_cnts_exp e
   | ANDALSO (e1, e2) -> (used_cnts_exp e1) + (used_cnts_exp e2)
   | ORELSE (e1, e2) -> (used_cnts_exp e1) + (used_cnts_exp e2)
   | LESS (e1, e2) -> (used_cnts_exp e1) + (used_cnts_exp e2)
   | READ -> 1
  )

let rec used_cnts cmd =
  match cmd with
  | SKIP -> 0
  | SEQ (cmd1, cmd2) -> (used_cnts cmd1) + (used_cnts cmd2)
  | IF (e, cmd1, cmd2) -> (used_cnts_exp e) + (used_cnts cmd1) + (used_cnts cmd2)
  | WHILE (e, cmd) -> (used_cnts_exp e) + (used_cnts cmd)
  | ASSIGN (id, e) -> (used_cnts_exp e)
  | PTRASSIGN (id, e) -> (used_cnts_exp e)
(* TODO : maybe i should count number of reads... *)

let used_varlist cmd = list_trim (used_vars cmd)

let rec compare_mem m1 m2 varlist =
  match varlist with
  | [] -> true
  | hd::tl -> (m1(hd) = m2(hd)) && (compare_mem m1 m2 tl)

let rec list_intersection l1 l2 =
  match l1 with
  | [] -> []
  | hd::tl -> if (List.mem hd l2) then hd::(list_intersection tl l2) else (list_intersection tl l2)

let leq_bound b1 b2 =
  match b1, b2 with
  | MIN, _ -> true
  | _, MIN -> false
  | _, MAX -> true
  | MAX, _ -> false
  | Z a, Z b -> a <= b
                       
let leq_itv i1 i2 =
  match i1, i2 with
  | BOT_ITV, _ -> true
  | _, BOT_ITV -> false
  | ITV (a1, b1), ITV (a2, b2) -> if ((leq_bound a2 a1) && (leq_bound b1 b2))
                                  then true
                                  else false
                                         
let leq_bool b1 b2 =
  match b1, b2 with
  | BOT_BOOL, _ -> true
  | _, BOT_BOOL -> false
  | _, TOP_BOOL -> true
  | TOP_BOOL, _ -> false
  | T, T -> true
  | F, F -> false
  | _, _ -> raise (Error ("T or F"))

let rec is_subset l1 l2 =
  match l1, l2 with
  | [], _ -> true
  | _, [] -> false
  | h1::t1, _ -> if (List.mem h1 l2) then (is_subset t1 l2) else false 
  
  
let leq_loc l1 l2 =
  match l1, l2 with
  | LSET [], _ -> true
  | _, LSET [] -> false
  | LSET l1', LSET l2' -> (is_subset l1' l2')
                  
let leq_value v1 v2 =
  match v1, v2 with
  | UNREACH, _ -> true
  | _, UNREACH -> false
  | RVAL (i1, b1, l1), RVAL (i2, b2, l2) -> (leq_itv i1 i2) && (leq_bool b1 b2) && (leq_loc l1 l2)
                                               
let rec leq_mem m1 m2 varlist =
  match varlist with
  | [] -> true
  | hd::tl -> (leq_value (m1(hd)) (m2(hd))) && (leq_mem m1 m2 tl)


(* join operaters : you may need these operaters *)
let bound_plus a b =
  match a, b with
  | MIN, MIN -> MIN
  | MIN, Z i -> MIN
  | Z i, MIN -> MIN
  | MAX, MAX -> MAX
  | Z i, MAX -> MAX
  | MAX, Z i -> MAX
  | Z i, Z j -> Z (i + j)
  | MIN, MAX -> raise (Error ("strange things"))
  | MAX, MIN -> raise (Error ("strange things"))
                      
let bound_leq a b =
  match a, b with
  | MIN, _ -> true
  | _, MAX -> true
  | _, MIN -> false
  | MAX, _ -> false
  | Z i1, Z i2 -> i1 <= i2              

let bound_eq a b =
  match a, b with
  | MIN, MIN -> true
  | MAX, MAX -> true
  | Z i, Z j -> i = j
  | _, _ -> false
              
let smaller_one a b = if bound_leq a b then a else b
let bigger_one a b = if bound_leq a b then b else a
                                                    
let itv_join i1 i2 =
  match i1, i2 with
  | BOT_ITV, _ -> i2 
  | _, BOT_ITV -> i1
  | (ITV (a1, b1), ITV (a2, b2)) -> ITV (smaller_one a1 a2, bigger_one b1 b2)

let itv_meet i1 i2 =
  match i1, i2 with
  | BOT_ITV, _ -> BOT_ITV 
  | _, BOT_ITV -> BOT_ITV
  | (ITV (a1, b1), ITV (a2, b2)) ->
     let lo = (bigger_one a1 a2) in
     let hi = (smaller_one b1 b2) in
     if (bound_leq lo hi) then (ITV (lo, hi)) else BOT_ITV
                                        
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
  | RVAL (i1, b1, l1), RVAL (i2, b2, l2) -> RVAL (itv_join i1 i2, bool_join b1 b2, loc_join l1 l2)

let meet v1 v2 =
  match v1, v2 with
  | UNREACH, _ -> UNREACH
  | _, UNREACH -> UNREACH
  | RVAL (i1, b1, l1), RVAL (i2, b2, l2) -> RVAL (itv_meet i1 i2, bool_meet b1 b2, loc_meet l1 l2)


let rec memory_join m1 m2 = fun x -> (join (m1(x)) (m2(x)))
                                       
let rec memory_meet m1 m2 = fun x -> (meet (m1(x)) (m2(x)))

(* TODO : fix widening and narrowing *)

(* widening operaters : you may need these operaters *)

let rec partial_botMemory mem varlist =
  match varlist with
  | [] -> mem
  | hd::tl -> (store (partial_botMemory mem tl) hd botValue)

let rec partial_unreachMemory mem varlist =
  match varlist with
  | [] -> mem
  | hd::tl -> (store (partial_unreachMemory mem tl) hd UNREACH)

let widen_aux_low x y =
  if bound_leq y x then
    if bound_eq y x then y else MIN
  else x
         
let widen_aux_high x y =
  if bound_leq x y then
    if bound_eq x y then y else MAX
  else x
         
let itv_widen i1 i2 =
  if i1 = i2 then i1
  else
    match i1, i2 with
    | BOT_ITV, _ -> i2
    | _, BOT_ITV -> i1
    | (ITV (a1, b1)), (ITV (a2, b2)) -> (ITV ((widen_aux_low a1 a2), (widen_aux_high b1 b2)))
                                          
let widening v1 v2 =
  match v1, v2 with
  | UNREACH, _ -> v2
  | _, UNREACH -> v1
  | RVAL (i1, b1, l1), RVAL (i2, b2, l2) -> RVAL (itv_widen i1 i2, bool_join b1 b2, loc_join l1 l2)

let rec memory_widening botm m1 m2 varlist =
  match varlist with
  | [] -> botm
  | hd::tl -> (store (memory_widening botm m1 m2 tl) hd (widening (m1(hd)) (m2(hd))))

let fix_with_widening f botm varlist =
  let rec fix_with_widening_rec m varlist =
    let m' = f m in
    if (leq_mem m' m varlist)
    then m
    else (fix_with_widening_rec (memory_widening botm m m' varlist) varlist)
  in
  (fix_with_widening_rec botm varlist)
    
(* narrowing operaters : you may need these operaters *)
let narrow_aux_low x y =
  if bound_leq x y then y
  else raise (Error ("x must smaller y"))
             
let narrow_aux_high x y =
  if bound_leq y x then y
  else raise (Error ("x must bigger y"))
             
let itv_narrow i1 i2 =
  if i1 = i2 then i1
  else
    match i1, i2 with
    | _, BOT_ITV -> BOT_ITV
    | BOT_ITV, _ -> raise (Error ("i1 must larger than i2"))
    | (ITV (a1, b1), ITV (a2, b2)) -> ITV (narrow_aux_low a1 a2, narrow_aux_high b1 b2)

let bool_narrow b1 b2 =
  match b1, b2 with
  | _, BOT_BOOL -> BOT_BOOL
  | TOP_BOOL, _ -> b2
  | T, T -> T
  | F, F -> F
  | _, _ -> raise (Error ("b1 must larger than b2"))

                  
let narrowing v1 v2 =
  match v1, v2 with
  | UNREACH, _ -> UNREACH
  | _, UNREACH -> UNREACH
  | RVAL (i1, b1, l1), RVAL (i2, b2, l2) ->
     RVAL (itv_narrow i1 i2, bool_narrow b1 b2, loc_meet l1 l2)

let rec memory_narrowing botm m1 m2 varlist =
  match varlist with
  | [] -> botm
  | hd::tl -> (store (memory_narrowing botm m1 m2 tl) hd (narrowing (m1(hd)) (m2(hd))))

let fix_with_narrowing f botm widen_mem varlist =
  let rec fix_with_narrowing_rec m varlist =
    let m' = f m in
    if (leq_mem m m' varlist)
    then m
    else (fix_with_narrowing_rec (memory_narrowing botm m m' varlist) varlist)
  in
  (fix_with_narrowing_rec widen_mem varlist)

    
(* exp evaluation : TODO you have to implement this *)
let rec eval : (memory * exp * int) -> value  = fun (mem, e, nth) ->
  match e with
  | NUM i -> RVAL ((ITV (Z i, Z i)) , BOT_BOOL, LSET [])
  | VAR x -> mem(x)
  | TRUE -> RVAL (BOT_ITV, T, LSET [])
  | FALSE -> RVAL (BOT_ITV, F, LSET [])
  | AT x -> RVAL (BOT_ITV, BOT_BOOL, LSET [x])
  | DEREF x ->
     begin
       match (mem(x)) with
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
  | ADD (e1, e2) ->
     begin
       match (eval (mem, e1, nth)), (eval (mem, e2, nth)) with
       | UNREACH, _ -> botValue
       | _, UNREACH -> botValue
       | RVAL (i1, _, _), RVAL (i2, _, _) ->
          begin
            match i1, i2 with
            | BOT_ITV, _ -> botValue
            | _, BOT_ITV -> botValue
            | (ITV (MIN, MAX)), _ -> RVAL ((ITV (MIN, MAX)), BOT_BOOL, LSET [])
            | (ITV (a1, b1)), (ITV (a2, b2)) -> RVAL ((ITV (bound_plus a1 a2, bound_plus b1 b2)), BOT_BOOL, LSET []) 
          end
     end
  | MINUS e ->
     begin
       match (eval (mem, e, nth)) with
       | UNREACH -> botValue
       | RVAL (i, _, _) ->
          begin
            match i with
            | BOT_ITV -> botValue
            | (ITV (MIN, MAX)) -> RVAL (ITV (MIN, MAX), BOT_BOOL, LSET [])
            | (ITV (Z a, Z b)) -> RVAL (ITV (Z (- b), Z (- a)), BOT_BOOL, LSET [])
            | (ITV (MAX, MAX)) -> RVAL (ITV (MIN, MIN), BOT_BOOL, LSET [])
            | (ITV (MAX, _)) -> raise (Error("strange format of itv"))
            | (ITV (Z a, MIN)) -> raise (Error("strange format of itv"))
            | (ITV (Z a, MAX)) -> RVAL (ITV (MIN, Z (- a)), BOT_BOOL, LSET [])
            | (ITV (MIN, Z a)) -> RVAL (ITV (Z (- a), MAX), BOT_BOOL, LSET [])
            | (ITV (MIN, MIN)) -> RVAL (ITV (MAX, MAX), BOT_BOOL, LSET [])
          end
     end
  | NOT e ->
     begin
       match (eval (mem, e, nth)) with
       | UNREACH -> botValue
       | RVAL (i, b, _) ->
          begin
            match b with
            | BOT_BOOL -> botValue
            | T -> RVAL (BOT_ITV, F, LSET [])
            | F -> RVAL (BOT_ITV, T, LSET [])
            | TOP_BOOL -> RVAL (BOT_ITV, TOP_BOOL, LSET [])         
          end
     end
  | ANDALSO (e1, e2) ->
     begin
       match (eval (mem, e1, nth)), (eval (mem, e2, nth)) with
       | UNREACH, _ -> botValue
       | _, UNREACH -> botValue
       | RVAL (_, b1, _), RVAL (_, b2, _) ->
          begin
            match b1, b2 with
            | BOT_BOOL, _ -> botValue
            | _, BOT_BOOL -> botValue
            | F, _ -> RVAL (BOT_ITV, F, LSET [])
            | _, F -> RVAL (BOT_ITV, F, LSET [])
            | T, T -> RVAL (BOT_ITV, T, LSET [])
            | T, TOP_BOOL -> RVAL (BOT_ITV, TOP_BOOL, LSET [])
            | TOP_BOOL, T -> RVAL (BOT_ITV, TOP_BOOL, LSET [])
            | TOP_BOOL, TOP_BOOL -> RVAL (BOT_ITV, TOP_BOOL, LSET [])
          end
     end  
  | ORELSE (e1, e2) ->
     begin
       match (eval (mem, e1, nth)), (eval (mem, e2, nth)) with
       | UNREACH, _ -> botValue
       | _, UNREACH -> botValue
       | RVAL (_, b1, _), RVAL (_, b2, _) ->
          begin
            match b1, b2 with
            | BOT_BOOL, _ -> botValue
            | _, BOT_BOOL -> botValue
            | T, _ -> RVAL (BOT_ITV, T, LSET [])
            | _, T -> RVAL (BOT_ITV, T, LSET [])
            | F, F -> RVAL (BOT_ITV, F, LSET [])
            | F, TOP_BOOL -> RVAL (BOT_ITV, TOP_BOOL, LSET [])
            | TOP_BOOL, F -> RVAL (BOT_ITV, TOP_BOOL, LSET [])
            | TOP_BOOL, TOP_BOOL-> RVAL (BOT_ITV, TOP_BOOL, LSET [])
          end
     end
  | LESS (e1, e2) ->
     begin
       match (eval (mem, e1, nth)), (eval (mem, e2, nth)) with
       | UNREACH, _ -> botValue
       | _, UNREACH -> botValue
       | RVAL (i1, b1, _), RVAL (i2, b2, _) ->
          begin
            match i1, i2 with
            | BOT_ITV, _ -> botValue
            | _, BOT_ITV -> botValue
            | (ITV (_, Z b1)), (ITV (Z a2, _)) when b1 < a2 -> RVAL (BOT_ITV, T, LSET [])
            | (ITV (Z a1, _)), (ITV (_, Z b2)) when b2 <= a1 -> RVAL (BOT_ITV, F, LSET [])
            | _, _ -> RVAL (BOT_ITV, TOP_BOOL, LSET [])
          end
     (*| (ITV (Z a1, Z b1)), (ITV (Z a2, Z b2)) -> if b1 < a2
                                                       then (BOT_ITV, T)
                                                       else
                                                         if b2 <= a1
                                                         then (BOT_ITV, F)
                                                        else (BOT_ITV, TOP_BOOL)  *)     
     end
  | READ ->
     (* let _ = print_string("hi read!") in *)
     let post_flag = !read_flag in
     (* let _ = print_string("post flag : ") in *)
     (* let _ = print_int(post_flag) in  *)
     (* let _ = print_newline() in *)
     read_flag := post_flag + 1;
     let new_flag = !read_flag in
     if (new_flag = nth)
     then
       RVAL (ITV (Z 100, MAX), BOT_BOOL, LSET []) (*number of READ*)
     else
       RVAL (ITV (MIN, MAX), BOT_BOOL, LSET [])



let rec assume : (memory * exp * int) -> memory = fun (mem, e, nth) ->
  match e with
  | NUM i -> botMemory
  | VAR id ->
     begin
       match mem(id) with
       | UNREACH -> botMemory
       | RVAL (i, b, l) ->
          begin
            match b with
            | F -> unreachMemory
            | BOT_BOOL -> botMemory
            | T -> mem
            | TOP_BOOL -> store mem id (RVAL (i, T, l))
          end
     end
  | DEREF x ->
     begin
       match (eval (mem, DEREF x, nth)) with
       | RVAL (_, F, _) -> unreachMemory
       | _ -> mem
     end
  | TRUE -> mem
  | FALSE -> unreachMemory
  | ADD (e1, e2) -> botMemory
  | MINUS e -> botMemory
  | NOT e -> assumeNot (mem, e, nth)
  | ORELSE (e1, e2) -> (memory_join (assume (mem, e1, nth)) (assume (mem, e2, nth)))
  | ANDALSO (e1, e2) -> (memory_meet (assume (mem, e1, nth)) (assume (mem, e2, nth))) 
  | LESS (e1, e2) ->
     begin
       match e1, e2 with
       | VAR id, NUM n ->
          begin
            match mem(id) with
            | UNREACH -> botMemory
            | RVAL (i, b, l) ->
               begin
                 let v = (RVAL (itv_meet (ITV (MIN, Z (n - 1))) i, b, l)) in
                 begin
                   match v with
                   | RVAL (BOT_ITV, _, _) -> unreachMemory
                   | _ -> store mem id v
                 end
               end
          end
       | NUM n, VAR id ->
          begin
            match mem(id) with
            | UNREACH -> botMemory
            | RVAL (i, b, l) ->
               begin
                 let v = (RVAL (itv_meet (ITV (Z (n + 1), MAX)) i, b, l)) in
                 begin
                   match v with
                   | RVAL (BOT_ITV, _, _) -> unreachMemory
                   | _ -> store mem id v
                 end
               end
          end
       | _, _ ->
          begin
            match (eval (mem, (LESS (e1, e2)), nth)) with
            | UNREACH -> botMemory
            | RVAL (_, T, _) -> mem
            | RVAL (_, F, _) -> unreachMemory
            | RVAL (_, TOP_BOOL, _) -> mem
            | RVAL (_, BOT_BOOL, _) -> botMemory
          end
     end
  | _ -> mem
and assumeNot : (memory * exp * int) -> memory = fun (mem, e, nth) ->
  match e with
  | NUM i -> botMemory
  | VAR id ->
     begin
       match mem(id) with
       | UNREACH -> botMemory
       | RVAL (i, b, l) ->
          begin
            match b with
            | T -> unreachMemory
            | BOT_BOOL -> botMemory
            | F -> mem
            | TOP_BOOL -> store mem id (RVAL (i, F, l)) 
          end
     end
  | DEREF x ->
     begin
       match (eval (mem, DEREF x, nth)) with
       | RVAL (_, T, _) -> unreachMemory
       | _ -> mem
     end
  | TRUE -> unreachMemory
  | FALSE -> mem 
  | ADD (e1, e2) -> botMemory
  | MINUS e -> botMemory
  | NOT e -> assume (mem, e, nth)
  | ORELSE (e1, e2) -> (memory_meet (assumeNot (mem, e1, nth)) (assumeNot (mem, e2, nth)))
  | ANDALSO (e1, e2) -> (memory_join (assumeNot (mem, e1, nth)) (assumeNot (mem, e2, nth)))  
  | LESS (e1, e2) ->
     begin
       match e1, e2 with
       | VAR id, NUM n ->
          begin
            match mem(id) with
            | UNREACH -> botMemory
            | RVAL (i, b, l) ->
               begin
                 let v = (RVAL (itv_meet (ITV (Z n, MAX)) i, b, l)) in
                 begin
                   match v with
                   | RVAL (BOT_ITV, _, _) -> unreachMemory
                   | _ -> store mem id v
                 end 
               end
               end
       | NUM n, VAR id ->
          begin
            match mem(id) with
            | UNREACH -> botMemory
            | RVAL (i, b, l) ->
               begin
                 let v = (RVAL (itv_meet (ITV (MIN, Z n)) i, b, l)) in 
                 begin
                   match v with
                   | RVAL (BOT_ITV, _, _) -> unreachMemory
                   | _ -> store mem id v
                 end
               end
          end
       | _, _ ->
          begin
            match (eval (mem, (LESS (e1, e2)), nth)) with
            | UNREACH -> botMemory
            | RVAL (_, F, _) -> mem
            | RVAL (_, T, _) -> botMemory
            | RVAL (_, TOP_BOOL, _) -> mem
            | RVAL (_, BOT_BOOL, _) -> botMemory
          end
     end
  | _ -> mem
           

let rec is_unreachmem mem vlist =
  match vlist with
  | [] -> false
  | hd :: tl -> match (mem(hd)) with
                | UNREACH -> true
                | _ -> (is_unreachmem mem tl)
                         
let rec analyzer : (memory * program * int) -> memory = fun (mem, pgm, nth) ->
  let varlist = used_varlist pgm in
  match (is_unreachmem mem varlist) with
  | true -> unreachMemory
  | false -> 
     begin
       match pgm with
       | SKIP -> mem
       | SEQ(cmd1, cmd2) ->
          let mem1 = analyzer (mem, cmd1, nth) in
          analyzer (mem1, cmd2, nth) 
       | IF(e, cmd1, cmd2) ->
          let mem1 = assume (mem, e, nth) in
          let read_in_e = (used_cnts_exp e) in
          let post_flag = !read_flag in
          read_flag := post_flag - read_in_e;
          let mem2 = assumeNot (mem, e, nth) in
          (* let _ = pp_memory mem1 varlist in *)
          (* let _ = print_newline() in *)
          (* let _ = pp_memory mem2 varlist in  *)
          (* let _ = print_newline() in *)
          (memory_join (analyzer (mem1, cmd1, nth)) (analyzer (mem2, cmd2, nth)))  
       | WHILE(e, cmd) ->
          begin
            match (eval (mem, e, nth)) with
            | RVAL (_, F, _) -> (partial_unreachMemory mem (used_varlist cmd))
            | _ ->
               begin
                 let f =
                   begin
                     fun m' ->
                     begin
                       let truemem = assume (m', e, nth) in
                       let cmem = analyzer (truemem, cmd, nth) in
                       (memory_join mem cmem)
                     end
                   end
                 in
                 let botm = (partial_botMemory mem varlist) in
                 let widen_mem = (fix_with_widening f botm varlist) in
                 let narrow_mem = (fix_with_narrowing f botm widen_mem varlist) in
                 assumeNot (narrow_mem, e, nth)
               end
          end
       | ASSIGN(id, e) ->
          let v = eval (mem, e, nth) in
          store mem id v
       | PTRASSIGN(id, e) ->
          let v = eval (mem, e, nth) in
          begin
            match (mem(id)) with
            | UNREACH -> botMemory
            | RVAL (z, b, l) ->
               begin
                 match l with
                 | LSET l' ->
                    begin
                      match l' with
                      | [] -> botMemory
                      | [x] -> store mem x v
                      | hd::tl ->
                         let rec ptrassign_aux mem l' v =
                           match l' with
                           | [] -> mem
                           | hd::tl -> (store (ptrassign_aux mem tl v) hd (join (mem(hd)) v))
                         in (ptrassign_aux mem l' v)
                    end
               end
          end
     end

type result =
  | YES
  | NO
  | DONTKNOW

let result_to_str : result -> string = fun a -> match a with
  | YES -> "Yes"
  | NO -> "No"
  | DONTKNOW -> "I don't know"

let get_result : memory -> result = fun mem ->
  match (mem("liberation")) with
  | RVAL (ITV (Z 1, Z 1), _, _) -> YES
  | RVAL (ITV (a, b), _, _) -> if ((bound_leq a (Z 1)) && (bound_leq (Z 1) b)) then DONTKNOW else NO 
  | _ -> NO

let final_result : result list -> result = fun l ->
  match l with
  | [] -> raise (Error ("NO Result"))
  | hd :: tl -> if (List.mem NO l)
                then NO
                else
                  begin
                    if (List.mem DONTKNOW l)
                    then DONTKNOW
                    else YES
                  end

                    
(* davinci analysis *)
let rec hellAnalyzer : program -> result = fun pgm ->
  let varlist = used_varlist pgm in
  let num_read = used_cnts pgm in
  (* let _ = print_int num_read in *)
  (* let _ = print_newline() in *)
  (* let _ = List.iter (print_string) varlist in *)
  (* let _ = print_newline() in *)
  let rec multianalyze n =
    if (n = 0)
    then []
    else
      begin
        let res = ((analyzer (botMemory, pgm, n))) in
        let gres = get_result res in 
        let _ = pp_memory res varlist in
        read_flag := 0;
        (gres :: (multianalyze (n - 1)))
      end
  in
  let result_list = (multianalyze num_read) in
  final_result(result_list)
  (* let _ =List.iter (print_string) (List.map result_to_str result_list) in *)
  (* YES *)
                     
  (* let mem_result = (analyzer (botMemory, pgm, num_read)) in *)
  (* let _ = pp_memory mem_result varlist in  *)
  (* get_result(mem_result) *)
            (* initialize read_flag plz*)
            (* let mem = analyzer (botMemory, pgm) in *)
            (* YES *)
            
            (*raise (Error ("not impled"))*)
            
