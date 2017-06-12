(*
 * SNU 4541.664A Program Analysis 2017 Spring
 * K- Interpreter Solution
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 *)


(*
 * K- Interpreter
 *)

module type KMINUS =
  sig
    exception Error of string
    type id = string
    type exp =
      | NUM of int
      | VAR of id
      | ADD of exp * exp
      | MINUS of exp
      | TRUE
      | FALSE
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

    type program = cmd
    type memory
    type value

    val botMemory : memory
    val eval : memory * exp -> value  (* exp eval *)
    val assume : memory * exp -> memory (* memory filtering *)
    val analyzer : memory * program -> memory
    val used_varlist : program -> id list
    val pp_memory : memory -> id list -> unit
  end

module K : KMINUS =
  struct
    exception Error of string
    type id = string
    type exp =
      | NUM of int
      | VAR of id
      | ADD of exp * exp
      | MINUS of exp
      | TRUE
      | FALSE
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



    type program = cmd
                     
    (* abstract domain type : "do not" change here *)
    type bound = MIN | Z of int | MAX
    type itv = ITV of bound * bound | BOT_ITV
    type bool_hat = TOP_BOOL | T | F | BOT_BOOL
                                         
    (* abstract memory, value type : "do not" change here *)
    type value = itv * bool_hat
    type memory = id -> value
                          
    (* bottom values *)
    let botValue = (BOT_ITV, BOT_BOOL)
    let botMemory = fun x -> botValue
                               
    (* memory operation *)                     
    let store mem id v = fun x -> if (x = id) then v else mem(x)
                                                             
    let rec compare_mem m1 m2 varlist =
      match varlist with
      | [] -> true
      | hd::tl -> (m1(hd) = m2(hd)) && (compare_mem m1 m2 tl)

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

    let leq_value v1 v2 =
      match v1, v2 with
      | (i1, b1), (i2, b2) -> (leq_itv i1 i2) && (leq_bool b1 b2)
                      
    let rec leq_mem m1 m2 varlist =
      match varlist with
      | [] -> true
      | hd::tl -> (leq_value (m1(hd)) (m2(hd))) && (leq_mem m1 m2 tl)
                                        
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
	   let (itv, b) = mem(hd) in
	   let _ = print_string(hd ^ " -> interval : ") in
	   let _ = pp_itv(itv) in
	   let _ = print_string(" bool : ") in
	   let _ = pp_bool(b) in
	   let _ = print_newline() in
	   pp_memory mem tl
      )
	                                                         
    (* var list gathering : "do not" change here *)
    let rec list_trim l =
      match l with
      | [] -> []
      | hd::tl -> if (List.mem hd tl) then list_trim tl else hd::(list_trim tl)

    let rec used_vars_exp exp =
      (match exp with
       | NUM i -> []
       | VAR id -> id::[]
       | ADD (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
       | MINUS e -> used_vars_exp e
       | TRUE -> []
       | FALSE -> []
       | NOT e -> used_vars_exp e
       | ANDALSO (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
       | ORELSE (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
       | LESS (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
      )
        
    let rec used_vars cmd =
      match cmd with
      | SKIP -> []
      | SEQ (cmd1, cmd2) -> (used_vars cmd1) @ (used_vars cmd2)
      | IF (e, cmd1, cmd2) -> (used_vars_exp e) @ (used_vars cmd1) @ (used_vars cmd2)
      | WHILE (e, cmd) -> (used_vars_exp e) @ (used_vars cmd)
      | ASSIGN (id, e) -> id::(used_vars_exp e)

    let used_varlist cmd = list_trim (used_vars cmd)
                                     
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
      | (ITV (a1, b1), ITV (a2, b2)) -> ITV (bigger_one a1 a2, smaller_one b1 b2)
                                            
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
                         
    let join v1 v2 = 
      match v1, v2 with
      | (i1, b1), (i2, b2) -> (itv_join i1 i2, bool_join b1 b2)

    let meet v1 v2 =
      match v1, v2 with
      | (i1, b1), (i2, b2) -> (itv_meet i1 i2, bool_meet b1 b2)
                   
    let rec memory_join m1 m2 = fun x -> (join (m1(x)) (m2(x)))
 
    let rec memory_meet m1 m2 = fun x -> (meet (m1(x)) (m2(x)))
                          
    (* widening operaters : you may need these operaters *)
    let rec partial_botMemory mem varlist =
      match varlist with
      | [] -> mem
      | hd::tl -> (store (partial_botMemory mem tl) hd botValue)
                    
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
      | (i1, b1), (i2, b2) -> (itv_widen i1 i2, bool_join b1 b2)

    let rec memory_widening botm m1 m2 varlist =
      match varlist with
      | [] -> botm
      | hd::tl -> (store (memory_widening botm m1 m2 tl) hd (widening (m1(hd)) (m2(hd))))

    let fix f varlist =
      let rec fix_rec m varlist =
        let m' = f m in
        if (compare_mem m m' varlist)
        then m
        else (fix_rec m' varlist)
      in
      (fix_rec botMemory varlist)

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
      | (i1, b1), (i2, b2) -> (itv_narrow i1 i2, bool_narrow b1 b2)

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
    let rec eval : (memory * exp) -> value  = fun (mem, e) ->
      match e with
      | NUM i -> ((ITV (Z i, Z i)) , BOT_BOOL)
      | VAR x -> mem(x)
      | TRUE -> (BOT_ITV, T)
      | FALSE -> (BOT_ITV, F)
      | ADD (e1, e2) ->
         begin
           let (i1, _) = eval (mem, e1) in
           let (i2, _) = eval (mem, e2) in
           match i1, i2 with
           | BOT_ITV, _ -> botValue
           | _, BOT_ITV -> botValue
           | (ITV (MIN, MAX)), _ -> ((ITV (MIN, MAX)), BOT_BOOL)
           | (ITV (a1, b1)), (ITV (a2, b2)) -> ((ITV (bound_plus a1 a2, bound_plus b1 b2)), BOT_BOOL) 
         end
      | MINUS e ->
         begin
           let (i, b) = eval (mem, e) in
           match i with
           | BOT_ITV -> botValue
           | (ITV (MIN, MAX)) -> (ITV (MIN, MAX), BOT_BOOL)
           | (ITV (Z a, Z b)) -> (ITV (Z (- b), Z (- a)), BOT_BOOL)
           | (ITV (MAX, MAX)) -> (ITV (MIN, MIN), BOT_BOOL)
           | (ITV (MAX, _)) -> raise (Error("strange format of itv"))
           | (ITV (Z a, MIN)) -> raise (Error("strange format of itv"))
           | (ITV (Z a, MAX)) -> (ITV (MIN, Z (- a)), BOT_BOOL)
           | (ITV (MIN, Z a)) -> (ITV (Z (- a), MAX), BOT_BOOL)
           | (ITV (MIN, MIN)) -> (ITV (MAX, MAX), BOT_BOOL)
         end
      | NOT e ->
         begin
           let (i, b) = eval (mem, e) in
           match b with
           | BOT_BOOL -> botValue
           | T -> (BOT_ITV, F)
           | F -> (BOT_ITV, T)
           | TOP_BOOL -> (BOT_ITV, TOP_BOOL)         
         end
      | ANDALSO (e1, e2) ->
         begin
           let (_, b1) = eval (mem, e1) in
           let (_, b2) = eval (mem, e2) in
           match b1, b2 with
           | BOT_BOOL, _ -> botValue
           | _, BOT_BOOL -> botValue
           | F, _ -> (BOT_ITV, F)
           | _, F -> (BOT_ITV, F)
           | T, T -> (BOT_ITV, T)
           | T, TOP_BOOL -> (BOT_ITV, TOP_BOOL)
           | TOP_BOOL, T -> (BOT_ITV, TOP_BOOL)
           | TOP_BOOL, TOP_BOOL -> (BOT_ITV, TOP_BOOL)
         end  
      | ORELSE (e1, e2) ->
         begin
           let (_, b1) = eval (mem, e1) in
           let (_, b2) = eval (mem, e2) in
           match b1, b2 with
           | BOT_BOOL, _ -> botValue
           | _, BOT_BOOL -> botValue
           | T, _ -> (BOT_ITV, T)
           | _, T -> (BOT_ITV, T)
           | F, F -> (BOT_ITV, F)
           | F, TOP_BOOL -> (BOT_ITV, TOP_BOOL)
           | TOP_BOOL, F -> (BOT_ITV, TOP_BOOL)
           | TOP_BOOL, TOP_BOOL-> (BOT_ITV, TOP_BOOL)
         end             
      | LESS (e1, e2) ->
         begin
           let (i1, b1) = eval (mem, e1) in
           let (i2, b2) = eval (mem, e2) in
           match i1, i2 with
           | BOT_ITV, _ -> botValue
           | _, BOT_ITV -> botValue
           | (ITV (_, Z b1)), (ITV (Z a2, _)) when b1 < a2 -> (BOT_ITV, T)
           | (ITV (Z a1, _)), (ITV (_, Z b2)) when b2 <= a1 -> (BOT_ITV, F)
           | _, _ -> (BOT_ITV, TOP_BOOL)
           (*| (ITV (Z a1, Z b1)), (ITV (Z a2, Z b2)) -> if b1 < a2
                                                       then (BOT_ITV, T)
                                                       else
                                                         if b2 <= a1
                                                         then (BOT_ITV, F)
                                                        else (BOT_ITV, TOP_BOOL)  *)     
         end
                   
    (* memory filtering by boolean expression *)
    let rec assume : (memory * exp) -> memory = fun (mem, e) ->
      match e with
      | NUM i -> botMemory
      | VAR id ->
         begin
           match mem(id) with
           | (i, b) ->
              begin
                match b with
                | F -> botMemory
                | BOT_BOOL -> botMemory
                | T -> mem
                | TOP_BOOL -> store mem id (i, T)
              end
         end
      | TRUE -> mem
      | FALSE -> botMemory
      | ADD (e1, e2) -> botMemory
      | MINUS e -> botMemory
      | NOT e -> assumeNot (mem, e)
      | ORELSE (e1, e2) -> (memory_join (assume (mem, e1)) (assume (mem, e2)))
      | ANDALSO (e1, e2) -> (memory_meet (assume (mem, e1)) (assume (mem, e2))) 
      | LESS (e1, e2) ->
         begin
           match e1, e2 with
           | VAR id, NUM n ->
              begin
               match mem(id) with
               | (i, b) -> store mem id (itv_meet (ITV (MIN, Z (n - 1))) i, b)
              end
           | NUM n, VAR id ->
              begin
                match mem(id) with
                | (i, b) -> store mem id (itv_meet (ITV (Z (n + 1), MAX)) i, b)
              end
           | _, _ ->
              begin
                match (eval (mem, (LESS (e1, e2)))) with
                | (_, T) -> mem
                | (_, F) -> botMemory
                | (_, TOP_BOOL) -> mem
                | (_, BOT_BOOL) -> botMemory
              end
         end     
    and assumeNot : (memory * exp) -> memory = fun (mem, e) ->
      match e with
      | NUM i -> botMemory
      | VAR id ->
         begin
           match mem(id) with        
           | (i, b) ->
              begin
                match b with
                | T -> botMemory
                | BOT_BOOL -> botMemory
                | F -> mem
                | TOP_BOOL -> store mem id (i, F) 
              end
         end
      | TRUE -> botMemory
      | FALSE -> mem 
      | ADD (e1, e2) -> botMemory
      | MINUS e -> botMemory
      | NOT e -> assume (mem, e)
      | ORELSE (e1, e2) -> (memory_meet (assumeNot (mem, e1)) (assumeNot (mem, e2)))
      | ANDALSO (e1, e2) -> (memory_join (assumeNot (mem, e1)) (assumeNot (mem, e2)))  
      | LESS (e1, e2) ->
         begin
           match e1, e2 with
           | VAR id, NUM n ->
              begin
                match mem(id) with
                | (i, b) -> store mem id (itv_meet (ITV (Z n, MAX)) i, b)
              end
           | NUM n, VAR id ->
              begin
                match mem(id) with
                | (i, b) -> store mem id (itv_meet (ITV (MIN, Z n)) i, b)
              end
           | _, _ ->
              begin
                match (eval (mem, (LESS (e1, e2)))) with
                | (_, F) -> mem
                | (_, T) -> botMemory
                | (_, TOP_BOOL) -> mem
                | (_, BOT_BOOL) -> botMemory
              end
         end
                    

    (* interval analysis for K- *)
    let rec analyzer : (memory * program) -> memory = fun (mem, pgm) ->
      let varlist = used_varlist pgm in
      match pgm with
      | SKIP -> mem
      | SEQ(cmd1, cmd2) ->
         let mem1 = analyzer (mem, cmd1) in
         analyzer (mem1, cmd2) 
      | IF(e, cmd1, cmd2) ->
         let mem1 = assume (mem, e) in
         let mem2 = assumeNot (mem, e) in
         (memory_join (analyzer (mem1, cmd1)) (analyzer (mem2, cmd2)))  
      | WHILE(e, cmd) ->
         begin
           let f =
             begin
               fun m' ->
               begin
                 let truemem = assume (m', e) in
                 let cmem = analyzer (truemem, cmd) in
                 (memory_join mem cmem)
               end
             end
           in
           let botm = (partial_botMemory mem varlist) in
           let widen_mem = (fix_with_widening f botm varlist) in
           let narrow_mem = (fix_with_narrowing f botm widen_mem varlist) in
           assumeNot (narrow_mem, e)
         end
      | ASSIGN(id, e) ->
         let v = eval (mem, e) in
         store mem id v
  end
    
