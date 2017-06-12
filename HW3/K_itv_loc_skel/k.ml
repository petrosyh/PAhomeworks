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
      | DEREF of id (* *x *)
      | AT of id (* &x *)
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
      | PTRASSIGN of id * exp   (* assign using ptr *)

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
      | DEREF of id
      | AT of id
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
      | PTRASSIGN of id * exp   (* assign using ptr *)


    type program = cmd
                     
    (* abstract domain type : "do not" change here *)
    type z_hat = BOT_Z | CONST of int | TOP_Z
    type bool_hat = TOP_BOOL | T | F | BOT_BOOL
    type loc_hat = LSET of string list

                                  
    (* abstract memory, value type : "do not" change here *)
    type value = z_hat * bool_hat * loc_hat
    type memory = id -> value
                          
    (* bottom values *)
    let botValue = (BOT_Z, BOT_BOOL, LSET [])
    let botMemory = fun x -> botValue
                               
    (* memory operation *)
    let store mem id v = fun x -> if (x = id) then v else mem(x)
                                                             
    let rec compare_mem m1 m2 varlist =
      match varlist with
      | [] -> true
      | hd::tl -> (m1(hd) = m2(hd)) && (compare_mem m1 m2 tl)
                                         
    (* memory pretty print : "do not" change here *)
    let rec pp_zhat : z_hat -> unit = fun z ->	
      match z with
      | TOP_Z -> print_string("TOP")
      | BOT_Z -> print_string("BOTTOM")
      | CONST i -> let _ = print_string("CONST") in print_int(i)

    let rec pp_lochat : loc_hat -> unit = fun loc ->
      match loc with
      | LSET [] -> ()
      | LSET (hd::tl) -> let _ = print_string(hd ^ ", ") in (pp_lochat (LSET tl))


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
	   let (zhat, b, lochat) = mem(hd) in
	   let _ = print_string(hd ^ " -> Z : ") in
	   let _ = pp_zhat(zhat) in
	   let _ = print_string(" bool : ") in
	   let _ = pp_bool(b) in
	   let _ = print_string(" loc : [ ") in
	   let _ = pp_lochat(lochat) in
	   let _ = print_string("]") in
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
       | VAR id | DEREF id | AT id -> id::[]
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
      | PTRASSIGN (id, e) -> id::(used_vars_exp e)

    let used_varlist cmd = list_trim (used_vars cmd)
                                     
    (* join operaters : you may need these operaters *)

    let zhat_join z1 z2 =
      match z1, z2 with
      | BOT_Z, _ -> z2
      | _, BOT_Z -> z1
      | CONST n1, CONST n2 -> if n1 = n2
                              then CONST n1
                              else TOP_Z
      | _, TOP_Z -> TOP_Z
      | TOP_Z, _ -> TOP_Z

    let zhat_meet z1 z2 =
      match z1, z2 with
      | BOT_Z, _ -> BOT_Z
      | _, BOT_Z -> BOT_Z
      | CONST n1, CONST n2 -> if n1 = n2
                              then CONST n1
                              else BOT_Z
      | _, TOP_Z -> z1
      | TOP_Z, _ -> z2                           
                                     
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

    let rec list_intersection l1 l2 =
      match l1 with
      | [] -> []
      | hd::tl -> if (List.mem hd l2) then hd::(list_intersection tl l2) else (list_intersection tl l2) 
      
    let loc_join l1 l2 =
      match l1, l2 with
      | LSET loc1, LSET loc2 -> LSET (list_trim (loc1 @ loc2))

    let loc_meet l1 l2 =
      match l1, l2 with
      | LSET loc1, LSET loc2 -> LSET (list_intersection loc1 loc2)
                         
    let join v1 v2 =
      match v1, v2 with
      | (z1, b1, l1), (z2, b2, l2) -> (zhat_join z1 z2, bool_join b1 b2, loc_join l1 l2)

    let meet v1 v2 =
      match v1, v2 with
      | (z1, b1, l1), (z2, b2, l2) -> (zhat_meet z1 z2, bool_meet b1 b2, loc_meet l1 l2)

    let rec memory_join m1 m2 = fun x -> (join (m1(x)) (m2(x)))

    let rec memory_meet m1 m2 = fun x -> (meet (m1(x)) (m2(x)))
                                           
    (* widening operaters : you may need these operaters *)
    let rec partial_botMemory mem varlist =
      match varlist with
      | [] -> mem
      | hd::tl -> (store (partial_botMemory mem tl) hd botValue)

    let fix botm f varlist =
      let rec fix_rec m varlist =
        let m' = f m in
        if (compare_mem m m' varlist)
        then m
        else (fix_rec m' varlist)
      in
      (fix_rec botm varlist)
        
        
    (* narrowing operaters : you may need these operaters *)
                                     
    (* exp evaluation : TODO you have to implement this *)
    let rec eval : (memory * exp) -> value  = fun (mem, e) ->
      match e with
      | NUM i -> (CONST i, BOT_BOOL, LSET [])
      | VAR x -> mem(x)
      | DEREF x ->
         begin
           let (z, b, l) = mem(x) in
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
      | AT x ->
         (BOT_Z, BOT_BOOL, LSET [x])
      | TRUE -> (BOT_Z, T, LSET [])
      | FALSE -> (BOT_Z, F, LSET [])
      | ADD (e1, e2) ->
         begin
           let (z1, _, _) = eval (mem, e1) in
           let (z2, _, _) = eval (mem, e2) in
           match z1, z2 with
           | BOT_Z, _ -> botValue
           | _, BOT_Z -> botValue
           | CONST a, CONST b -> (CONST (a + b), BOT_BOOL, LSET []) 
           | TOP_Z, _ -> (TOP_Z, BOT_BOOL, LSET [])
           | _, TOP_Z -> (TOP_Z, BOT_BOOL, LSET [])
         end
      | MINUS e ->
         begin
           let (z, b, l) = eval (mem, e) in
           match z with
           | BOT_Z -> botValue
           | TOP_Z -> (TOP_Z, BOT_BOOL, LSET [])
           | CONST n -> (CONST (-n), BOT_BOOL, LSET [])
         end
      | NOT e ->
         begin
           let (_, b, _) = eval (mem, e) in
           match b with
           | BOT_BOOL -> botValue
           | T -> (BOT_Z, F, LSET [])
           | F -> (BOT_Z, T, LSET [])
           | TOP_BOOL -> (BOT_Z, TOP_BOOL, LSET [])
         end
      | ANDALSO (e1, e2) ->
         begin
           let (_, b1, _) = eval (mem, e1) in
           let (_, b2, _) = eval (mem, e2) in
           match b1, b2 with
           | BOT_BOOL, _ -> botValue
           | _, BOT_BOOL -> botValue
           | F, _ -> (BOT_Z, F, LSET [])
           | _, F -> (BOT_Z, F, LSET [])
           | T, T -> (BOT_Z, T, LSET [])
           | T, TOP_BOOL -> (BOT_Z, TOP_BOOL, LSET [])
           | TOP_BOOL, T -> (BOT_Z, TOP_BOOL, LSET [])
           | TOP_BOOL, TOP_BOOL -> (BOT_Z, TOP_BOOL, LSET [])
         end
      | ORELSE (e1, e2) ->
         begin
           let (_, b1, _) = eval (mem, e1) in
           let (_, b2, _) = eval (mem, e2) in
           match b1, b2 with
           | BOT_BOOL, _ -> botValue
           | _, BOT_BOOL -> botValue
           | T, _ -> (BOT_Z, T, LSET [])
           | _, T -> (BOT_Z, T, LSET [])
           | F, F -> (BOT_Z, F, LSET [])
           | F, TOP_BOOL -> (BOT_Z, TOP_BOOL, LSET [])
           | TOP_BOOL, F -> (BOT_Z, TOP_BOOL, LSET [])
           | TOP_BOOL, TOP_BOOL-> (BOT_Z, TOP_BOOL, LSET [])
         end
      | LESS (e1, e2) ->
         begin
           let (z1, b1, l1) = eval (mem, e1) in
           let (z2, b2, l2) = eval (mem, e2) in
           match z1, z2 with
           | BOT_Z, _ -> botValue
           | _, BOT_Z -> botValue
           | CONST n1, CONST n2 ->
              begin
                match (n1 < n2) with
                | true -> (BOT_Z, T, LSET [])
                | false -> (BOT_Z, F, LSET [])
              end
           | _, _ -> (BOT_Z, TOP_BOOL, LSET [])
         end
                   
    (* TODO : fix it ex 2 version memory filtering by boolean expression *)
    let rec assume : (memory * exp) -> memory = fun (mem, e) ->
      match e with
      | NUM i -> botMemory
      | VAR id ->
         begin
           match mem(id) with
           | (z, b, l) ->
              begin
                match b with
                | F -> botMemory
                | BOT_BOOL -> botMemory
                | T -> mem
                | TOP_BOOL -> store mem id (z, T, l)
              end
         end
      | DEREF x ->
         begin
           match (eval (mem, DEREF x)) with
           | (_, F, _) -> botMemory
           | _ -> mem
         end
      (* implement more precisely if i can*)
      | TRUE -> mem
      | FALSE -> botMemory
      | ADD (e1, e2) -> botMemory
      | MINUS e -> botMemory
      | NOT e -> assumeNot (mem, e)
      | ORELSE (e1, e2) -> (memory_join (assume (mem, e1)) (assume (mem, e2)))
      | ANDALSO (e1, e2) -> (memory_meet (assume (mem, e1)) (assume (mem, e2)))
      | LESS (e1, e2) ->
         begin
           match (eval (mem, (LESS (e1, e2)))) with
           | (_, T, _) -> mem
           | (_, TOP_BOOL, _) -> mem
           | (_, F, _) -> botMemory
           | (_, BOT_BOOL,_) -> botMemory
         end
      | _ -> mem
    and assumeNot : (memory * exp) -> memory = fun (mem, e) ->
      match e with
      | NUM i -> botMemory
      | VAR id ->
         begin
           match mem(id) with
           | (z, b, l) ->
              begin
                match b with
                | T -> botMemory
                | BOT_BOOL -> botMemory
                | F -> mem
                | TOP_BOOL -> store mem id (z, F, l)
              end
         end
      | DEREF x ->
         begin
           match (eval (mem, DEREF x)) with
           | (_, T, _) -> botMemory
           | _ -> mem
         end
      (* implement more precisely if i can*) 
      | TRUE -> botMemory
      | FALSE -> mem
      | ADD (e1, e2) -> botMemory
      | MINUS e -> botMemory
      | NOT e -> assume (mem, e)
      | ORELSE (e1, e2) -> (memory_meet (assumeNot (mem, e1)) (assumeNot (mem, e2)))
      | ANDALSO (e1, e2) -> (memory_join (assumeNot (mem, e1)) (assumeNot (mem, e2)))
      | LESS (e1, e2) ->
         begin
           match (eval (mem, (LESS (e1, e2)))) with
           | (_, F, _) -> mem
           | (_, TOP_BOOL, _) -> mem
           | (_, T, _) -> botMemory
           | (_, BOT_BOOL, _) -> botMemory
         end
      | _ -> mem

    (* interval analysis for K- *)
    let rec analyzer : (memory * program) -> memory = fun (mem, pgm) ->
      let varlist = used_varlist pgm in
      match pgm with
      | SKIP -> mem
      | SEQ(cmd1, cmd2) -> let mem1 = analyzer (mem, cmd1) in analyzer (mem1, cmd2) 
      | IF(e, cmd1, cmd2) ->
         let mem1 = assume (mem, e) in
         let mem2 = assumeNot (mem, e) in
         (memory_join (analyzer (mem1, cmd1)) (analyzer (mem2, cmd2)))
      | WHILE(e, cmd) ->
         begin
           let f =
             begin
               fun m' ->
               let truemem = assume (m', e) in
               let cmem = analyzer (truemem, cmd) in
               (memory_join mem cmem)
             end
           in
           let botm = (partial_botMemory mem varlist) in
           (fix botm f varlist)
         end
      | ASSIGN(id, e) ->
         let v = eval (mem, e) in
         store mem id v
      | PTRASSIGN(id, e) ->
         let v = eval (mem, e) in
         let (z, b, l) = (mem(id)) in
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
