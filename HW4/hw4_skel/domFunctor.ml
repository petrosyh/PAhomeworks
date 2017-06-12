(*
 * SNU 4541.664A Program Analysis
 * Domain functors. See domExample.ml for its usage examples.
 *)

module type ELEM = sig
  type t
  val compare : t -> t -> int
end

module type SET = sig
  type elt
  type t

  exception Infinite

  val cmp_elt : elt -> elt -> int

  val empty : t
  val all : unit -> t
  val to_list : t -> elt list

  val add : elt -> t -> t
  val remove : elt -> t -> t
  val mem : elt -> t -> bool

  val subset : t -> t -> bool
  val union : t -> t -> t
  val inter : t -> t -> t
  val diff : t -> t -> t

  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
end

module type DOMAIN =
sig
  type t (* the type of abstract domain elements *)
  val bot : t
  val top : t
  val join : t -> t -> t
  val leq : t -> t -> bool (* leq x y is true if x is less/equal than y *)
end

module PrimitiveSet(A: ELEM) = 
struct
  include Set.Make(A)
  exception Infinite
  let cmp_elt = A.compare
  let all () = raise Infinite
  let to_list = elements
end

module ProductSet (A: SET) (B: SET) =
struct
  let cmp_elt (a,b) (a', b') = 
    if A.cmp_elt a a' = 0 then
      B.cmp_elt b b'
    else A.cmp_elt a a'

  include Set.Make (struct type t = A.elt * B.elt let compare = cmp_elt end)

  exception Infinite

  let all = fun () -> 
    try
      A.fold (fun a c ->
        B.fold (fun b c -> add (a, b) c) (B.all()) c
      ) (A.all()) empty
    with A.Infinite | B.Infinite -> raise Infinite

  let to_list = elements
end


module FlatDomain (A: ELEM) =
struct
  type t = BOT | TOP | ELT of A.t
  let bot = BOT
  let top = TOP

  let join x y = 
    match (x, y) with
    | (BOT, _) -> y
    | (_, BOT) -> x
    | (TOP, _) -> TOP
    | (_, TOP) -> TOP
    | (ELT a, ELT b) -> if A.compare a b = 0 then x else TOP

  let leq x y = 
    match (x, y) with
    | (BOT, _) -> true
    | (_, TOP) -> true
    | (TOP, _) -> false
    | (_, BOT) -> false
    | (ELT a, ELT b) -> A.compare a b = 0

  let make a = ELT a
end

module ProductDomain (A: DOMAIN) (B: DOMAIN) =
struct
  type t = A.t * B.t
  let bot = (A.bot, B.bot)
  let top = (A.top, B.top)

  let join x y = 
    let (a, b) = x in
    let (a', b') = y in
    A.join a a', B.join b b'

  let leq x y = 
    let (a, b) = x in
    let (a', b') = y in
    (A.leq a a') && (B.leq b b')

  let l x = fst x

  let r x = snd x

  let make a b = (a, b)
end

module PowerSetDomain (S: SET) =
struct
  type t = TOP | ELT of S.t
  let bot = ELT S.empty
  let top = TOP

  let join x y = 
    match (x,y) with
    | (TOP, _) -> TOP
    | (_, TOP) -> TOP
    | (ELT s, ELT s') -> ELT (S.union s s')

  let mem a s = 
    match s with 
    | TOP -> true
    | ELT s -> S.mem a s

  let fold f x a = 
    match x with 
    | TOP -> S.fold f (S.all()) a
    | ELT s -> S.fold f s a

  let map f x = 
    match x with 
    | TOP -> ELT (S.fold (fun a s' -> S.add (f a) s') (S.all()) S.empty)
    | ELT s -> ELT (S.fold (fun a s' -> S.add (f a) s') s S.empty)

  let make lst = 
    ELT (List.fold_left (fun s x -> S.add x s) S.empty lst)

  let leq x y = 
    match x, y with
    | (_, TOP) -> true
    | (TOP,ELT s) -> 
      (try (S.subset (S.all ()) s) with S.Infinite -> false)
    | (ELT s1, ELT s2) -> S.subset s1 s2

  let union x y = 
    match x,y with
    | (TOP, _) -> TOP
    | (_, TOP) -> TOP
    | (ELT s1, ELT s2) -> ELT (S.union s1 s2)

  let inter x y = 
    match x,y with
    | (TOP, _) -> y
    | (_, TOP) -> x
    | (ELT s1, ELT s2) -> ELT (S.inter s1 s2)

  let diff x y = 
    match x,y with
    | (TOP, ELT s1) -> ELT (S.diff (S.all ()) s1)
    | (_, TOP) -> ELT S.empty
    | (ELT s1, ELT s2) -> ELT (S.diff s1 s2)

  let remove a x = 
    match x with
    | ELT s -> ELT (S.remove a s)
    | TOP -> ELT (S.remove a (S.all ()))

  let to_list x = 
    match x with
    | TOP -> S.to_list (S.all())
    | ELT s -> S.to_list s
end

module FunDomainFromSet (A: SET) (B: DOMAIN) =
struct
  module Map = Map.Make(struct type t = A.elt let compare = A.cmp_elt end)

  type t = TOP | ELT of B.t Map.t

  let bot = ELT Map.empty

  let top = TOP

  let join x y = 
    match x,y with
    | (TOP, _) -> TOP
    | (_, TOP) -> TOP
    | (ELT m1, ELT m2) -> 
      ELT (
        Map.fold 
          (fun k v acc_m -> 
            if Map.mem k acc_m then
             Map.add k (B.join v (Map.find k acc_m)) acc_m
            else Map.add k v acc_m
          ) m1 m2
      )

  let leq x y = 
    match x,y with
    | (_, TOP) -> true
    | (TOP, ELT s) -> 
      (try
        (A.fold
          (fun e a -> 
            if Map.mem e s
            then (B.leq B.top (Map.find e s)) && a
            else false
          )
          (A.all ())
          true
        )
       with A.Infinite -> false)
    | (ELT s1, ELT s2) -> 
      Map.fold
         (fun k a b -> 
            if Map.mem k s2
            then (B.leq a (Map.find k s2)) && b
            else (B.leq a B.bot) && b
         )
         s1 true

  let image x l = 
    match x with
    | TOP -> B.top
    | ELT s -> 
      if Map.mem l s
      then Map.find l s
      else B.bot

  let update x l r = 
    match x with
    | TOP -> 
      if (B.leq B.top r) then TOP else
        ELT 
          (A.fold 
            (fun e a -> 
               if A.cmp_elt e l = 0
               then Map.add e r a
               else Map.add e B.top a
            ) (A.all ()) Map.empty
          )
    | ELT s -> ELT (Map.add l r s)

  let weakupdate x l r = 
    match x with
    | TOP -> TOP
    | ELT s -> 
      if Map.mem l s 
      then ELT (Map.add l (B.join r (Map.find l s)) s)
      else ELT (Map.add l r s)

  let map f x = 
    match x with
    | TOP -> 
      ELT 
        (A.fold
          (fun l a -> 
            let (l',r') = f l B.top in
            Map.add l' r' a
          ) (A.all ()) Map.empty)
    | ELT s ->
      ELT 
        (Map.fold
          (fun l r a ->
            let (l', r') = f l r in
            Map.add l' r' a
          ) s Map.empty)

  let fold f x acc = 
    match x with
    | TOP ->
      A.fold
        (fun l a ->
           f l B.top a
        ) (A.all ()) acc
    | ELT s ->
      Map.fold
        (fun l r a ->
          f l r a
        ) s acc

  let to_list x = 
    match x with
    | TOP -> List.map (fun l -> (l, B.top)) (A.to_list (A.all()))
    | ELT s -> Map.bindings s

  let make l = 
    ELT (List.fold_left (fun a (b,c) -> Map.add b c a) Map.empty l)
end

module FunDomain(A: ELEM)(B: DOMAIN) =
struct
  module S = PrimitiveSet(A)
  include FunDomainFromSet(S)(B)
end
