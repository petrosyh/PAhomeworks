(*
 * SNU 4541.664A Program Analysis
 * Example code for how to use domain functors
 *)

open Program
open DomFunctor

module Intv 
=
struct
  type bound = Z of int | Pinfty | Ninfty
  type t = BOT | ELT of bound * bound

  let top = ELT (Ninfty, Pinfty)
  let bot = BOT
  let bound_leq a b = 
    match a,b with
    | (Ninfty, _) -> true
    | (_, Pinfty) -> true
    | (_, Ninfty) -> false
    | (Pinfty, _) -> false
    | (Z i1, Z i2) -> i1 <= i2

  let smaller a b = if bound_leq a b then a else b

  let bigger a b = if bound_leq a b then b else a

  let join x y = 
    match x,y with
    | (BOT, _) -> y
    | (_, BOT) -> x
    | (ELT (l1, u1), ELT (l2, u2)) -> ELT (smaller l1 l2, bigger u1 u2)

  let leq x y = match x,y with
    | (BOT, _) -> true
    | (_, BOT) -> false
    | (ELT (l1,u1), ELT (l2,u2)) -> bound_leq l2 l1 && bound_leq u1 u2

  let make low upper = ELT (low, upper)
end


module Var = 
struct
  type t = string
  let compare = compare
end

module Loc = Var
module LocSet = PrimitiveSet(Loc)
module LocPowSet = PowerSetDomain (LocSet)
module Value = ProductDomain(Intv)(LocPowSet)
module Memory = FunDomain(Loc)(Value)
