
(* $Id$ *)

(*i*)
open Names
open Term
open Reduction
(*i*)

(* Reduction functions associated to tactics. *)

type red_expr =
  | Red
  | Hnf
  | Simpl
  | Cbv of Closure.flags
  | Lazy of Closure.flags
  | Unfold of (int list * section_path) list
  | Fold of constr list
  | Change of constr
  | Pattern of (int list * constr * constr) list

val reduction_of_redexp : red_expr -> 'a reduction_function

