(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Libnames
(*i*)

(* Abstract syntax trees. *)

type t =
  | Node of loc * string * t list
  | Nmeta of loc * string
  | Nvar of loc * identifier
  | Slam of loc * identifier option * t
  | Smetalam of loc * string * t
  | Num of loc * int
  | Str of loc * string
  | Id of loc * string
  | Path of loc * kernel_name
  | Dynamic of loc * Dyn.t

(* returns the list of metas occuring in the ast *)
val collect_metas : t -> int list

(* [subst_meta bl ast]: for each binding [(i,c_i)] in [bl], 
   replace the metavar [?i] by [c_i] in [ast] *)
val subst_meta : (int * t) list -> t -> t

(* hash-consing function *)
val hcons_ast: 
  (string -> string) * (Names.identifier -> Names.identifier)
  * (kernel_name -> kernel_name)
  -> (t -> t) * (loc -> loc)

val subst_ast: Names.substitution -> t -> t

(*i
val map_tactic_expr : (t -> t) -> (tactic_expr -> tactic_expr) -> tactic_expr -> tactic_expr
val fold_tactic_expr :
  ('a -> t -> 'a) -> ('a -> tactic_expr -> 'a) -> 'a -> tactic_expr -> 'a
val iter_tactic_expr : (tactic_expr -> unit) -> tactic_expr -> unit
i*)
