(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(* Abstract syntax trees. *)

type loc = int * int

type t =
  | Node of loc * string * t list
  | Nvar of loc * string
  | Slam of loc * string option * t
  | Num of loc * int
  | Id of loc * string
  | Str of loc * string
  | Path of loc * string list* string
  | Dynamic of loc * Dyn.t

(* returns the list of metas occuring in the ast *)
val collect_metas : t -> int list

(* [subst_meta bl ast]: for each binding [(i,c_i)] in [bl], 
   replace the metavar [?i] by [c_i] in [ast] *)
val subst_meta : (int * t) list -> t -> t

(* hash-consing function *)
val hcons_ast: (string -> string) -> (t -> t) * (loc -> loc)

