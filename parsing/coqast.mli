(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
(*i*)

(* Abstract syntax trees. *)

type loc = int * int

type t =
  | Node of loc * string * t list
  | Nmeta of loc * string
  | Nvar of loc * identifier
  | Slam of loc * identifier option * t
  | Smetalam of loc * string * t
  | Num of loc * int
  | Str of loc * string
  | Id of loc * string
  | Path of loc * section_path
  | Dynamic of loc * Dyn.t

(* returns the list of metas occuring in the ast *)
val collect_metas : t -> int list

(* [subst_meta bl ast]: for each binding [(i,c_i)] in [bl], 
   replace the metavar [?i] by [c_i] in [ast] *)
val subst_meta : (int * t) list -> t -> t

(* hash-consing function *)
val hcons_ast: 
  (string -> string) * (Names.identifier -> Names.identifier)
  * (section_path -> section_path)
  -> (t -> t) * (loc -> loc)
