(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Term

val unif_atoms_for_meta : int -> (bool * constr) -> (bool * constr) ->
  (int*constr) option

val find_instances : int -> (bool * constr) list -> Sequent.t -> constr list
