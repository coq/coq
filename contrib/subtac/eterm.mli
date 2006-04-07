(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Tacmach
open Term
open Evd
open Names

val mkMetas : int -> constr list

val eterm_term : evar_map -> constr -> types option -> constr * types option * (identifier * types) list

val etermtac : open_constr -> tactic
