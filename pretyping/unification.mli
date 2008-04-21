(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Term
open Environ
open Evd
(*i*)

type unify_flags = { 
  modulo_conv_on_closed_terms : Names.transparent_state option; 
  use_metas_eagerly : bool;
  modulo_delta : Names.transparent_state;
}

val default_unify_flags : unify_flags
val default_no_delta_unify_flags : unify_flags

(* The "unique" unification fonction *)
val w_unify :
  bool -> env -> conv_pb -> ?flags:unify_flags -> constr -> constr -> evar_defs -> evar_defs

(* [w_unify_to_subterm env (c,t) m] performs unification of [c] with a
   subterm of [t]. Constraints are added to [m] and the matched
   subterm of [t] is also returned. *)
val w_unify_to_subterm :
  env -> ?flags:unify_flags -> constr * constr -> evar_defs -> evar_defs * constr

val w_unify_meta_types : env -> ?flags:unify_flags -> evar_defs -> evar_defs

(*i This should be in another module i*)

(* [abstract_list_all env evd t c l]                       *)
(* abstracts the terms in l over c to get a term of type t *)
(* (exported for inv.ml) *)
val abstract_list_all :
  env -> evar_defs -> constr -> constr -> constr list -> constr
