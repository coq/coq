(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Evd
open Sign
open Environ
(*i*)

(*s [existential_value sigma ev] raises [NotInstantiatedEvar] if [ev] has
no body and [Not_found] if it does not exist in [sigma] *)

exception NotInstantiatedEvar
val existential_value : evar_map -> existential -> constr
val existential_type : evar_map -> existential -> types
val existential_opt_value : evar_map -> existential -> constr option
