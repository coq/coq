(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Mod_subst

(** [constr_substituted] are [constr] with possibly pending
    substitutions of kernel names. *)

type constr_substituted

val from_val : constr -> constr_substituted
val force : constr_substituted -> constr
val subst_constr_subst :
  substitution -> constr_substituted -> constr_substituted

(** Opaque proof terms are not loaded immediately, but are there
    in a lazy form. Forcing this lazy may trigger some unmarshal of
    the necessary structure. *)

type lazy_constr

val subst_lazy_constr : substitution -> lazy_constr -> lazy_constr
val force_lazy_constr : lazy_constr -> constr_substituted
val make_lazy_constr : constr_substituted Lazy.t -> lazy_constr
val lazy_constr_is_val : lazy_constr -> bool

val force_opaque : lazy_constr -> constr
val opaque_from_val : constr -> lazy_constr
