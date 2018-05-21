(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Mod_subst
open Glob_term
open Pattern
open EConstr
open Ltac_pretype

(** {5 Functions on patterns} *)

val constr_pattern_eq : constr_pattern -> constr_pattern -> bool

val occur_meta_pattern : constr_pattern -> bool

val subst_pattern : substitution -> constr_pattern -> constr_pattern

val noccurn_pattern : int -> constr_pattern -> bool

exception BoundPattern

(** [head_pattern_bound t] extracts the head variable/constant of the
   type [t] or raises [BoundPattern] (even if a sort); it raises an anomaly
   if [t] is an abstraction *)

val head_pattern_bound : constr_pattern -> GlobRef.t

(** [head_of_constr_reference c] assumes [r] denotes a reference and
   returns its label; raises an anomaly otherwise *)

val head_of_constr_reference : Evd.evar_map -> constr -> GlobRef.t

(** [pattern_of_constr c] translates a term [c] with metavariables into
   a pattern; currently, no destructor (Cases, Fix, Cofix) and no
   existential variable are allowed in [c] *)

val pattern_of_constr : Environ.env -> Evd.evar_map -> Constr.constr -> constr_pattern

(** [pattern_of_glob_constr l c] translates a term [c] with metavariables into
   a pattern; variables bound in [l] are replaced by the pattern to which they
    are bound *)

val pattern_of_glob_constr : glob_constr ->
      patvar list * constr_pattern

val instantiate_pattern : Environ.env ->
  Evd.evar_map -> extended_patvar_map ->
  constr_pattern -> constr_pattern

val lift_pattern : int -> constr_pattern -> constr_pattern
