(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

(** {5 Functions on patterns} *)

val constr_pattern_eq : Environ.env -> constr_pattern -> constr_pattern -> bool

val subst_pattern : Environ.env -> Evd.evar_map -> substitution -> 'i constr_pattern_r -> 'i constr_pattern_r

val noccurn_pattern : int -> _ constr_pattern_r -> bool

exception BoundPattern

(** [head_pattern_bound t] extracts the head variable/constant of the
   type [t] or raises [BoundPattern] (even if a sort); it raises an anomaly
   if [t] is an abstraction *)

val head_pattern_bound : constr_pattern -> GlobRef.t

(** [head_of_constr_reference c] assumes [r] denotes a reference and
   returns its label; raises an anomaly otherwise *)

val head_of_constr_reference : Evd.evar_map -> constr -> GlobRef.t
[@@ocaml.deprecated "(8.12) use [EConstr.destRef]"]

(** [pattern_of_constr c] translates a term [c] with metavariables into
   a pattern; currently, no destructor (Cases, Fix, Cofix) and no
   existential variable are allowed in [c] *)

val pattern_of_constr : Environ.env -> Evd.evar_map -> EConstr.constr -> constr_pattern

(** Do not use, for internal Rocq use only. *)
val legacy_bad_pattern_of_constr : Environ.env -> Evd.evar_map -> EConstr.constr -> constr_pattern

(** [pattern_of_glob_constr l c] translates a term [c] with metavariables into
   a pattern; variables bound in [l] are replaced by the pattern to which they
    are bound *)

val pattern_of_glob_constr : Environ.env -> glob_constr -> Id.Set.t * constr_pattern

val uninstantiated_pattern_of_glob_constr : Environ.env -> glob_constr -> Id.Set.t * [`uninstantiated] constr_pattern_r

val map_pattern_with_binders : (Name.t -> 'a -> 'a) ->
  ('a -> 'i constr_pattern_r -> 'i constr_pattern_r) -> 'a -> 'i constr_pattern_r -> 'i constr_pattern_r

val lift_pattern : int -> 'i constr_pattern_r -> 'i constr_pattern_r

(** Interp genargs *)

type 'a pat_interp_fun = Environ.env -> Evd.evar_map -> Ltac_pretype.ltac_var_map
  -> 'a -> Pattern.constr_pattern

val interp_pattern : [`uninstantiated] constr_pattern_r pat_interp_fun

val register_interp_pat : (_, 'g, _) Genarg.genarg_type -> 'g pat_interp_fun -> unit
