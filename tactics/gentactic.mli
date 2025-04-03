(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** Generic tactic expressions.
    Internally implemented using [Genarg]. *)

type raw_generic_tactic

type glob_generic_tactic

val of_raw_genarg : Genarg.raw_generic_argument -> raw_generic_tactic
(** The genarg must have registrations for all the following APIs. *)

val of_glob_genarg : Genarg.glob_generic_argument -> glob_generic_tactic
(** The genarg must have registrations for all the following APIs
    except those operating at the "raw" level. *)

val print_raw : Environ.env -> Evd.evar_map -> ?level:Constrexpr.entry_relative_level ->
  raw_generic_tactic -> Pp.t

val print_glob : Environ.env -> Evd.evar_map -> ?level:Constrexpr.entry_relative_level ->
  glob_generic_tactic -> Pp.t

val subst : Mod_subst.substitution -> glob_generic_tactic -> glob_generic_tactic

val intern : ?strict:bool -> Environ.env -> ?ltacvars:Id.Set.t -> raw_generic_tactic -> glob_generic_tactic
(** [strict] is default true *)

val interp : ?lfun:Geninterp.Val.t Id.Map.t -> glob_generic_tactic -> unit Proofview.tactic

val wit_generic_tactic : raw_generic_tactic Genarg.vernac_genarg_type

val to_raw_genarg : raw_generic_tactic -> Genarg.raw_generic_argument
(** For serlib *)
