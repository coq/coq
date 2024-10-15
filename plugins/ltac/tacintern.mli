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
open Tacexpr
open Genarg
open Constrexpr
open Genintern
open Tactypes

(** Globalization of tactic expressions :
    Conversion from [raw_tactic_expr] to [glob_tactic_expr] *)

type glob_sign = Genintern.glob_sign = {
  ltacvars : Id.Set.t;
  genv : Environ.env;
  extra : Genintern.Store.t;
  intern_sign : Genintern.intern_variable_status;
  strict_check : bool;
}

val make_empty_glob_sign : strict:bool -> glob_sign
 (** build an empty [glob_sign] using [Global.env()] as
     environment; strict_check if true *)

(** Main globalization functions *)

val glob_tactic : raw_tactic_expr -> glob_tactic_expr

val glob_tactic_env :
  Id.t list -> Environ.env -> raw_tactic_expr -> glob_tactic_expr

(** Low-level variants *)

val intern_pure_tactic : glob_sign -> raw_tactic_expr -> glob_tactic_expr

val intern_tactic_or_tacarg :
  glob_sign -> raw_tactic_expr -> Tacexpr.glob_tactic_expr

val intern_constr : glob_sign -> constr_expr -> glob_constr_and_expr

val intern_constr_with_bindings :
  glob_sign -> constr_expr * constr_expr bindings ->
  glob_constr_and_expr * glob_constr_and_expr bindings

val intern_hyp : glob_sign -> lident -> lident

(** Adds a globalization function for extra generic arguments *)

val intern_genarg : glob_sign -> raw_generic_argument -> glob_generic_argument

(** Reduction expressions *)

val intern_red_expr : glob_sign -> Genredexpr.raw_red_expr -> Genredexpr.glob_red_expr

val intern_strategy : glob_sign -> raw_strategy -> glob_strategy
