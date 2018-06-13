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
open Tacexpr
open Genarg
open Constrexpr
open Tactypes

(** Globalization of tactic expressions :
    Conversion from [raw_tactic_expr] to [glob_tactic_expr] *)

type glob_sign = Genintern.glob_sign = {
  ltacvars : Id.Set.t;
  genv : Environ.env;
  extra : Genintern.Store.t;
}

val fully_empty_glob_sign : glob_sign

val make_empty_glob_sign : unit -> glob_sign
 (** same as [fully_empty_glob_sign], but with [Global.env()] as
     environment *)

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

(** printing *)
val print_ltac : Libnames.qualid -> Pp.t

(** Reduction expressions *)

val intern_red_expr : glob_sign -> raw_red_expr -> glob_red_expr
val dump_glob_red_expr : raw_red_expr -> unit

(* Hooks *)
val strict_check : bool ref
