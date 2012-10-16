(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Names
open Proof_type
open Tacmach
open Tactic_debug
open Term
open Tacexpr
open Genarg
open Constrexpr
open Mod_subst
open Redexpr
open Misctypes
open Nametab

(** Globalization of tactic expressions :
    Conversion from [raw_tactic_expr] to [glob_tactic_expr] *)

type glob_sign = {
  ltacvars : identifier list * identifier list;
  ltacrecvars : (identifier * ltac_constant) list;
  gsigma : Evd.evar_map;
  genv : Environ.env }

val fully_empty_glob_sign : glob_sign

val make_empty_glob_sign : unit -> glob_sign
 (** same as [fully_empty_glob_sign], but with [Global.env()] as
     environment *)

(** Main globalization functions *)

val glob_tactic : raw_tactic_expr -> glob_tactic_expr

val glob_tactic_env :
  identifier list -> Environ.env -> raw_tactic_expr -> glob_tactic_expr

(** Low-level variants *)

val intern_pure_tactic : glob_sign -> raw_tactic_expr -> glob_tactic_expr

val intern_tactic_or_tacarg :
  glob_sign -> raw_tactic_expr -> Tacexpr.glob_tactic_expr

val intern_constr : glob_sign -> constr_expr -> glob_constr_and_expr

val intern_constr_with_bindings :
  glob_sign -> constr_expr * constr_expr bindings ->
  glob_constr_and_expr * glob_constr_and_expr bindings

val intern_hyp : glob_sign -> identifier Loc.located -> identifier Loc.located

(** Adds a globalization function for extra generic arguments *)

type intern_genarg_type =
    glob_sign -> raw_generic_argument -> glob_generic_argument

val add_intern_genarg : string -> intern_genarg_type -> unit

val intern_genarg : intern_genarg_type

(** Adds a definition of tactics in the table *)
val add_tacdef :
  Vernacexpr.locality_flag -> bool ->
  (Libnames.reference * bool * raw_tactic_expr) list -> unit
val add_primitive_tactic : string -> glob_tactic_expr -> unit

(** Tactic extensions *)
val add_tactic :
  string -> (typed_generic_argument list -> tactic) -> unit
val overwriting_add_tactic :
  string -> (typed_generic_argument list -> tactic) -> unit
val lookup_tactic :
  string -> (typed_generic_argument list) -> tactic

val lookup_ltacref : ltac_constant -> glob_tactic_expr

(** printing *)
val print_ltac : Libnames.qualid -> std_ppcmds

(** Reduction expressions *)

val intern_red_expr : glob_sign -> raw_red_expr -> glob_red_expr
val dump_glob_red_expr : raw_red_expr -> unit
