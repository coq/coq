(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Interpretation layer of redexprs such as hnf, cbv, etc. *)

open Constr
open EConstr
open Pattern
open Genredexpr
open Reductionops
open Locus

(** User-defined reductions *)
type 'l user_red_expr

val subst_user_red_expr : Genarg.glevel user_red_expr Gensubst.subst_fun
val eval_user_red_expr : Genarg.glevel user_red_expr -> e_reduction_function * cast_kind
val pr_raw_user_red_expr : Environ.env -> Evd.evar_map -> Genarg.rlevel user_red_expr -> Pp.t
val pr_glob_user_red_expr : Environ.env -> Evd.evar_map -> Genarg.glevel user_red_expr -> Pp.t

type raw_red_expr = Genarg.rlevel user_red_expr Genredexpr.raw_red_expr
type glob_red_expr = Genarg.glevel user_red_expr Genredexpr.glob_red_expr
type red_expr = (constr, Evaluable.t, constr_pattern, int, Genarg.glevel user_red_expr) red_expr_gen

type red_expr_val

val out_occurrences : occurrences_expr -> occurrences
val out_with_occurrences : 'a with_occurrences_expr -> 'a with_occurrences

val eval_red_expr : Environ.env -> red_expr -> red_expr_val

val reduction_of_red_expr_val : ?occs:(Locus.occurrences * int) ->
  red_expr_val -> e_reduction_function * cast_kind

(** Composition of {!reduction_of_red_expr_val} with {!eval_red_expr} *)
val reduction_of_red_expr :
  Environ.env -> red_expr -> e_reduction_function * cast_kind

(** [true] if we should use the vm to verify the reduction *)

(** Adding a custom reduction (function to be use at the ML level)
   NB: the effect is permanent. *)
val declare_reduction : string -> reduction_function -> unit

(** Adding a custom reduction (function to be called a vernac command).
   The boolean flag is the locality. *)
val declare_red_expr : bool -> string -> red_expr -> unit

(** Opaque and Transparent commands. *)

(** Sets the expansion strategy of a constant. When the boolean is
   true, the effect is non-synchronous (i.e. it does not survive
   section and module closure). *)
val set_strategy :
  bool -> (Conv_oracle.level * Evaluable.t list) list -> unit

(** call by value normalisation function using the virtual machine *)
val cbv_vm : reduction_function

(** VM normalisation preserving ordinary block-body syntax. *)
val cbv_vm_blocking : reduction_function

(** [subst_red_expr sub c] performs the substitution [sub] on all kernel
   names appearing in [c] *)
val subst_red_expr : Mod_subst.substitution -> red_expr -> red_expr

val wit_red_expr : (raw_red_expr, glob_red_expr, red_expr) Genarg.genarg_type

module Intern : sig
  open Libnames
  open Constrexpr
  open Names

  type ('constr,'ref,'pat) intern_env = {
    strict_check : bool;
    local_ref : qualid -> 'ref option;
    global_ref : ?short:lident -> Evaluable.t -> 'ref;
    intern_constr : constr_expr -> 'constr;
    ltac_sign : Constrintern.ltac_sign;
    intern_pattern : constr_expr -> 'pat;
    pattern_of_glob : Glob_term.glob_constr -> 'pat;
  }

  val intern_red_expr : ('a,'b,'c) intern_env -> raw_red_expr -> ('a,'b,'c, int Locus.or_var, Genarg.glevel user_red_expr) red_expr_gen

  val from_env : Environ.env -> (Glob_term.glob_constr, Evaluable.t, Glob_term.glob_constr) intern_env

end

module Interp : sig
  open Names

  type ('constr,'evref,'pat,'usr) interp_env = {
    interp_occurrence_var : lident -> int list;
    interp_constr : Environ.env -> Evd.evar_map -> 'constr -> Evd.evar_map * EConstr.constr;
    interp_constr_list : Environ.env -> Evd.evar_map -> 'constr -> Evd.evar_map * EConstr.constr list;
    interp_evaluable : Environ.env -> Evd.evar_map -> 'evref -> Evaluable.t;
    interp_pattern : Environ.env -> Evd.evar_map -> 'pat -> constr_pattern;
    interp_evaluable_or_pattern : Environ.env -> Evd.evar_map
      -> 'evref -> (Evaluable.t, constr_pattern) Util.union;
  }

  val interp_red_expr : ('constr,'evref,'pat,'usr) interp_env -> Environ.env -> Evd.evar_map
    -> ('constr,'evref,'pat, int Locus.or_var, Genarg.glevel user_red_expr) red_expr_gen -> Evd.evar_map * red_expr

  val without_ltac : (Glob_term.glob_constr, Evaluable.t, Glob_term.glob_constr, 'usr) interp_env

end

val interp_redexp_no_ltac : Environ.env -> Evd.evar_map -> raw_red_expr -> Evd.evar_map * red_expr

module User :
sig

type ('raw, 'glb) user_red_spec = {
  ured_intern : Constrintern.ltac_sign -> 'raw -> 'glb;
  ured_subst : Mod_subst.substitution -> 'glb -> 'glb;
  ured_eval : 'glb -> e_reduction_function * cast_kind;
  ured_rprint : Environ.env -> Evd.evar_map -> 'raw -> Pp.t;
  ured_gprint : Environ.env -> Evd.evar_map -> 'glb -> Pp.t;
}

type ('raw, 'glb) user_red
(** User-defined reductions are indexed by the kind of payload they contain at
    both raw and glob levels. *)

val create : string -> ('raw, 'glb) user_red_spec -> ('raw, 'glb) user_red
(** Create a new user-defined reduction. *)

val make : ('raw, 'glb) user_red -> 'raw -> Genarg.rlevel user_red_expr
(** Inject the required data into a user reduction expression. *)

end
