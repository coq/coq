(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Environ
open EConstr
open Evd
open Proof_type
open Redexpr
open Pattern
open Locus

(** Operations for handling terms under a local typing context. *)

type 'a sigma   = 'a Evd.sigma;;
type tactic     = Proof_type.tactic;;

val sig_it  : 'a sigma   -> 'a
val project : goal sigma -> evar_map

val re_sig : 'a -> evar_map -> 'a sigma

val unpackage : 'a sigma -> evar_map ref * 'a
val repackage : evar_map ref -> 'a -> 'a sigma
val apply_sig_tac :
  evar_map ref -> (goal sigma -> (goal list) sigma) -> goal -> (goal list)

val pf_concl              : goal sigma -> types
val pf_env                : goal sigma -> env
val pf_hyps               : goal sigma -> named_context
(*i val pf_untyped_hyps       : goal sigma -> (Id.t * constr) list i*)
val pf_hyps_types         : goal sigma -> (Id.t * types) list
val pf_nth_hyp_id         : goal sigma -> int -> Id.t
val pf_last_hyp           : goal sigma -> named_declaration
val pf_ids_of_hyps        : goal sigma -> Id.t list
val pf_global             : goal sigma -> Id.t -> constr
val pf_unsafe_type_of            : goal sigma -> constr -> types
val pf_type_of            : goal sigma -> constr -> evar_map * types
val pf_hnf_type_of        : goal sigma -> constr -> types

val pf_get_hyp            : goal sigma -> Id.t -> named_declaration
val pf_get_hyp_typ        : goal sigma -> Id.t -> types

val pf_get_new_id  : Id.t      -> goal sigma -> Id.t
val pf_get_new_ids : Id.t list -> goal sigma -> Id.t list

val pf_reduction_of_red_expr : goal sigma -> red_expr -> constr -> evar_map * constr


val pf_apply : (env -> evar_map -> 'a) -> goal sigma -> 'a
val pf_eapply : (env -> evar_map -> 'a -> evar_map * 'b) -> 
  goal sigma -> 'a -> goal sigma * 'b
val pf_reduce :
  (env -> evar_map -> constr -> constr) ->
  goal sigma -> constr -> constr
val pf_e_reduce :
  (env -> evar_map -> constr -> evar_map * constr) ->
  goal sigma -> constr -> evar_map * constr

val pf_whd_all       : goal sigma -> constr -> constr
val pf_hnf_constr              : goal sigma -> constr -> constr
val pf_nf                      : goal sigma -> constr -> constr
val pf_nf_betaiota             : goal sigma -> constr -> constr
val pf_reduce_to_quantified_ind : goal sigma -> types -> (inductive * EInstance.t) * types
val pf_reduce_to_atomic_ind     : goal sigma -> types -> (inductive * EInstance.t) * types
val pf_compute                 : goal sigma -> constr -> constr
val pf_unfoldn    : (occurrences * evaluable_global_reference) list
  -> goal sigma -> constr -> constr

val pf_const_value : goal sigma -> pconstant -> constr
val pf_conv_x      : goal sigma -> constr -> constr -> bool
val pf_conv_x_leq  : goal sigma -> constr -> constr -> bool

val pf_matches     : goal sigma -> constr_pattern -> constr -> patvar_map
val pf_is_matching : goal sigma -> constr_pattern -> constr -> bool


(** {6 The most primitive tactics. } *)

val refiner                   : rule -> tactic
val internal_cut_no_check     : bool -> Id.t -> types -> tactic
val refine_no_check           : constr -> tactic

(** {6 The most primitive tactics with consistency and type checking } *)

val internal_cut     : bool -> Id.t -> types -> tactic
val internal_cut_rev : bool -> Id.t -> types -> tactic
val refine           : constr -> tactic

(** {6 Pretty-printing functions (debug only). } *)
val pr_gls    : goal sigma -> Pp.std_ppcmds
val pr_glls   : goal list sigma -> Pp.std_ppcmds

(* Variants of [Tacmach] functions built with the new proof engine *)
module New : sig
  val pf_apply : (env -> evar_map -> 'a) -> ('b, 'r) Proofview.Goal.t -> 'a
  val pf_global : identifier -> ('a, 'r) Proofview.Goal.t -> constr
  (** FIXME: encapsulate the level in an existential type. *)
  val of_old : (Proof_type.goal Evd.sigma -> 'a) -> ([ `NF ], 'r) Proofview.Goal.t -> 'a

  val project : ('a, 'r) Proofview.Goal.t -> Evd.evar_map
  val pf_env : ('a, 'r) Proofview.Goal.t -> Environ.env
  val pf_concl : ('a, 'r) Proofview.Goal.t -> types

  (** WRONG: To be avoided at all costs, it typechecks the term entirely but
     forgets the universe constraints necessary to retypecheck it *)
  val pf_unsafe_type_of : ('a, 'r) Proofview.Goal.t -> constr -> types

  (** This function does no type inference and expects an already well-typed term.
      It recomputes its type in the fastest way possible (no conversion is ever involved) *)
  val pf_get_type_of : ('a, 'r) Proofview.Goal.t -> constr -> types

  (** This function entirely type-checks the term and computes its type
      and the implied universe constraints. *)
  val pf_type_of : ('a, 'r) Proofview.Goal.t -> constr -> evar_map * types
  val pf_conv_x : ('a, 'r) Proofview.Goal.t -> t -> t -> bool

  val pf_get_new_id  : identifier -> ('a, 'r) Proofview.Goal.t -> identifier
  val pf_ids_of_hyps : ('a, 'r) Proofview.Goal.t -> identifier list
  val pf_hyps_types : ('a, 'r) Proofview.Goal.t -> (identifier * types) list

  val pf_get_hyp : identifier -> ('a, 'r) Proofview.Goal.t -> named_declaration
  val pf_get_hyp_typ        : identifier -> ('a, 'r) Proofview.Goal.t -> types
  val pf_last_hyp           : ('a, 'r) Proofview.Goal.t -> named_declaration

  val pf_nf_concl : ([ `LZ ], 'r) Proofview.Goal.t -> types
  val pf_reduce_to_quantified_ind : ('a, 'r) Proofview.Goal.t -> types -> (inductive * EInstance.t) * types

  val pf_hnf_constr : ('a, 'r) Proofview.Goal.t -> constr -> types
  val pf_hnf_type_of : ('a, 'r) Proofview.Goal.t -> constr -> types

  val pf_whd_all : ('a, 'r) Proofview.Goal.t -> constr -> constr
  val pf_compute : ('a, 'r) Proofview.Goal.t -> constr -> constr

  val pf_matches : ('a, 'r) Proofview.Goal.t -> constr_pattern -> constr -> patvar_map

  val pf_nf_evar : ('a, 'r) Proofview.Goal.t -> constr -> constr

end
