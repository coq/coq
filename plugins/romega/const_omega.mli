(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)


(** Coq objects used in romega *)

(* from Logic *)
val coq_refl_equal : EConstr.t lazy_t
val coq_and : EConstr.t lazy_t
val coq_not : EConstr.t lazy_t
val coq_or : EConstr.t lazy_t
val coq_True : EConstr.t lazy_t
val coq_False : EConstr.t lazy_t
val coq_I : EConstr.t lazy_t

(* from ReflOmegaCore/ZOmega *)

val coq_t_int : EConstr.t lazy_t
val coq_t_plus : EConstr.t lazy_t
val coq_t_mult : EConstr.t lazy_t
val coq_t_opp : EConstr.t lazy_t
val coq_t_minus : EConstr.t lazy_t
val coq_t_var : EConstr.t lazy_t

val coq_proposition : EConstr.t lazy_t
val coq_p_eq : EConstr.t lazy_t
val coq_p_leq : EConstr.t lazy_t
val coq_p_geq : EConstr.t lazy_t
val coq_p_lt : EConstr.t lazy_t
val coq_p_gt : EConstr.t lazy_t
val coq_p_neq : EConstr.t lazy_t
val coq_p_true : EConstr.t lazy_t
val coq_p_false : EConstr.t lazy_t
val coq_p_not : EConstr.t lazy_t
val coq_p_or : EConstr.t lazy_t
val coq_p_and : EConstr.t lazy_t
val coq_p_imp : EConstr.t lazy_t
val coq_p_prop : EConstr.t lazy_t

val coq_s_bad_constant : EConstr.t lazy_t
val coq_s_divide : EConstr.t lazy_t
val coq_s_not_exact_divide : EConstr.t lazy_t
val coq_s_sum : EConstr.t lazy_t
val coq_s_merge_eq : EConstr.t lazy_t
val coq_s_split_ineq : EConstr.t lazy_t

val coq_direction : EConstr.t lazy_t
val coq_d_left : EConstr.t lazy_t
val coq_d_right : EConstr.t lazy_t

val coq_e_split : EConstr.t lazy_t
val coq_e_extract : EConstr.t lazy_t
val coq_e_solve : EConstr.t lazy_t

val coq_interp_sequent : EConstr.t lazy_t
val coq_do_omega : EConstr.t lazy_t

val mk_nat : int -> EConstr.t
val mk_N : int -> EConstr.t

(** Precondition: the type of the list is in Set *)
val mk_list : EConstr.t -> EConstr.t list -> EConstr.t
val mk_plist : EConstr.types list -> EConstr.types

(** Analyzing a coq term *)

(* The generic result shape of the analysis of a term.
   One-level depth, except when a number is found *)
type parse_term =
    Tplus of EConstr.t * EConstr.t
  | Tmult of EConstr.t * EConstr.t
  | Tminus of EConstr.t * EConstr.t
  | Topp of EConstr.t
  | Tsucc of EConstr.t
  | Tnum of Bigint.bigint
  | Tother

(* The generic result shape of the analysis of a relation.
   One-level depth. *)
type parse_rel =
    Req of EConstr.t * EConstr.t
  | Rne of EConstr.t * EConstr.t
  | Rlt of EConstr.t * EConstr.t
  | Rle of EConstr.t * EConstr.t
  | Rgt of EConstr.t * EConstr.t
  | Rge of EConstr.t * EConstr.t
  | Rtrue
  | Rfalse
  | Rnot of EConstr.t
  | Ror of EConstr.t * EConstr.t
  | Rand of EConstr.t * EConstr.t
  | Rimp of EConstr.t * EConstr.t
  | Riff of EConstr.t * EConstr.t
  | Rother

(* A module factorizing what we should now about the number representation *)
module type Int =
  sig
    (* the coq type of the numbers *)
    val typ : EConstr.t Lazy.t
    (* Is a constr expands to the type of these numbers *)
    val is_int_typ : Proofview.Goal.t -> EConstr.t -> bool
    (* the operations on the numbers *)
    val plus : EConstr.t Lazy.t
    val mult : EConstr.t Lazy.t
    val opp : EConstr.t Lazy.t
    val minus : EConstr.t Lazy.t
    (* building a coq number *)
    val mk : Bigint.bigint -> EConstr.t
    (* parsing a term (one level, except if a number is found) *)
    val parse_term : Evd.evar_map -> EConstr.t -> parse_term
    (* parsing a relation expression, including = < <= >= > *)
    val parse_rel : Proofview.Goal.t -> EConstr.t -> parse_rel
    (* Is a particular term only made of numbers and + * - ? *)
    val get_scalar : Evd.evar_map -> EConstr.t -> Bigint.bigint option
  end

(* Currently, we only use Z numbers *)
module Z : Int
