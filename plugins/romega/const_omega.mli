(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)


(** Coq objects used in romega *)

(* from Logic *)
val coq_refl_equal : Term.constr lazy_t
val coq_and : Term.constr lazy_t
val coq_not : Term.constr lazy_t
val coq_or : Term.constr lazy_t
val coq_True : Term.constr lazy_t
val coq_False : Term.constr lazy_t
val coq_I : Term.constr lazy_t

(* from ReflOmegaCore/ZOmega *)

val coq_t_int : Term.constr lazy_t
val coq_t_plus : Term.constr lazy_t
val coq_t_mult : Term.constr lazy_t
val coq_t_opp : Term.constr lazy_t
val coq_t_minus : Term.constr lazy_t
val coq_t_var : Term.constr lazy_t

val coq_proposition : Term.constr lazy_t
val coq_p_eq : Term.constr lazy_t
val coq_p_leq : Term.constr lazy_t
val coq_p_geq : Term.constr lazy_t
val coq_p_lt : Term.constr lazy_t
val coq_p_gt : Term.constr lazy_t
val coq_p_neq : Term.constr lazy_t
val coq_p_true : Term.constr lazy_t
val coq_p_false : Term.constr lazy_t
val coq_p_not : Term.constr lazy_t
val coq_p_or : Term.constr lazy_t
val coq_p_and : Term.constr lazy_t
val coq_p_imp : Term.constr lazy_t
val coq_p_prop : Term.constr lazy_t

val coq_s_bad_constant : Term.constr lazy_t
val coq_s_divide : Term.constr lazy_t
val coq_s_not_exact_divide : Term.constr lazy_t
val coq_s_sum : Term.constr lazy_t
val coq_s_merge_eq : Term.constr lazy_t
val coq_s_split_ineq : Term.constr lazy_t

val coq_direction : Term.constr lazy_t
val coq_d_left : Term.constr lazy_t
val coq_d_right : Term.constr lazy_t

val coq_e_split : Term.constr lazy_t
val coq_e_extract : Term.constr lazy_t
val coq_e_solve : Term.constr lazy_t

val coq_interp_sequent : Term.constr lazy_t
val coq_do_omega : Term.constr lazy_t

val mk_nat : int -> Term.constr
val mk_N : int -> Term.constr

(** Precondition: the type of the list is in Set *)
val mk_list : Term.constr -> Term.constr list -> Term.constr
val mk_plist : Term.types list -> Term.types

(** Analyzing a coq term *)

(* The generic result shape of the analysis of a term.
   One-level depth, except when a number is found *)
type parse_term =
    Tplus of Term.constr * Term.constr
  | Tmult of Term.constr * Term.constr
  | Tminus of Term.constr * Term.constr
  | Topp of Term.constr
  | Tsucc of Term.constr
  | Tnum of Bigint.bigint
  | Tother

(* The generic result shape of the analysis of a relation.
   One-level depth. *)
type parse_rel =
    Req of Term.constr * Term.constr
  | Rne of Term.constr * Term.constr
  | Rlt of Term.constr * Term.constr
  | Rle of Term.constr * Term.constr
  | Rgt of Term.constr * Term.constr
  | Rge of Term.constr * Term.constr
  | Rtrue
  | Rfalse
  | Rnot of Term.constr
  | Ror of Term.constr * Term.constr
  | Rand of Term.constr * Term.constr
  | Rimp of Term.constr * Term.constr
  | Riff of Term.constr * Term.constr
  | Rother

(* A module factorizing what we should now about the number representation *)
module type Int =
  sig
    (* the coq type of the numbers *)
    val typ : Term.constr Lazy.t
    (* the operations on the numbers *)
    val plus : Term.constr Lazy.t
    val mult : Term.constr Lazy.t
    val opp : Term.constr Lazy.t
    val minus : Term.constr Lazy.t
    (* building a coq number *)
    val mk : Bigint.bigint -> Term.constr
    (* parsing a term (one level, except if a number is found) *)
    val parse_term : Term.constr -> parse_term
    (* parsing a relation expression, including = < <= >= > *)
    val parse_rel : [ `NF ] Proofview.Goal.t -> Term.constr -> parse_rel
    (* Is a particular term only made of numbers and + * - ? *)
    val get_scalar : Term.constr -> Bigint.bigint option
  end

(* Currently, we only use Z numbers *)
module Z : Int
