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
val coq_h_step : Term.constr lazy_t
val coq_pair_step : Term.constr lazy_t
val coq_p_left : Term.constr lazy_t
val coq_p_right : Term.constr lazy_t
val coq_p_invert : Term.constr lazy_t
val coq_p_step : Term.constr lazy_t

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

val coq_f_equal : Term.constr lazy_t
val coq_f_cancel : Term.constr lazy_t
val coq_f_left : Term.constr lazy_t
val coq_f_right : Term.constr lazy_t

val coq_c_do_both : Term.constr lazy_t
val coq_c_do_left : Term.constr lazy_t
val coq_c_do_right : Term.constr lazy_t
val coq_c_do_seq : Term.constr lazy_t
val coq_c_nop : Term.constr lazy_t
val coq_c_opp_plus : Term.constr lazy_t
val coq_c_opp_opp : Term.constr lazy_t
val coq_c_opp_mult_r : Term.constr lazy_t
val coq_c_opp_one : Term.constr lazy_t
val coq_c_reduce : Term.constr lazy_t
val coq_c_mult_plus_distr : Term.constr lazy_t
val coq_c_opp_left : Term.constr lazy_t
val coq_c_mult_assoc_r : Term.constr lazy_t
val coq_c_plus_assoc_r : Term.constr lazy_t
val coq_c_plus_assoc_l : Term.constr lazy_t
val coq_c_plus_permute : Term.constr lazy_t
val coq_c_plus_comm : Term.constr lazy_t
val coq_c_red0 : Term.constr lazy_t
val coq_c_red1 : Term.constr lazy_t
val coq_c_red2 : Term.constr lazy_t
val coq_c_red3 : Term.constr lazy_t
val coq_c_red4 : Term.constr lazy_t
val coq_c_red5 : Term.constr lazy_t
val coq_c_red6 : Term.constr lazy_t
val coq_c_mult_opp_left : Term.constr lazy_t
val coq_c_mult_assoc_reduced : Term.constr lazy_t
val coq_c_minus : Term.constr lazy_t
val coq_c_mult_comm : Term.constr lazy_t

val coq_s_constant_not_nul : Term.constr lazy_t
val coq_s_constant_neg : Term.constr lazy_t
val coq_s_div_approx : Term.constr lazy_t
val coq_s_not_exact_divide : Term.constr lazy_t
val coq_s_exact_divide : Term.constr lazy_t
val coq_s_sum : Term.constr lazy_t
val coq_s_state : Term.constr lazy_t
val coq_s_contradiction : Term.constr lazy_t
val coq_s_merge_eq : Term.constr lazy_t
val coq_s_split_ineq : Term.constr lazy_t
val coq_s_constant_nul : Term.constr lazy_t
val coq_s_negate_contradict : Term.constr lazy_t
val coq_s_negate_contradict_inv : Term.constr lazy_t

val coq_direction : Term.constr lazy_t
val coq_d_left : Term.constr lazy_t
val coq_d_right : Term.constr lazy_t
val coq_d_mono : Term.constr lazy_t

val coq_e_split : Term.constr lazy_t
val coq_e_extract : Term.constr lazy_t
val coq_e_solve : Term.constr lazy_t

val coq_interp_sequent : Term.constr lazy_t
val coq_do_omega : Term.constr lazy_t

(** Building expressions *)

val do_left : Term.constr -> Term.constr
val do_right : Term.constr -> Term.constr
val do_both : Term.constr -> Term.constr -> Term.constr
val do_seq : Term.constr -> Term.constr -> Term.constr
val do_list : Term.constr list -> Term.constr

val mk_nat : int -> Term.constr
(** Precondition: the type of the list is in Set *)
val mk_list : Term.constr -> Term.constr list -> Term.constr
val mk_plist : Term.types list -> Term.types
val mk_shuffle_list : Term.constr list -> Term.constr

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
    val parse_rel : Proof_type.goal Tacmach.sigma -> Term.constr -> parse_rel
    (* Is a particular term only made of numbers and + * - ? *)
    val is_scalar : Term.constr -> bool
  end

(* Currently, we only use Z numbers *)
module Z : Int
