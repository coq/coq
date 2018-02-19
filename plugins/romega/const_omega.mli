(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)


(** Coq objects used in romega *)
open Constr

(* from Logic *)
val coq_refl_equal : constr lazy_t
val coq_and : constr lazy_t
val coq_not : constr lazy_t
val coq_or : constr lazy_t
val coq_True : constr lazy_t
val coq_False : constr lazy_t
val coq_I : constr lazy_t

(* from ReflOmegaCore/ZOmega *)

val coq_t_int : constr lazy_t
val coq_t_plus : constr lazy_t
val coq_t_mult : constr lazy_t
val coq_t_opp : constr lazy_t
val coq_t_minus : constr lazy_t
val coq_t_var : constr lazy_t

val coq_proposition : constr lazy_t
val coq_p_eq : constr lazy_t
val coq_p_leq : constr lazy_t
val coq_p_geq : constr lazy_t
val coq_p_lt : constr lazy_t
val coq_p_gt : constr lazy_t
val coq_p_neq : constr lazy_t
val coq_p_true : constr lazy_t
val coq_p_false : constr lazy_t
val coq_p_not : constr lazy_t
val coq_p_or : constr lazy_t
val coq_p_and : constr lazy_t
val coq_p_imp : constr lazy_t
val coq_p_prop : constr lazy_t

val coq_s_bad_constant : constr lazy_t
val coq_s_divide : constr lazy_t
val coq_s_not_exact_divide : constr lazy_t
val coq_s_sum : constr lazy_t
val coq_s_merge_eq : constr lazy_t
val coq_s_split_ineq : constr lazy_t

val coq_direction : constr lazy_t
val coq_d_left : constr lazy_t
val coq_d_right : constr lazy_t

val coq_e_split : constr lazy_t
val coq_e_extract : constr lazy_t
val coq_e_solve : constr lazy_t

val coq_interp_sequent : constr lazy_t
val coq_do_omega : constr lazy_t

val mk_nat : int -> constr
val mk_N : int -> constr

(** Precondition: the type of the list is in Set *)
val mk_list : constr -> constr list -> constr
val mk_plist : types list -> types

(** Analyzing a coq term *)

(* The generic result shape of the analysis of a term.
   One-level depth, except when a number is found *)
type parse_term =
    Tplus of constr * constr
  | Tmult of constr * constr
  | Tminus of constr * constr
  | Topp of constr
  | Tsucc of constr
  | Tnum of Bigint.bigint
  | Tother

(* The generic result shape of the analysis of a relation.
   One-level depth. *)
type parse_rel =
    Req of constr * constr
  | Rne of constr * constr
  | Rlt of constr * constr
  | Rle of constr * constr
  | Rgt of constr * constr
  | Rge of constr * constr
  | Rtrue
  | Rfalse
  | Rnot of constr
  | Ror of constr * constr
  | Rand of constr * constr
  | Rimp of constr * constr
  | Riff of constr * constr
  | Rother

(* A module factorizing what we should now about the number representation *)
module type Int =
  sig
    (* the coq type of the numbers *)
    val typ : constr Lazy.t
    (* Is a constr expands to the type of these numbers *)
    val is_int_typ : Proofview.Goal.t -> constr -> bool
    (* the operations on the numbers *)
    val plus : constr Lazy.t
    val mult : constr Lazy.t
    val opp : constr Lazy.t
    val minus : constr Lazy.t
    (* building a coq number *)
    val mk : Bigint.bigint -> constr
    (* parsing a term (one level, except if a number is found) *)
    val parse_term : constr -> parse_term
    (* parsing a relation expression, including = < <= >= > *)
    val parse_rel : Proofview.Goal.t -> constr -> parse_rel
    (* Is a particular term only made of numbers and + * - ? *)
    val get_scalar : constr -> Bigint.bigint option
  end

(* Currently, we only use Z numbers *)
module Z : Int
