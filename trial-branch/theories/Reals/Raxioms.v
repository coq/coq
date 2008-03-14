(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*********************************************************)
(**    Axiomatisation of the classical reals             *)
(*********************************************************)

Require Export ZArith_base.
Require Export Rdefinitions.
Open Local Scope R_scope.

(*********************************************************)
(** *            Field axioms                            *)
(*********************************************************)

(*********************************************************)
(** **   Addition                                        *)
(*********************************************************)

(**********)
Axiom Rplus_comm : forall r1 r2:R, r1 + r2 = r2 + r1.
Hint Resolve Rplus_comm: real.

(**********)
Axiom Rplus_assoc : forall r1 r2 r3:R, r1 + r2 + r3 = r1 + (r2 + r3).
Hint Resolve Rplus_assoc: real.

(**********)
Axiom Rplus_opp_r : forall r:R, r + - r = 0.
Hint Resolve Rplus_opp_r: real v62.

(**********)
Axiom Rplus_0_l : forall r:R, 0 + r = r.
Hint Resolve Rplus_0_l: real.

(***********************************************************)       
(** **    Multiplication                                   *)
(***********************************************************)

(**********)
Axiom Rmult_comm : forall r1 r2:R, r1 * r2 = r2 * r1.
Hint Resolve Rmult_comm: real v62. 

(**********)
Axiom Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 = r1 * (r2 * r3).
Hint Resolve Rmult_assoc: real v62.

(**********)
Axiom Rinv_l : forall r:R, r <> 0 -> / r * r = 1.
Hint Resolve Rinv_l: real.

(**********)
Axiom Rmult_1_l : forall r:R, 1 * r = r.
Hint Resolve Rmult_1_l: real.

(**********)
Axiom R1_neq_R0 : 1 <> 0.
Hint Resolve R1_neq_R0: real.

(*********************************************************)
(** **   Distributivity                                  *)
(*********************************************************)

(**********)
Axiom
  Rmult_plus_distr_l : forall r1 r2 r3:R, r1 * (r2 + r3) = r1 * r2 + r1 * r3.
Hint Resolve Rmult_plus_distr_l: real v62.

(*********************************************************)
(** *    Order axioms                                    *)
(*********************************************************)
(*********************************************************)
(** **   Total Order                                     *)
(*********************************************************)

(**********)
Axiom total_order_T : forall r1 r2:R, {r1 < r2} + {r1 = r2} + {r1 > r2}.

(*********************************************************)
(** **   Lower                                           *)
(*********************************************************)

(**********)
Axiom Rlt_asym : forall r1 r2:R, r1 < r2 -> ~ r2 < r1.

(**********)
Axiom Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.

(**********)
Axiom Rplus_lt_compat_l : forall r r1 r2:R, r1 < r2 -> r + r1 < r + r2.

(**********)
Axiom
  Rmult_lt_compat_l : forall r r1 r2:R, 0 < r -> r1 < r2 -> r * r1 < r * r2.

Hint Resolve Rlt_asym Rplus_lt_compat_l Rmult_lt_compat_l: real.

(**********************************************************) 
(** *    Injection from N to R                            *)
(**********************************************************)

(**********)
Boxed Fixpoint INR (n:nat) : R :=
  match n with
  | O => 0
  | S O => 1
  | S n => INR n + 1
  end.  
Arguments Scope INR [nat_scope].


(**********************************************************) 
(** *    Injection from [Z] to [R]                        *)
(**********************************************************)

(**********)
Definition IZR (z:Z) : R :=
  match z with
  | Z0 => 0
  | Zpos n => INR (nat_of_P n)
  | Zneg n => - INR (nat_of_P n)
  end.  
Arguments Scope IZR [Z_scope].

(**********************************************************)
(** *    [R] Archimedian                                  *)
(**********************************************************)

(**********)
Axiom archimed : forall r:R, IZR (up r) > r /\ IZR (up r) - r <= 1.

(**********************************************************)
(** *    [R] Complete                                     *)
(**********************************************************)

(**********)
Definition is_upper_bound (E:R -> Prop) (m:R) := forall x:R, E x -> x <= m.

(**********)
Definition bound (E:R -> Prop) :=  exists m : R, is_upper_bound E m.

(**********)
Definition is_lub (E:R -> Prop) (m:R) :=
  is_upper_bound E m /\ (forall b:R, is_upper_bound E b -> m <= b).

(**********)
Axiom
  completeness :
    forall E:R -> Prop,
      bound E -> (exists x : R, E x) -> sigT (fun m:R => is_lub E m).
