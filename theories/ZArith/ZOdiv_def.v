(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


Require Import BinPos BinNat Nnat ZArith_base Ndiv_def.

Open Scope Z_scope.

Definition ZOdiv_eucl (a b:Z) : Z * Z :=
  match a, b with
   | Z0,  _ => (Z0, Z0)
   | _, Z0  => (Z0, a)
   | Zpos na, Zpos nb =>
         let (nq, nr) := Pdiv_eucl na nb in
         (Z_of_N nq, Z_of_N nr)
   | Zneg na, Zpos nb =>
         let (nq, nr) := Pdiv_eucl na nb in
         (Zopp (Z_of_N nq), Zopp (Z_of_N nr))
   | Zpos na, Zneg nb =>
         let (nq, nr) := Pdiv_eucl na nb in
         (Zopp (Z_of_N nq), Z_of_N nr)
   | Zneg na, Zneg nb =>
         let (nq, nr) := Pdiv_eucl na nb in
         (Z_of_N nq, Zopp (Z_of_N nr))
  end.

Definition ZOdiv a b := fst (ZOdiv_eucl a b).
Definition ZOmod a b := snd (ZOdiv_eucl a b).

(* Proofs of specifications for this euclidean division. *)

Theorem ZOdiv_eucl_correct: forall a b,
  let (q,r) := ZOdiv_eucl a b in a = q * b + r.
Proof.
  destruct a; destruct b; simpl; auto;
  generalize (Pdiv_eucl_correct p p0); case Pdiv_eucl; auto; intros q r H.

  change (Zpos p) with (Z_of_N (Npos p)). rewrite H.
   rewrite Z_of_N_plus, Z_of_N_mult. reflexivity.

  change (Zpos p) with (Z_of_N (Npos p)). rewrite H.
   rewrite Z_of_N_plus, Z_of_N_mult. rewrite Zmult_opp_comm. reflexivity.

  change (Zneg p) with (-(Z_of_N (Npos p))); rewrite H.
   rewrite Z_of_N_plus, Z_of_N_mult.
  rewrite Zopp_plus_distr, Zopp_mult_distr_l; trivial.

  change (Zneg p) with (-(Z_of_N (Npos p))); rewrite H.
   rewrite Z_of_N_plus, Z_of_N_mult.
  rewrite Zopp_plus_distr, Zopp_mult_distr_r; trivial.
Qed.
