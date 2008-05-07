(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(** * *)

(** 
- Authors: Benjamin Grégoire, Laurent Théry
- Institution: INRIA
- Date: 2007
- Remark: File automatically generated
*)

Require Import BigNumPrelude.
Require Import ZArith.
Require Import Basic_type.
Require Import ZnZ.
Require Import Zn2Z.
Require Import Nbasic.
Require Import GenMul.
Require Import GenDivn1.
Require Import Wf_nat.
Require Import StreamMemo.

Module Type W0Type.
 Parameter w : Set.
 Parameter w_op : znz_op w.
 Parameter w_spec : znz_spec w_op.
End W0Type.

Module Make (W0:W0Type).
 Import W0.

 Definition w0 := W0.w.
 Definition w1 := zn2z w0.
 Definition w2 := zn2z w1.
 Definition w3 := zn2z w2.
 Definition w4 := zn2z w3.
 Definition w5 := zn2z w4.
 Definition w6 := zn2z w5.

 Definition w0_op := W0.w_op.
 Definition w1_op := mk_zn2z_op w0_op.
 Definition w2_op := mk_zn2z_op w1_op.
 Definition w3_op := mk_zn2z_op w2_op.
 Definition w4_op := mk_zn2z_op_karatsuba w3_op.
 Definition w5_op := mk_zn2z_op_karatsuba w4_op.
 Definition w6_op := mk_zn2z_op_karatsuba w5_op.
 Definition w7_op := mk_zn2z_op_karatsuba w6_op.
 Definition w8_op := mk_zn2z_op_karatsuba w7_op.
 Definition w9_op := mk_zn2z_op_karatsuba w8_op.

 Section Make_op.
  Variable mk : forall w', znz_op w' -> znz_op (zn2z w').

  Fixpoint make_op_aux (n:nat) : znz_op (word w6 (S n)):=
   match n return znz_op (word w6 (S n)) with
   | O => w7_op
   | S n1 =>
     match n1 return znz_op (word w6 (S (S n1))) with
     | O => w8_op
     | S n2 =>
       match n2 return znz_op (word w6 (S (S (S n2)))) with
       | O => w9_op
       | S n3 => mk _ (mk _ (mk _ (make_op_aux n3)))
       end
     end
   end.

 End Make_op.

 Definition omake_op := make_op_aux mk_zn2z_op_karatsuba.


 Definition make_op_list := dmemo_list _ omake_op.

 Definition make_op n := dmemo_get _ omake_op n make_op_list.

 Lemma make_op_omake: forall n, make_op n = omake_op n.
 intros n; unfold make_op, make_op_list.
 refine (dmemo_get_correct _ _ _).
 Qed.

 Inductive t_ : Set :=
  | N0 : w0 -> t_
  | N1 : w1 -> t_
  | N2 : w2 -> t_
  | N3 : w3 -> t_
  | N4 : w4 -> t_
  | N5 : w5 -> t_
  | N6 : w6 -> t_
  | Nn : forall n, word w6 (S n) -> t_.

 Definition t := t_.

 Definition w_0 := w0_op.(znz_0).

 Definition one0 := w0_op.(znz_1).
 Definition one1 := w1_op.(znz_1).
 Definition one2 := w2_op.(znz_1).
 Definition one3 := w3_op.(znz_1).
 Definition one4 := w4_op.(znz_1).
 Definition one5 := w5_op.(znz_1).
 Definition one6 := w6_op.(znz_1).

 Definition zero := N0 w_0.
 Definition one := N0 one0.

 Definition to_Z x :=
  match x with
  | N0 wx => w0_op.(znz_to_Z) wx
  | N1 wx => w1_op.(znz_to_Z) wx
  | N2 wx => w2_op.(znz_to_Z) wx
  | N3 wx => w3_op.(znz_to_Z) wx
  | N4 wx => w4_op.(znz_to_Z) wx
  | N5 wx => w5_op.(znz_to_Z) wx
  | N6 wx => w6_op.(znz_to_Z) wx
  | Nn n wx => (make_op n).(znz_to_Z) wx
  end.

 Open Scope Z_scope.
 Notation "[ x ]" := (to_Z x).
 
 (* Regular make op (no karatsuba) *)
 Fixpoint nmake_op (ww:Set) (ww_op: znz_op ww) (n: nat) : 
       znz_op (word ww n) :=
  match n return znz_op (word ww n) with 
   O => ww_op
  | S n1 => mk_zn2z_op (nmake_op ww ww_op n1) 
  end.

 (* Simplification by rewriting for nmake_op *)
 Theorem nmake_op_S: forall ww (w_op: znz_op ww) x, 
   nmake_op _ w_op (S x) = mk_zn2z_op (nmake_op _ w_op x).
 auto.
 Qed.

 (* Eval and extend functions for each level *)
 Let nmake_op0 := nmake_op _ w0_op.
 Let eval0n n := znz_to_Z  (nmake_op0 n).
 Let extend0 := GenBase.extend  (WW w_0).
 Let nmake_op1 := nmake_op _ w1_op.
 Let eval1n n := znz_to_Z  (nmake_op1 n).
 Let extend1 := GenBase.extend  (WW (W0: w1)).
 Let nmake_op2 := nmake_op _ w2_op.
 Let eval2n n := znz_to_Z  (nmake_op2 n).
 Let extend2 := GenBase.extend  (WW (W0: w2)).
 Let nmake_op3 := nmake_op _ w3_op.
 Let eval3n n := znz_to_Z  (nmake_op3 n).
 Let extend3 := GenBase.extend  (WW (W0: w3)).
 Let nmake_op4 := nmake_op _ w4_op.
 Let eval4n n := znz_to_Z  (nmake_op4 n).
 Let extend4 := GenBase.extend  (WW (W0: w4)).
 Let nmake_op5 := nmake_op _ w5_op.
 Let eval5n n := znz_to_Z  (nmake_op5 n).
 Let extend5 := GenBase.extend  (WW (W0: w5)).
 Let nmake_op6 := nmake_op _ w6_op.
 Let eval6n n := znz_to_Z  (nmake_op6 n).
 Let extend6 := GenBase.extend  (WW (W0: w6)).

 Theorem digits_gend:forall n ww (w_op: znz_op ww), 
    znz_digits (nmake_op _ w_op n) = 
    GenBase.gen_digits (znz_digits w_op) n.
 Proof. intros n; elim n; auto; clear n.
 intros n Hrec ww ww_op; simpl GenBase.gen_digits.
 rewrite <- Hrec; auto.
 Qed.

 Theorem nmake_gen: forall n ww (w_op: znz_op ww), 
    znz_to_Z (nmake_op _ w_op n) =
    @GenBase.gen_to_Z _ (znz_digits w_op) (znz_to_Z w_op) n.
 Proof. intros n; elim n; auto; clear n.
 intros n Hrec ww ww_op; simpl GenBase.gen_to_Z; unfold zn2z_to_Z.
 rewrite <- Hrec; auto.
 unfold GenBase.gen_wB; rewrite <- digits_gend; auto.
 Qed.

 Theorem digits_nmake:forall n ww (w_op: znz_op ww), 
    znz_digits (nmake_op _ w_op (S n)) = 
    xO (znz_digits (nmake_op _ w_op n)).
 Proof.
 auto.
 Qed.

 Theorem znz_nmake_op: forall ww ww_op n xh xl,
  znz_to_Z (nmake_op ww ww_op (S n)) (WW xh xl) =
   znz_to_Z (nmake_op ww ww_op n) xh *
    base (znz_digits (nmake_op ww ww_op n)) +
   znz_to_Z (nmake_op ww ww_op n) xl.
 Proof.
 auto.
 Qed.

 Theorem make_op_S: forall n,
   make_op (S n) = mk_zn2z_op_karatsuba (make_op n).
 intro n.
 do 2 rewrite make_op_omake.
 pattern n; apply lt_wf_ind; clear n.
 intros n; case n; clear n.
   intros _; unfold omake_op, make_op_aux, w8_op; apply refl_equal.
 intros n; case n; clear n.
   intros _; unfold omake_op, make_op_aux, w9_op; apply refl_equal.
 intros n; case n; clear n.
   intros _; unfold omake_op, make_op_aux, w9_op, w8_op; apply refl_equal.
 intros n Hrec.
   change (omake_op (S (S (S (S n))))) with
          (mk_zn2z_op_karatsuba (mk_zn2z_op_karatsuba (mk_zn2z_op_karatsuba (omake_op (S n))))).
   change (omake_op (S (S (S n)))) with
         (mk_zn2z_op_karatsuba (mk_zn2z_op_karatsuba (mk_zn2z_op_karatsuba (omake_op n)))).
   rewrite Hrec; auto with arith.
 Qed.
 
 Let znz_to_Z_1: forall x y,
   znz_to_Z w1_op (WW x y) = 
    znz_to_Z w0_op x * base (znz_digits w0_op) + znz_to_Z w0_op y.
 Proof.
 auto.
 Qed. 

 Let znz_to_Z_2: forall x y,
   znz_to_Z w2_op (WW x y) = 
    znz_to_Z w1_op x * base (znz_digits w1_op) + znz_to_Z w1_op y.
 Proof.
 auto.
 Qed. 

 Let znz_to_Z_3: forall x y,
   znz_to_Z w3_op (WW x y) = 
    znz_to_Z w2_op x * base (znz_digits w2_op) + znz_to_Z w2_op y.
 Proof.
 auto.
 Qed. 

 Let znz_to_Z_4: forall x y,
   znz_to_Z w4_op (WW x y) = 
    znz_to_Z w3_op x * base (znz_digits w3_op) + znz_to_Z w3_op y.
 Proof.
 auto.
 Qed. 

 Let znz_to_Z_5: forall x y,
   znz_to_Z w5_op (WW x y) = 
    znz_to_Z w4_op x * base (znz_digits w4_op) + znz_to_Z w4_op y.
 Proof.
 auto.
 Qed. 

 Let znz_to_Z_6: forall x y,
   znz_to_Z w6_op (WW x y) = 
    znz_to_Z w5_op x * base (znz_digits w5_op) + znz_to_Z w5_op y.
 Proof.
 auto.
 Qed. 

 Let znz_to_Z_7: forall x y,
   znz_to_Z w7_op (WW x y) = 
    znz_to_Z w6_op x * base (znz_digits w6_op) + znz_to_Z w6_op y.
 Proof.
 auto.
 Qed. 

 Let znz_to_Z_8: forall x y,
   znz_to_Z w8_op (WW x y) = 
    znz_to_Z w7_op x * base (znz_digits w7_op) + znz_to_Z w7_op y.
 Proof.
 auto.
 Qed. 

 Let znz_to_Z_n: forall n x y,
   znz_to_Z (make_op (S n)) (WW x y) = 
    znz_to_Z (make_op n) x * base (znz_digits (make_op n)) + znz_to_Z (make_op n) y.
 Proof.
 intros n x y; rewrite make_op_S; auto.
 Qed. 

 Let w0_spec: znz_spec w0_op := W0.w_spec.
 Let w1_spec: znz_spec w1_op := mk_znz2_spec w0_spec.
 Let w2_spec: znz_spec w2_op := mk_znz2_spec w1_spec.
 Let w3_spec: znz_spec w3_op := mk_znz2_spec w2_spec.
 Let w4_spec : znz_spec w4_op := mk_znz2_karatsuba_spec w3_spec.
 Let w5_spec : znz_spec w5_op := mk_znz2_karatsuba_spec w4_spec.
 Let w6_spec : znz_spec w6_op := mk_znz2_karatsuba_spec w5_spec.
 Let w7_spec : znz_spec w7_op := mk_znz2_karatsuba_spec w6_spec.
 Let w8_spec : znz_spec w8_op := mk_znz2_karatsuba_spec w7_spec.
 Let w9_spec : znz_spec w9_op := mk_znz2_karatsuba_spec w8_spec.

 Let wn_spec: forall n, znz_spec (make_op n).
  intros n; elim n; clear n.
    exact w7_spec.
  intros n Hrec; rewrite make_op_S.
  exact (mk_znz2_karatsuba_spec Hrec).
 Qed.
 
 Definition w0_eq0 := w0_op.(znz_eq0).
 Let spec_w0_eq0: forall x, if w0_eq0 x then [N0 x] = 0 else True.
 intros x; unfold w0_eq0, to_Z; generalize (spec_eq0 w0_spec x);
    case znz_eq0; auto.
 Qed.

 Definition w1_eq0 := w1_op.(znz_eq0).
 Let spec_w1_eq0: forall x, if w1_eq0 x then [N1 x] = 0 else True.
 intros x; unfold w1_eq0, to_Z; generalize (spec_eq0 w1_spec x);
    case znz_eq0; auto.
 Qed.

 Definition w2_eq0 := w2_op.(znz_eq0).
 Let spec_w2_eq0: forall x, if w2_eq0 x then [N2 x] = 0 else True.
 intros x; unfold w2_eq0, to_Z; generalize (spec_eq0 w2_spec x);
    case znz_eq0; auto.
 Qed.

 Definition w3_eq0 := w3_op.(znz_eq0).
 Let spec_w3_eq0: forall x, if w3_eq0 x then [N3 x] = 0 else True.
 intros x; unfold w3_eq0, to_Z; generalize (spec_eq0 w3_spec x);
    case znz_eq0; auto.
 Qed.

 Definition w4_eq0 := w4_op.(znz_eq0).
 Let spec_w4_eq0: forall x, if w4_eq0 x then [N4 x] = 0 else True.
 intros x; unfold w4_eq0, to_Z; generalize (spec_eq0 w4_spec x);
    case znz_eq0; auto.
 Qed.

 Definition w5_eq0 := w5_op.(znz_eq0).
 Let spec_w5_eq0: forall x, if w5_eq0 x then [N5 x] = 0 else True.
 intros x; unfold w5_eq0, to_Z; generalize (spec_eq0 w5_spec x);
    case znz_eq0; auto.
 Qed.

 Definition w6_eq0 := w6_op.(znz_eq0).
 Let spec_w6_eq0: forall x, if w6_eq0 x then [N6 x] = 0 else True.
 intros x; unfold w6_eq0, to_Z; generalize (spec_eq0 w6_spec x);
    case znz_eq0; auto.
 Qed.


 Theorem digits_w0:  znz_digits w0_op = znz_digits (nmake_op _ w0_op 0).
 auto.
 Qed.

 Let spec_gen_eval0n: forall n, eval0n n = GenBase.gen_to_Z (znz_digits w0_op) (znz_to_Z w0_op) n.
  intros n; exact (nmake_gen n w0 w0_op).
 Qed.

 Theorem digits_w1:  znz_digits w1_op = znz_digits (nmake_op _ w0_op 1).
 rewrite digits_nmake; rewrite <- digits_w0; auto.
 Qed.

 Let spec_gen_eval1n: forall n, eval1n n = GenBase.gen_to_Z (znz_digits w1_op) (znz_to_Z w1_op) n.
  intros n; exact (nmake_gen n w1 w1_op).
 Qed.

 Theorem digits_w2:  znz_digits w2_op = znz_digits (nmake_op _ w0_op 2).
 rewrite digits_nmake; rewrite <- digits_w1; auto.
 Qed.

 Let spec_gen_eval2n: forall n, eval2n n = GenBase.gen_to_Z (znz_digits w2_op) (znz_to_Z w2_op) n.
  intros n; exact (nmake_gen n w2 w2_op).
 Qed.

 Theorem digits_w3:  znz_digits w3_op = znz_digits (nmake_op _ w0_op 3).
 rewrite digits_nmake; rewrite <- digits_w2; auto.
 Qed.

 Let spec_gen_eval3n: forall n, eval3n n = GenBase.gen_to_Z (znz_digits w3_op) (znz_to_Z w3_op) n.
  intros n; exact (nmake_gen n w3 w3_op).
 Qed.

 Theorem digits_w4:  znz_digits w4_op = znz_digits (nmake_op _ w0_op 4).
 rewrite digits_nmake; rewrite <- digits_w3; auto.
 Qed.

 Let spec_gen_eval4n: forall n, eval4n n = GenBase.gen_to_Z (znz_digits w4_op) (znz_to_Z w4_op) n.
  intros n; exact (nmake_gen n w4 w4_op).
 Qed.

 Theorem digits_w5:  znz_digits w5_op = znz_digits (nmake_op _ w0_op 5).
 rewrite digits_nmake; rewrite <- digits_w4; auto.
 Qed.

 Let spec_gen_eval5n: forall n, eval5n n = GenBase.gen_to_Z (znz_digits w5_op) (znz_to_Z w5_op) n.
  intros n; exact (nmake_gen n w5 w5_op).
 Qed.

 Theorem digits_w6:  znz_digits w6_op = znz_digits (nmake_op _ w0_op 6).
 rewrite digits_nmake; rewrite <- digits_w5; auto.
 Qed.

 Let spec_gen_eval6n: forall n, eval6n n = GenBase.gen_to_Z (znz_digits w6_op) (znz_to_Z w6_op) n.
  intros n; exact (nmake_gen n w6 w6_op).
 Qed.

 Theorem digits_w0n0: znz_digits w0_op = znz_digits (nmake_op _ w0_op 0).
 auto.
 Qed.

 Let spec_eval0n0: forall x, [N0 x] = eval0n 0 x.
 intros x; rewrite spec_gen_eval0n; unfold GenBase.gen_to_Z, to_Z; auto.
 Qed.
 Let spec_extend0n1: forall x, [N0 x] = [N1 (extend0 0 x)].
 intros x; change (extend0 0 x) with (WW (znz_0 w0_op) x).
 unfold to_Z; rewrite znz_to_Z_1.
 rewrite (spec_0 w0_spec); auto.
 Qed.

 Theorem digits_w0n1: znz_digits w1_op = znz_digits (nmake_op _ w0_op 1).
 apply trans_equal with (xO (znz_digits w0_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w0n0.
 auto.
 Qed.

 Let spec_eval0n1: forall x, [N1 x] = eval0n 1 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_1.
 rewrite digits_w0n0.
 generalize (spec_eval0n0); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval0n, nmake_op0.
 rewrite (znz_nmake_op _ w0_op 0); auto.
 Qed.
 Let spec_extend0n2: forall x, [N0 x] = [N2 (extend0 1 x)].
 intros x; change (extend0 1 x) with (WW (znz_0 w1_op) (extend0 0 x)).
 unfold to_Z; rewrite znz_to_Z_2.
 rewrite (spec_0 w1_spec).
 generalize (spec_extend0n1 x); unfold to_Z.
 intros HH; rewrite <- HH; auto.
 Qed.

 Theorem digits_w0n2: znz_digits w2_op = znz_digits (nmake_op _ w0_op 2).
 apply trans_equal with (xO (znz_digits w1_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w0n1.
 auto.
 Qed.

 Let spec_eval0n2: forall x, [N2 x] = eval0n 2 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_2.
 rewrite digits_w0n1.
 generalize (spec_eval0n1); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval0n, nmake_op0.
 rewrite (znz_nmake_op _ w0_op 1); auto.
 Qed.
 Let spec_extend0n3: forall x, [N0 x] = [N3 (extend0 2 x)].
 intros x; change (extend0 2 x) with (WW (znz_0 w2_op) (extend0 1 x)).
 unfold to_Z; rewrite znz_to_Z_3.
 rewrite (spec_0 w2_spec).
 generalize (spec_extend0n2 x); unfold to_Z.
 intros HH; rewrite <- HH; auto.
 Qed.

 Theorem digits_w0n3: znz_digits w3_op = znz_digits (nmake_op _ w0_op 3).
 apply trans_equal with (xO (znz_digits w2_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w0n2.
 auto.
 Qed.

 Let spec_eval0n3: forall x, [N3 x] = eval0n 3 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_3.
 rewrite digits_w0n2.
 generalize (spec_eval0n2); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval0n, nmake_op0.
 rewrite (znz_nmake_op _ w0_op 2); auto.
 Qed.
 Let spec_extend0n4: forall x, [N0 x] = [N4 (extend0 3 x)].
 intros x; change (extend0 3 x) with (WW (znz_0 w3_op) (extend0 2 x)).
 unfold to_Z; rewrite znz_to_Z_4.
 rewrite (spec_0 w3_spec).
 generalize (spec_extend0n3 x); unfold to_Z.
 intros HH; rewrite <- HH; auto.
 Qed.

 Theorem digits_w0n4: znz_digits w4_op = znz_digits (nmake_op _ w0_op 4).
 apply trans_equal with (xO (znz_digits w3_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w0n3.
 auto.
 Qed.

 Let spec_eval0n4: forall x, [N4 x] = eval0n 4 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_4.
 rewrite digits_w0n3.
 generalize (spec_eval0n3); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval0n, nmake_op0.
 rewrite (znz_nmake_op _ w0_op 3); auto.
 Qed.
 Let spec_extend0n5: forall x, [N0 x] = [N5 (extend0 4 x)].
 intros x; change (extend0 4 x) with (WW (znz_0 w4_op) (extend0 3 x)).
 unfold to_Z; rewrite znz_to_Z_5.
 rewrite (spec_0 w4_spec).
 generalize (spec_extend0n4 x); unfold to_Z.
 intros HH; rewrite <- HH; auto.
 Qed.

 Theorem digits_w0n5: znz_digits w5_op = znz_digits (nmake_op _ w0_op 5).
 apply trans_equal with (xO (znz_digits w4_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w0n4.
 auto.
 Qed.

 Let spec_eval0n5: forall x, [N5 x] = eval0n 5 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_5.
 rewrite digits_w0n4.
 generalize (spec_eval0n4); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval0n, nmake_op0.
 rewrite (znz_nmake_op _ w0_op 4); auto.
 Qed.
 Let spec_extend0n6: forall x, [N0 x] = [N6 (extend0 5 x)].
 intros x; change (extend0 5 x) with (WW (znz_0 w5_op) (extend0 4 x)).
 unfold to_Z; rewrite znz_to_Z_6.
 rewrite (spec_0 w5_spec).
 generalize (spec_extend0n5 x); unfold to_Z.
 intros HH; rewrite <- HH; auto.
 Qed.

 Theorem digits_w0n6: znz_digits w6_op = znz_digits (nmake_op _ w0_op 6).
 apply trans_equal with (xO (znz_digits w5_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w0n5.
 auto.
 Qed.

 Let spec_eval0n6: forall x, [N6 x] = eval0n 6 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_6.
 rewrite digits_w0n5.
 generalize (spec_eval0n5); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval0n, nmake_op0.
 rewrite (znz_nmake_op _ w0_op 5); auto.
 Qed.
 Theorem digits_w0n7: znz_digits w7_op = znz_digits (nmake_op _ w0_op 7).
 apply trans_equal with (xO (znz_digits w6_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w0n6.
 auto.
 Qed.

 Let spec_eval0n7: forall x, [Nn 0  x] = eval0n 7 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_7.
 rewrite digits_w0n6.
 generalize (spec_eval0n6); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval0n, nmake_op0.
 rewrite (znz_nmake_op _ w0_op 6); auto.
 Qed.

 Let spec_eval0n8: forall x, [Nn 1  x] = eval0n 8 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_8.
 rewrite digits_w0n7.
 generalize (spec_eval0n7); unfold to_Z; change (make_op 0) with (w7_op); intros HH; repeat rewrite HH.
 unfold eval0n, nmake_op0.
 rewrite (znz_nmake_op _ w0_op 7); auto.
 Qed.

 Theorem digits_w1n0: znz_digits w1_op = znz_digits (nmake_op _ w1_op 0).
 apply trans_equal with (xO (znz_digits w0_op)).
  auto.
  unfold nmake_op; auto.
 Qed.

 Let spec_eval1n0: forall x, [N1 x] = eval1n 0 x.
 intros x; rewrite spec_gen_eval1n; unfold GenBase.gen_to_Z, to_Z; auto.
 Qed.
 Let spec_extend1n2: forall x, [N1 x] = [N2 (extend1 0 x)].
 intros x; change (extend1 0 x) with (WW (znz_0 w1_op) x).
 unfold to_Z; rewrite znz_to_Z_2.
 rewrite (spec_0 w1_spec); auto.
 Qed.

 Theorem digits_w1n1: znz_digits w2_op = znz_digits (nmake_op _ w1_op 1).
 apply trans_equal with (xO (znz_digits w1_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w1n0.
 auto.
 Qed.

 Let spec_eval1n1: forall x, [N2 x] = eval1n 1 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_2.
 rewrite digits_w1n0.
 generalize (spec_eval1n0); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval1n, nmake_op1.
 rewrite (znz_nmake_op _ w1_op 0); auto.
 Qed.
 Let spec_extend1n3: forall x, [N1 x] = [N3 (extend1 1 x)].
 intros x; change (extend1 1 x) with (WW (znz_0 w2_op) (extend1 0 x)).
 unfold to_Z; rewrite znz_to_Z_3.
 rewrite (spec_0 w2_spec).
 generalize (spec_extend1n2 x); unfold to_Z.
 intros HH; rewrite <- HH; auto.
 Qed.

 Theorem digits_w1n2: znz_digits w3_op = znz_digits (nmake_op _ w1_op 2).
 apply trans_equal with (xO (znz_digits w2_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w1n1.
 auto.
 Qed.

 Let spec_eval1n2: forall x, [N3 x] = eval1n 2 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_3.
 rewrite digits_w1n1.
 generalize (spec_eval1n1); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval1n, nmake_op1.
 rewrite (znz_nmake_op _ w1_op 1); auto.
 Qed.
 Let spec_extend1n4: forall x, [N1 x] = [N4 (extend1 2 x)].
 intros x; change (extend1 2 x) with (WW (znz_0 w3_op) (extend1 1 x)).
 unfold to_Z; rewrite znz_to_Z_4.
 rewrite (spec_0 w3_spec).
 generalize (spec_extend1n3 x); unfold to_Z.
 intros HH; rewrite <- HH; auto.
 Qed.

 Theorem digits_w1n3: znz_digits w4_op = znz_digits (nmake_op _ w1_op 3).
 apply trans_equal with (xO (znz_digits w3_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w1n2.
 auto.
 Qed.

 Let spec_eval1n3: forall x, [N4 x] = eval1n 3 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_4.
 rewrite digits_w1n2.
 generalize (spec_eval1n2); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval1n, nmake_op1.
 rewrite (znz_nmake_op _ w1_op 2); auto.
 Qed.
 Let spec_extend1n5: forall x, [N1 x] = [N5 (extend1 3 x)].
 intros x; change (extend1 3 x) with (WW (znz_0 w4_op) (extend1 2 x)).
 unfold to_Z; rewrite znz_to_Z_5.
 rewrite (spec_0 w4_spec).
 generalize (spec_extend1n4 x); unfold to_Z.
 intros HH; rewrite <- HH; auto.
 Qed.

 Theorem digits_w1n4: znz_digits w5_op = znz_digits (nmake_op _ w1_op 4).
 apply trans_equal with (xO (znz_digits w4_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w1n3.
 auto.
 Qed.

 Let spec_eval1n4: forall x, [N5 x] = eval1n 4 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_5.
 rewrite digits_w1n3.
 generalize (spec_eval1n3); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval1n, nmake_op1.
 rewrite (znz_nmake_op _ w1_op 3); auto.
 Qed.
 Let spec_extend1n6: forall x, [N1 x] = [N6 (extend1 4 x)].
 intros x; change (extend1 4 x) with (WW (znz_0 w5_op) (extend1 3 x)).
 unfold to_Z; rewrite znz_to_Z_6.
 rewrite (spec_0 w5_spec).
 generalize (spec_extend1n5 x); unfold to_Z.
 intros HH; rewrite <- HH; auto.
 Qed.

 Theorem digits_w1n5: znz_digits w6_op = znz_digits (nmake_op _ w1_op 5).
 apply trans_equal with (xO (znz_digits w5_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w1n4.
 auto.
 Qed.

 Let spec_eval1n5: forall x, [N6 x] = eval1n 5 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_6.
 rewrite digits_w1n4.
 generalize (spec_eval1n4); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval1n, nmake_op1.
 rewrite (znz_nmake_op _ w1_op 4); auto.
 Qed.
 Theorem digits_w1n6: znz_digits w7_op = znz_digits (nmake_op _ w1_op 6).
 apply trans_equal with (xO (znz_digits w6_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w1n5.
 auto.
 Qed.

 Let spec_eval1n6: forall x, [Nn 0  x] = eval1n 6 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_7.
 rewrite digits_w1n5.
 generalize (spec_eval1n5); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval1n, nmake_op1.
 rewrite (znz_nmake_op _ w1_op 5); auto.
 Qed.

 Let spec_eval1n7: forall x, [Nn 1  x] = eval1n 7 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_8.
 rewrite digits_w1n6.
 generalize (spec_eval1n6); unfold to_Z; change (make_op 0) with (w7_op); intros HH; repeat rewrite HH.
 unfold eval1n, nmake_op1.
 rewrite (znz_nmake_op _ w1_op 6); auto.
 Qed.

 Theorem digits_w2n0: znz_digits w2_op = znz_digits (nmake_op _ w2_op 0).
 apply trans_equal with (xO (znz_digits w1_op)).
  auto.
  unfold nmake_op; auto.
 Qed.

 Let spec_eval2n0: forall x, [N2 x] = eval2n 0 x.
 intros x; rewrite spec_gen_eval2n; unfold GenBase.gen_to_Z, to_Z; auto.
 Qed.
 Let spec_extend2n3: forall x, [N2 x] = [N3 (extend2 0 x)].
 intros x; change (extend2 0 x) with (WW (znz_0 w2_op) x).
 unfold to_Z; rewrite znz_to_Z_3.
 rewrite (spec_0 w2_spec); auto.
 Qed.

 Theorem digits_w2n1: znz_digits w3_op = znz_digits (nmake_op _ w2_op 1).
 apply trans_equal with (xO (znz_digits w2_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w2n0.
 auto.
 Qed.

 Let spec_eval2n1: forall x, [N3 x] = eval2n 1 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_3.
 rewrite digits_w2n0.
 generalize (spec_eval2n0); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval2n, nmake_op2.
 rewrite (znz_nmake_op _ w2_op 0); auto.
 Qed.
 Let spec_extend2n4: forall x, [N2 x] = [N4 (extend2 1 x)].
 intros x; change (extend2 1 x) with (WW (znz_0 w3_op) (extend2 0 x)).
 unfold to_Z; rewrite znz_to_Z_4.
 rewrite (spec_0 w3_spec).
 generalize (spec_extend2n3 x); unfold to_Z.
 intros HH; rewrite <- HH; auto.
 Qed.

 Theorem digits_w2n2: znz_digits w4_op = znz_digits (nmake_op _ w2_op 2).
 apply trans_equal with (xO (znz_digits w3_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w2n1.
 auto.
 Qed.

 Let spec_eval2n2: forall x, [N4 x] = eval2n 2 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_4.
 rewrite digits_w2n1.
 generalize (spec_eval2n1); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval2n, nmake_op2.
 rewrite (znz_nmake_op _ w2_op 1); auto.
 Qed.
 Let spec_extend2n5: forall x, [N2 x] = [N5 (extend2 2 x)].
 intros x; change (extend2 2 x) with (WW (znz_0 w4_op) (extend2 1 x)).
 unfold to_Z; rewrite znz_to_Z_5.
 rewrite (spec_0 w4_spec).
 generalize (spec_extend2n4 x); unfold to_Z.
 intros HH; rewrite <- HH; auto.
 Qed.

 Theorem digits_w2n3: znz_digits w5_op = znz_digits (nmake_op _ w2_op 3).
 apply trans_equal with (xO (znz_digits w4_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w2n2.
 auto.
 Qed.

 Let spec_eval2n3: forall x, [N5 x] = eval2n 3 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_5.
 rewrite digits_w2n2.
 generalize (spec_eval2n2); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval2n, nmake_op2.
 rewrite (znz_nmake_op _ w2_op 2); auto.
 Qed.
 Let spec_extend2n6: forall x, [N2 x] = [N6 (extend2 3 x)].
 intros x; change (extend2 3 x) with (WW (znz_0 w5_op) (extend2 2 x)).
 unfold to_Z; rewrite znz_to_Z_6.
 rewrite (spec_0 w5_spec).
 generalize (spec_extend2n5 x); unfold to_Z.
 intros HH; rewrite <- HH; auto.
 Qed.

 Theorem digits_w2n4: znz_digits w6_op = znz_digits (nmake_op _ w2_op 4).
 apply trans_equal with (xO (znz_digits w5_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w2n3.
 auto.
 Qed.

 Let spec_eval2n4: forall x, [N6 x] = eval2n 4 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_6.
 rewrite digits_w2n3.
 generalize (spec_eval2n3); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval2n, nmake_op2.
 rewrite (znz_nmake_op _ w2_op 3); auto.
 Qed.
 Theorem digits_w2n5: znz_digits w7_op = znz_digits (nmake_op _ w2_op 5).
 apply trans_equal with (xO (znz_digits w6_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w2n4.
 auto.
 Qed.

 Let spec_eval2n5: forall x, [Nn 0  x] = eval2n 5 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_7.
 rewrite digits_w2n4.
 generalize (spec_eval2n4); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval2n, nmake_op2.
 rewrite (znz_nmake_op _ w2_op 4); auto.
 Qed.

 Let spec_eval2n6: forall x, [Nn 1  x] = eval2n 6 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_8.
 rewrite digits_w2n5.
 generalize (spec_eval2n5); unfold to_Z; change (make_op 0) with (w7_op); intros HH; repeat rewrite HH.
 unfold eval2n, nmake_op2.
 rewrite (znz_nmake_op _ w2_op 5); auto.
 Qed.

 Theorem digits_w3n0: znz_digits w3_op = znz_digits (nmake_op _ w3_op 0).
 apply trans_equal with (xO (znz_digits w2_op)).
  auto.
  unfold nmake_op; auto.
 Qed.

 Let spec_eval3n0: forall x, [N3 x] = eval3n 0 x.
 intros x; rewrite spec_gen_eval3n; unfold GenBase.gen_to_Z, to_Z; auto.
 Qed.
 Let spec_extend3n4: forall x, [N3 x] = [N4 (extend3 0 x)].
 intros x; change (extend3 0 x) with (WW (znz_0 w3_op) x).
 unfold to_Z; rewrite znz_to_Z_4.
 rewrite (spec_0 w3_spec); auto.
 Qed.

 Theorem digits_w3n1: znz_digits w4_op = znz_digits (nmake_op _ w3_op 1).
 apply trans_equal with (xO (znz_digits w3_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w3n0.
 auto.
 Qed.

 Let spec_eval3n1: forall x, [N4 x] = eval3n 1 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_4.
 rewrite digits_w3n0.
 generalize (spec_eval3n0); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval3n, nmake_op3.
 rewrite (znz_nmake_op _ w3_op 0); auto.
 Qed.
 Let spec_extend3n5: forall x, [N3 x] = [N5 (extend3 1 x)].
 intros x; change (extend3 1 x) with (WW (znz_0 w4_op) (extend3 0 x)).
 unfold to_Z; rewrite znz_to_Z_5.
 rewrite (spec_0 w4_spec).
 generalize (spec_extend3n4 x); unfold to_Z.
 intros HH; rewrite <- HH; auto.
 Qed.

 Theorem digits_w3n2: znz_digits w5_op = znz_digits (nmake_op _ w3_op 2).
 apply trans_equal with (xO (znz_digits w4_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w3n1.
 auto.
 Qed.

 Let spec_eval3n2: forall x, [N5 x] = eval3n 2 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_5.
 rewrite digits_w3n1.
 generalize (spec_eval3n1); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval3n, nmake_op3.
 rewrite (znz_nmake_op _ w3_op 1); auto.
 Qed.
 Let spec_extend3n6: forall x, [N3 x] = [N6 (extend3 2 x)].
 intros x; change (extend3 2 x) with (WW (znz_0 w5_op) (extend3 1 x)).
 unfold to_Z; rewrite znz_to_Z_6.
 rewrite (spec_0 w5_spec).
 generalize (spec_extend3n5 x); unfold to_Z.
 intros HH; rewrite <- HH; auto.
 Qed.

 Theorem digits_w3n3: znz_digits w6_op = znz_digits (nmake_op _ w3_op 3).
 apply trans_equal with (xO (znz_digits w5_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w3n2.
 auto.
 Qed.

 Let spec_eval3n3: forall x, [N6 x] = eval3n 3 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_6.
 rewrite digits_w3n2.
 generalize (spec_eval3n2); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval3n, nmake_op3.
 rewrite (znz_nmake_op _ w3_op 2); auto.
 Qed.
 Theorem digits_w3n4: znz_digits w7_op = znz_digits (nmake_op _ w3_op 4).
 apply trans_equal with (xO (znz_digits w6_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w3n3.
 auto.
 Qed.

 Let spec_eval3n4: forall x, [Nn 0  x] = eval3n 4 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_7.
 rewrite digits_w3n3.
 generalize (spec_eval3n3); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval3n, nmake_op3.
 rewrite (znz_nmake_op _ w3_op 3); auto.
 Qed.

 Let spec_eval3n5: forall x, [Nn 1  x] = eval3n 5 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_8.
 rewrite digits_w3n4.
 generalize (spec_eval3n4); unfold to_Z; change (make_op 0) with (w7_op); intros HH; repeat rewrite HH.
 unfold eval3n, nmake_op3.
 rewrite (znz_nmake_op _ w3_op 4); auto.
 Qed.

 Theorem digits_w4n0: znz_digits w4_op = znz_digits (nmake_op _ w4_op 0).
 apply trans_equal with (xO (znz_digits w3_op)).
  auto.
  unfold nmake_op; auto.
 Qed.

 Let spec_eval4n0: forall x, [N4 x] = eval4n 0 x.
 intros x; rewrite spec_gen_eval4n; unfold GenBase.gen_to_Z, to_Z; auto.
 Qed.
 Let spec_extend4n5: forall x, [N4 x] = [N5 (extend4 0 x)].
 intros x; change (extend4 0 x) with (WW (znz_0 w4_op) x).
 unfold to_Z; rewrite znz_to_Z_5.
 rewrite (spec_0 w4_spec); auto.
 Qed.

 Theorem digits_w4n1: znz_digits w5_op = znz_digits (nmake_op _ w4_op 1).
 apply trans_equal with (xO (znz_digits w4_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w4n0.
 auto.
 Qed.

 Let spec_eval4n1: forall x, [N5 x] = eval4n 1 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_5.
 rewrite digits_w4n0.
 generalize (spec_eval4n0); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval4n, nmake_op4.
 rewrite (znz_nmake_op _ w4_op 0); auto.
 Qed.
 Let spec_extend4n6: forall x, [N4 x] = [N6 (extend4 1 x)].
 intros x; change (extend4 1 x) with (WW (znz_0 w5_op) (extend4 0 x)).
 unfold to_Z; rewrite znz_to_Z_6.
 rewrite (spec_0 w5_spec).
 generalize (spec_extend4n5 x); unfold to_Z.
 intros HH; rewrite <- HH; auto.
 Qed.

 Theorem digits_w4n2: znz_digits w6_op = znz_digits (nmake_op _ w4_op 2).
 apply trans_equal with (xO (znz_digits w5_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w4n1.
 auto.
 Qed.

 Let spec_eval4n2: forall x, [N6 x] = eval4n 2 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_6.
 rewrite digits_w4n1.
 generalize (spec_eval4n1); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval4n, nmake_op4.
 rewrite (znz_nmake_op _ w4_op 1); auto.
 Qed.
 Theorem digits_w4n3: znz_digits w7_op = znz_digits (nmake_op _ w4_op 3).
 apply trans_equal with (xO (znz_digits w6_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w4n2.
 auto.
 Qed.

 Let spec_eval4n3: forall x, [Nn 0  x] = eval4n 3 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_7.
 rewrite digits_w4n2.
 generalize (spec_eval4n2); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval4n, nmake_op4.
 rewrite (znz_nmake_op _ w4_op 2); auto.
 Qed.

 Let spec_eval4n4: forall x, [Nn 1  x] = eval4n 4 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_8.
 rewrite digits_w4n3.
 generalize (spec_eval4n3); unfold to_Z; change (make_op 0) with (w7_op); intros HH; repeat rewrite HH.
 unfold eval4n, nmake_op4.
 rewrite (znz_nmake_op _ w4_op 3); auto.
 Qed.

 Theorem digits_w5n0: znz_digits w5_op = znz_digits (nmake_op _ w5_op 0).
 apply trans_equal with (xO (znz_digits w4_op)).
  auto.
  unfold nmake_op; auto.
 Qed.

 Let spec_eval5n0: forall x, [N5 x] = eval5n 0 x.
 intros x; rewrite spec_gen_eval5n; unfold GenBase.gen_to_Z, to_Z; auto.
 Qed.
 Let spec_extend5n6: forall x, [N5 x] = [N6 (extend5 0 x)].
 intros x; change (extend5 0 x) with (WW (znz_0 w5_op) x).
 unfold to_Z; rewrite znz_to_Z_6.
 rewrite (spec_0 w5_spec); auto.
 Qed.

 Theorem digits_w5n1: znz_digits w6_op = znz_digits (nmake_op _ w5_op 1).
 apply trans_equal with (xO (znz_digits w5_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w5n0.
 auto.
 Qed.

 Let spec_eval5n1: forall x, [N6 x] = eval5n 1 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_6.
 rewrite digits_w5n0.
 generalize (spec_eval5n0); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval5n, nmake_op5.
 rewrite (znz_nmake_op _ w5_op 0); auto.
 Qed.
 Theorem digits_w5n2: znz_digits w7_op = znz_digits (nmake_op _ w5_op 2).
 apply trans_equal with (xO (znz_digits w6_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w5n1.
 auto.
 Qed.

 Let spec_eval5n2: forall x, [Nn 0  x] = eval5n 2 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_7.
 rewrite digits_w5n1.
 generalize (spec_eval5n1); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval5n, nmake_op5.
 rewrite (znz_nmake_op _ w5_op 1); auto.
 Qed.

 Let spec_eval5n3: forall x, [Nn 1  x] = eval5n 3 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_8.
 rewrite digits_w5n2.
 generalize (spec_eval5n2); unfold to_Z; change (make_op 0) with (w7_op); intros HH; repeat rewrite HH.
 unfold eval5n, nmake_op5.
 rewrite (znz_nmake_op _ w5_op 2); auto.
 Qed.

 Theorem digits_w6n0: znz_digits w6_op = znz_digits (nmake_op _ w6_op 0).
 apply trans_equal with (xO (znz_digits w5_op)).
  auto.
  unfold nmake_op; auto.
 Qed.

 Let spec_eval6n0: forall x, [N6 x] = eval6n 0 x.
 intros x; rewrite spec_gen_eval6n; unfold GenBase.gen_to_Z, to_Z; auto.
 Qed.
 Theorem digits_w6n1: znz_digits w7_op = znz_digits (nmake_op _ w6_op 1).
 apply trans_equal with (xO (znz_digits w6_op)).
  auto.
 rewrite digits_nmake.
 rewrite digits_w6n0.
 auto.
 Qed.

 Let spec_eval6n1: forall x, [Nn 0  x] = eval6n 1 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_7.
 rewrite digits_w6n0.
 generalize (spec_eval6n0); unfold to_Z; intros HH; repeat rewrite HH.
 unfold eval6n, nmake_op6.
 rewrite (znz_nmake_op _ w6_op 0); auto.
 Qed.

 Let spec_eval6n2: forall x, [Nn 1  x] = eval6n 2 x.
 intros x; case x.
   auto.
 intros xh xl; unfold to_Z; rewrite znz_to_Z_8.
 rewrite digits_w6n1.
 generalize (spec_eval6n1); unfold to_Z; change (make_op 0) with (w7_op); intros HH; repeat rewrite HH.
 unfold eval6n, nmake_op6.
 rewrite (znz_nmake_op _ w6_op 1); auto.
 Qed.

 Let digits_w6n: forall n,
   znz_digits (make_op n) = znz_digits (nmake_op _ w6_op (S n)).
 intros n; elim n; clear n.
  change (znz_digits (make_op 0)) with (xO (znz_digits w6_op)).
  rewrite nmake_op_S; apply sym_equal; auto.
  intros  n Hrec.
  replace (znz_digits (make_op (S n))) with (xO (znz_digits (make_op n))).
  rewrite Hrec.
  rewrite nmake_op_S; apply sym_equal; auto.
  rewrite make_op_S; apply sym_equal; auto.
 Qed.

 Let spec_eval6n: forall n x, [Nn n x] = eval6n (S n) x.
 intros n; elim n; clear n.
   exact spec_eval6n1.
 intros n Hrec x; case x; clear x.
  unfold to_Z, eval6n, nmake_op6.
    rewrite make_op_S; rewrite nmake_op_S; auto.
 intros xh xl.
  unfold to_Z in Hrec |- *.
  rewrite znz_to_Z_n.
  rewrite digits_w6n.
  repeat rewrite Hrec.
  unfold eval6n, nmake_op6.
  apply sym_equal; rewrite nmake_op_S; auto.
 Qed.

 Let spec_extend6n: forall n x, [N6 x] = [Nn n (extend6 n x)].
 intros n; elim n; clear n.
   intros x; change (extend6 0 x) with (WW (znz_0 w6_op) x).
   unfold to_Z.
   change (make_op 0) with w7_op.
   rewrite znz_to_Z_7; rewrite (spec_0 w6_spec); auto.
 intros n Hrec x.
   change (extend6 (S n) x) with (WW W0 (extend6 n x)).
   unfold to_Z in Hrec |- *; rewrite znz_to_Z_n; auto.
   rewrite <- Hrec.
  replace (znz_to_Z (make_op n) W0) with 0; auto.
  case n; auto; intros; rewrite make_op_S; auto.
 Qed.

 Theorem spec_pos: forall x, 0 <= [x].
 Proof.
 intros x; case x; clear x.
 intros x; case (spec_to_Z w0_spec x); auto.
 intros x; case (spec_to_Z w1_spec x); auto.
 intros x; case (spec_to_Z w2_spec x); auto.
 intros x; case (spec_to_Z w3_spec x); auto.
 intros x; case (spec_to_Z w4_spec x); auto.
 intros x; case (spec_to_Z w5_spec x); auto.
 intros x; case (spec_to_Z w6_spec x); auto.
 intros n x; case (spec_to_Z (wn_spec n) x); auto.
 Qed.

 Let spec_extendn_0: forall n wx, [Nn n (extend n _ wx)] = [Nn 0 wx].
 intros n; elim n; auto.
 intros n1 Hrec wx; simpl extend; rewrite <- Hrec; auto.
 unfold to_Z.
 case n1; auto; intros n2; repeat rewrite make_op_S; auto.
 Qed.
 Hint Rewrite spec_extendn_0: extr.

 Let spec_extendn0_0: forall n wx, [Nn (S n) (WW W0 wx)] = [Nn n wx].
 Proof.
 intros n x; unfold to_Z.
 rewrite znz_to_Z_n.
 rewrite <- (Zplus_0_l (znz_to_Z (make_op n) x)).
 apply (f_equal2 Zplus); auto.
 case n; auto.
 intros n1; rewrite make_op_S; auto.
 Qed.
 Hint Rewrite spec_extendn_0: extr.

 Let spec_extend_tr: forall m n (w: word _ (S n)),
 [Nn (m + n) (extend_tr w m)] = [Nn n w].
 Proof.
 induction m; auto.
 intros n x; simpl extend_tr.
 simpl plus; rewrite spec_extendn0_0; auto.
 Qed.
 Hint Rewrite spec_extend_tr: extr.

 Let spec_cast_l: forall n m x1,
 [Nn (Max.max n m)
 (castm (diff_r n m) (extend_tr x1 (snd (diff n m))))] =
 [Nn n x1].
 Proof.
 intros n m x1; case (diff_r n m); simpl castm.
 rewrite spec_extend_tr; auto.
 Qed.
 Hint Rewrite spec_cast_l: extr.

 Let spec_cast_r: forall n m x1,
 [Nn (Max.max n m)
  (castm (diff_l n m) (extend_tr x1 (fst (diff n m))))] =
 [Nn m x1].
 Proof.
 intros n m x1; case (diff_l n m); simpl castm.
 rewrite spec_extend_tr; auto.
 Qed.
 Hint Rewrite spec_cast_r: extr.

 Section LevelAndIter.

  Variable res: Set.
  Variable xxx: res.
  Variable P: Z -> Z -> res -> Prop.
  (* Abstraction function for each level *)
  Variable f0: w0 -> w0 -> res.
  Variable f0n: forall n, w0 -> word w0 (S n) -> res.
  Variable fn0: forall n, word w0 (S n) -> w0 -> res.
  Variable Pf0: forall x y, P [N0 x] [N0 y] (f0 x y).
  Variable Pf0n: forall n x y, Z_of_nat n <= 6 -> P [N0 x] (eval0n (S n) y) (f0n n x y).
  Variable Pfn0: forall n x y, Z_of_nat n <= 6 -> P (eval0n (S n) x) [N0 y] (fn0 n x y).

  Variable f1: w1 -> w1 -> res.
  Variable f1n: forall n, w1 -> word w1 (S n) -> res.
  Variable fn1: forall n, word w1 (S n) -> w1 -> res.
  Variable Pf1: forall x y, P [N1 x] [N1 y] (f1 x y).
  Variable Pf1n: forall n x y, Z_of_nat n <= 5 -> P [N1 x] (eval1n (S n) y) (f1n n x y).
  Variable Pfn1: forall n x y, Z_of_nat n <= 5 -> P (eval1n (S n) x) [N1 y] (fn1 n x y).

  Variable f2: w2 -> w2 -> res.
  Variable f2n: forall n, w2 -> word w2 (S n) -> res.
  Variable fn2: forall n, word w2 (S n) -> w2 -> res.
  Variable Pf2: forall x y, P [N2 x] [N2 y] (f2 x y).
  Variable Pf2n: forall n x y, Z_of_nat n <= 4 -> P [N2 x] (eval2n (S n) y) (f2n n x y).
  Variable Pfn2: forall n x y, Z_of_nat n <= 4 -> P (eval2n (S n) x) [N2 y] (fn2 n x y).

  Variable f3: w3 -> w3 -> res.
  Variable f3n: forall n, w3 -> word w3 (S n) -> res.
  Variable fn3: forall n, word w3 (S n) -> w3 -> res.
  Variable Pf3: forall x y, P [N3 x] [N3 y] (f3 x y).
  Variable Pf3n: forall n x y, Z_of_nat n <= 3 -> P [N3 x] (eval3n (S n) y) (f3n n x y).
  Variable Pfn3: forall n x y, Z_of_nat n <= 3 -> P (eval3n (S n) x) [N3 y] (fn3 n x y).

  Variable f4: w4 -> w4 -> res.
  Variable f4n: forall n, w4 -> word w4 (S n) -> res.
  Variable fn4: forall n, word w4 (S n) -> w4 -> res.
  Variable Pf4: forall x y, P [N4 x] [N4 y] (f4 x y).
  Variable Pf4n: forall n x y, Z_of_nat n <= 2 -> P [N4 x] (eval4n (S n) y) (f4n n x y).
  Variable Pfn4: forall n x y, Z_of_nat n <= 2 -> P (eval4n (S n) x) [N4 y] (fn4 n x y).

  Variable f5: w5 -> w5 -> res.
  Variable f5n: forall n, w5 -> word w5 (S n) -> res.
  Variable fn5: forall n, word w5 (S n) -> w5 -> res.
  Variable Pf5: forall x y, P [N5 x] [N5 y] (f5 x y).
  Variable Pf5n: forall n x y, Z_of_nat n <= 1 -> P [N5 x] (eval5n (S n) y) (f5n n x y).
  Variable Pfn5: forall n x y, Z_of_nat n <= 1 -> P (eval5n (S n) x) [N5 y] (fn5 n x y).

  Variable f6: w6 -> w6 -> res.
  Variable f6n: forall n, w6 -> word w6 (S n) -> res.
  Variable fn6: forall n, word w6 (S n) -> w6 -> res.
  Variable Pf6: forall x y, P [N6 x] [N6 y] (f6 x y).
  Variable Pf6n: forall n x y, P [N6 x] (eval6n (S n) y) (f6n n x y).
  Variable Pfn6: forall n x y, P (eval6n (S n) x) [N6 y] (fn6 n x y).

  Variable fnn: forall n, word w6 (S n) -> word w6 (S n) -> res.
  Variable Pfnn: forall n x y, P [Nn n x] [Nn n y] (fnn n x y).
  Variable fnm: forall n m, word w6 (S n) -> word w6 (S m) -> res.
  Variable Pfnm: forall n m x y, P [Nn n x] [Nn m y] (fnm n m x y).

  (* Special zero functions *)
  Variable f0t:  t_ -> res.
  Variable Pf0t: forall x, P 0 [x] (f0t x).
  Variable ft0:  t_ -> res.
  Variable Pft0: forall x, P [x] 0 (ft0 x).

  (* We level the two arguments before applying *)
  (* the functions at each leval                *)
  Definition same_level (x y: t_): res :=
    Eval lazy zeta beta iota delta [extend0 extend1 extend2 extend3 extend4 extend5 extend6 
                                         GenBase.extend GenBase.extend_aux
                                         ] in
  match x, y with
  | N0 wx, N0 wy => f0 wx wy
  | N0 wx, N1 wy => f1 (extend0 0 wx) wy
  | N0 wx, N2 wy => f2 (extend0 1 wx) wy
  | N0 wx, N3 wy => f3 (extend0 2 wx) wy
  | N0 wx, N4 wy => f4 (extend0 3 wx) wy
  | N0 wx, N5 wy => f5 (extend0 4 wx) wy
  | N0 wx, N6 wy => f6 (extend0 5 wx) wy
  | N0 wx, Nn m wy => fnn m (extend6 m (extend0 5 wx)) wy
  | N1 wx, N0 wy => f1 wx (extend0 0 wy)
  | N1 wx, N1 wy => f1 wx wy
  | N1 wx, N2 wy => f2 (extend1 0 wx) wy
  | N1 wx, N3 wy => f3 (extend1 1 wx) wy
  | N1 wx, N4 wy => f4 (extend1 2 wx) wy
  | N1 wx, N5 wy => f5 (extend1 3 wx) wy
  | N1 wx, N6 wy => f6 (extend1 4 wx) wy
  | N1 wx, Nn m wy => fnn m (extend6 m (extend1 4 wx)) wy
  | N2 wx, N0 wy => f2 wx (extend0 1 wy)
  | N2 wx, N1 wy => f2 wx (extend1 0 wy)
  | N2 wx, N2 wy => f2 wx wy
  | N2 wx, N3 wy => f3 (extend2 0 wx) wy
  | N2 wx, N4 wy => f4 (extend2 1 wx) wy
  | N2 wx, N5 wy => f5 (extend2 2 wx) wy
  | N2 wx, N6 wy => f6 (extend2 3 wx) wy
  | N2 wx, Nn m wy => fnn m (extend6 m (extend2 3 wx)) wy
  | N3 wx, N0 wy => f3 wx (extend0 2 wy)
  | N3 wx, N1 wy => f3 wx (extend1 1 wy)
  | N3 wx, N2 wy => f3 wx (extend2 0 wy)
  | N3 wx, N3 wy => f3 wx wy
  | N3 wx, N4 wy => f4 (extend3 0 wx) wy
  | N3 wx, N5 wy => f5 (extend3 1 wx) wy
  | N3 wx, N6 wy => f6 (extend3 2 wx) wy
  | N3 wx, Nn m wy => fnn m (extend6 m (extend3 2 wx)) wy
  | N4 wx, N0 wy => f4 wx (extend0 3 wy)
  | N4 wx, N1 wy => f4 wx (extend1 2 wy)
  | N4 wx, N2 wy => f4 wx (extend2 1 wy)
  | N4 wx, N3 wy => f4 wx (extend3 0 wy)
  | N4 wx, N4 wy => f4 wx wy
  | N4 wx, N5 wy => f5 (extend4 0 wx) wy
  | N4 wx, N6 wy => f6 (extend4 1 wx) wy
  | N4 wx, Nn m wy => fnn m (extend6 m (extend4 1 wx)) wy
  | N5 wx, N0 wy => f5 wx (extend0 4 wy)
  | N5 wx, N1 wy => f5 wx (extend1 3 wy)
  | N5 wx, N2 wy => f5 wx (extend2 2 wy)
  | N5 wx, N3 wy => f5 wx (extend3 1 wy)
  | N5 wx, N4 wy => f5 wx (extend4 0 wy)
  | N5 wx, N5 wy => f5 wx wy
  | N5 wx, N6 wy => f6 (extend5 0 wx) wy
  | N5 wx, Nn m wy => fnn m (extend6 m (extend5 0 wx)) wy
  | N6 wx, N0 wy => f6 wx (extend0 5 wy)
  | N6 wx, N1 wy => f6 wx (extend1 4 wy)
  | N6 wx, N2 wy => f6 wx (extend2 3 wy)
  | N6 wx, N3 wy => f6 wx (extend3 2 wy)
  | N6 wx, N4 wy => f6 wx (extend4 1 wy)
  | N6 wx, N5 wy => f6 wx (extend5 0 wy)
  | N6 wx, N6 wy => f6 wx wy
  | N6 wx, Nn m wy => fnn m (extend6 m wx) wy
  | Nn n wx, N0 wy => fnn n wx (extend6 n (extend0 5 wy))
  | Nn n wx, N1 wy => fnn n wx (extend6 n (extend1 4 wy))
  | Nn n wx, N2 wy => fnn n wx (extend6 n (extend2 3 wy))
  | Nn n wx, N3 wy => fnn n wx (extend6 n (extend3 2 wy))
  | Nn n wx, N4 wy => fnn n wx (extend6 n (extend4 1 wy))
  | Nn n wx, N5 wy => fnn n wx (extend6 n (extend5 0 wy))
  | Nn n wx, N6 wy => fnn n wx (extend6 n wy)
  | Nn n wx, Nn m wy =>
    let mn := Max.max n m in
    let d := diff n m in
     fnn mn
       (castm (diff_r n m) (extend_tr wx (snd d)))
       (castm (diff_l n m) (extend_tr wy (fst d)))
  end.

  Lemma spec_same_level: forall x y, P [x] [y] (same_level x y).
  Proof.
  intros x; case x; clear x; unfold same_level.
    intros x y; case y; clear y.
     intros y; apply Pf0.
     intros y; rewrite spec_extend0n1; apply Pf1.
     intros y; rewrite spec_extend0n2; apply Pf2.
     intros y; rewrite spec_extend0n3; apply Pf3.
     intros y; rewrite spec_extend0n4; apply Pf4.
     intros y; rewrite spec_extend0n5; apply Pf5.
     intros y; rewrite spec_extend0n6; apply Pf6.
     intros m y; rewrite spec_extend0n6; rewrite (spec_extend6n m); apply Pfnn.
    intros x y; case y; clear y.
     intros y; rewrite spec_extend0n1; apply Pf1.
     intros y; apply Pf1.
     intros y; rewrite spec_extend1n2; apply Pf2.
     intros y; rewrite spec_extend1n3; apply Pf3.
     intros y; rewrite spec_extend1n4; apply Pf4.
     intros y; rewrite spec_extend1n5; apply Pf5.
     intros y; rewrite spec_extend1n6; apply Pf6.
     intros m y; rewrite spec_extend1n6; rewrite (spec_extend6n m); apply Pfnn.
    intros x y; case y; clear y.
     intros y; rewrite spec_extend0n2; apply Pf2.
     intros y; rewrite spec_extend1n2; apply Pf2.
     intros y; apply Pf2.
     intros y; rewrite spec_extend2n3; apply Pf3.
     intros y; rewrite spec_extend2n4; apply Pf4.
     intros y; rewrite spec_extend2n5; apply Pf5.
     intros y; rewrite spec_extend2n6; apply Pf6.
     intros m y; rewrite spec_extend2n6; rewrite (spec_extend6n m); apply Pfnn.
    intros x y; case y; clear y.
     intros y; rewrite spec_extend0n3; apply Pf3.
     intros y; rewrite spec_extend1n3; apply Pf3.
     intros y; rewrite spec_extend2n3; apply Pf3.
     intros y; apply Pf3.
     intros y; rewrite spec_extend3n4; apply Pf4.
     intros y; rewrite spec_extend3n5; apply Pf5.
     intros y; rewrite spec_extend3n6; apply Pf6.
     intros m y; rewrite spec_extend3n6; rewrite (spec_extend6n m); apply Pfnn.
    intros x y; case y; clear y.
     intros y; rewrite spec_extend0n4; apply Pf4.
     intros y; rewrite spec_extend1n4; apply Pf4.
     intros y; rewrite spec_extend2n4; apply Pf4.
     intros y; rewrite spec_extend3n4; apply Pf4.
     intros y; apply Pf4.
     intros y; rewrite spec_extend4n5; apply Pf5.
     intros y; rewrite spec_extend4n6; apply Pf6.
     intros m y; rewrite spec_extend4n6; rewrite (spec_extend6n m); apply Pfnn.
    intros x y; case y; clear y.
     intros y; rewrite spec_extend0n5; apply Pf5.
     intros y; rewrite spec_extend1n5; apply Pf5.
     intros y; rewrite spec_extend2n5; apply Pf5.
     intros y; rewrite spec_extend3n5; apply Pf5.
     intros y; rewrite spec_extend4n5; apply Pf5.
     intros y; apply Pf5.
     intros y; rewrite spec_extend5n6; apply Pf6.
     intros m y; rewrite spec_extend5n6; rewrite (spec_extend6n m); apply Pfnn.
    intros x y; case y; clear y.
     intros y; rewrite spec_extend0n6; apply Pf6.
     intros y; rewrite spec_extend1n6; apply Pf6.
     intros y; rewrite spec_extend2n6; apply Pf6.
     intros y; rewrite spec_extend3n6; apply Pf6.
     intros y; rewrite spec_extend4n6; apply Pf6.
     intros y; rewrite spec_extend5n6; apply Pf6.
     intros y; apply Pf6.
     intros m y; rewrite (spec_extend6n m); apply Pfnn.
    intros n x y; case y; clear y.
    intros y; rewrite spec_extend0n6; rewrite (spec_extend6n n); apply Pfnn.
    intros y; rewrite spec_extend1n6; rewrite (spec_extend6n n); apply Pfnn.
    intros y; rewrite spec_extend2n6; rewrite (spec_extend6n n); apply Pfnn.
    intros y; rewrite spec_extend3n6; rewrite (spec_extend6n n); apply Pfnn.
    intros y; rewrite spec_extend4n6; rewrite (spec_extend6n n); apply Pfnn.
    intros y; rewrite spec_extend5n6; rewrite (spec_extend6n n); apply Pfnn.
    intros y; rewrite (spec_extend6n n); apply Pfnn.
    intros m y; rewrite <- (spec_cast_l n m x); 
          rewrite <- (spec_cast_r n m y); apply Pfnn.
  Qed.

  (* We level the two arguments before applying      *)
  (* the functions at each level (special zero case) *)
  Definition same_level0 (x y: t_): res :=
    Eval lazy zeta beta iota delta [extend0 extend1 extend2 extend3 extend4 extend5 extend6 
                                         GenBase.extend GenBase.extend_aux
                                         ] in
  match x with
  | N0 wx =>
    if w0_eq0 wx then f0t y else
    match y with
    | N0 wy => f0 wx wy
    | N1 wy => f1 (extend0 0 wx) wy
    | N2 wy => f2 (extend0 1 wx) wy
    | N3 wy => f3 (extend0 2 wx) wy
    | N4 wy => f4 (extend0 3 wx) wy
    | N5 wy => f5 (extend0 4 wx) wy
    | N6 wy => f6 (extend0 5 wx) wy
    | Nn m wy => fnn m (extend6 m (extend0 5 wx)) wy
    end
  | N1 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       f1 wx (extend0 0 wy)
    | N1 wy => f1 wx wy
    | N2 wy => f2 (extend1 0 wx) wy
    | N3 wy => f3 (extend1 1 wx) wy
    | N4 wy => f4 (extend1 2 wx) wy
    | N5 wy => f5 (extend1 3 wx) wy
    | N6 wy => f6 (extend1 4 wx) wy
    | Nn m wy => fnn m (extend6 m (extend1 4 wx)) wy
    end
  | N2 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       f2 wx (extend0 1 wy)
    | N1 wy =>
       f2 wx (extend1 0 wy)
    | N2 wy => f2 wx wy
    | N3 wy => f3 (extend2 0 wx) wy
    | N4 wy => f4 (extend2 1 wx) wy
    | N5 wy => f5 (extend2 2 wx) wy
    | N6 wy => f6 (extend2 3 wx) wy
    | Nn m wy => fnn m (extend6 m (extend2 3 wx)) wy
    end
  | N3 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       f3 wx (extend0 2 wy)
    | N1 wy =>
       f3 wx (extend1 1 wy)
    | N2 wy =>
       f3 wx (extend2 0 wy)
    | N3 wy => f3 wx wy
    | N4 wy => f4 (extend3 0 wx) wy
    | N5 wy => f5 (extend3 1 wx) wy
    | N6 wy => f6 (extend3 2 wx) wy
    | Nn m wy => fnn m (extend6 m (extend3 2 wx)) wy
    end
  | N4 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       f4 wx (extend0 3 wy)
    | N1 wy =>
       f4 wx (extend1 2 wy)
    | N2 wy =>
       f4 wx (extend2 1 wy)
    | N3 wy =>
       f4 wx (extend3 0 wy)
    | N4 wy => f4 wx wy
    | N5 wy => f5 (extend4 0 wx) wy
    | N6 wy => f6 (extend4 1 wx) wy
    | Nn m wy => fnn m (extend6 m (extend4 1 wx)) wy
    end
  | N5 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       f5 wx (extend0 4 wy)
    | N1 wy =>
       f5 wx (extend1 3 wy)
    | N2 wy =>
       f5 wx (extend2 2 wy)
    | N3 wy =>
       f5 wx (extend3 1 wy)
    | N4 wy =>
       f5 wx (extend4 0 wy)
    | N5 wy => f5 wx wy
    | N6 wy => f6 (extend5 0 wx) wy
    | Nn m wy => fnn m (extend6 m (extend5 0 wx)) wy
    end
  | N6 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       f6 wx (extend0 5 wy)
    | N1 wy =>
       f6 wx (extend1 4 wy)
    | N2 wy =>
       f6 wx (extend2 3 wy)
    | N3 wy =>
       f6 wx (extend3 2 wy)
    | N4 wy =>
       f6 wx (extend4 1 wy)
    | N5 wy =>
       f6 wx (extend5 0 wy)
    | N6 wy => f6 wx wy
    | Nn m wy => fnn m (extend6 m wx) wy
    end
  |  Nn n wx =>
     match y with
     | N0 wy =>
      if w0_eq0 wy then ft0 x else
      fnn n wx (extend6 n (extend0 5 wy))
     | N1 wy =>
      fnn n wx (extend6 n (extend1 4 wy))
     | N2 wy =>
      fnn n wx (extend6 n (extend2 3 wy))
     | N3 wy =>
      fnn n wx (extend6 n (extend3 2 wy))
     | N4 wy =>
      fnn n wx (extend6 n (extend4 1 wy))
     | N5 wy =>
      fnn n wx (extend6 n (extend5 0 wy))
     | N6 wy =>
      fnn n wx (extend6 n wy)
        | Nn m wy =>
            let mn := Max.max n m in
            let d := diff n m in
              fnn mn
              (castm (diff_r n m) (extend_tr wx (snd d)))
              (castm (diff_l n m) (extend_tr wy (fst d)))
    end
  end.

  Lemma spec_same_level0: forall x y, P [x] [y] (same_level0 x y).
  Proof.
  intros x; case x; clear x; unfold same_level0.
    intros x.
    generalize (spec_w0_eq0 x); case w0_eq0; intros H.
      intros y; rewrite H; apply Pf0t.
    clear H.
    intros y; case y; clear y.
     intros y; apply Pf0.
     intros y; rewrite spec_extend0n1; apply Pf1.
     intros y; rewrite spec_extend0n2; apply Pf2.
     intros y; rewrite spec_extend0n3; apply Pf3.
     intros y; rewrite spec_extend0n4; apply Pf4.
     intros y; rewrite spec_extend0n5; apply Pf5.
     intros y; rewrite spec_extend0n6; apply Pf6.
     intros m y; rewrite spec_extend0n6; rewrite (spec_extend6n m); apply Pfnn.
    intros x.
    intros y; case y; clear y.
     intros y.
     generalize (spec_w0_eq0 y); case w0_eq0; intros H.
       rewrite H; apply Pft0.
     clear H.
     rewrite spec_extend0n1; apply Pf1.
     intros y; apply Pf1.
     intros y; rewrite spec_extend1n2; apply Pf2.
     intros y; rewrite spec_extend1n3; apply Pf3.
     intros y; rewrite spec_extend1n4; apply Pf4.
     intros y; rewrite spec_extend1n5; apply Pf5.
     intros y; rewrite spec_extend1n6; apply Pf6.
     intros m y; rewrite spec_extend1n6; rewrite (spec_extend6n m); apply Pfnn.
    intros x.
    intros y; case y; clear y.
     intros y.
     generalize (spec_w0_eq0 y); case w0_eq0; intros H.
       rewrite H; apply Pft0.
     clear H.
     rewrite spec_extend0n2; apply Pf2.
     intros y.
     rewrite spec_extend1n2; apply Pf2.
     intros y; apply Pf2.
     intros y; rewrite spec_extend2n3; apply Pf3.
     intros y; rewrite spec_extend2n4; apply Pf4.
     intros y; rewrite spec_extend2n5; apply Pf5.
     intros y; rewrite spec_extend2n6; apply Pf6.
     intros m y; rewrite spec_extend2n6; rewrite (spec_extend6n m); apply Pfnn.
    intros x.
    intros y; case y; clear y.
     intros y.
     generalize (spec_w0_eq0 y); case w0_eq0; intros H.
       rewrite H; apply Pft0.
     clear H.
     rewrite spec_extend0n3; apply Pf3.
     intros y.
     rewrite spec_extend1n3; apply Pf3.
     intros y.
     rewrite spec_extend2n3; apply Pf3.
     intros y; apply Pf3.
     intros y; rewrite spec_extend3n4; apply Pf4.
     intros y; rewrite spec_extend3n5; apply Pf5.
     intros y; rewrite spec_extend3n6; apply Pf6.
     intros m y; rewrite spec_extend3n6; rewrite (spec_extend6n m); apply Pfnn.
    intros x.
    intros y; case y; clear y.
     intros y.
     generalize (spec_w0_eq0 y); case w0_eq0; intros H.
       rewrite H; apply Pft0.
     clear H.
     rewrite spec_extend0n4; apply Pf4.
     intros y.
     rewrite spec_extend1n4; apply Pf4.
     intros y.
     rewrite spec_extend2n4; apply Pf4.
     intros y.
     rewrite spec_extend3n4; apply Pf4.
     intros y; apply Pf4.
     intros y; rewrite spec_extend4n5; apply Pf5.
     intros y; rewrite spec_extend4n6; apply Pf6.
     intros m y; rewrite spec_extend4n6; rewrite (spec_extend6n m); apply Pfnn.
    intros x.
    intros y; case y; clear y.
     intros y.
     generalize (spec_w0_eq0 y); case w0_eq0; intros H.
       rewrite H; apply Pft0.
     clear H.
     rewrite spec_extend0n5; apply Pf5.
     intros y.
     rewrite spec_extend1n5; apply Pf5.
     intros y.
     rewrite spec_extend2n5; apply Pf5.
     intros y.
     rewrite spec_extend3n5; apply Pf5.
     intros y.
     rewrite spec_extend4n5; apply Pf5.
     intros y; apply Pf5.
     intros y; rewrite spec_extend5n6; apply Pf6.
     intros m y; rewrite spec_extend5n6; rewrite (spec_extend6n m); apply Pfnn.
    intros x.
    intros y; case y; clear y.
     intros y.
     generalize (spec_w0_eq0 y); case w0_eq0; intros H.
       rewrite H; apply Pft0.
     clear H.
     rewrite spec_extend0n6; apply Pf6.
     intros y.
     rewrite spec_extend1n6; apply Pf6.
     intros y.
     rewrite spec_extend2n6; apply Pf6.
     intros y.
     rewrite spec_extend3n6; apply Pf6.
     intros y.
     rewrite spec_extend4n6; apply Pf6.
     intros y.
     rewrite spec_extend5n6; apply Pf6.
     intros y; apply Pf6.
     intros m y; rewrite (spec_extend6n m); apply Pfnn.
    intros n x y; case y; clear y.
    intros y.
     generalize (spec_w0_eq0 y); case w0_eq0; intros H.
       rewrite H; apply Pft0.
     clear H.
    rewrite spec_extend0n6; rewrite (spec_extend6n n); apply Pfnn.
    intros y.
    rewrite spec_extend1n6; rewrite (spec_extend6n n); apply Pfnn.
    intros y.
    rewrite spec_extend2n6; rewrite (spec_extend6n n); apply Pfnn.
    intros y.
    rewrite spec_extend3n6; rewrite (spec_extend6n n); apply Pfnn.
    intros y.
    rewrite spec_extend4n6; rewrite (spec_extend6n n); apply Pfnn.
    intros y.
    rewrite spec_extend5n6; rewrite (spec_extend6n n); apply Pfnn.
    intros y.
    rewrite (spec_extend6n n); apply Pfnn.
  intros m y; rewrite <- (spec_cast_l n m x); 
          rewrite <- (spec_cast_r n m y); apply Pfnn.
  Qed.

  (* We iter the smaller argument with the bigger  *)
  Definition iter (x y: t_): res := 
    Eval lazy zeta beta iota delta [extend0 extend1 extend2 extend3 extend4 extend5 extend6 
                                         GenBase.extend GenBase.extend_aux
                                         ] in
  match x, y with
  | N0 wx, N0 wy => f0 wx wy
  | N0 wx, N1 wy => f0n 0 wx wy
  | N0 wx, N2 wy => f0n 1 wx wy
  | N0 wx, N3 wy => f0n 2 wx wy
  | N0 wx, N4 wy => f0n 3 wx wy
  | N0 wx, N5 wy => f0n 4 wx wy
  | N0 wx, N6 wy => f0n 5 wx wy
  | N0 wx, Nn m wy => f6n m (extend0 5 wx) wy
  | N1 wx, N0 wy => fn0 0 wx wy
  | N1 wx, N1 wy => f1 wx wy
  | N1 wx, N2 wy => f1n 0 wx wy
  | N1 wx, N3 wy => f1n 1 wx wy
  | N1 wx, N4 wy => f1n 2 wx wy
  | N1 wx, N5 wy => f1n 3 wx wy
  | N1 wx, N6 wy => f1n 4 wx wy
  | N1 wx, Nn m wy => f6n m (extend1 4 wx) wy
  | N2 wx, N0 wy => fn0 1 wx wy
  | N2 wx, N1 wy => fn1 0 wx wy
  | N2 wx, N2 wy => f2 wx wy
  | N2 wx, N3 wy => f2n 0 wx wy
  | N2 wx, N4 wy => f2n 1 wx wy
  | N2 wx, N5 wy => f2n 2 wx wy
  | N2 wx, N6 wy => f2n 3 wx wy
  | N2 wx, Nn m wy => f6n m (extend2 3 wx) wy
  | N3 wx, N0 wy => fn0 2 wx wy
  | N3 wx, N1 wy => fn1 1 wx wy
  | N3 wx, N2 wy => fn2 0 wx wy
  | N3 wx, N3 wy => f3 wx wy
  | N3 wx, N4 wy => f3n 0 wx wy
  | N3 wx, N5 wy => f3n 1 wx wy
  | N3 wx, N6 wy => f3n 2 wx wy
  | N3 wx, Nn m wy => f6n m (extend3 2 wx) wy
  | N4 wx, N0 wy => fn0 3 wx wy
  | N4 wx, N1 wy => fn1 2 wx wy
  | N4 wx, N2 wy => fn2 1 wx wy
  | N4 wx, N3 wy => fn3 0 wx wy
  | N4 wx, N4 wy => f4 wx wy
  | N4 wx, N5 wy => f4n 0 wx wy
  | N4 wx, N6 wy => f4n 1 wx wy
  | N4 wx, Nn m wy => f6n m (extend4 1 wx) wy
  | N5 wx, N0 wy => fn0 4 wx wy
  | N5 wx, N1 wy => fn1 3 wx wy
  | N5 wx, N2 wy => fn2 2 wx wy
  | N5 wx, N3 wy => fn3 1 wx wy
  | N5 wx, N4 wy => fn4 0 wx wy
  | N5 wx, N5 wy => f5 wx wy
  | N5 wx, N6 wy => f5n 0 wx wy
  | N5 wx, Nn m wy => f6n m (extend5 0 wx) wy
  | N6 wx, N0 wy => fn0 5 wx wy
  | N6 wx, N1 wy => fn1 4 wx wy
  | N6 wx, N2 wy => fn2 3 wx wy
  | N6 wx, N3 wy => fn3 2 wx wy
  | N6 wx, N4 wy => fn4 1 wx wy
  | N6 wx, N5 wy => fn5 0 wx wy
  | N6 wx, N6 wy => f6 wx wy
  | N6 wx, Nn m wy => f6n m wx wy
  | Nn n wx, N0 wy => fn6 n wx (extend0 5 wy)
  | Nn n wx, N1 wy => fn6 n wx (extend1 4 wy)
  | Nn n wx, N2 wy => fn6 n wx (extend2 3 wy)
  | Nn n wx, N3 wy => fn6 n wx (extend3 2 wy)
  | Nn n wx, N4 wy => fn6 n wx (extend4 1 wy)
  | Nn n wx, N5 wy => fn6 n wx (extend5 0 wy)
  | Nn n wx, N6 wy => fn6 n wx wy
  | Nn n wx, Nn m wy => fnm n m wx wy
  end.

  Ltac zg_tac := try
    (red; simpl Zcompare; auto;
     let t := fresh "H" in (intros t; discriminate H)).
  Lemma spec_iter: forall x y, P [x] [y] (iter x y).
  Proof.
  intros x; case x; clear x; unfold iter.
    intros x y; case y; clear y.
     intros y; apply Pf0.
     intros y; rewrite spec_eval0n1; apply (Pf0n 0); zg_tac.
     intros y; rewrite spec_eval0n2; apply (Pf0n 1); zg_tac.
     intros y; rewrite spec_eval0n3; apply (Pf0n 2); zg_tac.
     intros y; rewrite spec_eval0n4; apply (Pf0n 3); zg_tac.
     intros y; rewrite spec_eval0n5; apply (Pf0n 4); zg_tac.
     intros y; rewrite spec_eval0n6; apply (Pf0n 5); zg_tac.
     intros m y; rewrite spec_extend0n6; rewrite spec_eval6n; apply Pf6n.
    intros x y; case y; clear y.
     intros y; rewrite spec_eval0n1;  apply (Pfn0 0); zg_tac.
     intros y; apply Pf1.
     intros y; rewrite spec_eval1n1; apply (Pf1n 0); zg_tac.
     intros y; rewrite spec_eval1n2; apply (Pf1n 1); zg_tac.
     intros y; rewrite spec_eval1n3; apply (Pf1n 2); zg_tac.
     intros y; rewrite spec_eval1n4; apply (Pf1n 3); zg_tac.
     intros y; rewrite spec_eval1n5; apply (Pf1n 4); zg_tac.
     intros m y; rewrite spec_extend1n6; rewrite spec_eval6n; apply Pf6n.
    intros x y; case y; clear y.
     intros y; rewrite spec_eval0n2;  apply (Pfn0 1); zg_tac.
     intros y; rewrite spec_eval1n1;  apply (Pfn1 0); zg_tac.
     intros y; apply Pf2.
     intros y; rewrite spec_eval2n1; apply (Pf2n 0); zg_tac.
     intros y; rewrite spec_eval2n2; apply (Pf2n 1); zg_tac.
     intros y; rewrite spec_eval2n3; apply (Pf2n 2); zg_tac.
     intros y; rewrite spec_eval2n4; apply (Pf2n 3); zg_tac.
     intros m y; rewrite spec_extend2n6; rewrite spec_eval6n; apply Pf6n.
    intros x y; case y; clear y.
     intros y; rewrite spec_eval0n3;  apply (Pfn0 2); zg_tac.
     intros y; rewrite spec_eval1n2;  apply (Pfn1 1); zg_tac.
     intros y; rewrite spec_eval2n1;  apply (Pfn2 0); zg_tac.
     intros y; apply Pf3.
     intros y; rewrite spec_eval3n1; apply (Pf3n 0); zg_tac.
     intros y; rewrite spec_eval3n2; apply (Pf3n 1); zg_tac.
     intros y; rewrite spec_eval3n3; apply (Pf3n 2); zg_tac.
     intros m y; rewrite spec_extend3n6; rewrite spec_eval6n; apply Pf6n.
    intros x y; case y; clear y.
     intros y; rewrite spec_eval0n4;  apply (Pfn0 3); zg_tac.
     intros y; rewrite spec_eval1n3;  apply (Pfn1 2); zg_tac.
     intros y; rewrite spec_eval2n2;  apply (Pfn2 1); zg_tac.
     intros y; rewrite spec_eval3n1;  apply (Pfn3 0); zg_tac.
     intros y; apply Pf4.
     intros y; rewrite spec_eval4n1; apply (Pf4n 0); zg_tac.
     intros y; rewrite spec_eval4n2; apply (Pf4n 1); zg_tac.
     intros m y; rewrite spec_extend4n6; rewrite spec_eval6n; apply Pf6n.
    intros x y; case y; clear y.
     intros y; rewrite spec_eval0n5;  apply (Pfn0 4); zg_tac.
     intros y; rewrite spec_eval1n4;  apply (Pfn1 3); zg_tac.
     intros y; rewrite spec_eval2n3;  apply (Pfn2 2); zg_tac.
     intros y; rewrite spec_eval3n2;  apply (Pfn3 1); zg_tac.
     intros y; rewrite spec_eval4n1;  apply (Pfn4 0); zg_tac.
     intros y; apply Pf5.
     intros y; rewrite spec_eval5n1; apply (Pf5n 0); zg_tac.
     intros m y; rewrite spec_extend5n6; rewrite spec_eval6n; apply Pf6n.
    intros x y; case y; clear y.
     intros y; rewrite spec_eval0n6;  apply (Pfn0 5); zg_tac.
     intros y; rewrite spec_eval1n5;  apply (Pfn1 4); zg_tac.
     intros y; rewrite spec_eval2n4;  apply (Pfn2 3); zg_tac.
     intros y; rewrite spec_eval3n3;  apply (Pfn3 2); zg_tac.
     intros y; rewrite spec_eval4n2;  apply (Pfn4 1); zg_tac.
     intros y; rewrite spec_eval5n1;  apply (Pfn5 0); zg_tac.
     intros y; apply Pf6.
     intros m y; rewrite spec_eval6n; apply Pf6n.
    intros n x y; case y; clear y.
      intros y; rewrite spec_extend0n6; rewrite spec_eval6n; apply Pfn6.
      intros y; rewrite spec_extend1n6; rewrite spec_eval6n; apply Pfn6.
      intros y; rewrite spec_extend2n6; rewrite spec_eval6n; apply Pfn6.
      intros y; rewrite spec_extend3n6; rewrite spec_eval6n; apply Pfn6.
      intros y; rewrite spec_extend4n6; rewrite spec_eval6n; apply Pfn6.
      intros y; rewrite spec_extend5n6; rewrite spec_eval6n; apply Pfn6.
     intros y; rewrite spec_eval6n; apply Pfn6.
  intros m y; apply Pfnm.
  Qed.

  (* We iter the smaller argument with the bigger  (zero case) *)
  Definition iter0 (x y: t_): res :=
    Eval lazy zeta beta iota delta [extend0 extend1 extend2 extend3 extend4 extend5 extend6 
                                         GenBase.extend GenBase.extend_aux
                                         ] in
  match x with
  | N0 wx =>
    if w0_eq0 wx then f0t y else
    match y with
    | N0 wy => f0 wx wy
    | N1 wy => f0n 0 wx wy
    | N2 wy => f0n 1 wx wy
    | N3 wy => f0n 2 wx wy
    | N4 wy => f0n 3 wx wy
    | N5 wy => f0n 4 wx wy
    | N6 wy => f0n 5 wx wy
    | Nn m wy => f6n m (extend0 5 wx) wy
    end
  | N1 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       fn0 0 wx wy
    | N1 wy => f1 wx wy
    | N2 wy => f1n 0 wx wy
    | N3 wy => f1n 1 wx wy
    | N4 wy => f1n 2 wx wy
    | N5 wy => f1n 3 wx wy
    | N6 wy => f1n 4 wx wy
    | Nn m wy => f6n m (extend1 4 wx) wy
    end
  | N2 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       fn0 1 wx wy
    | N1 wy =>
       fn1 0 wx wy
    | N2 wy => f2 wx wy
    | N3 wy => f2n 0 wx wy
    | N4 wy => f2n 1 wx wy
    | N5 wy => f2n 2 wx wy
    | N6 wy => f2n 3 wx wy
    | Nn m wy => f6n m (extend2 3 wx) wy
    end
  | N3 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       fn0 2 wx wy
    | N1 wy =>
       fn1 1 wx wy
    | N2 wy =>
       fn2 0 wx wy
    | N3 wy => f3 wx wy
    | N4 wy => f3n 0 wx wy
    | N5 wy => f3n 1 wx wy
    | N6 wy => f3n 2 wx wy
    | Nn m wy => f6n m (extend3 2 wx) wy
    end
  | N4 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       fn0 3 wx wy
    | N1 wy =>
       fn1 2 wx wy
    | N2 wy =>
       fn2 1 wx wy
    | N3 wy =>
       fn3 0 wx wy
    | N4 wy => f4 wx wy
    | N5 wy => f4n 0 wx wy
    | N6 wy => f4n 1 wx wy
    | Nn m wy => f6n m (extend4 1 wx) wy
    end
  | N5 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       fn0 4 wx wy
    | N1 wy =>
       fn1 3 wx wy
    | N2 wy =>
       fn2 2 wx wy
    | N3 wy =>
       fn3 1 wx wy
    | N4 wy =>
       fn4 0 wx wy
    | N5 wy => f5 wx wy
    | N6 wy => f5n 0 wx wy
    | Nn m wy => f6n m (extend5 0 wx) wy
    end
  | N6 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       fn0 5 wx wy
    | N1 wy =>
       fn1 4 wx wy
    | N2 wy =>
       fn2 3 wx wy
    | N3 wy =>
       fn3 2 wx wy
    | N4 wy =>
       fn4 1 wx wy
    | N5 wy =>
       fn5 0 wx wy
    | N6 wy => f6 wx wy
    | Nn m wy => f6n m wx wy
    end
  | Nn n wx =>
    match y with
    | N0 wy =>
      if w0_eq0 wy then ft0 x else
      fn6 n wx (extend0 5 wy)
    | N1 wy =>
      fn6 n wx (extend1 4 wy)
    | N2 wy =>
      fn6 n wx (extend2 3 wy)
    | N3 wy =>
      fn6 n wx (extend3 2 wy)
    | N4 wy =>
      fn6 n wx (extend4 1 wy)
    | N5 wy =>
      fn6 n wx (extend5 0 wy)
    | N6 wy =>
      fn6 n wx wy
    | Nn m wy => fnm n m wx wy
    end
  end.

  Lemma spec_iter0: forall x y, P [x] [y] (iter0 x y).
  Proof.
  intros x; case x; clear x; unfold iter0.
    intros x.
    generalize (spec_w0_eq0 x); case w0_eq0; intros H.
      intros y; rewrite H; apply Pf0t.
    clear H.
    intros y; case y; clear y.
     intros y; apply Pf0.
     intros y; rewrite spec_eval0n1; apply (Pf0n 0); zg_tac.
     intros y; rewrite spec_eval0n2; apply (Pf0n 1); zg_tac.
     intros y; rewrite spec_eval0n3; apply (Pf0n 2); zg_tac.
     intros y; rewrite spec_eval0n4; apply (Pf0n 3); zg_tac.
     intros y; rewrite spec_eval0n5; apply (Pf0n 4); zg_tac.
     intros y; rewrite spec_eval0n6; apply (Pf0n 5); zg_tac.
     intros m y; rewrite spec_extend0n6; rewrite spec_eval6n; apply Pf6n.
    intros x.
    intros y; case y; clear y.
     intros y.
     generalize (spec_w0_eq0 y); case w0_eq0; intros H.
       rewrite H; apply Pft0.
     clear H.
     rewrite spec_eval0n1;  apply (Pfn0 0); zg_tac.
     intros y; apply Pf1.
     intros y; rewrite spec_eval1n1; apply (Pf1n 0); zg_tac.
     intros y; rewrite spec_eval1n2; apply (Pf1n 1); zg_tac.
     intros y; rewrite spec_eval1n3; apply (Pf1n 2); zg_tac.
     intros y; rewrite spec_eval1n4; apply (Pf1n 3); zg_tac.
     intros y; rewrite spec_eval1n5; apply (Pf1n 4); zg_tac.
     intros m y; rewrite spec_extend1n6; rewrite spec_eval6n; apply Pf6n.
    intros x.
    intros y; case y; clear y.
     intros y.
     generalize (spec_w0_eq0 y); case w0_eq0; intros H.
       rewrite H; apply Pft0.
     clear H.
     rewrite spec_eval0n2;  apply (Pfn0 1); zg_tac.
     intros y.
     rewrite spec_eval1n1;  apply (Pfn1 0); zg_tac.
     intros y; apply Pf2.
     intros y; rewrite spec_eval2n1; apply (Pf2n 0); zg_tac.
     intros y; rewrite spec_eval2n2; apply (Pf2n 1); zg_tac.
     intros y; rewrite spec_eval2n3; apply (Pf2n 2); zg_tac.
     intros y; rewrite spec_eval2n4; apply (Pf2n 3); zg_tac.
     intros m y; rewrite spec_extend2n6; rewrite spec_eval6n; apply Pf6n.
    intros x.
    intros y; case y; clear y.
     intros y.
     generalize (spec_w0_eq0 y); case w0_eq0; intros H.
       rewrite H; apply Pft0.
     clear H.
     rewrite spec_eval0n3;  apply (Pfn0 2); zg_tac.
     intros y.
     rewrite spec_eval1n2;  apply (Pfn1 1); zg_tac.
     intros y.
     rewrite spec_eval2n1;  apply (Pfn2 0); zg_tac.
     intros y; apply Pf3.
     intros y; rewrite spec_eval3n1; apply (Pf3n 0); zg_tac.
     intros y; rewrite spec_eval3n2; apply (Pf3n 1); zg_tac.
     intros y; rewrite spec_eval3n3; apply (Pf3n 2); zg_tac.
     intros m y; rewrite spec_extend3n6; rewrite spec_eval6n; apply Pf6n.
    intros x.
    intros y; case y; clear y.
     intros y.
     generalize (spec_w0_eq0 y); case w0_eq0; intros H.
       rewrite H; apply Pft0.
     clear H.
     rewrite spec_eval0n4;  apply (Pfn0 3); zg_tac.
     intros y.
     rewrite spec_eval1n3;  apply (Pfn1 2); zg_tac.
     intros y.
     rewrite spec_eval2n2;  apply (Pfn2 1); zg_tac.
     intros y.
     rewrite spec_eval3n1;  apply (Pfn3 0); zg_tac.
     intros y; apply Pf4.
     intros y; rewrite spec_eval4n1; apply (Pf4n 0); zg_tac.
     intros y; rewrite spec_eval4n2; apply (Pf4n 1); zg_tac.
     intros m y; rewrite spec_extend4n6; rewrite spec_eval6n; apply Pf6n.
    intros x.
    intros y; case y; clear y.
     intros y.
     generalize (spec_w0_eq0 y); case w0_eq0; intros H.
       rewrite H; apply Pft0.
     clear H.
     rewrite spec_eval0n5;  apply (Pfn0 4); zg_tac.
     intros y.
     rewrite spec_eval1n4;  apply (Pfn1 3); zg_tac.
     intros y.
     rewrite spec_eval2n3;  apply (Pfn2 2); zg_tac.
     intros y.
     rewrite spec_eval3n2;  apply (Pfn3 1); zg_tac.
     intros y.
     rewrite spec_eval4n1;  apply (Pfn4 0); zg_tac.
     intros y; apply Pf5.
     intros y; rewrite spec_eval5n1; apply (Pf5n 0); zg_tac.
     intros m y; rewrite spec_extend5n6; rewrite spec_eval6n; apply Pf6n.
    intros x.
    intros y; case y; clear y.
     intros y.
     generalize (spec_w0_eq0 y); case w0_eq0; intros H.
       rewrite H; apply Pft0.
     clear H.
     rewrite spec_eval0n6;  apply (Pfn0 5); zg_tac.
     intros y.
     rewrite spec_eval1n5;  apply (Pfn1 4); zg_tac.
     intros y.
     rewrite spec_eval2n4;  apply (Pfn2 3); zg_tac.
     intros y.
     rewrite spec_eval3n3;  apply (Pfn3 2); zg_tac.
     intros y.
     rewrite spec_eval4n2;  apply (Pfn4 1); zg_tac.
     intros y.
     rewrite spec_eval5n1;  apply (Pfn5 0); zg_tac.
     intros y; apply Pf6.
     intros m y; rewrite spec_eval6n; apply Pf6n.
    intros n x y; case y; clear y.
    intros y.
     generalize (spec_w0_eq0 y); case w0_eq0; intros H.
       rewrite H; apply Pft0.
     clear H.
      rewrite spec_extend0n6; rewrite spec_eval6n; apply Pfn6.
    intros y.
      rewrite spec_extend1n6; rewrite spec_eval6n; apply Pfn6.
    intros y.
      rewrite spec_extend2n6; rewrite spec_eval6n; apply Pfn6.
    intros y.
      rewrite spec_extend3n6; rewrite spec_eval6n; apply Pfn6.
    intros y.
      rewrite spec_extend4n6; rewrite spec_eval6n; apply Pfn6.
    intros y.
      rewrite spec_extend5n6; rewrite spec_eval6n; apply Pfn6.
    intros y.
     rewrite spec_eval6n; apply Pfn6.
  intros m y; apply Pfnm.
  Qed.

  End LevelAndIter.

 (***************************************************************)
 (*                                                             *)
 (*                           Reduction                         *)
 (*                                                             *)
 (***************************************************************)

 Definition reduce_0 (x:w) := N0 x.
 Definition reduce_1 :=
  Eval lazy beta iota delta[reduce_n1] in
   reduce_n1 _ _ zero w0_eq0 N0 N1.
 Definition reduce_2 :=
  Eval lazy beta iota delta[reduce_n1] in
   reduce_n1 _ _ zero w1_eq0 reduce_1 N2.
 Definition reduce_3 :=
  Eval lazy beta iota delta[reduce_n1] in
   reduce_n1 _ _ zero w2_eq0 reduce_2 N3.
 Definition reduce_4 :=
  Eval lazy beta iota delta[reduce_n1] in
   reduce_n1 _ _ zero w3_eq0 reduce_3 N4.
 Definition reduce_5 :=
  Eval lazy beta iota delta[reduce_n1] in
   reduce_n1 _ _ zero w4_eq0 reduce_4 N5.
 Definition reduce_6 :=
  Eval lazy beta iota delta[reduce_n1] in
   reduce_n1 _ _ zero w5_eq0 reduce_5 N6.
 Definition reduce_7 :=
  Eval lazy beta iota delta[reduce_n1] in
   reduce_n1 _ _ zero w6_eq0 reduce_6 (Nn 0).
 Definition reduce_n n := 
  Eval lazy beta iota delta[reduce_n] in
   reduce_n _ _ zero reduce_7 Nn n.

 Let spec_reduce_0: forall x, [reduce_0 x] = [N0 x].
 Proof.
 intros x; unfold to_Z, reduce_0.
 auto.
 Qed.
 
 Let spec_reduce_1: forall x, [reduce_1 x] = [N1 x].
 Proof.
 intros x; case x; unfold reduce_1.
 exact (spec_0 w0_spec).
 intros x1 y1.
 generalize (spec_w0_eq0 x1); 
   case w0_eq0; intros H1; auto.
 unfold to_Z; rewrite znz_to_Z_1.
 unfold to_Z in H1; rewrite H1; auto.
 Qed.
 
 Let spec_reduce_2: forall x, [reduce_2 x] = [N2 x].
 Proof.
 intros x; case x; unfold reduce_2.
 exact (spec_0 w0_spec).
 intros x1 y1.
 generalize (spec_w1_eq0 x1); 
   case w1_eq0; intros H1; auto.
 rewrite spec_reduce_1.
 unfold to_Z; rewrite znz_to_Z_2.
 unfold to_Z in H1; rewrite H1; auto.
 Qed.
 
 Let spec_reduce_3: forall x, [reduce_3 x] = [N3 x].
 Proof.
 intros x; case x; unfold reduce_3.
 exact (spec_0 w0_spec).
 intros x1 y1.
 generalize (spec_w2_eq0 x1); 
   case w2_eq0; intros H1; auto.
 rewrite spec_reduce_2.
 unfold to_Z; rewrite znz_to_Z_3.
 unfold to_Z in H1; rewrite H1; auto.
 Qed.
 
 Let spec_reduce_4: forall x, [reduce_4 x] = [N4 x].
 Proof.
 intros x; case x; unfold reduce_4.
 exact (spec_0 w0_spec).
 intros x1 y1.
 generalize (spec_w3_eq0 x1); 
   case w3_eq0; intros H1; auto.
 rewrite spec_reduce_3.
 unfold to_Z; rewrite znz_to_Z_4.
 unfold to_Z in H1; rewrite H1; auto.
 Qed.
 
 Let spec_reduce_5: forall x, [reduce_5 x] = [N5 x].
 Proof.
 intros x; case x; unfold reduce_5.
 exact (spec_0 w0_spec).
 intros x1 y1.
 generalize (spec_w4_eq0 x1); 
   case w4_eq0; intros H1; auto.
 rewrite spec_reduce_4.
 unfold to_Z; rewrite znz_to_Z_5.
 unfold to_Z in H1; rewrite H1; auto.
 Qed.
 
 Let spec_reduce_6: forall x, [reduce_6 x] = [N6 x].
 Proof.
 intros x; case x; unfold reduce_6.
 exact (spec_0 w0_spec).
 intros x1 y1.
 generalize (spec_w5_eq0 x1); 
   case w5_eq0; intros H1; auto.
 rewrite spec_reduce_5.
 unfold to_Z; rewrite znz_to_Z_6.
 unfold to_Z in H1; rewrite H1; auto.
 Qed.
 
 Let spec_reduce_7: forall x, [reduce_7 x] = [Nn 0 x].
 Proof.
 intros x; case x; unfold reduce_7.
 exact (spec_0 w0_spec).
 intros x1 y1.
 generalize (spec_w6_eq0 x1); 
   case w6_eq0; intros H1; auto.
 rewrite spec_reduce_6.
 unfold to_Z; rewrite znz_to_Z_7.
 unfold to_Z in H1; rewrite H1; auto.
 Qed.
 
 Let spec_reduce_n: forall n x, [reduce_n n x] = [Nn n x].
 Proof.
 intros n; elim n; simpl reduce_n.
   intros x; rewrite <- spec_reduce_7; auto.
 intros n1 Hrec x; case x.
 unfold to_Z; rewrite make_op_S; auto.
 exact (spec_0 w0_spec).
 intros x1 y1; case x1; auto.
 rewrite Hrec.
 rewrite spec_extendn0_0; auto.
 Qed.
 
 (***************************************************************)
 (*                                                             *)
 (*                           Successor                         *)
 (*                                                             *)
 (***************************************************************)

 Definition w0_succ_c := w0_op.(znz_succ_c).
 Definition w1_succ_c := w1_op.(znz_succ_c).
 Definition w2_succ_c := w2_op.(znz_succ_c).
 Definition w3_succ_c := w3_op.(znz_succ_c).
 Definition w4_succ_c := w4_op.(znz_succ_c).
 Definition w5_succ_c := w5_op.(znz_succ_c).
 Definition w6_succ_c := w6_op.(znz_succ_c).

 Definition w0_succ := w0_op.(znz_succ).
 Definition w1_succ := w1_op.(znz_succ).
 Definition w2_succ := w2_op.(znz_succ).
 Definition w3_succ := w3_op.(znz_succ).
 Definition w4_succ := w4_op.(znz_succ).
 Definition w5_succ := w5_op.(znz_succ).
 Definition w6_succ := w6_op.(znz_succ).

 Definition succ x :=
  match x with
  | N0 wx =>
    match w0_succ_c wx with
    | C0 r => N0 r
    | C1 r => N1 (WW one0 r)
    end
  | N1 wx =>
    match w1_succ_c wx with
    | C0 r => N1 r
    | C1 r => N2 (WW one1 r)
    end
  | N2 wx =>
    match w2_succ_c wx with
    | C0 r => N2 r
    | C1 r => N3 (WW one2 r)
    end
  | N3 wx =>
    match w3_succ_c wx with
    | C0 r => N3 r
    | C1 r => N4 (WW one3 r)
    end
  | N4 wx =>
    match w4_succ_c wx with
    | C0 r => N4 r
    | C1 r => N5 (WW one4 r)
    end
  | N5 wx =>
    match w5_succ_c wx with
    | C0 r => N5 r
    | C1 r => N6 (WW one5 r)
    end
  | N6 wx =>
    match w6_succ_c wx with
    | C0 r => N6 r
    | C1 r => Nn 0 (WW one6 r)
    end
  | Nn n wx =>
    let op := make_op n in
    match op.(znz_succ_c) wx with
    | C0 r => Nn n r
    | C1 r => Nn (S n) (WW op.(znz_1) r)
    end
  end.

 Theorem spec_succ: forall n, [succ n] = [n] + 1.
 Proof.
  intros n; case n; unfold succ, to_Z.
  intros n1; generalize (spec_succ_c w0_spec n1);
  unfold succ, to_Z, w0_succ_c; case znz_succ_c; auto.
     intros ww H; rewrite <- H.
     (rewrite znz_to_Z_1; unfold interp_carry;
           apply f_equal2 with (f := Zplus); auto;
           apply f_equal2 with (f := Zmult); auto;
           exact (spec_1 w0_spec)).
  intros n1; generalize (spec_succ_c w1_spec n1);
  unfold succ, to_Z, w1_succ_c; case znz_succ_c; auto.
     intros ww H; rewrite <- H.
     (rewrite znz_to_Z_2; unfold interp_carry;
           apply f_equal2 with (f := Zplus); auto;
           apply f_equal2 with (f := Zmult); auto;
           exact (spec_1 w1_spec)).
  intros n1; generalize (spec_succ_c w2_spec n1);
  unfold succ, to_Z, w2_succ_c; case znz_succ_c; auto.
     intros ww H; rewrite <- H.
     (rewrite znz_to_Z_3; unfold interp_carry;
           apply f_equal2 with (f := Zplus); auto;
           apply f_equal2 with (f := Zmult); auto;
           exact (spec_1 w2_spec)).
  intros n1; generalize (spec_succ_c w3_spec n1);
  unfold succ, to_Z, w3_succ_c; case znz_succ_c; auto.
     intros ww H; rewrite <- H.
     (rewrite znz_to_Z_4; unfold interp_carry;
           apply f_equal2 with (f := Zplus); auto;
           apply f_equal2 with (f := Zmult); auto;
           exact (spec_1 w3_spec)).
  intros n1; generalize (spec_succ_c w4_spec n1);
  unfold succ, to_Z, w4_succ_c; case znz_succ_c; auto.
     intros ww H; rewrite <- H.
     (rewrite znz_to_Z_5; unfold interp_carry;
           apply f_equal2 with (f := Zplus); auto;
           apply f_equal2 with (f := Zmult); auto;
           exact (spec_1 w4_spec)).
  intros n1; generalize (spec_succ_c w5_spec n1);
  unfold succ, to_Z, w5_succ_c; case znz_succ_c; auto.
     intros ww H; rewrite <- H.
     (rewrite znz_to_Z_6; unfold interp_carry;
           apply f_equal2 with (f := Zplus); auto;
           apply f_equal2 with (f := Zmult); auto;
           exact (spec_1 w5_spec)).
  intros n1; generalize (spec_succ_c w6_spec n1);
  unfold succ, to_Z, w6_succ_c; case znz_succ_c; auto.
     intros ww H; rewrite <- H.
     (rewrite znz_to_Z_7; unfold interp_carry;
           apply f_equal2 with (f := Zplus); auto;
           apply f_equal2 with (f := Zmult); auto;
           exact (spec_1 w6_spec)).
  intros k n1; generalize (spec_succ_c (wn_spec k) n1).
  unfold succ, to_Z; case znz_succ_c; auto.
  intros ww H; rewrite <- H.
     (rewrite (znz_to_Z_n k); unfold interp_carry;
           apply f_equal2 with (f := Zplus); auto;
           apply f_equal2 with (f := Zmult); auto;
           exact (spec_1 (wn_spec k))).
 Qed.

 (***************************************************************)
 (*                                                             *)
 (*                           Adddition                         *)
 (*                                                             *)
 (***************************************************************)

 Definition w0_add_c := znz_add_c w0_op.
 Definition w0_add x y :=
  match w0_add_c x y with
  | C0 r => N0 r
  | C1 r => N1 (WW one0 r)
  end.

 Definition w1_add_c := znz_add_c w1_op.
 Definition w1_add x y :=
  match w1_add_c x y with
  | C0 r => N1 r
  | C1 r => N2 (WW one1 r)
  end.

 Definition w2_add_c := znz_add_c w2_op.
 Definition w2_add x y :=
  match w2_add_c x y with
  | C0 r => N2 r
  | C1 r => N3 (WW one2 r)
  end.

 Definition w3_add_c := znz_add_c w3_op.
 Definition w3_add x y :=
  match w3_add_c x y with
  | C0 r => N3 r
  | C1 r => N4 (WW one3 r)
  end.

 Definition w4_add_c := znz_add_c w4_op.
 Definition w4_add x y :=
  match w4_add_c x y with
  | C0 r => N4 r
  | C1 r => N5 (WW one4 r)
  end.

 Definition w5_add_c := znz_add_c w5_op.
 Definition w5_add x y :=
  match w5_add_c x y with
  | C0 r => N5 r
  | C1 r => N6 (WW one5 r)
  end.

 Definition w6_add_c := znz_add_c w6_op.
 Definition w6_add x y :=
  match w6_add_c x y with
  | C0 r => N6 r
  | C1 r => Nn 0 (WW one6 r)
  end.

 Definition addn n (x y : word w6 (S n)) :=
  let op := make_op n in
  match op.(znz_add_c) x y with
  | C0 r => Nn n r
  | C1 r => Nn (S n) (WW op.(znz_1) r)  end.

 Let spec_w0_add: forall x y, [w0_add x y] = [N0 x] + [N0 y].
 Proof.
 intros n m; unfold to_Z, w0_add, w0_add_c.
  generalize (spec_add_c w0_spec n m); case znz_add_c; auto.
 intros ww H; rewrite <- H.
    rewrite znz_to_Z_1; unfold interp_carry;
    apply f_equal2 with (f := Zplus); auto;
    apply f_equal2 with (f := Zmult); auto;
    exact (spec_1 w0_spec).
 Qed.
 Hint Rewrite spec_w0_add: addr.

 Let spec_w1_add: forall x y, [w1_add x y] = [N1 x] + [N1 y].
 Proof.
 intros n m; unfold to_Z, w1_add, w1_add_c.
  generalize (spec_add_c w1_spec n m); case znz_add_c; auto.
 intros ww H; rewrite <- H.
    rewrite znz_to_Z_2; unfold interp_carry;
    apply f_equal2 with (f := Zplus); auto;
    apply f_equal2 with (f := Zmult); auto;
    exact (spec_1 w1_spec).
 Qed.
 Hint Rewrite spec_w1_add: addr.

 Let spec_w2_add: forall x y, [w2_add x y] = [N2 x] + [N2 y].
 Proof.
 intros n m; unfold to_Z, w2_add, w2_add_c.
  generalize (spec_add_c w2_spec n m); case znz_add_c; auto.
 intros ww H; rewrite <- H.
    rewrite znz_to_Z_3; unfold interp_carry;
    apply f_equal2 with (f := Zplus); auto;
    apply f_equal2 with (f := Zmult); auto;
    exact (spec_1 w2_spec).
 Qed.
 Hint Rewrite spec_w2_add: addr.

 Let spec_w3_add: forall x y, [w3_add x y] = [N3 x] + [N3 y].
 Proof.
 intros n m; unfold to_Z, w3_add, w3_add_c.
  generalize (spec_add_c w3_spec n m); case znz_add_c; auto.
 intros ww H; rewrite <- H.
    rewrite znz_to_Z_4; unfold interp_carry;
    apply f_equal2 with (f := Zplus); auto;
    apply f_equal2 with (f := Zmult); auto;
    exact (spec_1 w3_spec).
 Qed.
 Hint Rewrite spec_w3_add: addr.

 Let spec_w4_add: forall x y, [w4_add x y] = [N4 x] + [N4 y].
 Proof.
 intros n m; unfold to_Z, w4_add, w4_add_c.
  generalize (spec_add_c w4_spec n m); case znz_add_c; auto.
 intros ww H; rewrite <- H.
    rewrite znz_to_Z_5; unfold interp_carry;
    apply f_equal2 with (f := Zplus); auto;
    apply f_equal2 with (f := Zmult); auto;
    exact (spec_1 w4_spec).
 Qed.
 Hint Rewrite spec_w4_add: addr.

 Let spec_w5_add: forall x y, [w5_add x y] = [N5 x] + [N5 y].
 Proof.
 intros n m; unfold to_Z, w5_add, w5_add_c.
  generalize (spec_add_c w5_spec n m); case znz_add_c; auto.
 intros ww H; rewrite <- H.
    rewrite znz_to_Z_6; unfold interp_carry;
    apply f_equal2 with (f := Zplus); auto;
    apply f_equal2 with (f := Zmult); auto;
    exact (spec_1 w5_spec).
 Qed.
 Hint Rewrite spec_w5_add: addr.

 Let spec_w6_add: forall x y, [w6_add x y] = [N6 x] + [N6 y].
 Proof.
 intros n m; unfold to_Z, w6_add, w6_add_c.
  generalize (spec_add_c w6_spec n m); case znz_add_c; auto.
 intros ww H; rewrite <- H.
    rewrite znz_to_Z_7; unfold interp_carry;
    apply f_equal2 with (f := Zplus); auto;
    apply f_equal2 with (f := Zmult); auto;
    exact (spec_1 w6_spec).
 Qed.
 Hint Rewrite spec_w6_add: addr.

 Let spec_wn_add: forall n x y, [addn n x y] = [Nn n x] + [Nn n y].
 Proof.
 intros k n m; unfold to_Z, addn.
  generalize (spec_add_c (wn_spec k) n m); case znz_add_c; auto.
 intros ww H; rewrite <- H.
 rewrite (znz_to_Z_n k); unfold interp_carry;
        apply f_equal2 with (f := Zplus); auto;
        apply f_equal2 with (f := Zmult); auto;
        exact (spec_1 (wn_spec k)).
 Qed.
 Hint Rewrite spec_wn_add: addr.
 Definition add := Eval lazy beta delta [same_level] in
   (same_level t_ w0_add w1_add w2_add w3_add w4_add w5_add w6_add addn).

 Theorem spec_add: forall x y, [add x y] = [x] + [y].
 Proof.
 unfold add.
 generalize (spec_same_level t_ (fun x y res => [res] = x + y)).
 unfold same_level; intros HH; apply HH; clear HH.
 exact spec_w0_add.
 exact spec_w1_add.
 exact spec_w2_add.
 exact spec_w3_add.
 exact spec_w4_add.
 exact spec_w5_add.
 exact spec_w6_add.
 exact spec_wn_add.
 Qed.

 (***************************************************************)
 (*                                                             *)
 (*                           Predecessor                       *)
 (*                                                             *)
 (***************************************************************)

 Definition w0_pred_c := w0_op.(znz_pred_c).
 Definition w1_pred_c := w1_op.(znz_pred_c).
 Definition w2_pred_c := w2_op.(znz_pred_c).
 Definition w3_pred_c := w3_op.(znz_pred_c).
 Definition w4_pred_c := w4_op.(znz_pred_c).
 Definition w5_pred_c := w5_op.(znz_pred_c).
 Definition w6_pred_c := w6_op.(znz_pred_c).

 Definition pred x :=
  match x with
  | N0 wx =>
    match w0_pred_c wx with
    | C0 r => reduce_0 r
    | C1 r => zero
    end
  | N1 wx =>
    match w1_pred_c wx with
    | C0 r => reduce_1 r
    | C1 r => zero
    end
  | N2 wx =>
    match w2_pred_c wx with
    | C0 r => reduce_2 r
    | C1 r => zero
    end
  | N3 wx =>
    match w3_pred_c wx with
    | C0 r => reduce_3 r
    | C1 r => zero
    end
  | N4 wx =>
    match w4_pred_c wx with
    | C0 r => reduce_4 r
    | C1 r => zero
    end
  | N5 wx =>
    match w5_pred_c wx with
    | C0 r => reduce_5 r
    | C1 r => zero
    end
  | N6 wx =>
    match w6_pred_c wx with
    | C0 r => reduce_6 r
    | C1 r => zero
    end
  | Nn n wx =>
    let op := make_op n in
    match op.(znz_pred_c) wx with
    | C0 r => reduce_n n r
    | C1 r => zero
    end
  end.

 Theorem spec_pred: forall x, 0 < [x] -> [pred x] = [x] - 1.
 Proof.
 intros x; case x; unfold pred.
 intros x1 H1; unfold w0_pred_c; 
 generalize (spec_pred_c w0_spec x1); case znz_pred_c; intros y1.
 rewrite spec_reduce_0; auto.
 unfold interp_carry; unfold to_Z.
 case (spec_to_Z w0_spec x1); intros HH1 HH2.
 case (spec_to_Z w0_spec y1); intros HH3 HH4 HH5.
 assert (znz_to_Z w0_op x1 - 1 < 0); auto with zarith.
 unfold to_Z in H1; auto with zarith.
 intros x1 H1; unfold w1_pred_c; 
 generalize (spec_pred_c w1_spec x1); case znz_pred_c; intros y1.
 rewrite spec_reduce_1; auto.
 unfold interp_carry; unfold to_Z.
 case (spec_to_Z w1_spec x1); intros HH1 HH2.
 case (spec_to_Z w1_spec y1); intros HH3 HH4 HH5.
 assert (znz_to_Z w1_op x1 - 1 < 0); auto with zarith.
 unfold to_Z in H1; auto with zarith.
 intros x1 H1; unfold w2_pred_c; 
 generalize (spec_pred_c w2_spec x1); case znz_pred_c; intros y1.
 rewrite spec_reduce_2; auto.
 unfold interp_carry; unfold to_Z.
 case (spec_to_Z w2_spec x1); intros HH1 HH2.
 case (spec_to_Z w2_spec y1); intros HH3 HH4 HH5.
 assert (znz_to_Z w2_op x1 - 1 < 0); auto with zarith.
 unfold to_Z in H1; auto with zarith.
 intros x1 H1; unfold w3_pred_c; 
 generalize (spec_pred_c w3_spec x1); case znz_pred_c; intros y1.
 rewrite spec_reduce_3; auto.
 unfold interp_carry; unfold to_Z.
 case (spec_to_Z w3_spec x1); intros HH1 HH2.
 case (spec_to_Z w3_spec y1); intros HH3 HH4 HH5.
 assert (znz_to_Z w3_op x1 - 1 < 0); auto with zarith.
 unfold to_Z in H1; auto with zarith.
 intros x1 H1; unfold w4_pred_c; 
 generalize (spec_pred_c w4_spec x1); case znz_pred_c; intros y1.
 rewrite spec_reduce_4; auto.
 unfold interp_carry; unfold to_Z.
 case (spec_to_Z w4_spec x1); intros HH1 HH2.
 case (spec_to_Z w4_spec y1); intros HH3 HH4 HH5.
 assert (znz_to_Z w4_op x1 - 1 < 0); auto with zarith.
 unfold to_Z in H1; auto with zarith.
 intros x1 H1; unfold w5_pred_c; 
 generalize (spec_pred_c w5_spec x1); case znz_pred_c; intros y1.
 rewrite spec_reduce_5; auto.
 unfold interp_carry; unfold to_Z.
 case (spec_to_Z w5_spec x1); intros HH1 HH2.
 case (spec_to_Z w5_spec y1); intros HH3 HH4 HH5.
 assert (znz_to_Z w5_op x1 - 1 < 0); auto with zarith.
 unfold to_Z in H1; auto with zarith.
 intros x1 H1; unfold w6_pred_c; 
 generalize (spec_pred_c w6_spec x1); case znz_pred_c; intros y1.
 rewrite spec_reduce_6; auto.
 unfold interp_carry; unfold to_Z.
 case (spec_to_Z w6_spec x1); intros HH1 HH2.
 case (spec_to_Z w6_spec y1); intros HH3 HH4 HH5.
 assert (znz_to_Z w6_op x1 - 1 < 0); auto with zarith.
 unfold to_Z in H1; auto with zarith.
 intros n x1 H1;  
   generalize (spec_pred_c (wn_spec n) x1); case znz_pred_c; intros y1.
   rewrite spec_reduce_n; auto.
 unfold interp_carry; unfold to_Z.
 case (spec_to_Z (wn_spec n) x1); intros HH1 HH2.
 case (spec_to_Z (wn_spec n) y1); intros HH3 HH4 HH5.
 assert (znz_to_Z (make_op n) x1 - 1 < 0); auto with zarith.
 unfold to_Z in H1; auto with zarith.
 Qed.
 
 Let spec_pred0: forall x, [x] = 0 -> [pred x] = 0.
 Proof.
 intros x; case x; unfold pred.
 intros x1 H1; unfold w0_pred_c; 
   generalize (spec_pred_c w0_spec x1); case znz_pred_c; intros y1.
 unfold interp_carry; unfold to_Z.
 unfold to_Z in H1; auto with zarith.
 case (spec_to_Z w0_spec y1); intros HH3 HH4; auto with zarith.
 intros; exact (spec_0 w0_spec).
 intros x1 H1; unfold w1_pred_c; 
   generalize (spec_pred_c w1_spec x1); case znz_pred_c; intros y1.
 unfold interp_carry; unfold to_Z.
 unfold to_Z in H1; auto with zarith.
 case (spec_to_Z w1_spec y1); intros HH3 HH4; auto with zarith.
 intros; exact (spec_0 w0_spec).
 intros x1 H1; unfold w2_pred_c; 
   generalize (spec_pred_c w2_spec x1); case znz_pred_c; intros y1.
 unfold interp_carry; unfold to_Z.
 unfold to_Z in H1; auto with zarith.
 case (spec_to_Z w2_spec y1); intros HH3 HH4; auto with zarith.
 intros; exact (spec_0 w0_spec).
 intros x1 H1; unfold w3_pred_c; 
   generalize (spec_pred_c w3_spec x1); case znz_pred_c; intros y1.
 unfold interp_carry; unfold to_Z.
 unfold to_Z in H1; auto with zarith.
 case (spec_to_Z w3_spec y1); intros HH3 HH4; auto with zarith.
 intros; exact (spec_0 w0_spec).
 intros x1 H1; unfold w4_pred_c; 
   generalize (spec_pred_c w4_spec x1); case znz_pred_c; intros y1.
 unfold interp_carry; unfold to_Z.
 unfold to_Z in H1; auto with zarith.
 case (spec_to_Z w4_spec y1); intros HH3 HH4; auto with zarith.
 intros; exact (spec_0 w0_spec).
 intros x1 H1; unfold w5_pred_c; 
   generalize (spec_pred_c w5_spec x1); case znz_pred_c; intros y1.
 unfold interp_carry; unfold to_Z.
 unfold to_Z in H1; auto with zarith.
 case (spec_to_Z w5_spec y1); intros HH3 HH4; auto with zarith.
 intros; exact (spec_0 w0_spec).
 intros x1 H1; unfold w6_pred_c; 
   generalize (spec_pred_c w6_spec x1); case znz_pred_c; intros y1.
 unfold interp_carry; unfold to_Z.
 unfold to_Z in H1; auto with zarith.
 case (spec_to_Z w6_spec y1); intros HH3 HH4; auto with zarith.
 intros; exact (spec_0 w0_spec).
 intros n x1 H1; 
   generalize (spec_pred_c (wn_spec n) x1); case znz_pred_c; intros y1.
 unfold interp_carry; unfold to_Z.
 unfold to_Z in H1; auto with zarith.
 case (spec_to_Z (wn_spec n) y1); intros HH3 HH4; auto with zarith.
 intros; exact (spec_0 w0_spec).
 Qed.
 
 (***************************************************************)
 (*                                                             *)
 (*                           Subtraction                       *)
 (*                                                             *)
 (***************************************************************)

 Definition w0_sub_c := w0_op.(znz_sub_c).
 Definition w1_sub_c := w1_op.(znz_sub_c).
 Definition w2_sub_c := w2_op.(znz_sub_c).
 Definition w3_sub_c := w3_op.(znz_sub_c).
 Definition w4_sub_c := w4_op.(znz_sub_c).
 Definition w5_sub_c := w5_op.(znz_sub_c).
 Definition w6_sub_c := w6_op.(znz_sub_c).

 Definition w0_sub x y :=
  match w0_sub_c x y with
  | C0 r => reduce_0 r
  | C1 r => zero
  end.
 Definition w1_sub x y :=
  match w1_sub_c x y with
  | C0 r => reduce_1 r
  | C1 r => zero
  end.
 Definition w2_sub x y :=
  match w2_sub_c x y with
  | C0 r => reduce_2 r
  | C1 r => zero
  end.
 Definition w3_sub x y :=
  match w3_sub_c x y with
  | C0 r => reduce_3 r
  | C1 r => zero
  end.
 Definition w4_sub x y :=
  match w4_sub_c x y with
  | C0 r => reduce_4 r
  | C1 r => zero
  end.
 Definition w5_sub x y :=
  match w5_sub_c x y with
  | C0 r => reduce_5 r
  | C1 r => zero
  end.
 Definition w6_sub x y :=
  match w6_sub_c x y with
  | C0 r => reduce_6 r
  | C1 r => zero
  end.

 Definition subn n (x y : word w6 (S n)) :=
  let op := make_op n in
  match op.(znz_sub_c) x y with
  | C0 r => Nn n r
  | C1 r => N0 w_0  end.

 Let spec_w0_sub: forall x y, [N0 y] <= [N0 x] -> [w0_sub x y] = [N0 x] - [N0 y].
 Proof.
 intros n m; unfold w0_sub, w0_sub_c.
  generalize (spec_sub_c w0_spec n m); case znz_sub_c; 
    intros x; auto.
 unfold interp_carry; unfold zero, w_0, to_Z.
 rewrite (spec_0 w0_spec).
 case (spec_to_Z w0_spec x); intros; auto with zarith.
 Qed.

 Let spec_w1_sub: forall x y, [N1 y] <= [N1 x] -> [w1_sub x y] = [N1 x] - [N1 y].
 Proof.
 intros n m; unfold w1_sub, w1_sub_c.
  generalize (spec_sub_c w1_spec n m); case znz_sub_c; 
   intros x; try rewrite spec_reduce_1; auto.
 unfold interp_carry; unfold zero, w_0, to_Z.
 rewrite (spec_0 w0_spec).
 case (spec_to_Z w1_spec x); intros; auto with zarith.
 Qed.

 Let spec_w2_sub: forall x y, [N2 y] <= [N2 x] -> [w2_sub x y] = [N2 x] - [N2 y].
 Proof.
 intros n m; unfold w2_sub, w2_sub_c.
  generalize (spec_sub_c w2_spec n m); case znz_sub_c; 
   intros x; try rewrite spec_reduce_2; auto.
 unfold interp_carry; unfold zero, w_0, to_Z.
 rewrite (spec_0 w0_spec).
 case (spec_to_Z w2_spec x); intros; auto with zarith.
 Qed.

 Let spec_w3_sub: forall x y, [N3 y] <= [N3 x] -> [w3_sub x y] = [N3 x] - [N3 y].
 Proof.
 intros n m; unfold w3_sub, w3_sub_c.
  generalize (spec_sub_c w3_spec n m); case znz_sub_c; 
   intros x; try rewrite spec_reduce_3; auto.
 unfold interp_carry; unfold zero, w_0, to_Z.
 rewrite (spec_0 w0_spec).
 case (spec_to_Z w3_spec x); intros; auto with zarith.
 Qed.

 Let spec_w4_sub: forall x y, [N4 y] <= [N4 x] -> [w4_sub x y] = [N4 x] - [N4 y].
 Proof.
 intros n m; unfold w4_sub, w4_sub_c.
  generalize (spec_sub_c w4_spec n m); case znz_sub_c; 
   intros x; try rewrite spec_reduce_4; auto.
 unfold interp_carry; unfold zero, w_0, to_Z.
 rewrite (spec_0 w0_spec).
 case (spec_to_Z w4_spec x); intros; auto with zarith.
 Qed.

 Let spec_w5_sub: forall x y, [N5 y] <= [N5 x] -> [w5_sub x y] = [N5 x] - [N5 y].
 Proof.
 intros n m; unfold w5_sub, w5_sub_c.
  generalize (spec_sub_c w5_spec n m); case znz_sub_c; 
   intros x; try rewrite spec_reduce_5; auto.
 unfold interp_carry; unfold zero, w_0, to_Z.
 rewrite (spec_0 w0_spec).
 case (spec_to_Z w5_spec x); intros; auto with zarith.
 Qed.

 Let spec_w6_sub: forall x y, [N6 y] <= [N6 x] -> [w6_sub x y] = [N6 x] - [N6 y].
 Proof.
 intros n m; unfold w6_sub, w6_sub_c.
  generalize (spec_sub_c w6_spec n m); case znz_sub_c; 
   intros x; try rewrite spec_reduce_6; auto.
 unfold interp_carry; unfold zero, w_0, to_Z.
 rewrite (spec_0 w0_spec).
 case (spec_to_Z w6_spec x); intros; auto with zarith.
 Qed.

 Let spec_wn_sub: forall n x y, [Nn n y] <= [Nn n x] -> [subn n x y] = [Nn n x] - [Nn n y].
 Proof.
 intros k n m; unfold subn.
 generalize (spec_sub_c (wn_spec k) n m); case znz_sub_c; 
   intros x; auto.
 unfold interp_carry, to_Z.
 case (spec_to_Z (wn_spec k) x); intros; auto with zarith.
 Qed.

 Definition sub := Eval lazy beta delta [same_level] in
   (same_level t_ w0_sub w1_sub w2_sub w3_sub w4_sub w5_sub w6_sub subn).

 Theorem spec_sub: forall x y, [y] <= [x] -> [sub x y] = [x] - [y].
 Proof.
 unfold sub.
 generalize (spec_same_level t_ (fun x y res => y <= x -> [res] = x - y)).
 unfold same_level; intros HH; apply HH; clear HH.
 exact spec_w0_sub.
 exact spec_w1_sub.
 exact spec_w2_sub.
 exact spec_w3_sub.
 exact spec_w4_sub.
 exact spec_w5_sub.
 exact spec_w6_sub.
 exact spec_wn_sub.
 Qed.

 Let spec_w0_sub0: forall x y, [N0 x] < [N0 y] -> [w0_sub x y] = 0.
 Proof.
 intros n m; unfold w0_sub, w0_sub_c.
  generalize (spec_sub_c w0_spec n m); case znz_sub_c; 
   intros x; unfold interp_carry.
   unfold to_Z; case (spec_to_Z w0_spec x); intros; auto with zarith.
 intros; unfold to_Z, zero, w_0; rewrite (spec_0 w0_spec); auto.
 Qed.

 Let spec_w1_sub0: forall x y, [N1 x] < [N1 y] -> [w1_sub x y] = 0.
 Proof.
 intros n m; unfold w1_sub, w1_sub_c.
  generalize (spec_sub_c w1_spec n m); case znz_sub_c; 
   intros x; unfold interp_carry.
   unfold to_Z; case (spec_to_Z w1_spec x); intros; auto with zarith.
 intros; unfold to_Z, zero, w_0; rewrite (spec_0 w0_spec); auto.
 Qed.

 Let spec_w2_sub0: forall x y, [N2 x] < [N2 y] -> [w2_sub x y] = 0.
 Proof.
 intros n m; unfold w2_sub, w2_sub_c.
  generalize (spec_sub_c w2_spec n m); case znz_sub_c; 
   intros x; unfold interp_carry.
   unfold to_Z; case (spec_to_Z w2_spec x); intros; auto with zarith.
 intros; unfold to_Z, zero, w_0; rewrite (spec_0 w0_spec); auto.
 Qed.

 Let spec_w3_sub0: forall x y, [N3 x] < [N3 y] -> [w3_sub x y] = 0.
 Proof.
 intros n m; unfold w3_sub, w3_sub_c.
  generalize (spec_sub_c w3_spec n m); case znz_sub_c; 
   intros x; unfold interp_carry.
   unfold to_Z; case (spec_to_Z w3_spec x); intros; auto with zarith.
 intros; unfold to_Z, zero, w_0; rewrite (spec_0 w0_spec); auto.
 Qed.

 Let spec_w4_sub0: forall x y, [N4 x] < [N4 y] -> [w4_sub x y] = 0.
 Proof.
 intros n m; unfold w4_sub, w4_sub_c.
  generalize (spec_sub_c w4_spec n m); case znz_sub_c; 
   intros x; unfold interp_carry.
   unfold to_Z; case (spec_to_Z w4_spec x); intros; auto with zarith.
 intros; unfold to_Z, zero, w_0; rewrite (spec_0 w0_spec); auto.
 Qed.

 Let spec_w5_sub0: forall x y, [N5 x] < [N5 y] -> [w5_sub x y] = 0.
 Proof.
 intros n m; unfold w5_sub, w5_sub_c.
  generalize (spec_sub_c w5_spec n m); case znz_sub_c; 
   intros x; unfold interp_carry.
   unfold to_Z; case (spec_to_Z w5_spec x); intros; auto with zarith.
 intros; unfold to_Z, zero, w_0; rewrite (spec_0 w0_spec); auto.
 Qed.

 Let spec_w6_sub0: forall x y, [N6 x] < [N6 y] -> [w6_sub x y] = 0.
 Proof.
 intros n m; unfold w6_sub, w6_sub_c.
  generalize (spec_sub_c w6_spec n m); case znz_sub_c; 
   intros x; unfold interp_carry.
   unfold to_Z; case (spec_to_Z w6_spec x); intros; auto with zarith.
 intros; unfold to_Z, zero, w_0; rewrite (spec_0 w0_spec); auto.
 Qed.

 Let spec_wn_sub0: forall n x y, [Nn n x] < [Nn n y] -> [subn n x y] = 0.
 Proof.
 intros k n m; unfold subn.
 generalize (spec_sub_c (wn_spec k) n m); case znz_sub_c; 
   intros x; unfold interp_carry.
   unfold to_Z; case (spec_to_Z (wn_spec k) x); intros; auto with zarith.
 intros; unfold to_Z, w_0; rewrite (spec_0 (w0_spec)); auto.
 Qed.

 Theorem spec_sub0: forall x y, [x] < [y] -> [sub x y] = 0.
 Proof.
 unfold sub.
 generalize (spec_same_level t_ (fun x y res => x < y -> [res] = 0)).
 unfold same_level; intros HH; apply HH; clear HH.
 exact spec_w0_sub0.
 exact spec_w1_sub0.
 exact spec_w2_sub0.
 exact spec_w3_sub0.
 exact spec_w4_sub0.
 exact spec_w5_sub0.
 exact spec_w6_sub0.
 exact spec_wn_sub0.
 Qed.

 (***************************************************************)
 (*                                                             *)
 (*                           Comparison                        *)
 (*                                                             *)
 (***************************************************************)

 Definition compare_0 := w0_op.(znz_compare).
 Definition comparen_0 :=
  compare_mn_1 w0 w0 w_0 compare_0 (compare_0 w_0) compare_0.
 Definition compare_1 := w1_op.(znz_compare).
 Definition comparen_1 :=
  compare_mn_1 w1 w1 W0 compare_1 (compare_1 W0) compare_1.
 Definition compare_2 := w2_op.(znz_compare).
 Definition comparen_2 :=
  compare_mn_1 w2 w2 W0 compare_2 (compare_2 W0) compare_2.
 Definition compare_3 := w3_op.(znz_compare).
 Definition comparen_3 :=
  compare_mn_1 w3 w3 W0 compare_3 (compare_3 W0) compare_3.
 Definition compare_4 := w4_op.(znz_compare).
 Definition comparen_4 :=
  compare_mn_1 w4 w4 W0 compare_4 (compare_4 W0) compare_4.
 Definition compare_5 := w5_op.(znz_compare).
 Definition comparen_5 :=
  compare_mn_1 w5 w5 W0 compare_5 (compare_5 W0) compare_5.
 Definition compare_6 := w6_op.(znz_compare).
 Definition comparen_6 :=
  compare_mn_1 w6 w6 W0 compare_6 (compare_6 W0) compare_6.

 Definition comparenm n m wx wy :=
    let mn := Max.max n m in
    let d := diff n m in
    let op := make_op mn in
     op.(znz_compare)
       (castm (diff_r n m) (extend_tr wx (snd d)))
       (castm (diff_l n m) (extend_tr wy (fst d))).

 Definition compare := Eval lazy beta delta [iter] in 
   (iter _ 
      compare_0
      (fun n x y => opp_compare (comparen_0 (S n) y x))
      (fun n => comparen_0 (S n))
      compare_1
      (fun n x y => opp_compare (comparen_1 (S n) y x))
      (fun n => comparen_1 (S n))
      compare_2
      (fun n x y => opp_compare (comparen_2 (S n) y x))
      (fun n => comparen_2 (S n))
      compare_3
      (fun n x y => opp_compare (comparen_3 (S n) y x))
      (fun n => comparen_3 (S n))
      compare_4
      (fun n x y => opp_compare (comparen_4 (S n) y x))
      (fun n => comparen_4 (S n))
      compare_5
      (fun n x y => opp_compare (comparen_5 (S n) y x))
      (fun n => comparen_5 (S n))
      compare_6
      (fun n x y => opp_compare (comparen_6 (S n) y x))
      (fun n => comparen_6 (S n))
      comparenm).

 Let spec_compare_0: forall x y,
    match compare_0 x y with 
      Eq => [N0 x] = [N0 y]
    | Lt => [N0 x] < [N0 y]
    | Gt => [N0 x] > [N0 y]
    end.
  Proof.
  unfold compare_0, to_Z; exact (spec_compare w0_spec).
  Qed.

  Let spec_comparen_0:
  forall (n : nat) (x : word w0 n) (y : w0),
  match comparen_0 n x y with
  | Eq => eval0n n x = [N0 y]
  | Lt => eval0n n x < [N0 y]
  | Gt => eval0n n x > [N0 y]
  end.
  intros n x y.
  unfold comparen_0, to_Z; rewrite spec_gen_eval0n.
  apply spec_compare_mn_1.
  exact (spec_0 w0_spec).
  intros x1; exact (spec_compare w0_spec w_0 x1).
  exact (spec_to_Z w0_spec).
  exact (spec_compare w0_spec).
  exact (spec_compare w0_spec).
  exact (spec_to_Z w0_spec).
  Qed.

 Let spec_compare_1: forall x y,
    match compare_1 x y with 
      Eq => [N1 x] = [N1 y]
    | Lt => [N1 x] < [N1 y]
    | Gt => [N1 x] > [N1 y]
    end.
  Proof.
  unfold compare_1, to_Z; exact (spec_compare w1_spec).
  Qed.

  Let spec_comparen_1:
  forall (n : nat) (x : word w1 n) (y : w1),
  match comparen_1 n x y with
  | Eq => eval1n n x = [N1 y]
  | Lt => eval1n n x < [N1 y]
  | Gt => eval1n n x > [N1 y]
  end.
  intros n x y.
  unfold comparen_1, to_Z; rewrite spec_gen_eval1n.
  apply spec_compare_mn_1.
  exact (spec_0 w1_spec).
  intros x1; exact (spec_compare w1_spec W0 x1).
  exact (spec_to_Z w1_spec).
  exact (spec_compare w1_spec).
  exact (spec_compare w1_spec).
  exact (spec_to_Z w1_spec).
  Qed.

 Let spec_compare_2: forall x y,
    match compare_2 x y with 
      Eq => [N2 x] = [N2 y]
    | Lt => [N2 x] < [N2 y]
    | Gt => [N2 x] > [N2 y]
    end.
  Proof.
  unfold compare_2, to_Z; exact (spec_compare w2_spec).
  Qed.

  Let spec_comparen_2:
  forall (n : nat) (x : word w2 n) (y : w2),
  match comparen_2 n x y with
  | Eq => eval2n n x = [N2 y]
  | Lt => eval2n n x < [N2 y]
  | Gt => eval2n n x > [N2 y]
  end.
  intros n x y.
  unfold comparen_2, to_Z; rewrite spec_gen_eval2n.
  apply spec_compare_mn_1.
  exact (spec_0 w2_spec).
  intros x1; exact (spec_compare w2_spec W0 x1).
  exact (spec_to_Z w2_spec).
  exact (spec_compare w2_spec).
  exact (spec_compare w2_spec).
  exact (spec_to_Z w2_spec).
  Qed.

 Let spec_compare_3: forall x y,
    match compare_3 x y with 
      Eq => [N3 x] = [N3 y]
    | Lt => [N3 x] < [N3 y]
    | Gt => [N3 x] > [N3 y]
    end.
  Proof.
  unfold compare_3, to_Z; exact (spec_compare w3_spec).
  Qed.

  Let spec_comparen_3:
  forall (n : nat) (x : word w3 n) (y : w3),
  match comparen_3 n x y with
  | Eq => eval3n n x = [N3 y]
  | Lt => eval3n n x < [N3 y]
  | Gt => eval3n n x > [N3 y]
  end.
  intros n x y.
  unfold comparen_3, to_Z; rewrite spec_gen_eval3n.
  apply spec_compare_mn_1.
  exact (spec_0 w3_spec).
  intros x1; exact (spec_compare w3_spec W0 x1).
  exact (spec_to_Z w3_spec).
  exact (spec_compare w3_spec).
  exact (spec_compare w3_spec).
  exact (spec_to_Z w3_spec).
  Qed.

 Let spec_compare_4: forall x y,
    match compare_4 x y with 
      Eq => [N4 x] = [N4 y]
    | Lt => [N4 x] < [N4 y]
    | Gt => [N4 x] > [N4 y]
    end.
  Proof.
  unfold compare_4, to_Z; exact (spec_compare w4_spec).
  Qed.

  Let spec_comparen_4:
  forall (n : nat) (x : word w4 n) (y : w4),
  match comparen_4 n x y with
  | Eq => eval4n n x = [N4 y]
  | Lt => eval4n n x < [N4 y]
  | Gt => eval4n n x > [N4 y]
  end.
  intros n x y.
  unfold comparen_4, to_Z; rewrite spec_gen_eval4n.
  apply spec_compare_mn_1.
  exact (spec_0 w4_spec).
  intros x1; exact (spec_compare w4_spec W0 x1).
  exact (spec_to_Z w4_spec).
  exact (spec_compare w4_spec).
  exact (spec_compare w4_spec).
  exact (spec_to_Z w4_spec).
  Qed.

 Let spec_compare_5: forall x y,
    match compare_5 x y with 
      Eq => [N5 x] = [N5 y]
    | Lt => [N5 x] < [N5 y]
    | Gt => [N5 x] > [N5 y]
    end.
  Proof.
  unfold compare_5, to_Z; exact (spec_compare w5_spec).
  Qed.

  Let spec_comparen_5:
  forall (n : nat) (x : word w5 n) (y : w5),
  match comparen_5 n x y with
  | Eq => eval5n n x = [N5 y]
  | Lt => eval5n n x < [N5 y]
  | Gt => eval5n n x > [N5 y]
  end.
  intros n x y.
  unfold comparen_5, to_Z; rewrite spec_gen_eval5n.
  apply spec_compare_mn_1.
  exact (spec_0 w5_spec).
  intros x1; exact (spec_compare w5_spec W0 x1).
  exact (spec_to_Z w5_spec).
  exact (spec_compare w5_spec).
  exact (spec_compare w5_spec).
  exact (spec_to_Z w5_spec).
  Qed.

 Let spec_compare_6: forall x y,
    match compare_6 x y with 
      Eq => [N6 x] = [N6 y]
    | Lt => [N6 x] < [N6 y]
    | Gt => [N6 x] > [N6 y]
    end.
  Proof.
  unfold compare_6, to_Z; exact (spec_compare w6_spec).
  Qed.

  Let spec_comparen_6:
  forall (n : nat) (x : word w6 n) (y : w6),
  match comparen_6 n x y with
  | Eq => eval6n n x = [N6 y]
  | Lt => eval6n n x < [N6 y]
  | Gt => eval6n n x > [N6 y]
  end.
  intros n x y.
  unfold comparen_6, to_Z; rewrite spec_gen_eval6n.
  apply spec_compare_mn_1.
  exact (spec_0 w6_spec).
  intros x1; exact (spec_compare w6_spec W0 x1).
  exact (spec_to_Z w6_spec).
  exact (spec_compare w6_spec).
  exact (spec_compare w6_spec).
  exact (spec_to_Z w6_spec).
  Qed.

 Let spec_opp_compare: forall c (u v: Z),
  match c with Eq => u = v | Lt => u < v | Gt => u > v end ->
  match opp_compare c with Eq => v = u | Lt => v < u | Gt => v > u end.
 Proof.
 intros c u v; case c; unfold opp_compare; auto with zarith.
 Qed.

 Theorem spec_compare: forall x y,
    match compare x y with 
      Eq => [x] = [y]
    | Lt => [x] < [y]
    | Gt => [x] > [y]
    end.
 Proof.
 refine (spec_iter _ (fun x y res => 
                       match res with 
                        Eq => x = y
                      | Lt => x < y
                      | Gt => x > y
                      end)
      compare_0
      (fun n x y => opp_compare (comparen_0 (S n) y x))
      (fun n => comparen_0 (S n)) _ _ _
      compare_1
      (fun n x y => opp_compare (comparen_1 (S n) y x))
      (fun n => comparen_1 (S n)) _ _ _
      compare_2
      (fun n x y => opp_compare (comparen_2 (S n) y x))
      (fun n => comparen_2 (S n)) _ _ _
      compare_3
      (fun n x y => opp_compare (comparen_3 (S n) y x))
      (fun n => comparen_3 (S n)) _ _ _
      compare_4
      (fun n x y => opp_compare (comparen_4 (S n) y x))
      (fun n => comparen_4 (S n)) _ _ _
      compare_5
      (fun n x y => opp_compare (comparen_5 (S n) y x))
      (fun n => comparen_5 (S n)) _ _ _
      compare_6
      (fun n x y => opp_compare (comparen_6 (S n) y x))
      (fun n => comparen_6 (S n)) _ _ _
      comparenm _).
  exact spec_compare_0.
  intros n x y H;apply spec_opp_compare; apply spec_comparen_0.
  intros n x y H; exact (spec_comparen_0 (S n) x y).
  exact spec_compare_1.
  intros n x y H;apply spec_opp_compare; apply spec_comparen_1.
  intros n x y H; exact (spec_comparen_1 (S n) x y).
  exact spec_compare_2.
  intros n x y H;apply spec_opp_compare; apply spec_comparen_2.
  intros n x y H; exact (spec_comparen_2 (S n) x y).
  exact spec_compare_3.
  intros n x y H;apply spec_opp_compare; apply spec_comparen_3.
  intros n x y H; exact (spec_comparen_3 (S n) x y).
  exact spec_compare_4.
  intros n x y H;apply spec_opp_compare; apply spec_comparen_4.
  intros n x y H; exact (spec_comparen_4 (S n) x y).
  exact spec_compare_5.
  intros n x y H;apply spec_opp_compare; apply spec_comparen_5.
  intros n x y H; exact (spec_comparen_5 (S n) x y).
  exact spec_compare_6.
  intros n x y;apply spec_opp_compare; apply spec_comparen_6.
  intros n; exact (spec_comparen_6 (S n)).
  intros n m x y; unfold comparenm.
  rewrite <- (spec_cast_l n m x); rewrite <- (spec_cast_r n m y).
  unfold to_Z; apply (spec_compare  (wn_spec (Max.max n m))).
  Qed.

 Definition eq_bool x y :=
  match compare x y with
  | Eq => true
  | _  => false
  end.

 Theorem spec_eq_bool: forall x y,
    if eq_bool x y then [x] = [y] else [x] <> [y].
 Proof.
 intros x y; unfold eq_bool.
 generalize (spec_compare x y); case compare; auto with zarith.
  Qed.

 (***************************************************************)
 (*                                                             *)
 (*                           Multiplication                    *)
 (*                                                             *)
 (***************************************************************)

 Definition w0_mul_c := w0_op.(znz_mul_c).
 Definition w1_mul_c := w1_op.(znz_mul_c).
 Definition w2_mul_c := w2_op.(znz_mul_c).
 Definition w3_mul_c := w3_op.(znz_mul_c).
 Definition w4_mul_c := w4_op.(znz_mul_c).
 Definition w5_mul_c := w5_op.(znz_mul_c).
 Definition w6_mul_c := w6_op.(znz_mul_c).

 Definition w0_mul_add :=
   Eval lazy beta delta [w_mul_add] in
     @w_mul_add w0 w_0 w0_succ w0_add_c w0_mul_c.
 Definition w1_mul_add :=
   Eval lazy beta delta [w_mul_add] in
     @w_mul_add w1 W0 w1_succ w1_add_c w1_mul_c.
 Definition w2_mul_add :=
   Eval lazy beta delta [w_mul_add] in
     @w_mul_add w2 W0 w2_succ w2_add_c w2_mul_c.
 Definition w3_mul_add :=
   Eval lazy beta delta [w_mul_add] in
     @w_mul_add w3 W0 w3_succ w3_add_c w3_mul_c.
 Definition w4_mul_add :=
   Eval lazy beta delta [w_mul_add] in
     @w_mul_add w4 W0 w4_succ w4_add_c w4_mul_c.
 Definition w5_mul_add :=
   Eval lazy beta delta [w_mul_add] in
     @w_mul_add w5 W0 w5_succ w5_add_c w5_mul_c.
 Definition w6_mul_add :=
   Eval lazy beta delta [w_mul_add] in
     @w_mul_add w6 W0 w6_succ w6_add_c w6_mul_c.

 Definition w0_0W := w0_op.(znz_0W).
 Definition w1_0W := w1_op.(znz_0W).
 Definition w2_0W := w2_op.(znz_0W).
 Definition w3_0W := w3_op.(znz_0W).
 Definition w4_0W := w4_op.(znz_0W).
 Definition w5_0W := w5_op.(znz_0W).
 Definition w6_0W := w6_op.(znz_0W).

 Definition w0_mul_add_n1 :=
  @gen_mul_add_n1 w0 w_0 w0_op.(znz_WW) w0_0W w0_mul_add.
 Definition w1_mul_add_n1 :=
  @gen_mul_add_n1 w1 W0 w1_op.(znz_WW) w1_0W w1_mul_add.
 Definition w2_mul_add_n1 :=
  @gen_mul_add_n1 w2 W0 w2_op.(znz_WW) w2_0W w2_mul_add.
 Definition w3_mul_add_n1 :=
  @gen_mul_add_n1 w3 W0 w3_op.(znz_WW) w3_0W w3_mul_add.
 Definition w4_mul_add_n1 :=
  @gen_mul_add_n1 w4 W0 w4_op.(znz_WW) w4_0W w4_mul_add.
 Definition w5_mul_add_n1 :=
  @gen_mul_add_n1 w5 W0 w5_op.(znz_WW) w5_0W w5_mul_add.
 Definition w6_mul_add_n1 :=
  @gen_mul_add_n1 w6 W0 w6_op.(znz_WW) w6_0W w6_mul_add.

  Let to_Z0 n :=
  match n return word w0 (S n) -> t_ with
  | 0%nat => fun x => N1 x
  | 1%nat => fun x => N2 x
  | 2%nat => fun x => N3 x
  | 3%nat => fun x => N4 x
  | 4%nat => fun x => N5 x
  | 5%nat => fun x => N6 x
  | 6%nat => fun x => Nn 0 x
  | 7%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z1 n :=
  match n return word w1 (S n) -> t_ with
  | 0%nat => fun x => N2 x
  | 1%nat => fun x => N3 x
  | 2%nat => fun x => N4 x
  | 3%nat => fun x => N5 x
  | 4%nat => fun x => N6 x
  | 5%nat => fun x => Nn 0 x
  | 6%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z2 n :=
  match n return word w2 (S n) -> t_ with
  | 0%nat => fun x => N3 x
  | 1%nat => fun x => N4 x
  | 2%nat => fun x => N5 x
  | 3%nat => fun x => N6 x
  | 4%nat => fun x => Nn 0 x
  | 5%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z3 n :=
  match n return word w3 (S n) -> t_ with
  | 0%nat => fun x => N4 x
  | 1%nat => fun x => N5 x
  | 2%nat => fun x => N6 x
  | 3%nat => fun x => Nn 0 x
  | 4%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z4 n :=
  match n return word w4 (S n) -> t_ with
  | 0%nat => fun x => N5 x
  | 1%nat => fun x => N6 x
  | 2%nat => fun x => Nn 0 x
  | 3%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z5 n :=
  match n return word w5 (S n) -> t_ with
  | 0%nat => fun x => N6 x
  | 1%nat => fun x => Nn 0 x
  | 2%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

Theorem to_Z0_spec:
  forall n x, Z_of_nat n <= 7 -> [to_Z0 n x] = znz_to_Z (nmake_op _ w0_op (S n)) x.
 intros n; case n; clear n.
   unfold to_Z0.
   intros x H; rewrite spec_eval0n1; auto.
 intros n; case n; clear n.
   unfold to_Z0.
   intros x H; rewrite spec_eval0n2; auto.
 intros n; case n; clear n.
   unfold to_Z0.
   intros x H; rewrite spec_eval0n3; auto.
 intros n; case n; clear n.
   unfold to_Z0.
   intros x H; rewrite spec_eval0n4; auto.
 intros n; case n; clear n.
   unfold to_Z0.
   intros x H; rewrite spec_eval0n5; auto.
 intros n; case n; clear n.
   unfold to_Z0.
   intros x H; rewrite spec_eval0n6; auto.
 intros n; case n; clear n.
   unfold to_Z0.
   intros x H; rewrite spec_eval0n7; auto.
 intros n; case n; clear n.
   unfold to_Z0.
   intros x H; rewrite spec_eval0n8; auto.
 intros n x.
 repeat rewrite inj_S; unfold Zsucc; auto with zarith.
 Qed.

Theorem to_Z1_spec:
  forall n x, Z_of_nat n <= 6 -> [to_Z1 n x] = znz_to_Z (nmake_op _ w1_op (S n)) x.
 intros n; case n; clear n.
   unfold to_Z1.
   intros x H; rewrite spec_eval1n1; auto.
 intros n; case n; clear n.
   unfold to_Z1.
   intros x H; rewrite spec_eval1n2; auto.
 intros n; case n; clear n.
   unfold to_Z1.
   intros x H; rewrite spec_eval1n3; auto.
 intros n; case n; clear n.
   unfold to_Z1.
   intros x H; rewrite spec_eval1n4; auto.
 intros n; case n; clear n.
   unfold to_Z1.
   intros x H; rewrite spec_eval1n5; auto.
 intros n; case n; clear n.
   unfold to_Z1.
   intros x H; rewrite spec_eval1n6; auto.
 intros n; case n; clear n.
   unfold to_Z1.
   intros x H; rewrite spec_eval1n7; auto.
 intros n x.
 repeat rewrite inj_S; unfold Zsucc; auto with zarith.
 Qed.

Theorem to_Z2_spec:
  forall n x, Z_of_nat n <= 5 -> [to_Z2 n x] = znz_to_Z (nmake_op _ w2_op (S n)) x.
 intros n; case n; clear n.
   unfold to_Z2.
   intros x H; rewrite spec_eval2n1; auto.
 intros n; case n; clear n.
   unfold to_Z2.
   intros x H; rewrite spec_eval2n2; auto.
 intros n; case n; clear n.
   unfold to_Z2.
   intros x H; rewrite spec_eval2n3; auto.
 intros n; case n; clear n.
   unfold to_Z2.
   intros x H; rewrite spec_eval2n4; auto.
 intros n; case n; clear n.
   unfold to_Z2.
   intros x H; rewrite spec_eval2n5; auto.
 intros n; case n; clear n.
   unfold to_Z2.
   intros x H; rewrite spec_eval2n6; auto.
 intros n x.
 repeat rewrite inj_S; unfold Zsucc; auto with zarith.
 Qed.

Theorem to_Z3_spec:
  forall n x, Z_of_nat n <= 4 -> [to_Z3 n x] = znz_to_Z (nmake_op _ w3_op (S n)) x.
 intros n; case n; clear n.
   unfold to_Z3.
   intros x H; rewrite spec_eval3n1; auto.
 intros n; case n; clear n.
   unfold to_Z3.
   intros x H; rewrite spec_eval3n2; auto.
 intros n; case n; clear n.
   unfold to_Z3.
   intros x H; rewrite spec_eval3n3; auto.
 intros n; case n; clear n.
   unfold to_Z3.
   intros x H; rewrite spec_eval3n4; auto.
 intros n; case n; clear n.
   unfold to_Z3.
   intros x H; rewrite spec_eval3n5; auto.
 intros n x.
 repeat rewrite inj_S; unfold Zsucc; auto with zarith.
 Qed.

Theorem to_Z4_spec:
  forall n x, Z_of_nat n <= 3 -> [to_Z4 n x] = znz_to_Z (nmake_op _ w4_op (S n)) x.
 intros n; case n; clear n.
   unfold to_Z4.
   intros x H; rewrite spec_eval4n1; auto.
 intros n; case n; clear n.
   unfold to_Z4.
   intros x H; rewrite spec_eval4n2; auto.
 intros n; case n; clear n.
   unfold to_Z4.
   intros x H; rewrite spec_eval4n3; auto.
 intros n; case n; clear n.
   unfold to_Z4.
   intros x H; rewrite spec_eval4n4; auto.
 intros n x.
 repeat rewrite inj_S; unfold Zsucc; auto with zarith.
 Qed.

Theorem to_Z5_spec:
  forall n x, Z_of_nat n <= 2 -> [to_Z5 n x] = znz_to_Z (nmake_op _ w5_op (S n)) x.
 intros n; case n; clear n.
   unfold to_Z5.
   intros x H; rewrite spec_eval5n1; auto.
 intros n; case n; clear n.
   unfold to_Z5.
   intros x H; rewrite spec_eval5n2; auto.
 intros n; case n; clear n.
   unfold to_Z5.
   intros x H; rewrite spec_eval5n3; auto.
 intros n x.
 repeat rewrite inj_S; unfold Zsucc; auto with zarith.
 Qed.

 Definition w0_mul n x y :=
 let (w,r) := w0_mul_add_n1 (S n) x y w_0 in
 if w0_eq0 w then to_Z0 n r
 else to_Z0 (S n) (WW (extend0 n w) r).

 Definition w1_mul n x y :=
 let (w,r) := w1_mul_add_n1 (S n) x y W0 in
 if w1_eq0 w then to_Z1 n r
 else to_Z1 (S n) (WW (extend1 n w) r).

 Definition w2_mul n x y :=
 let (w,r) := w2_mul_add_n1 (S n) x y W0 in
 if w2_eq0 w then to_Z2 n r
 else to_Z2 (S n) (WW (extend2 n w) r).

 Definition w3_mul n x y :=
 let (w,r) := w3_mul_add_n1 (S n) x y W0 in
 if w3_eq0 w then to_Z3 n r
 else to_Z3 (S n) (WW (extend3 n w) r).

 Definition w4_mul n x y :=
 let (w,r) := w4_mul_add_n1 (S n) x y W0 in
 if w4_eq0 w then to_Z4 n r
 else to_Z4 (S n) (WW (extend4 n w) r).

 Definition w5_mul n x y :=
 let (w,r) := w5_mul_add_n1 (S n) x y W0 in
 if w5_eq0 w then to_Z5 n r
 else to_Z5 (S n) (WW (extend5 n w) r).

 Definition w6_mul n x y :=
 let (w,r) := w6_mul_add_n1 (S n) x y W0 in
 if w6_eq0 w then Nn n r
 else Nn (S n) (WW (extend6 n w) r).

 Definition mulnm n m x y :=
    let mn := Max.max n m in
    let d := diff n m in
    let op := make_op mn in
     reduce_n (S mn) (op.(znz_mul_c)
       (castm (diff_r n m) (extend_tr x (snd d)))
       (castm (diff_l n m) (extend_tr y (fst d)))).

 Definition mul := Eval lazy beta delta [iter0] in 
  (iter0 t_ 
    (fun x y => reduce_1 (w0_mul_c x y)) 
    (fun n x y => w0_mul n y x)
    w0_mul
    (fun x y => reduce_2 (w1_mul_c x y)) 
    (fun n x y => w1_mul n y x)
    w1_mul
    (fun x y => reduce_3 (w2_mul_c x y)) 
    (fun n x y => w2_mul n y x)
    w2_mul
    (fun x y => reduce_4 (w3_mul_c x y)) 
    (fun n x y => w3_mul n y x)
    w3_mul
    (fun x y => reduce_5 (w4_mul_c x y)) 
    (fun n x y => w4_mul n y x)
    w4_mul
    (fun x y => reduce_6 (w5_mul_c x y)) 
    (fun n x y => w5_mul n y x)
    w5_mul
    (fun x y => reduce_7 (w6_mul_c x y)) 
    (fun n x y => w6_mul n y x)
    w6_mul
    mulnm
    (fun _ => N0 w_0)
    (fun _ => N0 w_0)
  ).

 Let spec_w0_mul_add: forall x y z,
  let (q,r) := w0_mul_add x y z in
  znz_to_Z w0_op q * (base (znz_digits w0_op))  +  znz_to_Z w0_op r =
  znz_to_Z w0_op x * znz_to_Z w0_op y + znz_to_Z w0_op z :=
   (spec_mul_add w0_spec).

 Let spec_w1_mul_add: forall x y z,
  let (q,r) := w1_mul_add x y z in
  znz_to_Z w1_op q * (base (znz_digits w1_op))  +  znz_to_Z w1_op r =
  znz_to_Z w1_op x * znz_to_Z w1_op y + znz_to_Z w1_op z :=
   (spec_mul_add w1_spec).

 Let spec_w2_mul_add: forall x y z,
  let (q,r) := w2_mul_add x y z in
  znz_to_Z w2_op q * (base (znz_digits w2_op))  +  znz_to_Z w2_op r =
  znz_to_Z w2_op x * znz_to_Z w2_op y + znz_to_Z w2_op z :=
   (spec_mul_add w2_spec).

 Let spec_w3_mul_add: forall x y z,
  let (q,r) := w3_mul_add x y z in
  znz_to_Z w3_op q * (base (znz_digits w3_op))  +  znz_to_Z w3_op r =
  znz_to_Z w3_op x * znz_to_Z w3_op y + znz_to_Z w3_op z :=
   (spec_mul_add w3_spec).

 Let spec_w4_mul_add: forall x y z,
  let (q,r) := w4_mul_add x y z in
  znz_to_Z w4_op q * (base (znz_digits w4_op))  +  znz_to_Z w4_op r =
  znz_to_Z w4_op x * znz_to_Z w4_op y + znz_to_Z w4_op z :=
   (spec_mul_add w4_spec).

 Let spec_w5_mul_add: forall x y z,
  let (q,r) := w5_mul_add x y z in
  znz_to_Z w5_op q * (base (znz_digits w5_op))  +  znz_to_Z w5_op r =
  znz_to_Z w5_op x * znz_to_Z w5_op y + znz_to_Z w5_op z :=
   (spec_mul_add w5_spec).

 Let spec_w6_mul_add: forall x y z,
  let (q,r) := w6_mul_add x y z in
  znz_to_Z w6_op q * (base (znz_digits w6_op))  +  znz_to_Z w6_op r =
  znz_to_Z w6_op x * znz_to_Z w6_op y + znz_to_Z w6_op z :=
   (spec_mul_add w6_spec).

 Theorem spec_w0_mul_add_n1: forall n x y z,
  let (q,r) := w0_mul_add_n1 n x y z in
  znz_to_Z w0_op q * (base (znz_digits (nmake_op _ w0_op n)))  +
  znz_to_Z (nmake_op _ w0_op n) r =
  znz_to_Z (nmake_op _ w0_op n) x * znz_to_Z w0_op y +
  znz_to_Z w0_op z.
 Proof.
 intros n x y z; unfold w0_mul_add_n1.
 rewrite nmake_gen.
 rewrite digits_gend.
 change (base (GenBase.gen_digits (znz_digits w0_op) n)) with
        (GenBase.gen_wB (znz_digits w0_op) n).
 apply spec_gen_mul_add_n1; auto.
 exact (spec_0 w0_spec).
 exact (spec_WW w0_spec).
 exact (spec_0W w0_spec).
 exact (spec_mul_add w0_spec).
 Qed.

 Theorem spec_w1_mul_add_n1: forall n x y z,
  let (q,r) := w1_mul_add_n1 n x y z in
  znz_to_Z w1_op q * (base (znz_digits (nmake_op _ w1_op n)))  +
  znz_to_Z (nmake_op _ w1_op n) r =
  znz_to_Z (nmake_op _ w1_op n) x * znz_to_Z w1_op y +
  znz_to_Z w1_op z.
 Proof.
 intros n x y z; unfold w1_mul_add_n1.
 rewrite nmake_gen.
 rewrite digits_gend.
 change (base (GenBase.gen_digits (znz_digits w1_op) n)) with
        (GenBase.gen_wB (znz_digits w1_op) n).
 apply spec_gen_mul_add_n1; auto.
 exact (spec_WW w1_spec).
 exact (spec_0W w1_spec).
 exact (spec_mul_add w1_spec).
 Qed.

 Theorem spec_w2_mul_add_n1: forall n x y z,
  let (q,r) := w2_mul_add_n1 n x y z in
  znz_to_Z w2_op q * (base (znz_digits (nmake_op _ w2_op n)))  +
  znz_to_Z (nmake_op _ w2_op n) r =
  znz_to_Z (nmake_op _ w2_op n) x * znz_to_Z w2_op y +
  znz_to_Z w2_op z.
 Proof.
 intros n x y z; unfold w2_mul_add_n1.
 rewrite nmake_gen.
 rewrite digits_gend.
 change (base (GenBase.gen_digits (znz_digits w2_op) n)) with
        (GenBase.gen_wB (znz_digits w2_op) n).
 apply spec_gen_mul_add_n1; auto.
 exact (spec_WW w2_spec).
 exact (spec_0W w2_spec).
 exact (spec_mul_add w2_spec).
 Qed.

 Theorem spec_w3_mul_add_n1: forall n x y z,
  let (q,r) := w3_mul_add_n1 n x y z in
  znz_to_Z w3_op q * (base (znz_digits (nmake_op _ w3_op n)))  +
  znz_to_Z (nmake_op _ w3_op n) r =
  znz_to_Z (nmake_op _ w3_op n) x * znz_to_Z w3_op y +
  znz_to_Z w3_op z.
 Proof.
 intros n x y z; unfold w3_mul_add_n1.
 rewrite nmake_gen.
 rewrite digits_gend.
 change (base (GenBase.gen_digits (znz_digits w3_op) n)) with
        (GenBase.gen_wB (znz_digits w3_op) n).
 apply spec_gen_mul_add_n1; auto.
 exact (spec_WW w3_spec).
 exact (spec_0W w3_spec).
 exact (spec_mul_add w3_spec).
 Qed.

 Theorem spec_w4_mul_add_n1: forall n x y z,
  let (q,r) := w4_mul_add_n1 n x y z in
  znz_to_Z w4_op q * (base (znz_digits (nmake_op _ w4_op n)))  +
  znz_to_Z (nmake_op _ w4_op n) r =
  znz_to_Z (nmake_op _ w4_op n) x * znz_to_Z w4_op y +
  znz_to_Z w4_op z.
 Proof.
 intros n x y z; unfold w4_mul_add_n1.
 rewrite nmake_gen.
 rewrite digits_gend.
 change (base (GenBase.gen_digits (znz_digits w4_op) n)) with
        (GenBase.gen_wB (znz_digits w4_op) n).
 apply spec_gen_mul_add_n1; auto.
 exact (spec_WW w4_spec).
 exact (spec_0W w4_spec).
 exact (spec_mul_add w4_spec).
 Qed.

 Theorem spec_w5_mul_add_n1: forall n x y z,
  let (q,r) := w5_mul_add_n1 n x y z in
  znz_to_Z w5_op q * (base (znz_digits (nmake_op _ w5_op n)))  +
  znz_to_Z (nmake_op _ w5_op n) r =
  znz_to_Z (nmake_op _ w5_op n) x * znz_to_Z w5_op y +
  znz_to_Z w5_op z.
 Proof.
 intros n x y z; unfold w5_mul_add_n1.
 rewrite nmake_gen.
 rewrite digits_gend.
 change (base (GenBase.gen_digits (znz_digits w5_op) n)) with
        (GenBase.gen_wB (znz_digits w5_op) n).
 apply spec_gen_mul_add_n1; auto.
 exact (spec_WW w5_spec).
 exact (spec_0W w5_spec).
 exact (spec_mul_add w5_spec).
 Qed.

 Theorem spec_w6_mul_add_n1: forall n x y z,
  let (q,r) := w6_mul_add_n1 n x y z in
  znz_to_Z w6_op q * (base (znz_digits (nmake_op _ w6_op n)))  +
  znz_to_Z (nmake_op _ w6_op n) r =
  znz_to_Z (nmake_op _ w6_op n) x * znz_to_Z w6_op y +
  znz_to_Z w6_op z.
 Proof.
 intros n x y z; unfold w6_mul_add_n1.
 rewrite nmake_gen.
 rewrite digits_gend.
 change (base (GenBase.gen_digits (znz_digits w6_op) n)) with
        (GenBase.gen_wB (znz_digits w6_op) n).
 apply spec_gen_mul_add_n1; auto.
 exact (spec_WW w6_spec).
 exact (spec_0W w6_spec).
 exact (spec_mul_add w6_spec).
 Qed.

  Lemma nmake_op_WW: forall ww ww1 n x y,
    znz_to_Z (nmake_op ww ww1 (S n)) (WW x y) =
    znz_to_Z (nmake_op ww ww1 n) x * base (znz_digits (nmake_op ww ww1 n)) +
    znz_to_Z (nmake_op ww ww1 n) y.
    auto.
  Qed.

  Lemma extend0n_spec: forall n x1,
  znz_to_Z (nmake_op _ w0_op (S n)) (extend0 n x1) = 
  znz_to_Z w0_op x1.
  Proof.
    intros n1 x2; rewrite nmake_gen.
    unfold extend0.
    rewrite GenBase.spec_extend; auto.
    intros l; simpl; unfold w_0; rewrite (spec_0 w0_spec); ring.
  Qed.

  Lemma extend1n_spec: forall n x1,
  znz_to_Z (nmake_op _ w1_op (S n)) (extend1 n x1) = 
  znz_to_Z w1_op x1.
  Proof.
    intros n1 x2; rewrite nmake_gen.
    unfold extend1.
    rewrite GenBase.spec_extend; auto.
  Qed.

  Lemma extend2n_spec: forall n x1,
  znz_to_Z (nmake_op _ w2_op (S n)) (extend2 n x1) = 
  znz_to_Z w2_op x1.
  Proof.
    intros n1 x2; rewrite nmake_gen.
    unfold extend2.
    rewrite GenBase.spec_extend; auto.
  Qed.

  Lemma extend3n_spec: forall n x1,
  znz_to_Z (nmake_op _ w3_op (S n)) (extend3 n x1) = 
  znz_to_Z w3_op x1.
  Proof.
    intros n1 x2; rewrite nmake_gen.
    unfold extend3.
    rewrite GenBase.spec_extend; auto.
  Qed.

  Lemma extend4n_spec: forall n x1,
  znz_to_Z (nmake_op _ w4_op (S n)) (extend4 n x1) = 
  znz_to_Z w4_op x1.
  Proof.
    intros n1 x2; rewrite nmake_gen.
    unfold extend4.
    rewrite GenBase.spec_extend; auto.
  Qed.

  Lemma extend5n_spec: forall n x1,
  znz_to_Z (nmake_op _ w5_op (S n)) (extend5 n x1) = 
  znz_to_Z w5_op x1.
  Proof.
    intros n1 x2; rewrite nmake_gen.
    unfold extend5.
    rewrite GenBase.spec_extend; auto.
  Qed.

  Lemma extend6n_spec: forall n x1,
  znz_to_Z (nmake_op _ w6_op (S n)) (extend6 n x1) = 
  znz_to_Z w6_op x1.
  Proof.
    intros n1 x2; rewrite nmake_gen.
    unfold extend6.
    rewrite GenBase.spec_extend; auto.
  Qed.

  Lemma spec_muln:
    forall n (x: word _ (S n)) y,
     [Nn (S n) (znz_mul_c (make_op n) x y)] = [Nn n x] * [Nn n y].
  Proof.
    intros n x y; unfold to_Z.
    rewrite <- (spec_mul_c (wn_spec n)).
    rewrite make_op_S.
    case znz_mul_c; auto.
  Qed.
  Theorem spec_mul: forall x y, [mul x y] = [x] * [y].
  Proof.
    assert(F0: 
    forall n x y,
    Z_of_nat n <= 6 ->     [w0_mul n x y] = eval0n (S n) x * [N0 y]).
    intros n x y H; unfold w0_mul.
    generalize (spec_w0_mul_add_n1 (S n) x y w_0).
    case w0_mul_add_n1; intros x1 y1.
    change (znz_to_Z (nmake_op _ w0_op (S n)) x) with (eval0n (S n) x).
    change (znz_to_Z w0_op y) with ([N0 y]).
    unfold w_0; rewrite (spec_0 w0_spec); rewrite Zplus_0_r.
    intros H1; rewrite <- H1; clear H1.
    generalize (spec_w0_eq0 x1); case w0_eq0; intros HH.
    unfold to_Z in HH; rewrite HH.
    rewrite to_Z0_spec; auto with zarith.
    rewrite to_Z0_spec; try (rewrite inj_S; auto with zarith).
    rewrite nmake_op_WW; rewrite extend0n_spec; auto.
    assert(F1: 
    forall n x y,
    Z_of_nat n <= 5 ->     [w1_mul n x y] = eval1n (S n) x * [N1 y]).
    intros n x y H; unfold w1_mul.
    generalize (spec_w1_mul_add_n1 (S n) x y W0).
    case w1_mul_add_n1; intros x1 y1.
    change (znz_to_Z (nmake_op _ w1_op (S n)) x) with (eval1n (S n) x).
    change (znz_to_Z w1_op y) with ([N1 y]).
    change (znz_to_Z w1_op W0) with 0; rewrite Zplus_0_r.
    intros H1; rewrite <- H1; clear H1.
    generalize (spec_w1_eq0 x1); case w1_eq0; intros HH.
    unfold to_Z in HH; rewrite HH.
    rewrite to_Z1_spec; auto with zarith.
    rewrite to_Z1_spec; try (rewrite inj_S; auto with zarith).
    rewrite nmake_op_WW; rewrite extend1n_spec; auto.
    assert(F2: 
    forall n x y,
    Z_of_nat n <= 4 ->     [w2_mul n x y] = eval2n (S n) x * [N2 y]).
    intros n x y H; unfold w2_mul.
    generalize (spec_w2_mul_add_n1 (S n) x y W0).
    case w2_mul_add_n1; intros x1 y1.
    change (znz_to_Z (nmake_op _ w2_op (S n)) x) with (eval2n (S n) x).
    change (znz_to_Z w2_op y) with ([N2 y]).
    change (znz_to_Z w2_op W0) with 0; rewrite Zplus_0_r.
    intros H1; rewrite <- H1; clear H1.
    generalize (spec_w2_eq0 x1); case w2_eq0; intros HH.
    unfold to_Z in HH; rewrite HH.
    rewrite to_Z2_spec; auto with zarith.
    rewrite to_Z2_spec; try (rewrite inj_S; auto with zarith).
    rewrite nmake_op_WW; rewrite extend2n_spec; auto.
    assert(F3: 
    forall n x y,
    Z_of_nat n <= 3 ->     [w3_mul n x y] = eval3n (S n) x * [N3 y]).
    intros n x y H; unfold w3_mul.
    generalize (spec_w3_mul_add_n1 (S n) x y W0).
    case w3_mul_add_n1; intros x1 y1.
    change (znz_to_Z (nmake_op _ w3_op (S n)) x) with (eval3n (S n) x).
    change (znz_to_Z w3_op y) with ([N3 y]).
    change (znz_to_Z w3_op W0) with 0; rewrite Zplus_0_r.
    intros H1; rewrite <- H1; clear H1.
    generalize (spec_w3_eq0 x1); case w3_eq0; intros HH.
    unfold to_Z in HH; rewrite HH.
    rewrite to_Z3_spec; auto with zarith.
    rewrite to_Z3_spec; try (rewrite inj_S; auto with zarith).
    rewrite nmake_op_WW; rewrite extend3n_spec; auto.
    assert(F4: 
    forall n x y,
    Z_of_nat n <= 2 ->     [w4_mul n x y] = eval4n (S n) x * [N4 y]).
    intros n x y H; unfold w4_mul.
    generalize (spec_w4_mul_add_n1 (S n) x y W0).
    case w4_mul_add_n1; intros x1 y1.
    change (znz_to_Z (nmake_op _ w4_op (S n)) x) with (eval4n (S n) x).
    change (znz_to_Z w4_op y) with ([N4 y]).
    change (znz_to_Z w4_op W0) with 0; rewrite Zplus_0_r.
    intros H1; rewrite <- H1; clear H1.
    generalize (spec_w4_eq0 x1); case w4_eq0; intros HH.
    unfold to_Z in HH; rewrite HH.
    rewrite to_Z4_spec; auto with zarith.
    rewrite to_Z4_spec; try (rewrite inj_S; auto with zarith).
    rewrite nmake_op_WW; rewrite extend4n_spec; auto.
    assert(F5: 
    forall n x y,
    Z_of_nat n <= 1 ->     [w5_mul n x y] = eval5n (S n) x * [N5 y]).
    intros n x y H; unfold w5_mul.
    generalize (spec_w5_mul_add_n1 (S n) x y W0).
    case w5_mul_add_n1; intros x1 y1.
    change (znz_to_Z (nmake_op _ w5_op (S n)) x) with (eval5n (S n) x).
    change (znz_to_Z w5_op y) with ([N5 y]).
    change (znz_to_Z w5_op W0) with 0; rewrite Zplus_0_r.
    intros H1; rewrite <- H1; clear H1.
    generalize (spec_w5_eq0 x1); case w5_eq0; intros HH.
    unfold to_Z in HH; rewrite HH.
    rewrite to_Z5_spec; auto with zarith.
    rewrite to_Z5_spec; try (rewrite inj_S; auto with zarith).
    rewrite nmake_op_WW; rewrite extend5n_spec; auto.
    assert(F6: 
    forall n x y,
    [w6_mul n x y] = eval6n (S n) x * [N6 y]).
    intros n x y; unfold w6_mul.
    generalize (spec_w6_mul_add_n1 (S n) x y W0).
    case w6_mul_add_n1; intros x1 y1.
    change (znz_to_Z (nmake_op _ w6_op (S n)) x) with (eval6n (S n) x).
    change (znz_to_Z w6_op y) with ([N6 y]).
    change (znz_to_Z w6_op W0) with 0; rewrite Zplus_0_r.
    intros H1; rewrite <- H1; clear H1.
    generalize (spec_w6_eq0 x1); case w6_eq0; intros HH.
    unfold to_Z in HH; rewrite HH.
    rewrite spec_eval6n; unfold eval6n, nmake_op6; auto.
    rewrite spec_eval6n; unfold eval6n, nmake_op6.
    rewrite nmake_op_WW; rewrite extend6n_spec; auto.
    refine (spec_iter0 t_ (fun x y res => [res] = x * y)
    (fun x y => reduce_1 (w0_mul_c x y)) 
    (fun n x y => w0_mul n y x)
    w0_mul _ _ _
    (fun x y => reduce_2 (w1_mul_c x y)) 
    (fun n x y => w1_mul n y x)
    w1_mul _ _ _
    (fun x y => reduce_3 (w2_mul_c x y)) 
    (fun n x y => w2_mul n y x)
    w2_mul _ _ _
    (fun x y => reduce_4 (w3_mul_c x y)) 
    (fun n x y => w3_mul n y x)
    w3_mul _ _ _
    (fun x y => reduce_5 (w4_mul_c x y)) 
    (fun n x y => w4_mul n y x)
    w4_mul _ _ _
    (fun x y => reduce_6 (w5_mul_c x y)) 
    (fun n x y => w5_mul n y x)
    w5_mul _ _ _
    (fun x y => reduce_7 (w6_mul_c x y)) 
    (fun n x y => w6_mul n y x)
    w6_mul _ _ _
    mulnm _
    (fun _ => N0 w_0) _
    (fun _ => N0 w_0) _
  ).
    intros x y; rewrite spec_reduce_1.
    unfold w0_mul_c, to_Z.
    generalize (spec_mul_c w0_spec x y).
    intros HH; rewrite <- HH; clear HH; auto.
    intros n x y H; rewrite F0; auto with zarith.
    intros n x y H; rewrite F0; auto with zarith. 
    intros x y; rewrite spec_reduce_2.
    unfold w1_mul_c, to_Z.
    generalize (spec_mul_c w1_spec x y).
    intros HH; rewrite <- HH; clear HH; auto.
    intros n x y H; rewrite F1; auto with zarith.
    intros n x y H; rewrite F1; auto with zarith. 
    intros x y; rewrite spec_reduce_3.
    unfold w2_mul_c, to_Z.
    generalize (spec_mul_c w2_spec x y).
    intros HH; rewrite <- HH; clear HH; auto.
    intros n x y H; rewrite F2; auto with zarith.
    intros n x y H; rewrite F2; auto with zarith. 
    intros x y; rewrite spec_reduce_4.
    unfold w3_mul_c, to_Z.
    generalize (spec_mul_c w3_spec x y).
    intros HH; rewrite <- HH; clear HH; auto.
    intros n x y H; rewrite F3; auto with zarith.
    intros n x y H; rewrite F3; auto with zarith. 
    intros x y; rewrite spec_reduce_5.
    unfold w4_mul_c, to_Z.
    generalize (spec_mul_c w4_spec x y).
    intros HH; rewrite <- HH; clear HH; auto.
    intros n x y H; rewrite F4; auto with zarith.
    intros n x y H; rewrite F4; auto with zarith. 
    intros x y; rewrite spec_reduce_6.
    unfold w5_mul_c, to_Z.
    generalize (spec_mul_c w5_spec x y).
    intros HH; rewrite <- HH; clear HH; auto.
    intros n x y H; rewrite F5; auto with zarith.
    intros n x y H; rewrite F5; auto with zarith. 
    intros x y; rewrite spec_reduce_7.
    unfold w6_mul_c, to_Z.
    generalize (spec_mul_c w6_spec x y).
    intros HH; rewrite <- HH; clear HH; auto.
    intros n x y; rewrite F6; auto with zarith.
    intros n x y; rewrite F6; auto with zarith. 
    intros n m x y; unfold mulnm.
    rewrite spec_reduce_n.
    rewrite <- (spec_cast_l n m x).
    rewrite <- (spec_cast_r n m y).
    rewrite spec_muln; rewrite spec_cast_l; rewrite spec_cast_r; auto.
    intros x; unfold to_Z, w_0; rewrite (spec_0 w0_spec); ring.
    intros x; unfold to_Z, w_0; rewrite (spec_0 w0_spec); ring.
  Qed.

 (***************************************************************)
 (*                                                             *)
 (*                           Square                            *)
 (*                                                             *)
 (***************************************************************)

 Definition w0_square_c := w0_op.(znz_square_c).
 Definition w1_square_c := w1_op.(znz_square_c).
 Definition w2_square_c := w2_op.(znz_square_c).
 Definition w3_square_c := w3_op.(znz_square_c).
 Definition w4_square_c := w4_op.(znz_square_c).
 Definition w5_square_c := w5_op.(znz_square_c).
 Definition w6_square_c := w6_op.(znz_square_c).

 Definition square x :=
  match x with
  | N0 wx => reduce_1 (w0_square_c wx)
  | N1 wx => N2 (w1_square_c wx)
  | N2 wx => N3 (w2_square_c wx)
  | N3 wx => N4 (w3_square_c wx)
  | N4 wx => N5 (w4_square_c wx)
  | N5 wx => N6 (w5_square_c wx)
  | N6 wx => Nn 0 (w6_square_c wx)
  | Nn n wx =>
    let op := make_op n in
    Nn (S n) (op.(znz_square_c) wx)
  end.

 Theorem spec_square: forall x, [square x] = [x] * [x].
 Proof.
  intros x; case x; unfold square; clear x.
  intros x; rewrite spec_reduce_1; unfold to_Z.
   exact (spec_square_c w0_spec x).
  intros x; unfold to_Z.
    exact (spec_square_c w1_spec x).
  intros x; unfold to_Z.
    exact (spec_square_c w2_spec x).
  intros x; unfold to_Z.
    exact (spec_square_c w3_spec x).
  intros x; unfold to_Z.
    exact (spec_square_c w4_spec x).
  intros x; unfold to_Z.
    exact (spec_square_c w5_spec x).
  intros x; unfold to_Z.
    exact (spec_square_c w6_spec x).
  intros n x; unfold to_Z.
    rewrite make_op_S.
    exact (spec_square_c (wn_spec n) x).
Qed.

 (***************************************************************)
 (*                                                             *)
 (*                           Power                             *)
 (*                                                             *)
 (***************************************************************)

 Fixpoint power_pos (x:t) (p:positive) {struct p} : t :=
  match p with
  | xH => x
  | xO p => square (power_pos x p)
  | xI p => mul (square (power_pos x p)) x
  end.

 Theorem spec_power_pos: forall x n, [power_pos x n] = [x] ^ Zpos n.
 Proof.
 intros x n; generalize x; elim n; clear n x; simpl power_pos.
 intros; rewrite spec_mul; rewrite spec_square; rewrite H.
 rewrite Zpos_xI; rewrite Zpower_exp; auto with zarith.
 rewrite (Zmult_comm 2); rewrite Zpower_mult; auto with zarith.
 rewrite Zpower_2; rewrite Zpower_1_r; auto.
 intros; rewrite spec_square; rewrite H.
 rewrite Zpos_xO; auto with zarith.
 rewrite (Zmult_comm 2); rewrite Zpower_mult; auto with zarith.
 rewrite Zpower_2; auto.
 intros; rewrite Zpower_1_r; auto.
 Qed.


 (***************************************************************)
 (*                                                             *)
 (*                           Square root                       *)
 (*                                                             *)
 (***************************************************************)

 Definition w0_sqrt := w0_op.(znz_sqrt).
 Definition w1_sqrt := w1_op.(znz_sqrt).
 Definition w2_sqrt := w2_op.(znz_sqrt).
 Definition w3_sqrt := w3_op.(znz_sqrt).
 Definition w4_sqrt := w4_op.(znz_sqrt).
 Definition w5_sqrt := w5_op.(znz_sqrt).
 Definition w6_sqrt := w6_op.(znz_sqrt).

 Definition sqrt x :=
  match x with
  | N0 wx => reduce_0 (w0_sqrt wx)
  | N1 wx => reduce_1 (w1_sqrt wx)
  | N2 wx => reduce_2 (w2_sqrt wx)
  | N3 wx => reduce_3 (w3_sqrt wx)
  | N4 wx => reduce_4 (w4_sqrt wx)
  | N5 wx => reduce_5 (w5_sqrt wx)
  | N6 wx => reduce_6 (w6_sqrt wx)
  | Nn n wx =>
    let op := make_op n in
    reduce_n n (op.(znz_sqrt) wx)
  end.

 Theorem spec_sqrt: forall x, [sqrt x] ^ 2 <= [x] < ([sqrt x] + 1) ^ 2.
 Proof.
 intros x; unfold sqrt; case x; clear x.
 intros x; rewrite spec_reduce_0; exact (spec_sqrt w0_spec x).
 intros x; rewrite spec_reduce_1; exact (spec_sqrt w1_spec x).
 intros x; rewrite spec_reduce_2; exact (spec_sqrt w2_spec x).
 intros x; rewrite spec_reduce_3; exact (spec_sqrt w3_spec x).
 intros x; rewrite spec_reduce_4; exact (spec_sqrt w4_spec x).
 intros x; rewrite spec_reduce_5; exact (spec_sqrt w5_spec x).
 intros x; rewrite spec_reduce_6; exact (spec_sqrt w6_spec x).
 intros n x; rewrite spec_reduce_n; exact (spec_sqrt (wn_spec n) x).
 Qed.

 (***************************************************************)
 (*                                                             *)
 (*                           Division                          *)
 (*                                                             *)
 (***************************************************************)

 Definition w0_div_gt := w0_op.(znz_div_gt).
 Definition w1_div_gt := w1_op.(znz_div_gt).
 Definition w2_div_gt := w2_op.(znz_div_gt).
 Definition w3_div_gt := w3_op.(znz_div_gt).
 Definition w4_div_gt := w4_op.(znz_div_gt).
 Definition w5_div_gt := w5_op.(znz_div_gt).
 Definition w6_div_gt := w6_op.(znz_div_gt).

 Let spec_divn1 ww (ww_op: znz_op ww) (ww_spec: znz_spec ww_op) := 
   (spec_gen_divn1 
    ww_op.(znz_zdigits) ww_op.(znz_0)
    ww_op.(znz_WW) ww_op.(znz_head0)
    ww_op.(znz_add_mul_div) ww_op.(znz_div21)
    ww_op.(znz_compare) ww_op.(znz_sub) (znz_to_Z ww_op)
    (spec_to_Z ww_spec) 
    (spec_zdigits ww_spec)
   (spec_0 ww_spec) (spec_WW ww_spec) (spec_head0 ww_spec)
   (spec_add_mul_div ww_spec) (spec_div21 ww_spec) 
    (ZnZ.spec_compare ww_spec) (ZnZ.spec_sub ww_spec)).
  
 Definition w0_divn1 n x y :=
  let (u, v) :=
  gen_divn1 w0_op.(znz_zdigits) w0_op.(znz_0)
    w0_op.(znz_WW) w0_op.(znz_head0)
    w0_op.(znz_add_mul_div) w0_op.(znz_div21)
    w0_op.(znz_compare) w0_op.(znz_sub) (S n) x y in
   (to_Z0 _ u, N0 v).
 Definition w1_divn1 n x y :=
  let (u, v) :=
  gen_divn1 w1_op.(znz_zdigits) w1_op.(znz_0)
    w1_op.(znz_WW) w1_op.(znz_head0)
    w1_op.(znz_add_mul_div) w1_op.(znz_div21)
    w1_op.(znz_compare) w1_op.(znz_sub) (S n) x y in
   (to_Z1 _ u, N1 v).
 Definition w2_divn1 n x y :=
  let (u, v) :=
  gen_divn1 w2_op.(znz_zdigits) w2_op.(znz_0)
    w2_op.(znz_WW) w2_op.(znz_head0)
    w2_op.(znz_add_mul_div) w2_op.(znz_div21)
    w2_op.(znz_compare) w2_op.(znz_sub) (S n) x y in
   (to_Z2 _ u, N2 v).
 Definition w3_divn1 n x y :=
  let (u, v) :=
  gen_divn1 w3_op.(znz_zdigits) w3_op.(znz_0)
    w3_op.(znz_WW) w3_op.(znz_head0)
    w3_op.(znz_add_mul_div) w3_op.(znz_div21)
    w3_op.(znz_compare) w3_op.(znz_sub) (S n) x y in
   (to_Z3 _ u, N3 v).
 Definition w4_divn1 n x y :=
  let (u, v) :=
  gen_divn1 w4_op.(znz_zdigits) w4_op.(znz_0)
    w4_op.(znz_WW) w4_op.(znz_head0)
    w4_op.(znz_add_mul_div) w4_op.(znz_div21)
    w4_op.(znz_compare) w4_op.(znz_sub) (S n) x y in
   (to_Z4 _ u, N4 v).
 Definition w5_divn1 n x y :=
  let (u, v) :=
  gen_divn1 w5_op.(znz_zdigits) w5_op.(znz_0)
    w5_op.(znz_WW) w5_op.(znz_head0)
    w5_op.(znz_add_mul_div) w5_op.(znz_div21)
    w5_op.(znz_compare) w5_op.(znz_sub) (S n) x y in
   (to_Z5 _ u, N5 v).
 Definition w6_divn1 n x y :=
  let (u, v) :=
  gen_divn1 w6_op.(znz_zdigits) w6_op.(znz_0)
    w6_op.(znz_WW) w6_op.(znz_head0)
    w6_op.(znz_add_mul_div) w6_op.(znz_div21)
    w6_op.(znz_compare) w6_op.(znz_sub) (S n) x y in
   (Nn _ u, N6 v).

 Lemma spec_get_end0: forall n x y,
    eval0n n x  <= [N0 y] -> 
     [N0 (GenBase.get_low w_0 n x)] = eval0n n x.
 Proof.
 intros n x y H.
 rewrite spec_gen_eval0n; unfold to_Z.
 apply GenBase.spec_get_low.
 exact (spec_0 w0_spec).
 exact (spec_to_Z w0_spec).
 apply Zle_lt_trans with [N0 y]; auto.
   rewrite <- spec_gen_eval0n; auto.
 unfold to_Z; case (spec_to_Z w0_spec y); auto.
 Qed.

 Lemma spec_get_end1: forall n x y,
    eval1n n x  <= [N1 y] -> 
     [N1 (GenBase.get_low W0 n x)] = eval1n n x.
 Proof.
 intros n x y H.
 rewrite spec_gen_eval1n; unfold to_Z.
 apply GenBase.spec_get_low.
 exact (spec_0 w1_spec).
 exact (spec_to_Z w1_spec).
 apply Zle_lt_trans with [N1 y]; auto.
   rewrite <- spec_gen_eval1n; auto.
 unfold to_Z; case (spec_to_Z w1_spec y); auto.
 Qed.

 Lemma spec_get_end2: forall n x y,
    eval2n n x  <= [N2 y] -> 
     [N2 (GenBase.get_low W0 n x)] = eval2n n x.
 Proof.
 intros n x y H.
 rewrite spec_gen_eval2n; unfold to_Z.
 apply GenBase.spec_get_low.
 exact (spec_0 w2_spec).
 exact (spec_to_Z w2_spec).
 apply Zle_lt_trans with [N2 y]; auto.
   rewrite <- spec_gen_eval2n; auto.
 unfold to_Z; case (spec_to_Z w2_spec y); auto.
 Qed.

 Lemma spec_get_end3: forall n x y,
    eval3n n x  <= [N3 y] -> 
     [N3 (GenBase.get_low W0 n x)] = eval3n n x.
 Proof.
 intros n x y H.
 rewrite spec_gen_eval3n; unfold to_Z.
 apply GenBase.spec_get_low.
 exact (spec_0 w3_spec).
 exact (spec_to_Z w3_spec).
 apply Zle_lt_trans with [N3 y]; auto.
   rewrite <- spec_gen_eval3n; auto.
 unfold to_Z; case (spec_to_Z w3_spec y); auto.
 Qed.

 Lemma spec_get_end4: forall n x y,
    eval4n n x  <= [N4 y] -> 
     [N4 (GenBase.get_low W0 n x)] = eval4n n x.
 Proof.
 intros n x y H.
 rewrite spec_gen_eval4n; unfold to_Z.
 apply GenBase.spec_get_low.
 exact (spec_0 w4_spec).
 exact (spec_to_Z w4_spec).
 apply Zle_lt_trans with [N4 y]; auto.
   rewrite <- spec_gen_eval4n; auto.
 unfold to_Z; case (spec_to_Z w4_spec y); auto.
 Qed.

 Lemma spec_get_end5: forall n x y,
    eval5n n x  <= [N5 y] -> 
     [N5 (GenBase.get_low W0 n x)] = eval5n n x.
 Proof.
 intros n x y H.
 rewrite spec_gen_eval5n; unfold to_Z.
 apply GenBase.spec_get_low.
 exact (spec_0 w5_spec).
 exact (spec_to_Z w5_spec).
 apply Zle_lt_trans with [N5 y]; auto.
   rewrite <- spec_gen_eval5n; auto.
 unfold to_Z; case (spec_to_Z w5_spec y); auto.
 Qed.

 Lemma spec_get_end6: forall n x y,
    eval6n n x  <= [N6 y] -> 
     [N6 (GenBase.get_low W0 n x)] = eval6n n x.
 Proof.
 intros n x y H.
 rewrite spec_gen_eval6n; unfold to_Z.
 apply GenBase.spec_get_low.
 exact (spec_0 w6_spec).
 exact (spec_to_Z w6_spec).
 apply Zle_lt_trans with [N6 y]; auto.
   rewrite <- spec_gen_eval6n; auto.
 unfold to_Z; case (spec_to_Z w6_spec y); auto.
 Qed.

 Let div_gt0 x y := let (u,v) := (w0_div_gt x y) in (reduce_0 u, reduce_0 v).
 Let div_gt1 x y := let (u,v) := (w1_div_gt x y) in (reduce_1 u, reduce_1 v).
 Let div_gt2 x y := let (u,v) := (w2_div_gt x y) in (reduce_2 u, reduce_2 v).
 Let div_gt3 x y := let (u,v) := (w3_div_gt x y) in (reduce_3 u, reduce_3 v).
 Let div_gt4 x y := let (u,v) := (w4_div_gt x y) in (reduce_4 u, reduce_4 v).
 Let div_gt5 x y := let (u,v) := (w5_div_gt x y) in (reduce_5 u, reduce_5 v).
 Let div_gt6 x y := let (u,v) := (w6_div_gt x y) in (reduce_6 u, reduce_6 v).

 Let div_gtnm n m wx wy :=
    let mn := Max.max n m in
    let d := diff n m in
    let op := make_op mn in
    let (q, r):= op.(znz_div_gt)
         (castm (diff_r n m) (extend_tr wx (snd d)))
         (castm (diff_l n m) (extend_tr wy (fst d))) in
    (reduce_n mn q, reduce_n mn r).

 Definition div_gt := Eval lazy beta delta [iter] in
   (iter _ 
      div_gt0
      (fun n x y => div_gt0 x (GenBase.get_low w_0 (S n) y))
      w0_divn1
      div_gt1
      (fun n x y => div_gt1 x (GenBase.get_low W0 (S n) y))
      w1_divn1
      div_gt2
      (fun n x y => div_gt2 x (GenBase.get_low W0 (S n) y))
      w2_divn1
      div_gt3
      (fun n x y => div_gt3 x (GenBase.get_low W0 (S n) y))
      w3_divn1
      div_gt4
      (fun n x y => div_gt4 x (GenBase.get_low W0 (S n) y))
      w4_divn1
      div_gt5
      (fun n x y => div_gt5 x (GenBase.get_low W0 (S n) y))
      w5_divn1
      div_gt6
      (fun n x y => div_gt6 x (GenBase.get_low W0 (S n) y))
      w6_divn1
      div_gtnm).

 Theorem spec_div_gt: forall x y,
       [x] > [y] -> 0 < [y] ->
      let (q,r) := div_gt x y in
      [q] = [x] / [y] /\ [r] = [x] mod [y].
 Proof.
 assert (FO:
   forall x y, [x] > [y] -> 0 < [y] ->
      let (q,r) := div_gt x y in
      [x] = [q] * [y] + [r] /\ 0 <= [r] < [y]).
  refine (spec_iter (t_*t_) (fun x y res => x > y -> 0 < y ->
      let (q,r) := res in
      x = [q] * y + [r] /\ 0 <= [r] < y)
      div_gt0
      (fun n x y => div_gt0 x (GenBase.get_low w_0 (S n) y))
      w0_divn1 _ _ _
      div_gt1
      (fun n x y => div_gt1 x (GenBase.get_low W0 (S n) y))
      w1_divn1 _ _ _
      div_gt2
      (fun n x y => div_gt2 x (GenBase.get_low W0 (S n) y))
      w2_divn1 _ _ _
      div_gt3
      (fun n x y => div_gt3 x (GenBase.get_low W0 (S n) y))
      w3_divn1 _ _ _
      div_gt4
      (fun n x y => div_gt4 x (GenBase.get_low W0 (S n) y))
      w4_divn1 _ _ _
      div_gt5
      (fun n x y => div_gt5 x (GenBase.get_low W0 (S n) y))
      w5_divn1 _ _ _
      div_gt6
      (fun n x y => div_gt6 x (GenBase.get_low W0 (S n) y))
      w6_divn1 _ _ _
      div_gtnm _).
  intros x y H1 H2; unfold div_gt0, w0_div_gt.
    generalize (spec_div_gt w0_spec x y H1 H2); case znz_div_gt.
    intros xx yy; repeat rewrite spec_reduce_0; auto.
  intros n x y H1 H2 H3; unfold div_gt0, w0_div_gt.
    generalize (spec_div_gt w0_spec x 
                (GenBase.get_low w_0 (S n) y)).
    unfold w0;case znz_div_gt.
    intros xx yy H4; repeat rewrite spec_reduce_0.
    generalize (spec_get_end0 (S n) y x); unfold to_Z; intros H5.
    unfold to_Z in H2; rewrite H5 in H4; auto with zarith.
  intros n x y H1 H2 H3.
    generalize
     (spec_divn1 w0 w0_op w0_spec (S n) x y H3).
    unfold w0_divn1;unfold w0; case gen_divn1.
    intros xx yy H4.
    rewrite to_Z0_spec; auto with zarith.
    repeat rewrite <- spec_gen_eval0n in H4; auto.
  intros x y H1 H2; unfold div_gt1, w1_div_gt.
    generalize (spec_div_gt w1_spec x y H1 H2); case znz_div_gt.
    intros xx yy; repeat rewrite spec_reduce_1; auto.
  intros n x y H1 H2 H3; unfold div_gt1, w1_div_gt.
    generalize (spec_div_gt w1_spec x 
                (GenBase.get_low W0 (S n) y)).
    unfold w1;unfold w0;case znz_div_gt.
    intros xx yy H4; repeat rewrite spec_reduce_1.
    generalize (spec_get_end1 (S n) y x); unfold to_Z; intros H5.
    unfold to_Z in H2; rewrite H5 in H4; auto with zarith.
  intros n x y H1 H2 H3.
    generalize
     (spec_divn1 w1 w1_op w1_spec (S n) x y H3).
    unfold w1_divn1;unfold w1;unfold w0; case gen_divn1.
    intros xx yy H4.
    rewrite to_Z1_spec; auto with zarith.
    repeat rewrite <- spec_gen_eval1n in H4; auto.
  intros x y H1 H2; unfold div_gt2, w2_div_gt.
    generalize (spec_div_gt w2_spec x y H1 H2); case znz_div_gt.
    intros xx yy; repeat rewrite spec_reduce_2; auto.
  intros n x y H1 H2 H3; unfold div_gt2, w2_div_gt.
    generalize (spec_div_gt w2_spec x 
                (GenBase.get_low W0 (S n) y)).
    unfold w2;unfold w1;unfold w0;case znz_div_gt.
    intros xx yy H4; repeat rewrite spec_reduce_2.
    generalize (spec_get_end2 (S n) y x); unfold to_Z; intros H5.
    unfold to_Z in H2; rewrite H5 in H4; auto with zarith.
  intros n x y H1 H2 H3.
    generalize
     (spec_divn1 w2 w2_op w2_spec (S n) x y H3).
    unfold w2_divn1;unfold w2;unfold w1;unfold w0; case gen_divn1.
    intros xx yy H4.
    rewrite to_Z2_spec; auto with zarith.
    repeat rewrite <- spec_gen_eval2n in H4; auto.
  intros x y H1 H2; unfold div_gt3, w3_div_gt.
    generalize (spec_div_gt w3_spec x y H1 H2); case znz_div_gt.
    intros xx yy; repeat rewrite spec_reduce_3; auto.
  intros n x y H1 H2 H3; unfold div_gt3, w3_div_gt.
    generalize (spec_div_gt w3_spec x 
                (GenBase.get_low W0 (S n) y)).
    unfold w3;unfold w2;unfold w1;unfold w0;case znz_div_gt.
    intros xx yy H4; repeat rewrite spec_reduce_3.
    generalize (spec_get_end3 (S n) y x); unfold to_Z; intros H5.
    unfold to_Z in H2; rewrite H5 in H4; auto with zarith.
  intros n x y H1 H2 H3.
    generalize
     (spec_divn1 w3 w3_op w3_spec (S n) x y H3).
    unfold w3_divn1;unfold w3;unfold w2;unfold w1;unfold w0; case gen_divn1.
    intros xx yy H4.
    rewrite to_Z3_spec; auto with zarith.
    repeat rewrite <- spec_gen_eval3n in H4; auto.
  intros x y H1 H2; unfold div_gt4, w4_div_gt.
    generalize (spec_div_gt w4_spec x y H1 H2); case znz_div_gt.
    intros xx yy; repeat rewrite spec_reduce_4; auto.
  intros n x y H1 H2 H3; unfold div_gt4, w4_div_gt.
    generalize (spec_div_gt w4_spec x 
                (GenBase.get_low W0 (S n) y)).
    unfold w4;unfold w3;unfold w2;unfold w1;unfold w0;case znz_div_gt.
    intros xx yy H4; repeat rewrite spec_reduce_4.
    generalize (spec_get_end4 (S n) y x); unfold to_Z; intros H5.
    unfold to_Z in H2; rewrite H5 in H4; auto with zarith.
  intros n x y H1 H2 H3.
    generalize
     (spec_divn1 w4 w4_op w4_spec (S n) x y H3).
    unfold w4_divn1;unfold w4;unfold w3;unfold w2;unfold w1;unfold w0; case gen_divn1.
    intros xx yy H4.
    rewrite to_Z4_spec; auto with zarith.
    repeat rewrite <- spec_gen_eval4n in H4; auto.
  intros x y H1 H2; unfold div_gt5, w5_div_gt.
    generalize (spec_div_gt w5_spec x y H1 H2); case znz_div_gt.
    intros xx yy; repeat rewrite spec_reduce_5; auto.
  intros n x y H1 H2 H3; unfold div_gt5, w5_div_gt.
    generalize (spec_div_gt w5_spec x 
                (GenBase.get_low W0 (S n) y)).
    unfold w5;unfold w4;unfold w3;unfold w2;unfold w1;unfold w0;case znz_div_gt.
    intros xx yy H4; repeat rewrite spec_reduce_5.
    generalize (spec_get_end5 (S n) y x); unfold to_Z; intros H5.
    unfold to_Z in H2; rewrite H5 in H4; auto with zarith.
  intros n x y H1 H2 H3.
    generalize
     (spec_divn1 w5 w5_op w5_spec (S n) x y H3).
    unfold w5_divn1;unfold w5;unfold w4;unfold w3;unfold w2;unfold w1;unfold w0; case gen_divn1.
    intros xx yy H4.
    rewrite to_Z5_spec; auto with zarith.
    repeat rewrite <- spec_gen_eval5n in H4; auto.
  intros x y H1 H2; unfold div_gt6, w6_div_gt.
    generalize (spec_div_gt w6_spec x y H1 H2); case znz_div_gt.
    intros xx yy; repeat rewrite spec_reduce_6; auto.
  intros n x y H2 H3; unfold div_gt6, w6_div_gt.
    generalize (spec_div_gt w6_spec x 
                (GenBase.get_low W0 (S n) y)).
    unfold w6;unfold w5;unfold w4;unfold w3;unfold w2;unfold w1;unfold w0;case znz_div_gt.
    intros xx yy H4; repeat rewrite spec_reduce_6.
    generalize (spec_get_end6 (S n) y x); unfold to_Z; intros H5.
    unfold to_Z in H2; rewrite H5 in H4; auto with zarith.
  intros n x y H2 H3.
    generalize
     (spec_divn1 w6 w6_op w6_spec (S n) x y H3).
    unfold w6_divn1;unfold w6;unfold w5;unfold w4;unfold w3;unfold w2;unfold w1;unfold w0; case gen_divn1.
    intros xx yy H4.
    repeat rewrite <- spec_gen_eval6n in H4; auto.
    rewrite spec_eval6n; auto.
  intros n m x y H1 H2; unfold div_gtnm.
    generalize (spec_div_gt (wn_spec (Max.max n m))
                   (castm (diff_r n m)
                     (extend_tr x (snd (diff n m))))
                   (castm (diff_l n m)
                     (extend_tr y (fst (diff n m))))).
    case znz_div_gt.
    intros xx yy HH.
    repeat rewrite spec_reduce_n.
    rewrite <- (spec_cast_l n m x).
    rewrite <- (spec_cast_r n m y).
    unfold to_Z; apply HH.
    rewrite <- (spec_cast_l n m x) in H1; auto.
    rewrite <- (spec_cast_r n m y) in H1; auto.
    rewrite <- (spec_cast_r n m y) in H2; auto.
  intros x y H1 H2; generalize (FO x y H1 H2); case div_gt.
  intros q r (H3, H4); split.
  apply (Zdiv_unique [x] [y] [q] [r]); auto.
  rewrite Zmult_comm; auto.
  apply (Zmod_unique [x] [y] [q] [r]); auto.
  rewrite Zmult_comm; auto.
  Qed.

 Definition div_eucl x y :=
  match compare x y with
  | Eq => (one, zero)
  | Lt => (zero, x)
  | Gt => div_gt x y
  end.

 Theorem spec_div_eucl: forall x y,
      0 < [y] ->
      let (q,r) := div_eucl x y in
      ([q], [r]) = Zdiv_eucl [x] [y].
 Proof.
 assert (F0: [zero] = 0).
   exact (spec_0 w0_spec).
 assert (F1: [one] = 1).
   exact (spec_1 w0_spec).
 intros x y H; generalize (spec_compare x y);
   unfold div_eucl; case compare; try rewrite F0;
   try rewrite F1; intros; auto with zarith.
 rewrite H0; generalize (Z_div_same [y] (Zlt_gt _ _ H))
                        (Z_mod_same [y] (Zlt_gt _ _ H));
  unfold Zdiv, Zmod; case Zdiv_eucl; intros; subst; auto.
 assert (F2: 0 <= [x] < [y]).
   generalize (spec_pos x); auto.
 generalize (Zdiv_small _ _ F2)
            (Zmod_small _ _ F2);
  unfold Zdiv, Zmod; case Zdiv_eucl; intros; subst; auto.
 generalize (spec_div_gt _ _ H0 H); auto.
 unfold Zdiv, Zmod; case Zdiv_eucl; case div_gt.
 intros a b c d (H1, H2); subst; auto.
 Qed.

 Definition div x y := fst (div_eucl x y).

 Theorem spec_div:
   forall x y, 0 < [y] -> [div x y] = [x] / [y].
 Proof.
 intros x y H1; unfold div; generalize (spec_div_eucl x y H1);
   case div_eucl; simpl fst.
 intros xx yy; unfold Zdiv; case Zdiv_eucl; intros qq rr H; 
  injection H; auto.
 Qed.

 (***************************************************************)
 (*                                                             *)
 (*                           Modulo                            *)
 (*                                                             *)
 (***************************************************************)

 Definition w0_mod_gt := w0_op.(znz_mod_gt).
 Definition w1_mod_gt := w1_op.(znz_mod_gt).
 Definition w2_mod_gt := w2_op.(znz_mod_gt).
 Definition w3_mod_gt := w3_op.(znz_mod_gt).
 Definition w4_mod_gt := w4_op.(znz_mod_gt).
 Definition w5_mod_gt := w5_op.(znz_mod_gt).
 Definition w6_mod_gt := w6_op.(znz_mod_gt).

 Definition w0_modn1 :=
  gen_modn1 w0_op.(znz_zdigits) w0_op.(znz_0)
    w0_op.(znz_head0) w0_op.(znz_add_mul_div) w0_op.(znz_div21)
    w0_op.(znz_compare) w0_op.(znz_sub).
 Definition w1_modn1 :=
  gen_modn1 w1_op.(znz_zdigits) w1_op.(znz_0)
    w1_op.(znz_head0) w1_op.(znz_add_mul_div) w1_op.(znz_div21)
    w1_op.(znz_compare) w1_op.(znz_sub).
 Definition w2_modn1 :=
  gen_modn1 w2_op.(znz_zdigits) w2_op.(znz_0)
    w2_op.(znz_head0) w2_op.(znz_add_mul_div) w2_op.(znz_div21)
    w2_op.(znz_compare) w2_op.(znz_sub).
 Definition w3_modn1 :=
  gen_modn1 w3_op.(znz_zdigits) w3_op.(znz_0)
    w3_op.(znz_head0) w3_op.(znz_add_mul_div) w3_op.(znz_div21)
    w3_op.(znz_compare) w3_op.(znz_sub).
 Definition w4_modn1 :=
  gen_modn1 w4_op.(znz_zdigits) w4_op.(znz_0)
    w4_op.(znz_head0) w4_op.(znz_add_mul_div) w4_op.(znz_div21)
    w4_op.(znz_compare) w4_op.(znz_sub).
 Definition w5_modn1 :=
  gen_modn1 w5_op.(znz_zdigits) w5_op.(znz_0)
    w5_op.(znz_head0) w5_op.(znz_add_mul_div) w5_op.(znz_div21)
    w5_op.(znz_compare) w5_op.(znz_sub).
 Definition w6_modn1 :=
  gen_modn1 w6_op.(znz_zdigits) w6_op.(znz_0)
    w6_op.(znz_head0) w6_op.(znz_add_mul_div) w6_op.(znz_div21)
    w6_op.(znz_compare) w6_op.(znz_sub).

 Let mod_gtnm n m wx wy :=
    let mn := Max.max n m in
    let d := diff n m in
    let op := make_op mn in
    reduce_n mn (op.(znz_mod_gt)
         (castm (diff_r n m) (extend_tr wx (snd d)))
         (castm (diff_l n m) (extend_tr wy (fst d)))).

 Definition mod_gt := Eval lazy beta delta[iter] in
   (iter _ 
      (fun x y => reduce_0 (w0_mod_gt x y))
      (fun n x y => reduce_0 (w0_mod_gt x (GenBase.get_low w_0 (S n) y)))
      (fun n x y => reduce_0 (w0_modn1 (S n) x y))
      (fun x y => reduce_1 (w1_mod_gt x y))
      (fun n x y => reduce_1 (w1_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_1 (w1_modn1 (S n) x y))
      (fun x y => reduce_2 (w2_mod_gt x y))
      (fun n x y => reduce_2 (w2_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_2 (w2_modn1 (S n) x y))
      (fun x y => reduce_3 (w3_mod_gt x y))
      (fun n x y => reduce_3 (w3_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_3 (w3_modn1 (S n) x y))
      (fun x y => reduce_4 (w4_mod_gt x y))
      (fun n x y => reduce_4 (w4_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_4 (w4_modn1 (S n) x y))
      (fun x y => reduce_5 (w5_mod_gt x y))
      (fun n x y => reduce_5 (w5_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_5 (w5_modn1 (S n) x y))
      (fun x y => reduce_6 (w6_mod_gt x y))
      (fun n x y => reduce_6 (w6_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_6 (w6_modn1 (S n) x y))
      mod_gtnm).

 Let spec_modn1 ww (ww_op: znz_op ww) (ww_spec: znz_spec ww_op) := 
   (spec_gen_modn1 
    ww_op.(znz_zdigits) ww_op.(znz_0)
    ww_op.(znz_WW) ww_op.(znz_head0)
    ww_op.(znz_add_mul_div) ww_op.(znz_div21)
    ww_op.(znz_compare) ww_op.(znz_sub) (znz_to_Z ww_op)
    (spec_to_Z ww_spec) 
    (spec_zdigits ww_spec)
   (spec_0 ww_spec) (spec_WW ww_spec) (spec_head0 ww_spec)
   (spec_add_mul_div ww_spec) (spec_div21 ww_spec) 
    (ZnZ.spec_compare ww_spec) (ZnZ.spec_sub ww_spec)).

 Theorem spec_mod_gt:
   forall x y, [x] > [y] -> 0 < [y] -> [mod_gt x y] = [x] mod [y].
 Proof.
 refine (spec_iter _ (fun x y res => x > y -> 0 < y ->
      [res] = x mod y)
      (fun x y => reduce_0 (w0_mod_gt x y))
      (fun n x y => reduce_0 (w0_mod_gt x (GenBase.get_low w_0 (S n) y)))
      (fun n x y => reduce_0 (w0_modn1 (S n) x y)) _ _ _
      (fun x y => reduce_1 (w1_mod_gt x y))
      (fun n x y => reduce_1 (w1_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_1 (w1_modn1 (S n) x y)) _ _ _
      (fun x y => reduce_2 (w2_mod_gt x y))
      (fun n x y => reduce_2 (w2_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_2 (w2_modn1 (S n) x y)) _ _ _
      (fun x y => reduce_3 (w3_mod_gt x y))
      (fun n x y => reduce_3 (w3_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_3 (w3_modn1 (S n) x y)) _ _ _
      (fun x y => reduce_4 (w4_mod_gt x y))
      (fun n x y => reduce_4 (w4_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_4 (w4_modn1 (S n) x y)) _ _ _
      (fun x y => reduce_5 (w5_mod_gt x y))
      (fun n x y => reduce_5 (w5_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_5 (w5_modn1 (S n) x y)) _ _ _
      (fun x y => reduce_6 (w6_mod_gt x y))
      (fun n x y => reduce_6 (w6_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_6 (w6_modn1 (S n) x y)) _ _ _
      mod_gtnm _).
 intros x y H1 H2; rewrite spec_reduce_0.
   exact (spec_mod_gt w0_spec x y H1 H2).
 intros n x y H1 H2 H3; rewrite spec_reduce_0.
 unfold w0_mod_gt.
 rewrite <- (spec_get_end0 (S n) y x); auto with zarith.
 unfold to_Z; apply (spec_mod_gt w0_spec); auto.
 rewrite <- (spec_get_end0 (S n) y x) in H2; auto with zarith.
 rewrite <- (spec_get_end0 (S n) y x) in H3; auto with zarith.
 intros n x y H1 H2 H3; rewrite spec_reduce_0.
 unfold w0_modn1, to_Z; rewrite spec_gen_eval0n.
 apply (spec_modn1 _ _ w0_spec); auto.
 intros x y H1 H2; rewrite spec_reduce_1.
   exact (spec_mod_gt w1_spec x y H1 H2).
 intros n x y H1 H2 H3; rewrite spec_reduce_1.
 unfold w1_mod_gt.
 rewrite <- (spec_get_end1 (S n) y x); auto with zarith.
 unfold to_Z; apply (spec_mod_gt w1_spec); auto.
 rewrite <- (spec_get_end1 (S n) y x) in H2; auto with zarith.
 rewrite <- (spec_get_end1 (S n) y x) in H3; auto with zarith.
 intros n x y H1 H2 H3; rewrite spec_reduce_1.
 unfold w1_modn1, to_Z; rewrite spec_gen_eval1n.
 apply (spec_modn1 _ _ w1_spec); auto.
 intros x y H1 H2; rewrite spec_reduce_2.
   exact (spec_mod_gt w2_spec x y H1 H2).
 intros n x y H1 H2 H3; rewrite spec_reduce_2.
 unfold w2_mod_gt.
 rewrite <- (spec_get_end2 (S n) y x); auto with zarith.
 unfold to_Z; apply (spec_mod_gt w2_spec); auto.
 rewrite <- (spec_get_end2 (S n) y x) in H2; auto with zarith.
 rewrite <- (spec_get_end2 (S n) y x) in H3; auto with zarith.
 intros n x y H1 H2 H3; rewrite spec_reduce_2.
 unfold w2_modn1, to_Z; rewrite spec_gen_eval2n.
 apply (spec_modn1 _ _ w2_spec); auto.
 intros x y H1 H2; rewrite spec_reduce_3.
   exact (spec_mod_gt w3_spec x y H1 H2).
 intros n x y H1 H2 H3; rewrite spec_reduce_3.
 unfold w3_mod_gt.
 rewrite <- (spec_get_end3 (S n) y x); auto with zarith.
 unfold to_Z; apply (spec_mod_gt w3_spec); auto.
 rewrite <- (spec_get_end3 (S n) y x) in H2; auto with zarith.
 rewrite <- (spec_get_end3 (S n) y x) in H3; auto with zarith.
 intros n x y H1 H2 H3; rewrite spec_reduce_3.
 unfold w3_modn1, to_Z; rewrite spec_gen_eval3n.
 apply (spec_modn1 _ _ w3_spec); auto.
 intros x y H1 H2; rewrite spec_reduce_4.
   exact (spec_mod_gt w4_spec x y H1 H2).
 intros n x y H1 H2 H3; rewrite spec_reduce_4.
 unfold w4_mod_gt.
 rewrite <- (spec_get_end4 (S n) y x); auto with zarith.
 unfold to_Z; apply (spec_mod_gt w4_spec); auto.
 rewrite <- (spec_get_end4 (S n) y x) in H2; auto with zarith.
 rewrite <- (spec_get_end4 (S n) y x) in H3; auto with zarith.
 intros n x y H1 H2 H3; rewrite spec_reduce_4.
 unfold w4_modn1, to_Z; rewrite spec_gen_eval4n.
 apply (spec_modn1 _ _ w4_spec); auto.
 intros x y H1 H2; rewrite spec_reduce_5.
   exact (spec_mod_gt w5_spec x y H1 H2).
 intros n x y H1 H2 H3; rewrite spec_reduce_5.
 unfold w5_mod_gt.
 rewrite <- (spec_get_end5 (S n) y x); auto with zarith.
 unfold to_Z; apply (spec_mod_gt w5_spec); auto.
 rewrite <- (spec_get_end5 (S n) y x) in H2; auto with zarith.
 rewrite <- (spec_get_end5 (S n) y x) in H3; auto with zarith.
 intros n x y H1 H2 H3; rewrite spec_reduce_5.
 unfold w5_modn1, to_Z; rewrite spec_gen_eval5n.
 apply (spec_modn1 _ _ w5_spec); auto.
 intros x y H1 H2; rewrite spec_reduce_6.
   exact (spec_mod_gt w6_spec x y H1 H2).
 intros n x y H2 H3; rewrite spec_reduce_6.
 unfold w6_mod_gt.
 rewrite <- (spec_get_end6 (S n) y x); auto with zarith.
 unfold to_Z; apply (spec_mod_gt w6_spec); auto.
 rewrite <- (spec_get_end6 (S n) y x) in H2; auto with zarith.
 rewrite <- (spec_get_end6 (S n) y x) in H3; auto with zarith.
 intros n x y H2 H3; rewrite spec_reduce_6.
 unfold w6_modn1, to_Z; rewrite spec_gen_eval6n.
 apply (spec_modn1 _ _ w6_spec); auto.
 intros n m x y H1 H2; unfold mod_gtnm.
    repeat rewrite spec_reduce_n.
    rewrite <- (spec_cast_l n m x).
    rewrite <- (spec_cast_r n m y).
    unfold to_Z; apply (spec_mod_gt (wn_spec (Max.max n m))).
    rewrite <- (spec_cast_l n m x) in H1; auto.
    rewrite <- (spec_cast_r n m y) in H1; auto.
    rewrite <- (spec_cast_r n m y) in H2; auto.
 Qed.

 Definition modulo x y := 
  match compare x y with
  | Eq => zero
  | Lt => x
  | Gt => mod_gt x y
  end.

 Theorem spec_modulo:
   forall x y, 0 < [y] -> [modulo x y] = [x] mod [y].
 Proof.
 assert (F0: [zero] = 0).
   exact (spec_0 w0_spec).
 assert (F1: [one] = 1).
   exact (spec_1 w0_spec).
 intros x y H; generalize (spec_compare x y);
   unfold modulo; case compare; try rewrite F0;
   try rewrite F1; intros; try split; auto with zarith.
 rewrite H0; apply sym_equal; apply Z_mod_same; auto with zarith.
 apply sym_equal; apply Zmod_small; auto with zarith.
 generalize (spec_pos x); auto with zarith.
 apply spec_mod_gt; auto.
 Qed.

 (***************************************************************)
 (*                                                             *)
 (*                           Gcd                               *)
 (*                                                             *)
 (***************************************************************)

 Definition digits x :=
  match x with
  | N0 _ => w0_op.(znz_digits)
  | N1 _ => w1_op.(znz_digits)
  | N2 _ => w2_op.(znz_digits)
  | N3 _ => w3_op.(znz_digits)
  | N4 _ => w4_op.(znz_digits)
  | N5 _ => w5_op.(znz_digits)
  | N6 _ => w6_op.(znz_digits)
  | Nn n _ => (make_op n).(znz_digits)
  end.

 Theorem spec_digits: forall x, 0 <= [x] < 2 ^  Zpos (digits x).
 Proof.
 intros x; case x; clear x.
  intros x; unfold to_Z, digits;
   generalize (spec_to_Z w0_spec x); unfold base; intros H; exact H.
  intros x; unfold to_Z, digits;
   generalize (spec_to_Z w1_spec x); unfold base; intros H; exact H.
  intros x; unfold to_Z, digits;
   generalize (spec_to_Z w2_spec x); unfold base; intros H; exact H.
  intros x; unfold to_Z, digits;
   generalize (spec_to_Z w3_spec x); unfold base; intros H; exact H.
  intros x; unfold to_Z, digits;
   generalize (spec_to_Z w4_spec x); unfold base; intros H; exact H.
  intros x; unfold to_Z, digits;
   generalize (spec_to_Z w5_spec x); unfold base; intros H; exact H.
  intros x; unfold to_Z, digits;
   generalize (spec_to_Z w6_spec x); unfold base; intros H; exact H.
  intros n x; unfold to_Z, digits;
   generalize (spec_to_Z (wn_spec n) x); unfold base; intros H; exact H.
 Qed.

 Definition gcd_gt_body a b cont :=
  match compare b zero with
  | Gt =>
    let r := mod_gt a b in
    match compare r zero with
    | Gt => cont r (mod_gt b r)
    | _ => b
    end
  | _ => a
  end.

 Theorem Zspec_gcd_gt_body: forall a b cont p,
    [a] > [b] -> [a] < 2 ^ p ->
      (forall a1 b1, [a1] < 2 ^ (p - 1) -> [a1] > [b1] ->
         Zis_gcd  [a1] [b1] [cont a1 b1]) ->                   
      Zis_gcd [a] [b] [gcd_gt_body a b cont].
 Proof.
 assert (F1: [zero] = 0).
   unfold zero, w_0, to_Z; rewrite (spec_0 w0_spec); auto.
 intros a b cont p H2 H3 H4; unfold gcd_gt_body.
 generalize (spec_compare b zero); case compare; try rewrite F1.
   intros HH; rewrite HH; apply Zis_gcd_0.
 intros HH; absurd (0 <= [b]); auto with zarith.
 case (spec_digits b); auto with zarith.
 intros H5; generalize (spec_compare (mod_gt a b) zero); 
   case compare; try rewrite F1.
 intros H6; rewrite <- (Zmult_1_r [b]).
 rewrite (Z_div_mod_eq [a] [b]); auto with zarith.
 rewrite <- spec_mod_gt; auto with zarith.
 rewrite H6; rewrite Zplus_0_r.
 apply Zis_gcd_mult; apply Zis_gcd_1.
 intros; apply False_ind.
 case (spec_digits (mod_gt a b)); auto with zarith.
 intros H6; apply GenDiv.Zis_gcd_mod; auto with zarith.
 apply GenDiv.Zis_gcd_mod; auto with zarith.
 rewrite <- spec_mod_gt; auto with zarith.
 assert (F2: [b] > [mod_gt a b]).
   case (Z_mod_lt [a] [b]); auto with zarith.
   repeat rewrite <- spec_mod_gt; auto with zarith.
 assert (F3: [mod_gt a b] > [mod_gt b  (mod_gt a b)]).
   case (Z_mod_lt [b] [mod_gt a b]); auto with zarith.
   rewrite <- spec_mod_gt; auto with zarith.
 repeat rewrite <- spec_mod_gt; auto with zarith.
 apply H4; auto with zarith.
 apply Zmult_lt_reg_r with 2; auto with zarith.
 apply Zle_lt_trans with ([b] + [mod_gt a b]); auto with zarith.
 apply Zle_lt_trans with (([a]/[b]) * [b] + [mod_gt a b]); auto with zarith.
   apply Zplus_le_compat_r.
 pattern [b] at 1; rewrite <- (Zmult_1_l [b]).
 apply Zmult_le_compat_r; auto with zarith.
 case (Zle_lt_or_eq 0 ([a]/[b])); auto with zarith.
 intros HH; rewrite (Z_div_mod_eq [a] [b]) in H2;
   try rewrite <- HH in H2; auto with zarith.
 case (Z_mod_lt [a] [b]); auto with zarith.
 rewrite Zmult_comm; rewrite spec_mod_gt; auto with zarith.
 rewrite <- Z_div_mod_eq; auto with zarith.
 pattern 2 at 2; rewrite <- (Zpower_1_r 2).
 rewrite <- Zpower_exp; auto with zarith.
 ring_simplify (p - 1 + 1); auto.
 case (Zle_lt_or_eq 0 p); auto with zarith.
 generalize H3; case p; simpl Zpower; auto with zarith.
 intros HH; generalize H3; rewrite <- HH; simpl Zpower; auto with zarith.
 Qed.

 Fixpoint gcd_gt_aux (p:positive) (cont:t->t->t) (a b:t) {struct p} : t :=
  gcd_gt_body a b
    (fun a b =>
       match p with
       | xH => cont a b
       | xO p => gcd_gt_aux p (gcd_gt_aux p cont) a b
       | xI p => gcd_gt_aux p (gcd_gt_aux p cont) a b
       end).

 Theorem Zspec_gcd_gt_aux: forall p n a b cont,
    [a] > [b] -> [a] < 2 ^ (Zpos p + n) ->
      (forall a1 b1, [a1] < 2 ^ n -> [a1] > [b1] ->
            Zis_gcd [a1] [b1] [cont a1 b1]) ->
          Zis_gcd [a] [b] [gcd_gt_aux p cont a b].
 intros p; elim p; clear p.
 intros p Hrec n a b cont H2 H3 H4.
   unfold gcd_gt_aux; apply Zspec_gcd_gt_body with (Zpos (xI p) + n); auto.
   intros a1 b1 H6 H7.
     apply Hrec with (Zpos p + n); auto.
       replace (Zpos p + (Zpos p + n)) with
         (Zpos (xI p) + n  - 1); auto.
       rewrite Zpos_xI; ring.
   intros a2 b2 H9 H10.
     apply Hrec with n; auto.
 intros p Hrec n a b cont H2 H3 H4.
   unfold gcd_gt_aux; apply Zspec_gcd_gt_body with (Zpos (xO p) + n); auto.
   intros a1 b1 H6 H7.
     apply Hrec with (Zpos p + n - 1); auto.
       replace (Zpos p + (Zpos p + n - 1)) with
         (Zpos (xO p) + n  - 1); auto.
       rewrite Zpos_xO; ring.
   intros a2 b2 H9 H10.
     apply Hrec with (n - 1); auto.
       replace (Zpos p + (n - 1)) with
         (Zpos p + n  - 1); auto with zarith.
   intros a3 b3 H12 H13; apply H4; auto with zarith.
    apply Zlt_le_trans with (1 := H12).
    case (Zle_or_lt 1 n); intros HH.
    apply Zpower_le_monotone; auto with zarith.
    apply Zle_trans with 0; auto with zarith.
    assert (HH1: n - 1 < 0); auto with zarith.
    generalize HH1; case (n - 1); auto with zarith.
    intros p1 HH2; discriminate.
 intros n a b cont H H2 H3.
  simpl gcd_gt_aux.
  apply Zspec_gcd_gt_body with (n + 1); auto with zarith.
  rewrite Zplus_comm; auto.
  intros a1 b1 H5 H6; apply H3; auto.
  replace n with (n + 1 - 1); auto; try ring.
 Qed.

 Definition gcd_cont a b :=
  match compare one b with
  | Eq => one
  | _ => a
  end.

 Definition gcd_gt a b := gcd_gt_aux (digits a) gcd_cont a b.

 Theorem spec_gcd_gt: forall a b,
   [a] > [b] -> [gcd_gt a b] = Zgcd [a] [b].
 Proof.
 intros a b H2.
 case (spec_digits (gcd_gt a b)); intros H3 H4.
 case (spec_digits a); intros H5 H6.
 apply sym_equal; apply Zis_gcd_gcd; auto with zarith.
 unfold gcd_gt; apply Zspec_gcd_gt_aux with 0; auto with zarith.
 intros a1 a2; rewrite Zpower_0_r.
 case (spec_digits a2); intros H7 H8;
   intros; apply False_ind; auto with zarith.
 Qed.

 Definition gcd a b :=
  match compare a b with
  | Eq => a
  | Lt => gcd_gt b a
  | Gt => gcd_gt a b
  end.

 Theorem spec_gcd: forall a b, [gcd a b] = Zgcd [a] [b].
 Proof.
 intros a b.
 case (spec_digits a); intros H1 H2.
 case (spec_digits b); intros H3 H4.
 unfold gcd; generalize (spec_compare a b); case compare.
 intros HH; rewrite HH; apply sym_equal; apply Zis_gcd_gcd; auto.
   apply Zis_gcd_refl.
 intros; apply trans_equal with (Zgcd [b] [a]).
   apply spec_gcd_gt; auto with zarith.
 apply Zis_gcd_gcd; auto with zarith.
 apply Zgcd_is_pos.
 apply Zis_gcd_sym; apply Zgcd_is_gcd.
 intros; apply spec_gcd_gt; auto.
 Qed.

 (***************************************************************)
 (*                                                             *)
 (*                          Conversion                         *)
 (*                                                             *)
 (***************************************************************)

 Definition pheight p := 
   Peano.pred (nat_of_P (get_height w0_op.(znz_digits) (plength p))).

 Theorem pheight_correct: forall p, 
    Zpos p < 2 ^ (Zpos (znz_digits w0_op) * 2 ^ (Z_of_nat (pheight p))).
 Proof.
 intros p; unfold pheight.
 assert (F1: forall x, Z_of_nat (Peano.pred (nat_of_P x)) = Zpos x - 1).
  intros x.
  assert (Zsucc (Z_of_nat (Peano.pred (nat_of_P x))) = Zpos x); auto with zarith.
    rewrite <- inj_S.
    rewrite <- (fun x => S_pred x 0); auto with zarith.
    rewrite Zpos_eq_Z_of_nat_o_nat_of_P; auto.
    apply lt_le_trans with 1%nat; auto with zarith.
    exact (le_Pmult_nat x 1).
  rewrite F1; clear F1.
 assert (F2:= (get_height_correct (znz_digits w0_op) (plength p))).
 apply Zlt_le_trans with (Zpos (Psucc p)).
   rewrite Zpos_succ_morphism; auto with zarith.
  apply Zle_trans with (1 := plength_pred_correct (Psucc p)).
 rewrite Ppred_succ.
 apply Zpower_le_monotone; auto with zarith.
 Qed.

 Definition of_pos x :=
  let h := pheight x in
  match h with
  | 0%nat => reduce_0 (snd (w0_op.(znz_of_pos) x))
  | 1%nat => reduce_1 (snd (w1_op.(znz_of_pos) x))
  | 2%nat => reduce_2 (snd (w2_op.(znz_of_pos) x))
  | 3%nat => reduce_3 (snd (w3_op.(znz_of_pos) x))
  | 4%nat => reduce_4 (snd (w4_op.(znz_of_pos) x))
  | 5%nat => reduce_5 (snd (w5_op.(znz_of_pos) x))
  | 6%nat => reduce_6 (snd (w6_op.(znz_of_pos) x))
  | _ =>
    let n := minus h 7 in
    reduce_n n (snd ((make_op n).(znz_of_pos) x))
  end.

 Theorem spec_of_pos: forall x,
   [of_pos x] = Zpos x.
 Proof.
 assert (F := spec_more_than_1_digit w0_spec).
 intros x; unfold of_pos; case_eq (pheight x).
 intros H1; rewrite spec_reduce_0; unfold to_Z.
 apply (znz_of_pos_correct w0_spec).
 apply Zlt_le_trans with (1 := pheight_correct x).
   rewrite H1; simpl Z_of_nat; change (2^0) with (1).
   unfold base.
   apply Zpower_le_monotone; split; auto with zarith.
 intros n; case n; clear n.
 intros H1; rewrite spec_reduce_1; unfold to_Z.
 apply (znz_of_pos_correct w1_spec).
 apply Zlt_le_trans with (1 := pheight_correct x).
   rewrite H1; simpl Z_of_nat; change (2^1) with (2).
   unfold base.
   apply Zpower_le_monotone; split; auto with zarith.
   apply Zeq_le; apply Zmult_comm.
 intros n; case n; clear n.
 intros H1; rewrite spec_reduce_2; unfold to_Z.
 apply (znz_of_pos_correct w2_spec).
 apply Zlt_le_trans with (1 := pheight_correct x).
   rewrite H1; simpl Z_of_nat; change (2^2) with (2 * 2).
   unfold base.
   apply Zpower_le_monotone; split; auto with zarith.
   apply Zeq_le; apply Zmult_comm.
 intros n; case n; clear n.
 intros H1; rewrite spec_reduce_3; unfold to_Z.
 apply (znz_of_pos_correct w3_spec).
 apply Zlt_le_trans with (1 := pheight_correct x).
   rewrite H1; simpl Z_of_nat; change (2^3) with (2 * 2 * 2).
   unfold base.
   apply Zpower_le_monotone; split; auto with zarith. 
   apply Zeq_le; apply Zmult_comm.
 intros n; case n; clear n.
 intros H1; rewrite spec_reduce_4; unfold to_Z.
 apply (znz_of_pos_correct w4_spec).
 apply Zlt_le_trans with (1 := pheight_correct x).
   rewrite H1; simpl Z_of_nat; change (2^4) with (2 * 2 * 2 * 2).
   unfold base.
   apply Zpower_le_monotone; split; auto with zarith.
   apply Zeq_le; apply Zmult_comm.
 intros n; case n; clear n.
 intros H1; rewrite spec_reduce_5; unfold to_Z.
 apply (znz_of_pos_correct w5_spec).
 apply Zlt_le_trans with (1 := pheight_correct x).
   rewrite H1; simpl Z_of_nat; change (2^5) with (2 * 2 * 2 * 2 * 2).
   unfold base.
   apply Zpower_le_monotone; split; auto with zarith.
   apply Zeq_le; apply Zmult_comm.
 intros n; case n; clear n.
 intros H1; rewrite spec_reduce_6; unfold to_Z.
 apply (znz_of_pos_correct w6_spec).
 apply Zlt_le_trans with (1 := pheight_correct x).
   rewrite H1; simpl Z_of_nat; change (2^6) with (2 * 2 * 2 * 2 * 2 * 2).
   unfold base.
   apply Zpower_le_monotone; split; auto with zarith.
   apply Zeq_le; apply Zmult_comm.
 intros n.
 intros H1; rewrite spec_reduce_n; unfold to_Z.
 simpl minus; rewrite <- minus_n_O.
 apply (znz_of_pos_correct (wn_spec n)).
 apply Zlt_le_trans with (1 := pheight_correct x).
   unfold base.
   apply Zpower_le_monotone; auto with zarith.
   split; auto with zarith.
   rewrite H1.
  elim n; clear n H1.
   simpl Z_of_nat; change (2^7) with (2 * 2 * 2 * 2 * 2 * 2 * 2).
   rewrite Zmult_comm; repeat rewrite <- Zmult_assoc.
     repeat rewrite <- Zpos_xO.
   refine (Zle_refl _).
  intros n Hrec.
  rewrite make_op_S.
  change (@znz_digits (word _ (S (S n))) (mk_zn2z_op_karatsuba (make_op n))) with
    (xO (znz_digits (make_op n))).
  rewrite (fun x y => (Zpos_xO (@znz_digits x y))).
  rewrite inj_S; unfold Zsucc.
  rewrite Zplus_comm; rewrite Zpower_exp; auto with zarith.
  rewrite Zpower_1_r.
  assert (tmp: forall x y z, x * (y * z) = y * (x * z));
   [intros; ring | rewrite tmp; clear tmp].
  apply Zmult_le_compat_l; auto with zarith.
  Qed.

 Definition of_N x :=
  match x with
  | BinNat.N0 => zero
  | Npos p => of_pos p
  end.

 Theorem spec_of_N: forall x,
   [of_N x] = Z_of_N x.
 Proof.
 intros x; case x.
  simpl of_N.
  unfold zero, w_0, to_Z; rewrite (spec_0 w0_spec); auto.
 intros p; exact (spec_of_pos p).
 Qed.

 (***************************************************************)
 (*                                                             *)
 (*                          Shift                              *)
 (*                                                             *)
 (***************************************************************)

 Definition head0 w := match w with
 | N0 w=> reduce_0 (w0_op.(znz_head0) w)
 | N1 w=> reduce_1 (w1_op.(znz_head0) w)
 | N2 w=> reduce_2 (w2_op.(znz_head0) w)
 | N3 w=> reduce_3 (w3_op.(znz_head0) w)
 | N4 w=> reduce_4 (w4_op.(znz_head0) w)
 | N5 w=> reduce_5 (w5_op.(znz_head0) w)
 | N6 w=> reduce_6 (w6_op.(znz_head0) w)
 | Nn n w=> reduce_n n ((make_op n).(znz_head0) w)
 end.

 Theorem spec_head00: forall x, [x] = 0 ->[head0 x] = Zpos (digits x).
 Proof.
 intros x; case x; unfold head0; clear x.
   intros x; rewrite spec_reduce_0; exact (spec_head00 w0_spec x).
   intros x; rewrite spec_reduce_1; exact (spec_head00 w1_spec x).
   intros x; rewrite spec_reduce_2; exact (spec_head00 w2_spec x).
   intros x; rewrite spec_reduce_3; exact (spec_head00 w3_spec x).
   intros x; rewrite spec_reduce_4; exact (spec_head00 w4_spec x).
   intros x; rewrite spec_reduce_5; exact (spec_head00 w5_spec x).
   intros x; rewrite spec_reduce_6; exact (spec_head00 w6_spec x).
 intros n x; rewrite spec_reduce_n; exact (spec_head00 (wn_spec n) x).
 Qed.
  
 Theorem spec_head0: forall x, 0 < [x] ->
   2 ^ (Zpos (digits x) - 1) <= 2 ^ [head0 x] * [x] < 2 ^ Zpos (digits x).
 Proof.
 assert (F0: forall x, (x - 1) + 1 = x).
   intros; ring. 
 intros x; case x; unfold digits, head0; clear x.
 intros x Hx; rewrite spec_reduce_0.
 assert (F1:= spec_more_than_1_digit w0_spec).
 generalize (spec_head0 w0_spec x Hx).
 unfold base.
 pattern (Zpos (znz_digits w0_op)) at 1; 
 rewrite <- (fun x => (F0 (Zpos x))).
 rewrite Zpower_exp; auto with zarith.
 rewrite Zpower_1_r; rewrite Z_div_mult; auto with zarith.
 intros x Hx; rewrite spec_reduce_1.
 assert (F1:= spec_more_than_1_digit w1_spec).
 generalize (spec_head0 w1_spec x Hx).
 unfold base.
 pattern (Zpos (znz_digits w1_op)) at 1; 
 rewrite <- (fun x => (F0 (Zpos x))).
 rewrite Zpower_exp; auto with zarith.
 rewrite Zpower_1_r; rewrite Z_div_mult; auto with zarith.
 intros x Hx; rewrite spec_reduce_2.
 assert (F1:= spec_more_than_1_digit w2_spec).
 generalize (spec_head0 w2_spec x Hx).
 unfold base.
 pattern (Zpos (znz_digits w2_op)) at 1; 
 rewrite <- (fun x => (F0 (Zpos x))).
 rewrite Zpower_exp; auto with zarith.
 rewrite Zpower_1_r; rewrite Z_div_mult; auto with zarith.
 intros x Hx; rewrite spec_reduce_3.
 assert (F1:= spec_more_than_1_digit w3_spec).
 generalize (spec_head0 w3_spec x Hx).
 unfold base.
 pattern (Zpos (znz_digits w3_op)) at 1; 
 rewrite <- (fun x => (F0 (Zpos x))).
 rewrite Zpower_exp; auto with zarith.
 rewrite Zpower_1_r; rewrite Z_div_mult; auto with zarith.
 intros x Hx; rewrite spec_reduce_4.
 assert (F1:= spec_more_than_1_digit w4_spec).
 generalize (spec_head0 w4_spec x Hx).
 unfold base.
 pattern (Zpos (znz_digits w4_op)) at 1; 
 rewrite <- (fun x => (F0 (Zpos x))).
 rewrite Zpower_exp; auto with zarith.
 rewrite Zpower_1_r; rewrite Z_div_mult; auto with zarith.
 intros x Hx; rewrite spec_reduce_5.
 assert (F1:= spec_more_than_1_digit w5_spec).
 generalize (spec_head0 w5_spec x Hx).
 unfold base.
 pattern (Zpos (znz_digits w5_op)) at 1; 
 rewrite <- (fun x => (F0 (Zpos x))).
 rewrite Zpower_exp; auto with zarith.
 rewrite Zpower_1_r; rewrite Z_div_mult; auto with zarith.
 intros x Hx; rewrite spec_reduce_6.
 assert (F1:= spec_more_than_1_digit w6_spec).
 generalize (spec_head0 w6_spec x Hx).
 unfold base.
 pattern (Zpos (znz_digits w6_op)) at 1; 
 rewrite <- (fun x => (F0 (Zpos x))).
 rewrite Zpower_exp; auto with zarith.
 rewrite Zpower_1_r; rewrite Z_div_mult; auto with zarith.
 intros n x Hx; rewrite spec_reduce_n.
 assert (F1:= spec_more_than_1_digit (wn_spec n)).
 generalize (spec_head0 (wn_spec n) x Hx).
 unfold base.
 pattern (Zpos (znz_digits (make_op n))) at 1; 
 rewrite <- (fun x => (F0 (Zpos x))).
 rewrite Zpower_exp; auto with zarith.
 rewrite Zpower_1_r; rewrite Z_div_mult; auto with zarith.
 Qed.

 Definition tail0 w := match w with
 | N0 w=> reduce_0 (w0_op.(znz_tail0) w)
 | N1 w=> reduce_1 (w1_op.(znz_tail0) w)
 | N2 w=> reduce_2 (w2_op.(znz_tail0) w)
 | N3 w=> reduce_3 (w3_op.(znz_tail0) w)
 | N4 w=> reduce_4 (w4_op.(znz_tail0) w)
 | N5 w=> reduce_5 (w5_op.(znz_tail0) w)
 | N6 w=> reduce_6 (w6_op.(znz_tail0) w)
 | Nn n w=> reduce_n n ((make_op n).(znz_tail0) w)
 end.

 Theorem spec_tail00: forall x, [x] = 0 ->[tail0 x] = Zpos (digits x).
 Proof.
 intros x; case x; unfold tail0; clear x.
   intros x; rewrite spec_reduce_0; exact (spec_tail00 w0_spec x).
   intros x; rewrite spec_reduce_1; exact (spec_tail00 w1_spec x).
   intros x; rewrite spec_reduce_2; exact (spec_tail00 w2_spec x).
   intros x; rewrite spec_reduce_3; exact (spec_tail00 w3_spec x).
   intros x; rewrite spec_reduce_4; exact (spec_tail00 w4_spec x).
   intros x; rewrite spec_reduce_5; exact (spec_tail00 w5_spec x).
   intros x; rewrite spec_reduce_6; exact (spec_tail00 w6_spec x).
 intros n x; rewrite spec_reduce_n; exact (spec_tail00 (wn_spec n) x).
 Qed.
  
 Theorem spec_tail0: forall x,
   0 < [x] -> exists y, 0 <= y /\ [x] = (2 * y + 1) * 2 ^ [tail0 x].
 Proof.
 intros x; case x; clear x; unfold tail0.
 intros x Hx; rewrite spec_reduce_0; exact (spec_tail0 w0_spec x Hx).
 intros x Hx; rewrite spec_reduce_1; exact (spec_tail0 w1_spec x Hx).
 intros x Hx; rewrite spec_reduce_2; exact (spec_tail0 w2_spec x Hx).
 intros x Hx; rewrite spec_reduce_3; exact (spec_tail0 w3_spec x Hx).
 intros x Hx; rewrite spec_reduce_4; exact (spec_tail0 w4_spec x Hx).
 intros x Hx; rewrite spec_reduce_5; exact (spec_tail0 w5_spec x Hx).
 intros x Hx; rewrite spec_reduce_6; exact (spec_tail0 w6_spec x Hx).
 intros n x Hx; rewrite spec_reduce_n; exact (spec_tail0 (wn_spec n) x Hx).
 Qed.

 Definition Ndigits x :=
  match x with
  | N0 _ => N0 w0_op.(znz_zdigits)
  | N1 _ => reduce_1 w1_op.(znz_zdigits)
  | N2 _ => reduce_2 w2_op.(znz_zdigits)
  | N3 _ => reduce_3 w3_op.(znz_zdigits)
  | N4 _ => reduce_4 w4_op.(znz_zdigits)
  | N5 _ => reduce_5 w5_op.(znz_zdigits)
  | N6 _ => reduce_6 w6_op.(znz_zdigits)
  | Nn n _ => reduce_n n (make_op n).(znz_zdigits)
  end.

 Theorem spec_Ndigits: forall x, [Ndigits x] = Zpos (digits x).
 Proof.
 intros x; case x; clear x; unfold Ndigits, digits.
 intros _; try rewrite spec_reduce_0; exact (spec_zdigits w0_spec).
 intros _; try rewrite spec_reduce_1; exact (spec_zdigits w1_spec).
 intros _; try rewrite spec_reduce_2; exact (spec_zdigits w2_spec).
 intros _; try rewrite spec_reduce_3; exact (spec_zdigits w3_spec).
 intros _; try rewrite spec_reduce_4; exact (spec_zdigits w4_spec).
 intros _; try rewrite spec_reduce_5; exact (spec_zdigits w5_spec).
 intros _; try rewrite spec_reduce_6; exact (spec_zdigits w6_spec).
 intros n _; try rewrite spec_reduce_n; exact (spec_zdigits (wn_spec n)).
 Qed.

 Definition shiftr0 n x := w0_op.(znz_add_mul_div) (w0_op.(znz_sub) w0_op.(znz_zdigits) n) w0_op.(znz_0) x.
 Definition shiftr1 n x := w1_op.(znz_add_mul_div) (w1_op.(znz_sub) w1_op.(znz_zdigits) n) w1_op.(znz_0) x.
 Definition shiftr2 n x := w2_op.(znz_add_mul_div) (w2_op.(znz_sub) w2_op.(znz_zdigits) n) w2_op.(znz_0) x.
 Definition shiftr3 n x := w3_op.(znz_add_mul_div) (w3_op.(znz_sub) w3_op.(znz_zdigits) n) w3_op.(znz_0) x.
 Definition shiftr4 n x := w4_op.(znz_add_mul_div) (w4_op.(znz_sub) w4_op.(znz_zdigits) n) w4_op.(znz_0) x.
 Definition shiftr5 n x := w5_op.(znz_add_mul_div) (w5_op.(znz_sub) w5_op.(znz_zdigits) n) w5_op.(znz_0) x.
 Definition shiftr6 n x := w6_op.(znz_add_mul_div) (w6_op.(znz_sub) w6_op.(znz_zdigits) n) w6_op.(znz_0) x.
 Definition shiftrn n p x := (make_op n).(znz_add_mul_div) ((make_op n).(znz_sub) (make_op n).(znz_zdigits) p) (make_op n).(znz_0) x.

 Definition shiftr := Eval lazy beta delta [same_level] in 
     same_level _ (fun n x => N0 (shiftr0 n x))
           (fun n x => reduce_1 (shiftr1 n x))
           (fun n x => reduce_2 (shiftr2 n x))
           (fun n x => reduce_3 (shiftr3 n x))
           (fun n x => reduce_4 (shiftr4 n x))
           (fun n x => reduce_5 (shiftr5 n x))
           (fun n x => reduce_6 (shiftr6 n x))
           (fun n p x => reduce_n n (shiftrn n p x)).

 Theorem spec_shiftr: forall n x,
  [n] <= [Ndigits x] -> [shiftr n x] = [x] / 2 ^ [n].
 Proof.
 assert (F0: forall x y, x - (x - y) = y).
   intros; ring.
 assert (F2: forall x y z, 0 <= x -> 0 <= y -> x < z -> 0 <= x / 2 ^ y < z).
   intros x y z HH HH1 HH2.
   split; auto with zarith.
   apply Zle_lt_trans with (2 := HH2); auto with zarith.
   apply Zdiv_le_upper_bound; auto with zarith.
   pattern x at 1; replace x with (x * 2 ^ 0); auto with zarith.
   apply Zmult_le_compat_l; auto.
   apply Zpower_le_monotone; auto with zarith.
   rewrite Zpower_0_r; ring.
  assert (F3: forall x y, 0 <= y -> y <= x -> 0 <= x - y < 2 ^ x).
    intros xx y HH HH1.
    split; auto with zarith.
    apply Zle_lt_trans with xx; auto with zarith.
    apply Zpower2_lt_lin; auto with zarith.
  assert (F4: forall ww ww1 ww2 
         (ww_op: znz_op ww) (ww1_op: znz_op ww1) (ww2_op: znz_op ww2)
           xx yy xx1 yy1,
  znz_to_Z ww2_op yy <= znz_to_Z ww1_op (znz_zdigits ww1_op) ->
  znz_to_Z ww1_op (znz_zdigits ww1_op) <= znz_to_Z ww_op (znz_zdigits ww_op) ->
  znz_spec ww_op -> znz_spec ww1_op -> znz_spec ww2_op ->
  znz_to_Z ww_op xx1 = znz_to_Z ww1_op xx ->
  znz_to_Z ww_op yy1 = znz_to_Z ww2_op yy ->
  znz_to_Z ww_op
  (znz_add_mul_div ww_op (znz_sub ww_op (znz_zdigits ww_op)  yy1)
     (znz_0 ww_op) xx1) = znz_to_Z ww1_op xx / 2 ^ znz_to_Z ww2_op yy).
  intros ww ww1 ww2 ww_op ww1_op ww2_op xx yy xx1 yy1 Hl Hl1 Hw Hw1 Hw2 Hx Hy.
     case (spec_to_Z Hw xx1); auto with zarith; intros HH1 HH2.
     case (spec_to_Z Hw yy1); auto with zarith; intros HH3 HH4.
     rewrite <- Hx.
     rewrite <- Hy.
     generalize (spec_add_mul_div Hw
                  (znz_0 ww_op) xx1
                  (znz_sub ww_op (znz_zdigits ww_op) 
                    yy1)
                ).
     rewrite (spec_0 Hw).
     rewrite Zmult_0_l; rewrite Zplus_0_l.
     rewrite (ZnZ.spec_sub Hw).
     rewrite Zmod_small; auto with zarith.
     rewrite (spec_zdigits Hw).
     rewrite F0.
     rewrite Zmod_small; auto with zarith.
     unfold base; rewrite (spec_zdigits Hw) in Hl1 |- *;
      auto with zarith.
  assert (F5: forall n m, (n <= m)%nat ->
     Zpos (znz_digits (make_op n)) <= Zpos (znz_digits (make_op m))).
    intros n m HH; elim HH; clear m HH; auto with zarith.
    intros m HH Hrec; apply Zle_trans with (1 := Hrec).
    rewrite make_op_S.
    match goal with |- Zpos ?Y <= ?X => change X with (Zpos (xO Y)) end.
    rewrite Zpos_xO.
    assert (0 <= Zpos (znz_digits (make_op n))); auto with zarith.
  assert (F6: forall n, Zpos (znz_digits w6_op) <= Zpos (znz_digits (make_op n))).
    intros n ; apply Zle_trans with (Zpos (znz_digits (make_op 0))).
    change (znz_digits (make_op 0)) with (xO (znz_digits w6_op)).
    rewrite Zpos_xO.
    assert (0 <= Zpos (znz_digits w6_op)); auto with zarith.
    apply F5; auto with arith.
  intros x; case x; clear x; unfold shiftr, same_level.
    intros x y; case y; clear y.
     intros y; unfold shiftr0, Ndigits.
     repeat rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=w0_spec)(4:=w0_spec)(5:=w0_spec); auto with zarith.
     intros y; unfold shiftr1, Ndigits.
       repeat rewrite spec_reduce_0; repeat rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=w1_spec)(4:=w1_spec)(5:=w0_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n1 x)).
     intros y; unfold shiftr2, Ndigits.
       repeat rewrite spec_reduce_0; repeat rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=w2_spec)(4:=w2_spec)(5:=w0_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n2 x)).
     intros y; unfold shiftr3, Ndigits.
       repeat rewrite spec_reduce_0; repeat rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=w3_spec)(4:=w3_spec)(5:=w0_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n3 x)).
     intros y; unfold shiftr4, Ndigits.
       repeat rewrite spec_reduce_0; repeat rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w4_spec)(5:=w0_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n4 x)).
     intros y; unfold shiftr5, Ndigits.
       repeat rewrite spec_reduce_0; repeat rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w5_spec)(5:=w0_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n5 x)).
     intros y; unfold shiftr6, Ndigits.
       repeat rewrite spec_reduce_0; repeat rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w6_spec)(5:=w0_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n6 x)).
     intros m y; unfold shiftrn, Ndigits.
       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w0_spec); auto with zarith.
       change ([Nn m (extend6 m (extend0 5 x))] = [N0 x]).
       rewrite <- (spec_extend6n m); rewrite <- spec_extend0n6; auto.
    intros x y; case y; clear y.
     intros y; unfold shiftr1, Ndigits.
       repeat rewrite spec_reduce_1; repeat rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=w1_spec)(4:=w0_spec)(5:=w1_spec); auto with zarith.
       rewrite (spec_zdigits w1_spec).
       rewrite (spec_zdigits w0_spec).
       change (znz_digits w1_op) with  (xO (znz_digits w0_op)).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w0_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n1 y)).
     intros y; unfold shiftr1, Ndigits.
     repeat rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=w1_spec)(4:=w1_spec)(5:=w1_spec); auto with zarith.
     intros y; unfold shiftr2, Ndigits.
       repeat rewrite spec_reduce_1; repeat rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=w2_spec)(4:=w2_spec)(5:=w1_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n2 x)).
     intros y; unfold shiftr3, Ndigits.
       repeat rewrite spec_reduce_1; repeat rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=w3_spec)(4:=w3_spec)(5:=w1_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n3 x)).
     intros y; unfold shiftr4, Ndigits.
       repeat rewrite spec_reduce_1; repeat rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w4_spec)(5:=w1_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n4 x)).
     intros y; unfold shiftr5, Ndigits.
       repeat rewrite spec_reduce_1; repeat rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w5_spec)(5:=w1_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n5 x)).
     intros y; unfold shiftr6, Ndigits.
       repeat rewrite spec_reduce_1; repeat rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w6_spec)(5:=w1_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n6 x)).
     intros m y; unfold shiftrn, Ndigits.
       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w1_spec); auto with zarith.
       change ([Nn m (extend6 m (extend1 4 x))] = [N1 x]).
       rewrite <- (spec_extend6n m); rewrite <- spec_extend1n6; auto.
    intros x y; case y; clear y.
     intros y; unfold shiftr2, Ndigits.
       repeat rewrite spec_reduce_2; repeat rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=w2_spec)(4:=w0_spec)(5:=w2_spec); auto with zarith.
       rewrite (spec_zdigits w2_spec).
       rewrite (spec_zdigits w0_spec).
       change (znz_digits w2_op) with  (xO (xO (znz_digits w0_op))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w0_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n2 y)).
     intros y; unfold shiftr2, Ndigits.
       repeat rewrite spec_reduce_2; repeat rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=w2_spec)(4:=w1_spec)(5:=w2_spec); auto with zarith.
       rewrite (spec_zdigits w2_spec).
       rewrite (spec_zdigits w1_spec).
       change (znz_digits w2_op) with  (xO (znz_digits w1_op)).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w1_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n2 y)).
     intros y; unfold shiftr2, Ndigits.
     repeat rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=w2_spec)(4:=w2_spec)(5:=w2_spec); auto with zarith.
     intros y; unfold shiftr3, Ndigits.
       repeat rewrite spec_reduce_2; repeat rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=w3_spec)(4:=w3_spec)(5:=w2_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n3 x)).
     intros y; unfold shiftr4, Ndigits.
       repeat rewrite spec_reduce_2; repeat rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w4_spec)(5:=w2_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n4 x)).
     intros y; unfold shiftr5, Ndigits.
       repeat rewrite spec_reduce_2; repeat rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w5_spec)(5:=w2_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n5 x)).
     intros y; unfold shiftr6, Ndigits.
       repeat rewrite spec_reduce_2; repeat rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w6_spec)(5:=w2_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n6 x)).
     intros m y; unfold shiftrn, Ndigits.
       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w2_spec); auto with zarith.
       change ([Nn m (extend6 m (extend2 3 x))] = [N2 x]).
       rewrite <- (spec_extend6n m); rewrite <- spec_extend2n6; auto.
    intros x y; case y; clear y.
     intros y; unfold shiftr3, Ndigits.
       repeat rewrite spec_reduce_3; repeat rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=w3_spec)(4:=w0_spec)(5:=w3_spec); auto with zarith.
       rewrite (spec_zdigits w3_spec).
       rewrite (spec_zdigits w0_spec).
       change (znz_digits w3_op) with  (xO (xO (xO (znz_digits w0_op)))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w0_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n3 y)).
     intros y; unfold shiftr3, Ndigits.
       repeat rewrite spec_reduce_3; repeat rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=w3_spec)(4:=w1_spec)(5:=w3_spec); auto with zarith.
       rewrite (spec_zdigits w3_spec).
       rewrite (spec_zdigits w1_spec).
       change (znz_digits w3_op) with  (xO (xO (znz_digits w1_op))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w1_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n3 y)).
     intros y; unfold shiftr3, Ndigits.
       repeat rewrite spec_reduce_3; repeat rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=w3_spec)(4:=w2_spec)(5:=w3_spec); auto with zarith.
       rewrite (spec_zdigits w3_spec).
       rewrite (spec_zdigits w2_spec).
       change (znz_digits w3_op) with  (xO (znz_digits w2_op)).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w2_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n3 y)).
     intros y; unfold shiftr3, Ndigits.
     repeat rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=w3_spec)(4:=w3_spec)(5:=w3_spec); auto with zarith.
     intros y; unfold shiftr4, Ndigits.
       repeat rewrite spec_reduce_3; repeat rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w4_spec)(5:=w3_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend3n4 x)).
     intros y; unfold shiftr5, Ndigits.
       repeat rewrite spec_reduce_3; repeat rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w5_spec)(5:=w3_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend3n5 x)).
     intros y; unfold shiftr6, Ndigits.
       repeat rewrite spec_reduce_3; repeat rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w6_spec)(5:=w3_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend3n6 x)).
     intros m y; unfold shiftrn, Ndigits.
       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w3_spec); auto with zarith.
       change ([Nn m (extend6 m (extend3 2 x))] = [N3 x]).
       rewrite <- (spec_extend6n m); rewrite <- spec_extend3n6; auto.
    intros x y; case y; clear y.
     intros y; unfold shiftr4, Ndigits.
       repeat rewrite spec_reduce_4; repeat rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w0_spec)(5:=w4_spec); auto with zarith.
       rewrite (spec_zdigits w4_spec).
       rewrite (spec_zdigits w0_spec).
       change (znz_digits w4_op) with  (xO (xO (xO (xO (znz_digits w0_op))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w0_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n4 y)).
     intros y; unfold shiftr4, Ndigits.
       repeat rewrite spec_reduce_4; repeat rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w1_spec)(5:=w4_spec); auto with zarith.
       rewrite (spec_zdigits w4_spec).
       rewrite (spec_zdigits w1_spec).
       change (znz_digits w4_op) with  (xO (xO (xO (znz_digits w1_op)))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w1_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n4 y)).
     intros y; unfold shiftr4, Ndigits.
       repeat rewrite spec_reduce_4; repeat rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w2_spec)(5:=w4_spec); auto with zarith.
       rewrite (spec_zdigits w4_spec).
       rewrite (spec_zdigits w2_spec).
       change (znz_digits w4_op) with  (xO (xO (znz_digits w2_op))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w2_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n4 y)).
     intros y; unfold shiftr4, Ndigits.
       repeat rewrite spec_reduce_4; repeat rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w3_spec)(5:=w4_spec); auto with zarith.
       rewrite (spec_zdigits w4_spec).
       rewrite (spec_zdigits w3_spec).
       change (znz_digits w4_op) with  (xO (znz_digits w3_op)).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w3_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend3n4 y)).
     intros y; unfold shiftr4, Ndigits.
     repeat rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w4_spec)(5:=w4_spec); auto with zarith.
     intros y; unfold shiftr5, Ndigits.
       repeat rewrite spec_reduce_4; repeat rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w5_spec)(5:=w4_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend4n5 x)).
     intros y; unfold shiftr6, Ndigits.
       repeat rewrite spec_reduce_4; repeat rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w6_spec)(5:=w4_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend4n6 x)).
     intros m y; unfold shiftrn, Ndigits.
       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w4_spec); auto with zarith.
       change ([Nn m (extend6 m (extend4 1 x))] = [N4 x]).
       rewrite <- (spec_extend6n m); rewrite <- spec_extend4n6; auto.
    intros x y; case y; clear y.
     intros y; unfold shiftr5, Ndigits.
       repeat rewrite spec_reduce_5; repeat rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w0_spec)(5:=w5_spec); auto with zarith.
       rewrite (spec_zdigits w5_spec).
       rewrite (spec_zdigits w0_spec).
       change (znz_digits w5_op) with  (xO (xO (xO (xO (xO (znz_digits w0_op)))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w0_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n5 y)).
     intros y; unfold shiftr5, Ndigits.
       repeat rewrite spec_reduce_5; repeat rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w1_spec)(5:=w5_spec); auto with zarith.
       rewrite (spec_zdigits w5_spec).
       rewrite (spec_zdigits w1_spec).
       change (znz_digits w5_op) with  (xO (xO (xO (xO (znz_digits w1_op))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w1_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n5 y)).
     intros y; unfold shiftr5, Ndigits.
       repeat rewrite spec_reduce_5; repeat rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w2_spec)(5:=w5_spec); auto with zarith.
       rewrite (spec_zdigits w5_spec).
       rewrite (spec_zdigits w2_spec).
       change (znz_digits w5_op) with  (xO (xO (xO (znz_digits w2_op)))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w2_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n5 y)).
     intros y; unfold shiftr5, Ndigits.
       repeat rewrite spec_reduce_5; repeat rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w3_spec)(5:=w5_spec); auto with zarith.
       rewrite (spec_zdigits w5_spec).
       rewrite (spec_zdigits w3_spec).
       change (znz_digits w5_op) with  (xO (xO (znz_digits w3_op))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w3_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend3n5 y)).
     intros y; unfold shiftr5, Ndigits.
       repeat rewrite spec_reduce_5; repeat rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w4_spec)(5:=w5_spec); auto with zarith.
       rewrite (spec_zdigits w5_spec).
       rewrite (spec_zdigits w4_spec).
       change (znz_digits w5_op) with  (xO (znz_digits w4_op)).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w4_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend4n5 y)).
     intros y; unfold shiftr5, Ndigits.
     repeat rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w5_spec)(5:=w5_spec); auto with zarith.
     intros y; unfold shiftr6, Ndigits.
       repeat rewrite spec_reduce_5; repeat rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w6_spec)(5:=w5_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend5n6 x)).
     intros m y; unfold shiftrn, Ndigits.
       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w5_spec); auto with zarith.
       change ([Nn m (extend6 m (extend5 0 x))] = [N5 x]).
       rewrite <- (spec_extend6n m); rewrite <- spec_extend5n6; auto.
    intros x y; case y; clear y.
     intros y; unfold shiftr6, Ndigits.
       repeat rewrite spec_reduce_6; repeat rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w0_spec)(5:=w6_spec); auto with zarith.
       rewrite (spec_zdigits w6_spec).
       rewrite (spec_zdigits w0_spec).
       change (znz_digits w6_op) with  (xO (xO (xO (xO (xO (xO (znz_digits w0_op))))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w0_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n6 y)).
     intros y; unfold shiftr6, Ndigits.
       repeat rewrite spec_reduce_6; repeat rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w1_spec)(5:=w6_spec); auto with zarith.
       rewrite (spec_zdigits w6_spec).
       rewrite (spec_zdigits w1_spec).
       change (znz_digits w6_op) with  (xO (xO (xO (xO (xO (znz_digits w1_op)))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w1_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n6 y)).
     intros y; unfold shiftr6, Ndigits.
       repeat rewrite spec_reduce_6; repeat rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w2_spec)(5:=w6_spec); auto with zarith.
       rewrite (spec_zdigits w6_spec).
       rewrite (spec_zdigits w2_spec).
       change (znz_digits w6_op) with  (xO (xO (xO (xO (znz_digits w2_op))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w2_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n6 y)).
     intros y; unfold shiftr6, Ndigits.
       repeat rewrite spec_reduce_6; repeat rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w3_spec)(5:=w6_spec); auto with zarith.
       rewrite (spec_zdigits w6_spec).
       rewrite (spec_zdigits w3_spec).
       change (znz_digits w6_op) with  (xO (xO (xO (znz_digits w3_op)))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w3_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend3n6 y)).
     intros y; unfold shiftr6, Ndigits.
       repeat rewrite spec_reduce_6; repeat rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w4_spec)(5:=w6_spec); auto with zarith.
       rewrite (spec_zdigits w6_spec).
       rewrite (spec_zdigits w4_spec).
       change (znz_digits w6_op) with  (xO (xO (znz_digits w4_op))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w4_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend4n6 y)).
     intros y; unfold shiftr6, Ndigits.
       repeat rewrite spec_reduce_6; repeat rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w5_spec)(5:=w6_spec); auto with zarith.
       rewrite (spec_zdigits w6_spec).
       rewrite (spec_zdigits w5_spec).
       change (znz_digits w6_op) with  (xO (znz_digits w5_op)).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w5_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend5n6 y)).
     intros y; unfold shiftr6, Ndigits.
     repeat rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w6_spec)(5:=w6_spec); auto with zarith.
     intros m y; unfold shiftrn, Ndigits.
       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w6_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend6n m x)).
    intros n x y; case y; clear y;
     intros y; unfold shiftrn, Ndigits; try rewrite spec_reduce_n.
     try rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec n))(4:=w0_spec)(5:=wn_spec n); auto with zarith.
       rewrite (spec_zdigits w0_spec).
       rewrite (spec_zdigits (wn_spec n)).
       apply Zle_trans with (2 := F6 n).
       change (znz_digits w6_op) with  (xO (xO (xO (xO (xO (xO(znz_digits w0_op))))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (H: 0 <= Zpos (znz_digits w0_op)); auto with zarith.
       change ([Nn n (extend6 n (extend0 5 y))] = [N0 y]).
       rewrite <- (spec_extend6n n); auto.
       try (rewrite <- spec_extend0n6; auto).
     try rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec n))(4:=w1_spec)(5:=wn_spec n); auto with zarith.
       rewrite (spec_zdigits w1_spec).
       rewrite (spec_zdigits (wn_spec n)).
       apply Zle_trans with (2 := F6 n).
       change (znz_digits w6_op) with  (xO (xO (xO (xO (xO(znz_digits w1_op)))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (H: 0 <= Zpos (znz_digits w1_op)); auto with zarith.
       change ([Nn n (extend6 n (extend1 4 y))] = [N1 y]).
       rewrite <- (spec_extend6n n); auto.
       try (rewrite <- spec_extend1n6; auto).
     try rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec n))(4:=w2_spec)(5:=wn_spec n); auto with zarith.
       rewrite (spec_zdigits w2_spec).
       rewrite (spec_zdigits (wn_spec n)).
       apply Zle_trans with (2 := F6 n).
       change (znz_digits w6_op) with  (xO (xO (xO (xO(znz_digits w2_op))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (H: 0 <= Zpos (znz_digits w2_op)); auto with zarith.
       change ([Nn n (extend6 n (extend2 3 y))] = [N2 y]).
       rewrite <- (spec_extend6n n); auto.
       try (rewrite <- spec_extend2n6; auto).
     try rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec n))(4:=w3_spec)(5:=wn_spec n); auto with zarith.
       rewrite (spec_zdigits w3_spec).
       rewrite (spec_zdigits (wn_spec n)).
       apply Zle_trans with (2 := F6 n).
       change (znz_digits w6_op) with  (xO (xO (xO(znz_digits w3_op)))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (H: 0 <= Zpos (znz_digits w3_op)); auto with zarith.
       change ([Nn n (extend6 n (extend3 2 y))] = [N3 y]).
       rewrite <- (spec_extend6n n); auto.
       try (rewrite <- spec_extend3n6; auto).
     try rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec n))(4:=w4_spec)(5:=wn_spec n); auto with zarith.
       rewrite (spec_zdigits w4_spec).
       rewrite (spec_zdigits (wn_spec n)).
       apply Zle_trans with (2 := F6 n).
       change (znz_digits w6_op) with  (xO (xO(znz_digits w4_op))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (H: 0 <= Zpos (znz_digits w4_op)); auto with zarith.
       change ([Nn n (extend6 n (extend4 1 y))] = [N4 y]).
       rewrite <- (spec_extend6n n); auto.
       try (rewrite <- spec_extend4n6; auto).
     try rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec n))(4:=w5_spec)(5:=wn_spec n); auto with zarith.
       rewrite (spec_zdigits w5_spec).
       rewrite (spec_zdigits (wn_spec n)).
       apply Zle_trans with (2 := F6 n).
       change (znz_digits w6_op) with  (xO(znz_digits w5_op)).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (H: 0 <= Zpos (znz_digits w5_op)); auto with zarith.
       change ([Nn n (extend6 n (extend5 0 y))] = [N5 y]).
       rewrite <- (spec_extend6n n); auto.
       try (rewrite <- spec_extend5n6; auto).
     try rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec n))(4:=w6_spec)(5:=wn_spec n); auto with zarith.
       rewrite (spec_zdigits w6_spec).
       rewrite (spec_zdigits (wn_spec n)).
       apply Zle_trans with (2 := F6 n).
       change (znz_digits w6_op) with (znz_digits w6_op).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (H: 0 <= Zpos (znz_digits w6_op)); auto with zarith.
       change ([Nn n (extend6 n y)] = [N6 y]).
       rewrite <- (spec_extend6n n); auto.
     generalize y; clear y; intros m y.
     rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec (Max.max n m)))(4:=wn_spec m)(5:=wn_spec n); auto with zarith.
     rewrite (spec_zdigits (wn_spec m)).
     rewrite (spec_zdigits (wn_spec (Max.max n m))).
     apply F5; auto with arith.
     exact (spec_cast_r n m y).
     exact (spec_cast_l n m x).
 Qed.

 Definition safe_shiftr n x := 
   match compare n (Ndigits x) with
    |  Lt => shiftr n x 
   | _ => N0 w_0
   end.

 Theorem spec_safe_shiftr: forall n x,
   [safe_shiftr n x] = [x] / 2 ^ [n].
 Proof.
 intros n x; unfold safe_shiftr;
    generalize (spec_compare n (Ndigits x)); case compare; intros H.
 apply trans_equal with (1 := spec_0 w0_spec).
 apply sym_equal; apply Zdiv_small; rewrite H.
 rewrite spec_Ndigits; exact (spec_digits x).
 rewrite <- spec_shiftr; auto with zarith.
 apply trans_equal with (1 := spec_0 w0_spec).
 apply sym_equal; apply Zdiv_small.
 rewrite spec_Ndigits in H; case (spec_digits x); intros H1 H2.
 split; auto.
 apply Zlt_le_trans with (1 := H2).
 apply Zpower_le_monotone; auto with zarith.
 Qed.


 Definition shiftl0 n x := w0_op.(znz_add_mul_div) n x w0_op.(znz_0).
 Definition shiftl1 n x := w1_op.(znz_add_mul_div) n x w1_op.(znz_0).
 Definition shiftl2 n x := w2_op.(znz_add_mul_div) n x w2_op.(znz_0).
 Definition shiftl3 n x := w3_op.(znz_add_mul_div) n x w3_op.(znz_0).
 Definition shiftl4 n x := w4_op.(znz_add_mul_div) n x w4_op.(znz_0).
 Definition shiftl5 n x := w5_op.(znz_add_mul_div) n x w5_op.(znz_0).
 Definition shiftl6 n x := w6_op.(znz_add_mul_div) n x w6_op.(znz_0).
 Definition shiftln n p x := (make_op n).(znz_add_mul_div) p x (make_op n).(znz_0).
 Definition shiftl := Eval lazy beta delta [same_level] in
    same_level _ (fun n x => N0 (shiftl0 n x))
           (fun n x => reduce_1 (shiftl1 n x))
           (fun n x => reduce_2 (shiftl2 n x))
           (fun n x => reduce_3 (shiftl3 n x))
           (fun n x => reduce_4 (shiftl4 n x))
           (fun n x => reduce_5 (shiftl5 n x))
           (fun n x => reduce_6 (shiftl6 n x))
           (fun n p x => reduce_n n (shiftln n p x)).


 Theorem spec_shiftl: forall n x,
  [n] <= [head0 x] -> [shiftl n x] = [x] * 2 ^ [n].
 Proof.
 assert (F0: forall x y, x - (x - y) = y).
   intros; ring.
 assert (F2: forall x y z, 0 <= x -> 0 <= y -> x < z -> 0 <= x / 2 ^ y < z).
   intros x y z HH HH1 HH2.
   split; auto with zarith.
   apply Zle_lt_trans with (2 := HH2); auto with zarith.
   apply Zdiv_le_upper_bound; auto with zarith.
   pattern x at 1; replace x with (x * 2 ^ 0); auto with zarith.
   apply Zmult_le_compat_l; auto.
   apply Zpower_le_monotone; auto with zarith.
   rewrite Zpower_0_r; ring.
  assert (F3: forall x y, 0 <= y -> y <= x -> 0 <= x - y < 2 ^ x).
    intros xx y HH HH1.
    split; auto with zarith.
    apply Zle_lt_trans with xx; auto with zarith.
    apply Zpower2_lt_lin; auto with zarith.
  assert (F4: forall ww ww1 ww2 
         (ww_op: znz_op ww) (ww1_op: znz_op ww1) (ww2_op: znz_op ww2)
           xx yy xx1 yy1,
  znz_to_Z ww2_op yy <= znz_to_Z ww1_op (znz_head0 ww1_op xx) ->
  znz_to_Z ww1_op (znz_zdigits ww1_op) <= znz_to_Z ww_op (znz_zdigits ww_op) ->
  znz_spec ww_op -> znz_spec ww1_op -> znz_spec ww2_op ->
  znz_to_Z ww_op xx1 = znz_to_Z ww1_op xx ->
  znz_to_Z ww_op yy1 = znz_to_Z ww2_op yy ->
  znz_to_Z ww_op
  (znz_add_mul_div ww_op yy1
     xx1 (znz_0 ww_op)) = znz_to_Z ww1_op xx * 2 ^ znz_to_Z ww2_op yy).
  intros ww ww1 ww2 ww_op ww1_op ww2_op xx yy xx1 yy1 Hl Hl1 Hw Hw1 Hw2 Hx Hy.
     case (spec_to_Z Hw xx1); auto with zarith; intros HH1 HH2.
     case (spec_to_Z Hw yy1); auto with zarith; intros HH3 HH4.
     rewrite <- Hx.
     rewrite <- Hy.
     generalize (spec_add_mul_div Hw xx1 (znz_0 ww_op) yy1).
     rewrite (spec_0 Hw).
     assert (F1: znz_to_Z ww1_op (znz_head0 ww1_op xx) <= Zpos (znz_digits ww1_op)).
     case (Zle_lt_or_eq _ _ HH1); intros HH5.
     apply Zlt_le_weak.
     case (ZnZ.spec_head0 Hw1 xx).
       rewrite <- Hx; auto.
     intros _ Hu; unfold base in Hu.
     case (Zle_or_lt (Zpos (znz_digits ww1_op))
                     (znz_to_Z ww1_op (znz_head0 ww1_op xx))); auto; intros H1.
     absurd (2 ^  (Zpos (znz_digits ww1_op)) <= 2 ^ (znz_to_Z ww1_op (znz_head0 ww1_op xx))).
       apply Zlt_not_le.
       case (spec_to_Z Hw1 xx); intros HHx3 HHx4.
       rewrite <- (Zmult_1_r (2 ^ znz_to_Z ww1_op (znz_head0 ww1_op xx))).
       apply Zle_lt_trans with (2 := Hu).
       apply Zmult_le_compat_l; auto with zarith.
     apply Zpower_le_monotone; auto with zarith.
     rewrite (ZnZ.spec_head00 Hw1 xx); auto with zarith.
     rewrite Zdiv_0_l; auto with zarith.
     rewrite Zplus_0_r.
     case (Zle_lt_or_eq _ _ HH1); intros HH5.
     rewrite Zmod_small; auto with zarith.
     intros HH; apply HH.
     rewrite Hy; apply Zle_trans with (1:= Hl).
     rewrite <- (spec_zdigits Hw). 
     apply Zle_trans with (2 := Hl1); auto.
     rewrite  (spec_zdigits Hw1); auto with zarith.
     split; auto with zarith .
     apply Zlt_le_trans with (base (znz_digits ww1_op)).
     rewrite Hx.
     case (ZnZ.spec_head0 Hw1 xx); auto.
       rewrite <- Hx; auto.
     intros _ Hu; rewrite Zmult_comm in Hu.
     apply Zle_lt_trans with (2 := Hu).
     apply Zmult_le_compat_l; auto with zarith.
     apply Zpower_le_monotone; auto with zarith.
     unfold base; apply Zpower_le_monotone; auto with zarith.
     split; auto with zarith.
     rewrite <- (spec_zdigits Hw); auto with zarith.
     rewrite <- (spec_zdigits Hw1); auto with zarith.
     rewrite <- HH5.
     rewrite Zmult_0_l.
     rewrite Zmod_small; auto with zarith.
     intros HH; apply HH.
     rewrite Hy; apply Zle_trans with (1 := Hl).
     rewrite (ZnZ.spec_head00 Hw1 xx); auto with zarith.
     rewrite <- (spec_zdigits Hw); auto with zarith.
     rewrite <- (spec_zdigits Hw1); auto with zarith.
  assert (F5: forall n m, (n <= m)%nat ->
     Zpos (znz_digits (make_op n)) <= Zpos (znz_digits (make_op m))).
    intros n m HH; elim HH; clear m HH; auto with zarith.
    intros m HH Hrec; apply Zle_trans with (1 := Hrec).
    rewrite make_op_S.
    match goal with |- Zpos ?Y <= ?X => change X with (Zpos (xO Y)) end.
    rewrite Zpos_xO.
    assert (0 <= Zpos (znz_digits (make_op n))); auto with zarith.
  assert (F6: forall n, Zpos (znz_digits w6_op) <= Zpos (znz_digits (make_op n))).
    intros n ; apply Zle_trans with (Zpos (znz_digits (make_op 0))).
    change (znz_digits (make_op 0)) with (xO (znz_digits w6_op)).
    rewrite Zpos_xO.
    assert (0 <= Zpos (znz_digits w6_op)); auto with zarith.
    apply F5; auto with arith.
  intros x; case x; clear x; unfold shiftl, same_level.
    intros x y; case y; clear y.
     intros y; unfold shiftl0, head0.
     repeat rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=w0_spec)(4:=w0_spec)(5:=w0_spec); auto with zarith.
     intros y; unfold shiftl1, head0.
       repeat rewrite spec_reduce_0; repeat rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=w1_spec)(4:=w1_spec)(5:=w0_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n1 x)).
     intros y; unfold shiftl2, head0.
       repeat rewrite spec_reduce_0; repeat rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=w2_spec)(4:=w2_spec)(5:=w0_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n2 x)).
     intros y; unfold shiftl3, head0.
       repeat rewrite spec_reduce_0; repeat rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=w3_spec)(4:=w3_spec)(5:=w0_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n3 x)).
     intros y; unfold shiftl4, head0.
       repeat rewrite spec_reduce_0; repeat rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w4_spec)(5:=w0_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n4 x)).
     intros y; unfold shiftl5, head0.
       repeat rewrite spec_reduce_0; repeat rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w5_spec)(5:=w0_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n5 x)).
     intros y; unfold shiftl6, head0.
       repeat rewrite spec_reduce_0; repeat rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w6_spec)(5:=w0_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n6 x)).
     intros m y; unfold shiftln, head0.
       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w0_spec); auto with zarith.
       change ([Nn m (extend6 m (extend0 5 x))] = [N0 x]).
       rewrite <- (spec_extend6n m); rewrite <- spec_extend0n6; auto.
    intros x y; case y; clear y.
     intros y; unfold shiftl1, head0.
       repeat rewrite spec_reduce_1; repeat rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=w1_spec)(4:=w0_spec)(5:=w1_spec); auto with zarith.
       rewrite (spec_zdigits w1_spec).
       rewrite (spec_zdigits w0_spec).
       change (znz_digits w1_op) with  (xO (znz_digits w0_op)).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w0_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n1 y)).
     intros y; unfold shiftl1, head0.
     repeat rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=w1_spec)(4:=w1_spec)(5:=w1_spec); auto with zarith.
     intros y; unfold shiftl2, head0.
       repeat rewrite spec_reduce_1; repeat rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=w2_spec)(4:=w2_spec)(5:=w1_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n2 x)).
     intros y; unfold shiftl3, head0.
       repeat rewrite spec_reduce_1; repeat rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=w3_spec)(4:=w3_spec)(5:=w1_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n3 x)).
     intros y; unfold shiftl4, head0.
       repeat rewrite spec_reduce_1; repeat rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w4_spec)(5:=w1_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n4 x)).
     intros y; unfold shiftl5, head0.
       repeat rewrite spec_reduce_1; repeat rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w5_spec)(5:=w1_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n5 x)).
     intros y; unfold shiftl6, head0.
       repeat rewrite spec_reduce_1; repeat rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w6_spec)(5:=w1_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n6 x)).
     intros m y; unfold shiftln, head0.
       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w1_spec); auto with zarith.
       change ([Nn m (extend6 m (extend1 4 x))] = [N1 x]).
       rewrite <- (spec_extend6n m); rewrite <- spec_extend1n6; auto.
    intros x y; case y; clear y.
     intros y; unfold shiftl2, head0.
       repeat rewrite spec_reduce_2; repeat rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=w2_spec)(4:=w0_spec)(5:=w2_spec); auto with zarith.
       rewrite (spec_zdigits w2_spec).
       rewrite (spec_zdigits w0_spec).
       change (znz_digits w2_op) with  (xO (xO (znz_digits w0_op))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w0_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n2 y)).
     intros y; unfold shiftl2, head0.
       repeat rewrite spec_reduce_2; repeat rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=w2_spec)(4:=w1_spec)(5:=w2_spec); auto with zarith.
       rewrite (spec_zdigits w2_spec).
       rewrite (spec_zdigits w1_spec).
       change (znz_digits w2_op) with  (xO (znz_digits w1_op)).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w1_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n2 y)).
     intros y; unfold shiftl2, head0.
     repeat rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=w2_spec)(4:=w2_spec)(5:=w2_spec); auto with zarith.
     intros y; unfold shiftl3, head0.
       repeat rewrite spec_reduce_2; repeat rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=w3_spec)(4:=w3_spec)(5:=w2_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n3 x)).
     intros y; unfold shiftl4, head0.
       repeat rewrite spec_reduce_2; repeat rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w4_spec)(5:=w2_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n4 x)).
     intros y; unfold shiftl5, head0.
       repeat rewrite spec_reduce_2; repeat rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w5_spec)(5:=w2_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n5 x)).
     intros y; unfold shiftl6, head0.
       repeat rewrite spec_reduce_2; repeat rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w6_spec)(5:=w2_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n6 x)).
     intros m y; unfold shiftln, head0.
       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w2_spec); auto with zarith.
       change ([Nn m (extend6 m (extend2 3 x))] = [N2 x]).
       rewrite <- (spec_extend6n m); rewrite <- spec_extend2n6; auto.
    intros x y; case y; clear y.
     intros y; unfold shiftl3, head0.
       repeat rewrite spec_reduce_3; repeat rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=w3_spec)(4:=w0_spec)(5:=w3_spec); auto with zarith.
       rewrite (spec_zdigits w3_spec).
       rewrite (spec_zdigits w0_spec).
       change (znz_digits w3_op) with  (xO (xO (xO (znz_digits w0_op)))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w0_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n3 y)).
     intros y; unfold shiftl3, head0.
       repeat rewrite spec_reduce_3; repeat rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=w3_spec)(4:=w1_spec)(5:=w3_spec); auto with zarith.
       rewrite (spec_zdigits w3_spec).
       rewrite (spec_zdigits w1_spec).
       change (znz_digits w3_op) with  (xO (xO (znz_digits w1_op))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w1_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n3 y)).
     intros y; unfold shiftl3, head0.
       repeat rewrite spec_reduce_3; repeat rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=w3_spec)(4:=w2_spec)(5:=w3_spec); auto with zarith.
       rewrite (spec_zdigits w3_spec).
       rewrite (spec_zdigits w2_spec).
       change (znz_digits w3_op) with  (xO (znz_digits w2_op)).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w2_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n3 y)).
     intros y; unfold shiftl3, head0.
     repeat rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=w3_spec)(4:=w3_spec)(5:=w3_spec); auto with zarith.
     intros y; unfold shiftl4, head0.
       repeat rewrite spec_reduce_3; repeat rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w4_spec)(5:=w3_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend3n4 x)).
     intros y; unfold shiftl5, head0.
       repeat rewrite spec_reduce_3; repeat rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w5_spec)(5:=w3_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend3n5 x)).
     intros y; unfold shiftl6, head0.
       repeat rewrite spec_reduce_3; repeat rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w6_spec)(5:=w3_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend3n6 x)).
     intros m y; unfold shiftln, head0.
       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w3_spec); auto with zarith.
       change ([Nn m (extend6 m (extend3 2 x))] = [N3 x]).
       rewrite <- (spec_extend6n m); rewrite <- spec_extend3n6; auto.
    intros x y; case y; clear y.
     intros y; unfold shiftl4, head0.
       repeat rewrite spec_reduce_4; repeat rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w0_spec)(5:=w4_spec); auto with zarith.
       rewrite (spec_zdigits w4_spec).
       rewrite (spec_zdigits w0_spec).
       change (znz_digits w4_op) with  (xO (xO (xO (xO (znz_digits w0_op))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w0_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n4 y)).
     intros y; unfold shiftl4, head0.
       repeat rewrite spec_reduce_4; repeat rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w1_spec)(5:=w4_spec); auto with zarith.
       rewrite (spec_zdigits w4_spec).
       rewrite (spec_zdigits w1_spec).
       change (znz_digits w4_op) with  (xO (xO (xO (znz_digits w1_op)))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w1_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n4 y)).
     intros y; unfold shiftl4, head0.
       repeat rewrite spec_reduce_4; repeat rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w2_spec)(5:=w4_spec); auto with zarith.
       rewrite (spec_zdigits w4_spec).
       rewrite (spec_zdigits w2_spec).
       change (znz_digits w4_op) with  (xO (xO (znz_digits w2_op))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w2_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n4 y)).
     intros y; unfold shiftl4, head0.
       repeat rewrite spec_reduce_4; repeat rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w3_spec)(5:=w4_spec); auto with zarith.
       rewrite (spec_zdigits w4_spec).
       rewrite (spec_zdigits w3_spec).
       change (znz_digits w4_op) with  (xO (znz_digits w3_op)).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w3_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend3n4 y)).
     intros y; unfold shiftl4, head0.
     repeat rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=w4_spec)(4:=w4_spec)(5:=w4_spec); auto with zarith.
     intros y; unfold shiftl5, head0.
       repeat rewrite spec_reduce_4; repeat rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w5_spec)(5:=w4_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend4n5 x)).
     intros y; unfold shiftl6, head0.
       repeat rewrite spec_reduce_4; repeat rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w6_spec)(5:=w4_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend4n6 x)).
     intros m y; unfold shiftln, head0.
       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w4_spec); auto with zarith.
       change ([Nn m (extend6 m (extend4 1 x))] = [N4 x]).
       rewrite <- (spec_extend6n m); rewrite <- spec_extend4n6; auto.
    intros x y; case y; clear y.
     intros y; unfold shiftl5, head0.
       repeat rewrite spec_reduce_5; repeat rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w0_spec)(5:=w5_spec); auto with zarith.
       rewrite (spec_zdigits w5_spec).
       rewrite (spec_zdigits w0_spec).
       change (znz_digits w5_op) with  (xO (xO (xO (xO (xO (znz_digits w0_op)))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w0_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n5 y)).
     intros y; unfold shiftl5, head0.
       repeat rewrite spec_reduce_5; repeat rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w1_spec)(5:=w5_spec); auto with zarith.
       rewrite (spec_zdigits w5_spec).
       rewrite (spec_zdigits w1_spec).
       change (znz_digits w5_op) with  (xO (xO (xO (xO (znz_digits w1_op))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w1_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n5 y)).
     intros y; unfold shiftl5, head0.
       repeat rewrite spec_reduce_5; repeat rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w2_spec)(5:=w5_spec); auto with zarith.
       rewrite (spec_zdigits w5_spec).
       rewrite (spec_zdigits w2_spec).
       change (znz_digits w5_op) with  (xO (xO (xO (znz_digits w2_op)))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w2_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n5 y)).
     intros y; unfold shiftl5, head0.
       repeat rewrite spec_reduce_5; repeat rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w3_spec)(5:=w5_spec); auto with zarith.
       rewrite (spec_zdigits w5_spec).
       rewrite (spec_zdigits w3_spec).
       change (znz_digits w5_op) with  (xO (xO (znz_digits w3_op))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w3_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend3n5 y)).
     intros y; unfold shiftl5, head0.
       repeat rewrite spec_reduce_5; repeat rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w4_spec)(5:=w5_spec); auto with zarith.
       rewrite (spec_zdigits w5_spec).
       rewrite (spec_zdigits w4_spec).
       change (znz_digits w5_op) with  (xO (znz_digits w4_op)).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w4_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend4n5 y)).
     intros y; unfold shiftl5, head0.
     repeat rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=w5_spec)(4:=w5_spec)(5:=w5_spec); auto with zarith.
     intros y; unfold shiftl6, head0.
       repeat rewrite spec_reduce_5; repeat rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w6_spec)(5:=w5_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend5n6 x)).
     intros m y; unfold shiftln, head0.
       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w5_spec); auto with zarith.
       change ([Nn m (extend6 m (extend5 0 x))] = [N5 x]).
       rewrite <- (spec_extend6n m); rewrite <- spec_extend5n6; auto.
    intros x y; case y; clear y.
     intros y; unfold shiftl6, head0.
       repeat rewrite spec_reduce_6; repeat rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w0_spec)(5:=w6_spec); auto with zarith.
       rewrite (spec_zdigits w6_spec).
       rewrite (spec_zdigits w0_spec).
       change (znz_digits w6_op) with  (xO (xO (xO (xO (xO (xO (znz_digits w0_op))))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w0_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend0n6 y)).
     intros y; unfold shiftl6, head0.
       repeat rewrite spec_reduce_6; repeat rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w1_spec)(5:=w6_spec); auto with zarith.
       rewrite (spec_zdigits w6_spec).
       rewrite (spec_zdigits w1_spec).
       change (znz_digits w6_op) with  (xO (xO (xO (xO (xO (znz_digits w1_op)))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w1_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend1n6 y)).
     intros y; unfold shiftl6, head0.
       repeat rewrite spec_reduce_6; repeat rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w2_spec)(5:=w6_spec); auto with zarith.
       rewrite (spec_zdigits w6_spec).
       rewrite (spec_zdigits w2_spec).
       change (znz_digits w6_op) with  (xO (xO (xO (xO (znz_digits w2_op))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w2_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend2n6 y)).
     intros y; unfold shiftl6, head0.
       repeat rewrite spec_reduce_6; repeat rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w3_spec)(5:=w6_spec); auto with zarith.
       rewrite (spec_zdigits w6_spec).
       rewrite (spec_zdigits w3_spec).
       change (znz_digits w6_op) with  (xO (xO (xO (znz_digits w3_op)))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w3_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend3n6 y)).
     intros y; unfold shiftl6, head0.
       repeat rewrite spec_reduce_6; repeat rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w4_spec)(5:=w6_spec); auto with zarith.
       rewrite (spec_zdigits w6_spec).
       rewrite (spec_zdigits w4_spec).
       change (znz_digits w6_op) with  (xO (xO (znz_digits w4_op))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w4_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend4n6 y)).
     intros y; unfold shiftl6, head0.
       repeat rewrite spec_reduce_6; repeat rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w5_spec)(5:=w6_spec); auto with zarith.
       rewrite (spec_zdigits w6_spec).
       rewrite (spec_zdigits w5_spec).
       change (znz_digits w6_op) with  (xO (znz_digits w5_op)).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (0 <= Zpos (znz_digits w5_op)); auto with zarith.
       try (apply sym_equal; exact (spec_extend5n6 y)).
     intros y; unfold shiftl6, head0.
     repeat rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=w6_spec)(4:=w6_spec)(5:=w6_spec); auto with zarith.
     intros m y; unfold shiftln, head0.
       repeat rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec m))(4:=wn_spec m)(5:=w6_spec); auto with zarith.
       try (apply sym_equal; exact (spec_extend6n m x)).
    intros n x y; case y; clear y;
     intros y; unfold shiftln, head0; try rewrite spec_reduce_n.
     try rewrite spec_reduce_0; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec n))(4:=w0_spec)(5:=wn_spec n); auto with zarith.
       rewrite (spec_zdigits w0_spec).
       rewrite (spec_zdigits (wn_spec n)).
       apply Zle_trans with (2 := F6 n).
       change (znz_digits w6_op) with  (xO (xO (xO (xO (xO (xO(znz_digits w0_op))))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (H: 0 <= Zpos (znz_digits w0_op)); auto with zarith.
       change ([Nn n (extend6 n (extend0 5 y))] = [N0 y]).
       rewrite <- (spec_extend6n n); auto.
       try (rewrite <- spec_extend0n6; auto).
     try rewrite spec_reduce_1; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec n))(4:=w1_spec)(5:=wn_spec n); auto with zarith.
       rewrite (spec_zdigits w1_spec).
       rewrite (spec_zdigits (wn_spec n)).
       apply Zle_trans with (2 := F6 n).
       change (znz_digits w6_op) with  (xO (xO (xO (xO (xO(znz_digits w1_op)))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (H: 0 <= Zpos (znz_digits w1_op)); auto with zarith.
       change ([Nn n (extend6 n (extend1 4 y))] = [N1 y]).
       rewrite <- (spec_extend6n n); auto.
       try (rewrite <- spec_extend1n6; auto).
     try rewrite spec_reduce_2; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec n))(4:=w2_spec)(5:=wn_spec n); auto with zarith.
       rewrite (spec_zdigits w2_spec).
       rewrite (spec_zdigits (wn_spec n)).
       apply Zle_trans with (2 := F6 n).
       change (znz_digits w6_op) with  (xO (xO (xO (xO(znz_digits w2_op))))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (H: 0 <= Zpos (znz_digits w2_op)); auto with zarith.
       change ([Nn n (extend6 n (extend2 3 y))] = [N2 y]).
       rewrite <- (spec_extend6n n); auto.
       try (rewrite <- spec_extend2n6; auto).
     try rewrite spec_reduce_3; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec n))(4:=w3_spec)(5:=wn_spec n); auto with zarith.
       rewrite (spec_zdigits w3_spec).
       rewrite (spec_zdigits (wn_spec n)).
       apply Zle_trans with (2 := F6 n).
       change (znz_digits w6_op) with  (xO (xO (xO(znz_digits w3_op)))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (H: 0 <= Zpos (znz_digits w3_op)); auto with zarith.
       change ([Nn n (extend6 n (extend3 2 y))] = [N3 y]).
       rewrite <- (spec_extend6n n); auto.
       try (rewrite <- spec_extend3n6; auto).
     try rewrite spec_reduce_4; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec n))(4:=w4_spec)(5:=wn_spec n); auto with zarith.
       rewrite (spec_zdigits w4_spec).
       rewrite (spec_zdigits (wn_spec n)).
       apply Zle_trans with (2 := F6 n).
       change (znz_digits w6_op) with  (xO (xO(znz_digits w4_op))).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (H: 0 <= Zpos (znz_digits w4_op)); auto with zarith.
       change ([Nn n (extend6 n (extend4 1 y))] = [N4 y]).
       rewrite <- (spec_extend6n n); auto.
       try (rewrite <- spec_extend4n6; auto).
     try rewrite spec_reduce_5; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec n))(4:=w5_spec)(5:=wn_spec n); auto with zarith.
       rewrite (spec_zdigits w5_spec).
       rewrite (spec_zdigits (wn_spec n)).
       apply Zle_trans with (2 := F6 n).
       change (znz_digits w6_op) with  (xO(znz_digits w5_op)).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (H: 0 <= Zpos (znz_digits w5_op)); auto with zarith.
       change ([Nn n (extend6 n (extend5 0 y))] = [N5 y]).
       rewrite <- (spec_extend6n n); auto.
       try (rewrite <- spec_extend5n6; auto).
     try rewrite spec_reduce_6; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec n))(4:=w6_spec)(5:=wn_spec n); auto with zarith.
       rewrite (spec_zdigits w6_spec).
       rewrite (spec_zdigits (wn_spec n)).
       apply Zle_trans with (2 := F6 n).
       change (znz_digits w6_op) with (znz_digits w6_op).
       repeat rewrite (fun x => Zpos_xO (xO x)).
       repeat rewrite (fun x y => Zpos_xO (@znz_digits x y)).
       assert (H: 0 <= Zpos (znz_digits w6_op)); auto with zarith.
       change ([Nn n (extend6 n y)] = [N6 y]).
       rewrite <- (spec_extend6n n); auto.
     generalize y; clear y; intros m y.
     repeat rewrite spec_reduce_n; unfold to_Z; intros H1.
       apply F4 with (3:=(wn_spec (Max.max n m)))(4:=wn_spec m)(5:=wn_spec n); auto with zarith.
     rewrite (spec_zdigits (wn_spec m)).
     rewrite (spec_zdigits (wn_spec (Max.max n m))).
     apply F5; auto with arith.
     exact (spec_cast_r n m y).
     exact (spec_cast_l n m x).
 Qed.

 Definition double_size w := match w with
 | N0 x => N1 (WW (znz_0 w0_op) x)
 | N1 x => N2 (WW (znz_0 w1_op) x)
 | N2 x => N3 (WW (znz_0 w2_op) x)
 | N3 x => N4 (WW (znz_0 w3_op) x)
 | N4 x => N5 (WW (znz_0 w4_op) x)
 | N5 x => N6 (WW (znz_0 w5_op) x)
 | N6 x => Nn 0 (WW (znz_0 w6_op) x)
 | Nn n x => Nn (S n) (WW (znz_0 (make_op n)) x)
 end.

 Theorem spec_double_size_digits: 
   forall x, digits (double_size x) = xO (digits x).
 Proof.
 intros x; case x; unfold double_size, digits; clear x; auto.
 intros n x; rewrite make_op_S; auto.
 Qed.

 Theorem spec_double_size: forall x, [double_size x] = [x].
 Proof.
 intros x; case x; unfold double_size; clear x.
   intros x; unfold to_Z, make_op; 
     rewrite znz_to_Z_1; rewrite (spec_0 w0_spec); auto with zarith.
   intros x; unfold to_Z, make_op; 
     rewrite znz_to_Z_2; rewrite (spec_0 w1_spec); auto with zarith.
   intros x; unfold to_Z, make_op; 
     rewrite znz_to_Z_3; rewrite (spec_0 w2_spec); auto with zarith.
   intros x; unfold to_Z, make_op; 
     rewrite znz_to_Z_4; rewrite (spec_0 w3_spec); auto with zarith.
   intros x; unfold to_Z, make_op; 
     rewrite znz_to_Z_5; rewrite (spec_0 w4_spec); auto with zarith.
   intros x; unfold to_Z, make_op; 
     rewrite znz_to_Z_6; rewrite (spec_0 w5_spec); auto with zarith.
   intros x; unfold to_Z, make_op; 
     rewrite znz_to_Z_7; rewrite (spec_0 w6_spec); auto with zarith.
   intros n x; unfold to_Z;
     generalize (znz_to_Z_n n); simpl word.
     intros HH; rewrite HH; clear HH.
     generalize (spec_0 (wn_spec n)); simpl word.
     intros HH; rewrite HH; clear HH; auto with zarith.
 Qed.

 Theorem spec_double_size_head0: 
   forall x, 2 * [head0 x] <= [head0 (double_size x)].
 Proof.
 intros x.
 assert (F1:= spec_pos (head0 x)).
 assert (F2: 0 < Zpos (digits x)).
   red; auto.
 case (Zle_lt_or_eq _ _ (spec_pos x)); intros HH.
 generalize HH; rewrite <- (spec_double_size x); intros HH1.
 case (spec_head0 x HH); intros _ HH2.
 case (spec_head0 _ HH1).
 rewrite (spec_double_size x); rewrite (spec_double_size_digits x).
 intros HH3 _.
 case (Zle_or_lt ([head0 (double_size x)]) (2 * [head0 x])); auto; intros HH4.
 absurd (2 ^ (2 * [head0 x] )* [x] < 2 ^ [head0 (double_size x)] * [x]); auto.
 apply Zle_not_lt.
 apply Zmult_le_compat_r; auto with zarith.
 apply Zpower_le_monotone; auto; auto with zarith.
 generalize (spec_pos (head0 (double_size x))); auto with zarith.
 assert (HH5: 2 ^[head0 x] <= 2 ^(Zpos (digits x) - 1)).
   case (Zle_lt_or_eq 1 [x]); auto with zarith; intros HH5.
   apply Zmult_le_reg_r with (2 ^ 1); auto with zarith.
   rewrite <- (fun x y z => Zpower_exp x (y - z)); auto with zarith.
   assert (tmp: forall x, x - 1 + 1 = x); [intros; ring | rewrite tmp; clear tmp].
   apply Zle_trans with (2 := Zlt_le_weak _ _ HH2).
   apply Zmult_le_compat_l; auto with zarith.
   rewrite Zpower_1_r; auto with zarith.
   apply Zpower_le_monotone; auto with zarith.
   split; auto with zarith. 
   case (Zle_or_lt (Zpos (digits x)) [head0 x]); auto with zarith; intros HH6.
   absurd (2 ^ Zpos (digits x) <= 2 ^ [head0 x] * [x]); auto with zarith.
   rewrite <- HH5; rewrite Zmult_1_r.
   apply Zpower_le_monotone; auto with zarith.
 rewrite (Zmult_comm 2).
 rewrite Zpower_mult; auto with zarith.
 rewrite Zpower_2.
 apply Zlt_le_trans with (2 := HH3).
 rewrite <- Zmult_assoc.
 replace (Zpos (xO (digits x)) - 1) with
   ((Zpos (digits x) - 1) + (Zpos (digits x))).
 rewrite Zpower_exp; auto with zarith.
 apply Zmult_lt_compat2; auto with zarith.
 split; auto with zarith.
 apply Zmult_lt_0_compat; auto with zarith.
 rewrite Zpos_xO; ring.
 apply Zlt_le_weak; auto.
 repeat rewrite spec_head00; auto.
 rewrite spec_double_size_digits.
 rewrite Zpos_xO; auto with zarith.
 rewrite spec_double_size; auto.
 Qed.

 Theorem spec_double_size_head0_pos: 
   forall x, 0 < [head0 (double_size x)].
 Proof.
 intros x.
 assert (F: 0 < Zpos (digits x)).
  red; auto.
 case (Zle_lt_or_eq _ _ (spec_pos (head0 (double_size x)))); auto; intros F0.
 case (Zle_lt_or_eq _ _ (spec_pos (head0 x))); intros F1.
   apply Zlt_le_trans with (2 := (spec_double_size_head0 x)); auto with zarith.
 case (Zle_lt_or_eq _ _ (spec_pos x)); intros F3.
 generalize F3; rewrite <- (spec_double_size x); intros F4.
 absurd (2 ^ (Zpos (xO (digits x)) - 1) < 2 ^ (Zpos (digits x))).
   apply Zle_not_lt.
   apply Zpower_le_monotone; auto with zarith.
   split; auto with zarith.
   rewrite Zpos_xO; auto with zarith.
 case (spec_head0 x F3).
 rewrite <- F1; rewrite Zpower_0_r; rewrite Zmult_1_l; intros _ HH.
 apply Zle_lt_trans with (2 := HH).
 case (spec_head0 _ F4).
 rewrite (spec_double_size x); rewrite (spec_double_size_digits x).
 rewrite <- F0; rewrite Zpower_0_r; rewrite Zmult_1_l; auto.
 generalize F1; rewrite (spec_head00 _ (sym_equal F3)); auto with zarith.
 Qed.

 Definition safe_shiftl_aux_body cont n x :=
   match compare n (head0 x)  with
      Gt => cont n (double_size x)
   |  _ => shiftl n x
   end.

 Theorem spec_safe_shift_aux_body: forall n p x cont,
       2^ Zpos p  <=  [head0 x]  ->
      (forall x, 2 ^ (Zpos p + 1) <= [head0 x]->
         [cont n x] = [x] * 2 ^ [n]) ->
      [safe_shiftl_aux_body cont n x] = [x] * 2 ^ [n].
 Proof.
 intros n p x cont H1 H2; unfold safe_shiftl_aux_body.
 generalize (spec_compare n (head0 x)); case compare; intros H.
  apply spec_shiftl; auto with zarith.
  apply spec_shiftl; auto with zarith.
 rewrite H2.
 rewrite spec_double_size; auto.
 rewrite Zplus_comm; rewrite Zpower_exp; auto with zarith.
 apply Zle_trans with (2 := spec_double_size_head0 x).
 rewrite Zpower_1_r; apply Zmult_le_compat_l; auto with zarith.
 Qed.

 Fixpoint safe_shiftl_aux p cont n x  {struct p} :=
   safe_shiftl_aux_body 
       (fun n x => match p with
        | xH => cont n x
        | xO p => safe_shiftl_aux p (safe_shiftl_aux p cont) n x
        | xI p => safe_shiftl_aux p (safe_shiftl_aux p cont) n x
        end) n x.

 Theorem spec_safe_shift_aux: forall p q n x cont,
    2 ^ (Zpos q) <= [head0 x] ->
      (forall x, 2 ^ (Zpos p + Zpos q) <= [head0 x] ->
         [cont n x] = [x] * 2 ^ [n]) ->      
      [safe_shiftl_aux p cont n x] = [x] * 2 ^ [n].
 Proof.
 intros p; elim p; unfold safe_shiftl_aux; fold safe_shiftl_aux; clear p.
 intros p Hrec q n x cont H1 H2.
 apply spec_safe_shift_aux_body with (q); auto.
 intros x1 H3; apply Hrec with (q + 1)%positive; auto.
 intros x2 H4; apply Hrec with (p + q + 1)%positive; auto.
 rewrite <- Pplus_assoc.
 rewrite Zpos_plus_distr; auto.
 intros x3 H5; apply H2.
 rewrite Zpos_xI.
 replace (2 * Zpos p + 1 + Zpos q) with (Zpos p + Zpos (p + q + 1));
   auto.
 repeat rewrite Zpos_plus_distr; ring.
 intros p Hrec q n x cont H1 H2.
 apply spec_safe_shift_aux_body with (q); auto.
 intros x1 H3; apply Hrec with (q); auto.
 apply Zle_trans with (2 := H3); auto with zarith.
 apply Zpower_le_monotone; auto with zarith.
 intros x2 H4; apply Hrec with (p + q)%positive; auto.
 intros x3 H5; apply H2.
 rewrite (Zpos_xO p).
 replace (2 * Zpos p + Zpos q) with (Zpos p + Zpos (p + q));
   auto.
 repeat rewrite Zpos_plus_distr; ring.
 intros q n x cont H1 H2.
 apply spec_safe_shift_aux_body with (q); auto.
 rewrite Zplus_comm; auto.
 Qed.

 Definition safe_shiftl n x :=
  safe_shiftl_aux_body
   (safe_shiftl_aux_body
    (safe_shiftl_aux (digits n) shiftl)) n x.

 Theorem spec_safe_shift: forall n x,
   [safe_shiftl n x] = [x] * 2 ^ [n].
 Proof.
 intros n x; unfold safe_shiftl, safe_shiftl_aux_body.
 generalize (spec_compare n (head0 x)); case compare; intros H.
  apply spec_shiftl; auto with zarith.
  apply spec_shiftl; auto with zarith.
 rewrite <- (spec_double_size x).
 generalize (spec_compare n (head0 (double_size x))); case compare; intros H1.
  apply spec_shiftl; auto with zarith.
  apply spec_shiftl; auto with zarith.
 rewrite <- (spec_double_size (double_size x)).
 apply spec_safe_shift_aux with 1%positive.
 apply Zle_trans with (2 := spec_double_size_head0 (double_size x)).
 replace (2 ^ 1) with (2 * 1).
 apply Zmult_le_compat_l; auto with zarith.
 generalize (spec_double_size_head0_pos x); auto with zarith.
 rewrite Zpower_1_r; ring.
 intros x1 H2; apply spec_shiftl.
 apply Zle_trans with (2 := H2).
 apply Zle_trans with (2 ^ Zpos (digits n)); auto with zarith.
 case (spec_digits n); auto with zarith.
 apply Zpower_le_monotone; auto with zarith.
 Qed.

 Definition is_even x :=
  match x with
  | N0 wx => w0_op.(znz_is_even) wx
  | N1 wx => w1_op.(znz_is_even) wx
  | N2 wx => w2_op.(znz_is_even) wx
  | N3 wx => w3_op.(znz_is_even) wx
  | N4 wx => w4_op.(znz_is_even) wx
  | N5 wx => w5_op.(znz_is_even) wx
  | N6 wx => w6_op.(znz_is_even) wx
  | Nn n wx => (make_op n).(znz_is_even) wx
  end.

 Theorem spec_is_even: forall x,
   if is_even x then [x] mod 2 = 0 else [x] mod 2 = 1.
 Proof.
 intros x; case x; unfold is_even, to_Z; clear x.
   intros x; exact (spec_is_even w0_spec x).
   intros x; exact (spec_is_even w1_spec x).
   intros x; exact (spec_is_even w2_spec x).
   intros x; exact (spec_is_even w3_spec x).
   intros x; exact (spec_is_even w4_spec x).
   intros x; exact (spec_is_even w5_spec x).
   intros x; exact (spec_is_even w6_spec x).
  intros n x; exact (spec_is_even (wn_spec n) x).
 Qed.

 Theorem spec_0: [zero] = 0.
 Proof.
 exact (spec_0 w0_spec).
 Qed.

 Theorem spec_1: [one] = 1.
 Proof.
 exact (spec_1 w0_spec).
 Qed.

End Make.
