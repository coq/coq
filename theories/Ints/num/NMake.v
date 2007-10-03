Require Import ZAux.
Require Import ZArith.
Require Import Basic_type.
Require Import ZnZ.
Require Import Zn2Z.
Require Import Nbasic.
Require Import GenMul.
Require Import GenDivn1.
Require Import Wf_nat.

(***************************************************************)
(*                                                             *)
(*        File automatically generated DO NOT EDIT             *)
(*        Constructors: 13  Generated Proofs: false            *)
(*                                                             *)
(***************************************************************)

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
 Definition w7 := zn2z w6.
 Definition w8 := zn2z w7.
 Definition w9 := zn2z w8.
 Definition w10 := zn2z w9.
 Definition w11 := zn2z w10.
 Definition w12 := zn2z w11.
 Definition w13 := zn2z w12.

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
 Definition w10_op := mk_zn2z_op_karatsuba w9_op.
 Definition w11_op := mk_zn2z_op_karatsuba w10_op.
 Definition w12_op := mk_zn2z_op_karatsuba w11_op.
 Definition w13_op := mk_zn2z_op_karatsuba w12_op.
 Definition w14_op := mk_zn2z_op_karatsuba w13_op.
 Definition w15_op := mk_zn2z_op_karatsuba w14_op.
 Definition w16_op := mk_zn2z_op_karatsuba w15_op.

 Section Make_op.
  Variable mk : forall w', znz_op w' -> znz_op (zn2z w').

  Fixpoint make_op_aux (n:nat) : znz_op (word w13 (S n)):=
   match n return znz_op (word w13 (S n)) with
   | O => w14_op
   | S n1 =>
     match n1 return znz_op (word w13 (S (S n1))) with
     | O => w15_op
     | S n2 =>
       match n2 return znz_op (word w13 (S (S (S n2)))) with
       | O => w16_op
       | S n3 => mk _ (mk _ (mk _ (make_op_aux n3)))
       end
     end
   end.

 End Make_op.

 Definition make_op := make_op_aux mk_zn2z_op_karatsuba.

 Inductive t_ : Set :=
  | N0 : w0 -> t_
  | N1 : w1 -> t_
  | N2 : w2 -> t_
  | N3 : w3 -> t_
  | N4 : w4 -> t_
  | N5 : w5 -> t_
  | N6 : w6 -> t_
  | N7 : w7 -> t_
  | N8 : w8 -> t_
  | N9 : w9 -> t_
  | N10 : w10 -> t_
  | N11 : w11 -> t_
  | N12 : w12 -> t_
  | N13 : w13 -> t_
  | Nn : forall n, word w13 (S n) -> t_.

 Definition t := t_.

 Definition w_0 := w0_op.(znz_0).

 Definition one0 := w0_op.(znz_1).
 Definition one1 := w1_op.(znz_1).
 Definition one2 := w2_op.(znz_1).
 Definition one3 := w3_op.(znz_1).
 Definition one4 := w4_op.(znz_1).
 Definition one5 := w5_op.(znz_1).
 Definition one6 := w6_op.(znz_1).
 Definition one7 := w7_op.(znz_1).
 Definition one8 := w8_op.(znz_1).
 Definition one9 := w9_op.(znz_1).
 Definition one10 := w10_op.(znz_1).
 Definition one11 := w11_op.(znz_1).
 Definition one12 := w12_op.(znz_1).
 Definition one13 := w13_op.(znz_1).

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
  | N7 wx => w7_op.(znz_to_Z) wx
  | N8 wx => w8_op.(znz_to_Z) wx
  | N9 wx => w9_op.(znz_to_Z) wx
  | N10 wx => w10_op.(znz_to_Z) wx
  | N11 wx => w11_op.(znz_to_Z) wx
  | N12 wx => w12_op.(znz_to_Z) wx
  | N13 wx => w13_op.(znz_to_Z) wx
  | Nn n wx => (make_op n).(znz_to_Z) wx
  end.

 Open Scope Z_scope.
 Notation "[ x ]" := (to_Z x).
 
 (* Eval and extend functions for each level *)
 Let extend0 := GenBase.extend  (WW w_0).
 Let extend1 := GenBase.extend  (WW (W0: w1)).
 Let extend2 := GenBase.extend  (WW (W0: w2)).
 Let extend3 := GenBase.extend  (WW (W0: w3)).
 Let extend4 := GenBase.extend  (WW (W0: w4)).
 Let extend5 := GenBase.extend  (WW (W0: w5)).
 Let extend6 := GenBase.extend  (WW (W0: w6)).
 Let extend7 := GenBase.extend  (WW (W0: w7)).
 Let extend8 := GenBase.extend  (WW (W0: w8)).
 Let extend9 := GenBase.extend  (WW (W0: w9)).
 Let extend10 := GenBase.extend  (WW (W0: w10)).
 Let extend11 := GenBase.extend  (WW (W0: w11)).
 Let extend12 := GenBase.extend  (WW (W0: w12)).
 Let extend13 := GenBase.extend  (WW (W0: w13)).

 Definition w0_eq0 := w0_op.(znz_eq0).
 Let spec_w0_eq0: forall x, if w0_eq0 x then [N0 x] = 0 else True.
 Admitted.

 Definition w1_eq0 := w1_op.(znz_eq0).
 Let spec_w1_eq0: forall x, if w1_eq0 x then [N1 x] = 0 else True.
 Admitted.

 Definition w2_eq0 := w2_op.(znz_eq0).
 Let spec_w2_eq0: forall x, if w2_eq0 x then [N2 x] = 0 else True.
 Admitted.

 Definition w3_eq0 := w3_op.(znz_eq0).
 Let spec_w3_eq0: forall x, if w3_eq0 x then [N3 x] = 0 else True.
 Admitted.

 Definition w4_eq0 := w4_op.(znz_eq0).
 Let spec_w4_eq0: forall x, if w4_eq0 x then [N4 x] = 0 else True.
 Admitted.

 Definition w5_eq0 := w5_op.(znz_eq0).
 Let spec_w5_eq0: forall x, if w5_eq0 x then [N5 x] = 0 else True.
 Admitted.

 Definition w6_eq0 := w6_op.(znz_eq0).
 Let spec_w6_eq0: forall x, if w6_eq0 x then [N6 x] = 0 else True.
 Admitted.

 Definition w7_eq0 := w7_op.(znz_eq0).
 Let spec_w7_eq0: forall x, if w7_eq0 x then [N7 x] = 0 else True.
 Admitted.

 Definition w8_eq0 := w8_op.(znz_eq0).
 Let spec_w8_eq0: forall x, if w8_eq0 x then [N8 x] = 0 else True.
 Admitted.

 Definition w9_eq0 := w9_op.(znz_eq0).
 Let spec_w9_eq0: forall x, if w9_eq0 x then [N9 x] = 0 else True.
 Admitted.

 Definition w10_eq0 := w10_op.(znz_eq0).
 Let spec_w10_eq0: forall x, if w10_eq0 x then [N10 x] = 0 else True.
 Admitted.

 Definition w11_eq0 := w11_op.(znz_eq0).
 Let spec_w11_eq0: forall x, if w11_eq0 x then [N11 x] = 0 else True.
 Admitted.

 Definition w12_eq0 := w12_op.(znz_eq0).
 Let spec_w12_eq0: forall x, if w12_eq0 x then [N12 x] = 0 else True.
 Admitted.

 Definition w13_eq0 := w13_op.(znz_eq0).
 Let spec_w13_eq0: forall x, if w13_eq0 x then [N13 x] = 0 else True.
 Admitted.


 Theorem spec_pos: forall x, 0 <= [x].
 Admitted.

 Section LevelAndIter.

  Variable res: Set.
  Variable xxx: res.
  Variable P: Z -> Z -> res -> Prop.
  (* Abstraction function for each level *)
  Variable f0: w0 -> w0 -> res.
  Variable f0n: forall n, w0 -> word w0 (S n) -> res.
  Variable fn0: forall n, word w0 (S n) -> w0 -> res.

  Variable f1: w1 -> w1 -> res.
  Variable f1n: forall n, w1 -> word w1 (S n) -> res.
  Variable fn1: forall n, word w1 (S n) -> w1 -> res.

  Variable f2: w2 -> w2 -> res.
  Variable f2n: forall n, w2 -> word w2 (S n) -> res.
  Variable fn2: forall n, word w2 (S n) -> w2 -> res.

  Variable f3: w3 -> w3 -> res.
  Variable f3n: forall n, w3 -> word w3 (S n) -> res.
  Variable fn3: forall n, word w3 (S n) -> w3 -> res.

  Variable f4: w4 -> w4 -> res.
  Variable f4n: forall n, w4 -> word w4 (S n) -> res.
  Variable fn4: forall n, word w4 (S n) -> w4 -> res.

  Variable f5: w5 -> w5 -> res.
  Variable f5n: forall n, w5 -> word w5 (S n) -> res.
  Variable fn5: forall n, word w5 (S n) -> w5 -> res.

  Variable f6: w6 -> w6 -> res.
  Variable f6n: forall n, w6 -> word w6 (S n) -> res.
  Variable fn6: forall n, word w6 (S n) -> w6 -> res.

  Variable f7: w7 -> w7 -> res.
  Variable f7n: forall n, w7 -> word w7 (S n) -> res.
  Variable fn7: forall n, word w7 (S n) -> w7 -> res.

  Variable f8: w8 -> w8 -> res.
  Variable f8n: forall n, w8 -> word w8 (S n) -> res.
  Variable fn8: forall n, word w8 (S n) -> w8 -> res.

  Variable f9: w9 -> w9 -> res.
  Variable f9n: forall n, w9 -> word w9 (S n) -> res.
  Variable fn9: forall n, word w9 (S n) -> w9 -> res.

  Variable f10: w10 -> w10 -> res.
  Variable f10n: forall n, w10 -> word w10 (S n) -> res.
  Variable fn10: forall n, word w10 (S n) -> w10 -> res.

  Variable f11: w11 -> w11 -> res.
  Variable f11n: forall n, w11 -> word w11 (S n) -> res.
  Variable fn11: forall n, word w11 (S n) -> w11 -> res.

  Variable f12: w12 -> w12 -> res.
  Variable f12n: forall n, w12 -> word w12 (S n) -> res.
  Variable fn12: forall n, word w12 (S n) -> w12 -> res.

  Variable f13: w13 -> w13 -> res.
  Variable f13n: forall n, w13 -> word w13 (S n) -> res.
  Variable fn13: forall n, word w13 (S n) -> w13 -> res.

  Variable fnn: forall n, word w13 (S n) -> word w13 (S n) -> res.
  Variable fnm: forall n m, word w13 (S n) -> word w13 (S m) -> res.

  (* Special zero functions *)
  Variable f0t:  t_ -> res.
  Variable ft0:  t_ -> res.

  (* We level the two arguments before applying *)
  (* the functions at each leval                *)
  Definition same_level (x y: t_): res :=
    Eval lazy zeta beta iota delta [extend0 extend1 extend2 extend3 extend4 extend5 extend6 extend7 extend8 extend9 extend10 extend11 extend12 extend13 
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
  | N0 wx, N7 wy => f7 (extend0 6 wx) wy
  | N0 wx, N8 wy => f8 (extend0 7 wx) wy
  | N0 wx, N9 wy => f9 (extend0 8 wx) wy
  | N0 wx, N10 wy => f10 (extend0 9 wx) wy
  | N0 wx, N11 wy => f11 (extend0 10 wx) wy
  | N0 wx, N12 wy => f12 (extend0 11 wx) wy
  | N0 wx, N13 wy => f13 (extend0 12 wx) wy
  | N0 wx, Nn m wy => fnn m (extend13 m (extend0 12 wx)) wy
  | N1 wx, N0 wy => f1 wx (extend0 0 wy)
  | N1 wx, N1 wy => f1 wx wy
  | N1 wx, N2 wy => f2 (extend1 0 wx) wy
  | N1 wx, N3 wy => f3 (extend1 1 wx) wy
  | N1 wx, N4 wy => f4 (extend1 2 wx) wy
  | N1 wx, N5 wy => f5 (extend1 3 wx) wy
  | N1 wx, N6 wy => f6 (extend1 4 wx) wy
  | N1 wx, N7 wy => f7 (extend1 5 wx) wy
  | N1 wx, N8 wy => f8 (extend1 6 wx) wy
  | N1 wx, N9 wy => f9 (extend1 7 wx) wy
  | N1 wx, N10 wy => f10 (extend1 8 wx) wy
  | N1 wx, N11 wy => f11 (extend1 9 wx) wy
  | N1 wx, N12 wy => f12 (extend1 10 wx) wy
  | N1 wx, N13 wy => f13 (extend1 11 wx) wy
  | N1 wx, Nn m wy => fnn m (extend13 m (extend1 11 wx)) wy
  | N2 wx, N0 wy => f2 wx (extend0 1 wy)
  | N2 wx, N1 wy => f2 wx (extend1 0 wy)
  | N2 wx, N2 wy => f2 wx wy
  | N2 wx, N3 wy => f3 (extend2 0 wx) wy
  | N2 wx, N4 wy => f4 (extend2 1 wx) wy
  | N2 wx, N5 wy => f5 (extend2 2 wx) wy
  | N2 wx, N6 wy => f6 (extend2 3 wx) wy
  | N2 wx, N7 wy => f7 (extend2 4 wx) wy
  | N2 wx, N8 wy => f8 (extend2 5 wx) wy
  | N2 wx, N9 wy => f9 (extend2 6 wx) wy
  | N2 wx, N10 wy => f10 (extend2 7 wx) wy
  | N2 wx, N11 wy => f11 (extend2 8 wx) wy
  | N2 wx, N12 wy => f12 (extend2 9 wx) wy
  | N2 wx, N13 wy => f13 (extend2 10 wx) wy
  | N2 wx, Nn m wy => fnn m (extend13 m (extend2 10 wx)) wy
  | N3 wx, N0 wy => f3 wx (extend0 2 wy)
  | N3 wx, N1 wy => f3 wx (extend1 1 wy)
  | N3 wx, N2 wy => f3 wx (extend2 0 wy)
  | N3 wx, N3 wy => f3 wx wy
  | N3 wx, N4 wy => f4 (extend3 0 wx) wy
  | N3 wx, N5 wy => f5 (extend3 1 wx) wy
  | N3 wx, N6 wy => f6 (extend3 2 wx) wy
  | N3 wx, N7 wy => f7 (extend3 3 wx) wy
  | N3 wx, N8 wy => f8 (extend3 4 wx) wy
  | N3 wx, N9 wy => f9 (extend3 5 wx) wy
  | N3 wx, N10 wy => f10 (extend3 6 wx) wy
  | N3 wx, N11 wy => f11 (extend3 7 wx) wy
  | N3 wx, N12 wy => f12 (extend3 8 wx) wy
  | N3 wx, N13 wy => f13 (extend3 9 wx) wy
  | N3 wx, Nn m wy => fnn m (extend13 m (extend3 9 wx)) wy
  | N4 wx, N0 wy => f4 wx (extend0 3 wy)
  | N4 wx, N1 wy => f4 wx (extend1 2 wy)
  | N4 wx, N2 wy => f4 wx (extend2 1 wy)
  | N4 wx, N3 wy => f4 wx (extend3 0 wy)
  | N4 wx, N4 wy => f4 wx wy
  | N4 wx, N5 wy => f5 (extend4 0 wx) wy
  | N4 wx, N6 wy => f6 (extend4 1 wx) wy
  | N4 wx, N7 wy => f7 (extend4 2 wx) wy
  | N4 wx, N8 wy => f8 (extend4 3 wx) wy
  | N4 wx, N9 wy => f9 (extend4 4 wx) wy
  | N4 wx, N10 wy => f10 (extend4 5 wx) wy
  | N4 wx, N11 wy => f11 (extend4 6 wx) wy
  | N4 wx, N12 wy => f12 (extend4 7 wx) wy
  | N4 wx, N13 wy => f13 (extend4 8 wx) wy
  | N4 wx, Nn m wy => fnn m (extend13 m (extend4 8 wx)) wy
  | N5 wx, N0 wy => f5 wx (extend0 4 wy)
  | N5 wx, N1 wy => f5 wx (extend1 3 wy)
  | N5 wx, N2 wy => f5 wx (extend2 2 wy)
  | N5 wx, N3 wy => f5 wx (extend3 1 wy)
  | N5 wx, N4 wy => f5 wx (extend4 0 wy)
  | N5 wx, N5 wy => f5 wx wy
  | N5 wx, N6 wy => f6 (extend5 0 wx) wy
  | N5 wx, N7 wy => f7 (extend5 1 wx) wy
  | N5 wx, N8 wy => f8 (extend5 2 wx) wy
  | N5 wx, N9 wy => f9 (extend5 3 wx) wy
  | N5 wx, N10 wy => f10 (extend5 4 wx) wy
  | N5 wx, N11 wy => f11 (extend5 5 wx) wy
  | N5 wx, N12 wy => f12 (extend5 6 wx) wy
  | N5 wx, N13 wy => f13 (extend5 7 wx) wy
  | N5 wx, Nn m wy => fnn m (extend13 m (extend5 7 wx)) wy
  | N6 wx, N0 wy => f6 wx (extend0 5 wy)
  | N6 wx, N1 wy => f6 wx (extend1 4 wy)
  | N6 wx, N2 wy => f6 wx (extend2 3 wy)
  | N6 wx, N3 wy => f6 wx (extend3 2 wy)
  | N6 wx, N4 wy => f6 wx (extend4 1 wy)
  | N6 wx, N5 wy => f6 wx (extend5 0 wy)
  | N6 wx, N6 wy => f6 wx wy
  | N6 wx, N7 wy => f7 (extend6 0 wx) wy
  | N6 wx, N8 wy => f8 (extend6 1 wx) wy
  | N6 wx, N9 wy => f9 (extend6 2 wx) wy
  | N6 wx, N10 wy => f10 (extend6 3 wx) wy
  | N6 wx, N11 wy => f11 (extend6 4 wx) wy
  | N6 wx, N12 wy => f12 (extend6 5 wx) wy
  | N6 wx, N13 wy => f13 (extend6 6 wx) wy
  | N6 wx, Nn m wy => fnn m (extend13 m (extend6 6 wx)) wy
  | N7 wx, N0 wy => f7 wx (extend0 6 wy)
  | N7 wx, N1 wy => f7 wx (extend1 5 wy)
  | N7 wx, N2 wy => f7 wx (extend2 4 wy)
  | N7 wx, N3 wy => f7 wx (extend3 3 wy)
  | N7 wx, N4 wy => f7 wx (extend4 2 wy)
  | N7 wx, N5 wy => f7 wx (extend5 1 wy)
  | N7 wx, N6 wy => f7 wx (extend6 0 wy)
  | N7 wx, N7 wy => f7 wx wy
  | N7 wx, N8 wy => f8 (extend7 0 wx) wy
  | N7 wx, N9 wy => f9 (extend7 1 wx) wy
  | N7 wx, N10 wy => f10 (extend7 2 wx) wy
  | N7 wx, N11 wy => f11 (extend7 3 wx) wy
  | N7 wx, N12 wy => f12 (extend7 4 wx) wy
  | N7 wx, N13 wy => f13 (extend7 5 wx) wy
  | N7 wx, Nn m wy => fnn m (extend13 m (extend7 5 wx)) wy
  | N8 wx, N0 wy => f8 wx (extend0 7 wy)
  | N8 wx, N1 wy => f8 wx (extend1 6 wy)
  | N8 wx, N2 wy => f8 wx (extend2 5 wy)
  | N8 wx, N3 wy => f8 wx (extend3 4 wy)
  | N8 wx, N4 wy => f8 wx (extend4 3 wy)
  | N8 wx, N5 wy => f8 wx (extend5 2 wy)
  | N8 wx, N6 wy => f8 wx (extend6 1 wy)
  | N8 wx, N7 wy => f8 wx (extend7 0 wy)
  | N8 wx, N8 wy => f8 wx wy
  | N8 wx, N9 wy => f9 (extend8 0 wx) wy
  | N8 wx, N10 wy => f10 (extend8 1 wx) wy
  | N8 wx, N11 wy => f11 (extend8 2 wx) wy
  | N8 wx, N12 wy => f12 (extend8 3 wx) wy
  | N8 wx, N13 wy => f13 (extend8 4 wx) wy
  | N8 wx, Nn m wy => fnn m (extend13 m (extend8 4 wx)) wy
  | N9 wx, N0 wy => f9 wx (extend0 8 wy)
  | N9 wx, N1 wy => f9 wx (extend1 7 wy)
  | N9 wx, N2 wy => f9 wx (extend2 6 wy)
  | N9 wx, N3 wy => f9 wx (extend3 5 wy)
  | N9 wx, N4 wy => f9 wx (extend4 4 wy)
  | N9 wx, N5 wy => f9 wx (extend5 3 wy)
  | N9 wx, N6 wy => f9 wx (extend6 2 wy)
  | N9 wx, N7 wy => f9 wx (extend7 1 wy)
  | N9 wx, N8 wy => f9 wx (extend8 0 wy)
  | N9 wx, N9 wy => f9 wx wy
  | N9 wx, N10 wy => f10 (extend9 0 wx) wy
  | N9 wx, N11 wy => f11 (extend9 1 wx) wy
  | N9 wx, N12 wy => f12 (extend9 2 wx) wy
  | N9 wx, N13 wy => f13 (extend9 3 wx) wy
  | N9 wx, Nn m wy => fnn m (extend13 m (extend9 3 wx)) wy
  | N10 wx, N0 wy => f10 wx (extend0 9 wy)
  | N10 wx, N1 wy => f10 wx (extend1 8 wy)
  | N10 wx, N2 wy => f10 wx (extend2 7 wy)
  | N10 wx, N3 wy => f10 wx (extend3 6 wy)
  | N10 wx, N4 wy => f10 wx (extend4 5 wy)
  | N10 wx, N5 wy => f10 wx (extend5 4 wy)
  | N10 wx, N6 wy => f10 wx (extend6 3 wy)
  | N10 wx, N7 wy => f10 wx (extend7 2 wy)
  | N10 wx, N8 wy => f10 wx (extend8 1 wy)
  | N10 wx, N9 wy => f10 wx (extend9 0 wy)
  | N10 wx, N10 wy => f10 wx wy
  | N10 wx, N11 wy => f11 (extend10 0 wx) wy
  | N10 wx, N12 wy => f12 (extend10 1 wx) wy
  | N10 wx, N13 wy => f13 (extend10 2 wx) wy
  | N10 wx, Nn m wy => fnn m (extend13 m (extend10 2 wx)) wy
  | N11 wx, N0 wy => f11 wx (extend0 10 wy)
  | N11 wx, N1 wy => f11 wx (extend1 9 wy)
  | N11 wx, N2 wy => f11 wx (extend2 8 wy)
  | N11 wx, N3 wy => f11 wx (extend3 7 wy)
  | N11 wx, N4 wy => f11 wx (extend4 6 wy)
  | N11 wx, N5 wy => f11 wx (extend5 5 wy)
  | N11 wx, N6 wy => f11 wx (extend6 4 wy)
  | N11 wx, N7 wy => f11 wx (extend7 3 wy)
  | N11 wx, N8 wy => f11 wx (extend8 2 wy)
  | N11 wx, N9 wy => f11 wx (extend9 1 wy)
  | N11 wx, N10 wy => f11 wx (extend10 0 wy)
  | N11 wx, N11 wy => f11 wx wy
  | N11 wx, N12 wy => f12 (extend11 0 wx) wy
  | N11 wx, N13 wy => f13 (extend11 1 wx) wy
  | N11 wx, Nn m wy => fnn m (extend13 m (extend11 1 wx)) wy
  | N12 wx, N0 wy => f12 wx (extend0 11 wy)
  | N12 wx, N1 wy => f12 wx (extend1 10 wy)
  | N12 wx, N2 wy => f12 wx (extend2 9 wy)
  | N12 wx, N3 wy => f12 wx (extend3 8 wy)
  | N12 wx, N4 wy => f12 wx (extend4 7 wy)
  | N12 wx, N5 wy => f12 wx (extend5 6 wy)
  | N12 wx, N6 wy => f12 wx (extend6 5 wy)
  | N12 wx, N7 wy => f12 wx (extend7 4 wy)
  | N12 wx, N8 wy => f12 wx (extend8 3 wy)
  | N12 wx, N9 wy => f12 wx (extend9 2 wy)
  | N12 wx, N10 wy => f12 wx (extend10 1 wy)
  | N12 wx, N11 wy => f12 wx (extend11 0 wy)
  | N12 wx, N12 wy => f12 wx wy
  | N12 wx, N13 wy => f13 (extend12 0 wx) wy
  | N12 wx, Nn m wy => fnn m (extend13 m (extend12 0 wx)) wy
  | N13 wx, N0 wy => f13 wx (extend0 12 wy)
  | N13 wx, N1 wy => f13 wx (extend1 11 wy)
  | N13 wx, N2 wy => f13 wx (extend2 10 wy)
  | N13 wx, N3 wy => f13 wx (extend3 9 wy)
  | N13 wx, N4 wy => f13 wx (extend4 8 wy)
  | N13 wx, N5 wy => f13 wx (extend5 7 wy)
  | N13 wx, N6 wy => f13 wx (extend6 6 wy)
  | N13 wx, N7 wy => f13 wx (extend7 5 wy)
  | N13 wx, N8 wy => f13 wx (extend8 4 wy)
  | N13 wx, N9 wy => f13 wx (extend9 3 wy)
  | N13 wx, N10 wy => f13 wx (extend10 2 wy)
  | N13 wx, N11 wy => f13 wx (extend11 1 wy)
  | N13 wx, N12 wy => f13 wx (extend12 0 wy)
  | N13 wx, N13 wy => f13 wx wy
  | N13 wx, Nn m wy => fnn m (extend13 m wx) wy
  | Nn n wx, N0 wy => fnn n wx (extend13 n (extend0 12 wy))
  | Nn n wx, N1 wy => fnn n wx (extend13 n (extend1 11 wy))
  | Nn n wx, N2 wy => fnn n wx (extend13 n (extend2 10 wy))
  | Nn n wx, N3 wy => fnn n wx (extend13 n (extend3 9 wy))
  | Nn n wx, N4 wy => fnn n wx (extend13 n (extend4 8 wy))
  | Nn n wx, N5 wy => fnn n wx (extend13 n (extend5 7 wy))
  | Nn n wx, N6 wy => fnn n wx (extend13 n (extend6 6 wy))
  | Nn n wx, N7 wy => fnn n wx (extend13 n (extend7 5 wy))
  | Nn n wx, N8 wy => fnn n wx (extend13 n (extend8 4 wy))
  | Nn n wx, N9 wy => fnn n wx (extend13 n (extend9 3 wy))
  | Nn n wx, N10 wy => fnn n wx (extend13 n (extend10 2 wy))
  | Nn n wx, N11 wy => fnn n wx (extend13 n (extend11 1 wy))
  | Nn n wx, N12 wy => fnn n wx (extend13 n (extend12 0 wy))
  | Nn n wx, N13 wy => fnn n wx (extend13 n wy)
  | Nn n wx, Nn m wy =>
    let mn := Max.max n m in
    let d := diff n m in
     fnn mn
       (castm (diff_r n m) (extend_tr wx (snd d)))
       (castm (diff_l n m) (extend_tr wy (fst d)))
  end.

  (* We level the two arguments before applying      *)
  (* the functions at each level (special zero case) *)
  Definition same_level0 (x y: t_): res :=
    Eval lazy zeta beta iota delta [extend0 extend1 extend2 extend3 extend4 extend5 extend6 extend7 extend8 extend9 extend10 extend11 extend12 extend13 
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
    | N7 wy => f7 (extend0 6 wx) wy
    | N8 wy => f8 (extend0 7 wx) wy
    | N9 wy => f9 (extend0 8 wx) wy
    | N10 wy => f10 (extend0 9 wx) wy
    | N11 wy => f11 (extend0 10 wx) wy
    | N12 wy => f12 (extend0 11 wx) wy
    | N13 wy => f13 (extend0 12 wx) wy
    | Nn m wy => fnn m (extend13 m (extend0 12 wx)) wy
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
    | N7 wy => f7 (extend1 5 wx) wy
    | N8 wy => f8 (extend1 6 wx) wy
    | N9 wy => f9 (extend1 7 wx) wy
    | N10 wy => f10 (extend1 8 wx) wy
    | N11 wy => f11 (extend1 9 wx) wy
    | N12 wy => f12 (extend1 10 wx) wy
    | N13 wy => f13 (extend1 11 wx) wy
    | Nn m wy => fnn m (extend13 m (extend1 11 wx)) wy
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
    | N7 wy => f7 (extend2 4 wx) wy
    | N8 wy => f8 (extend2 5 wx) wy
    | N9 wy => f9 (extend2 6 wx) wy
    | N10 wy => f10 (extend2 7 wx) wy
    | N11 wy => f11 (extend2 8 wx) wy
    | N12 wy => f12 (extend2 9 wx) wy
    | N13 wy => f13 (extend2 10 wx) wy
    | Nn m wy => fnn m (extend13 m (extend2 10 wx)) wy
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
    | N7 wy => f7 (extend3 3 wx) wy
    | N8 wy => f8 (extend3 4 wx) wy
    | N9 wy => f9 (extend3 5 wx) wy
    | N10 wy => f10 (extend3 6 wx) wy
    | N11 wy => f11 (extend3 7 wx) wy
    | N12 wy => f12 (extend3 8 wx) wy
    | N13 wy => f13 (extend3 9 wx) wy
    | Nn m wy => fnn m (extend13 m (extend3 9 wx)) wy
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
    | N7 wy => f7 (extend4 2 wx) wy
    | N8 wy => f8 (extend4 3 wx) wy
    | N9 wy => f9 (extend4 4 wx) wy
    | N10 wy => f10 (extend4 5 wx) wy
    | N11 wy => f11 (extend4 6 wx) wy
    | N12 wy => f12 (extend4 7 wx) wy
    | N13 wy => f13 (extend4 8 wx) wy
    | Nn m wy => fnn m (extend13 m (extend4 8 wx)) wy
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
    | N7 wy => f7 (extend5 1 wx) wy
    | N8 wy => f8 (extend5 2 wx) wy
    | N9 wy => f9 (extend5 3 wx) wy
    | N10 wy => f10 (extend5 4 wx) wy
    | N11 wy => f11 (extend5 5 wx) wy
    | N12 wy => f12 (extend5 6 wx) wy
    | N13 wy => f13 (extend5 7 wx) wy
    | Nn m wy => fnn m (extend13 m (extend5 7 wx)) wy
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
    | N7 wy => f7 (extend6 0 wx) wy
    | N8 wy => f8 (extend6 1 wx) wy
    | N9 wy => f9 (extend6 2 wx) wy
    | N10 wy => f10 (extend6 3 wx) wy
    | N11 wy => f11 (extend6 4 wx) wy
    | N12 wy => f12 (extend6 5 wx) wy
    | N13 wy => f13 (extend6 6 wx) wy
    | Nn m wy => fnn m (extend13 m (extend6 6 wx)) wy
    end
  | N7 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       f7 wx (extend0 6 wy)
    | N1 wy =>
       f7 wx (extend1 5 wy)
    | N2 wy =>
       f7 wx (extend2 4 wy)
    | N3 wy =>
       f7 wx (extend3 3 wy)
    | N4 wy =>
       f7 wx (extend4 2 wy)
    | N5 wy =>
       f7 wx (extend5 1 wy)
    | N6 wy =>
       f7 wx (extend6 0 wy)
    | N7 wy => f7 wx wy
    | N8 wy => f8 (extend7 0 wx) wy
    | N9 wy => f9 (extend7 1 wx) wy
    | N10 wy => f10 (extend7 2 wx) wy
    | N11 wy => f11 (extend7 3 wx) wy
    | N12 wy => f12 (extend7 4 wx) wy
    | N13 wy => f13 (extend7 5 wx) wy
    | Nn m wy => fnn m (extend13 m (extend7 5 wx)) wy
    end
  | N8 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       f8 wx (extend0 7 wy)
    | N1 wy =>
       f8 wx (extend1 6 wy)
    | N2 wy =>
       f8 wx (extend2 5 wy)
    | N3 wy =>
       f8 wx (extend3 4 wy)
    | N4 wy =>
       f8 wx (extend4 3 wy)
    | N5 wy =>
       f8 wx (extend5 2 wy)
    | N6 wy =>
       f8 wx (extend6 1 wy)
    | N7 wy =>
       f8 wx (extend7 0 wy)
    | N8 wy => f8 wx wy
    | N9 wy => f9 (extend8 0 wx) wy
    | N10 wy => f10 (extend8 1 wx) wy
    | N11 wy => f11 (extend8 2 wx) wy
    | N12 wy => f12 (extend8 3 wx) wy
    | N13 wy => f13 (extend8 4 wx) wy
    | Nn m wy => fnn m (extend13 m (extend8 4 wx)) wy
    end
  | N9 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       f9 wx (extend0 8 wy)
    | N1 wy =>
       f9 wx (extend1 7 wy)
    | N2 wy =>
       f9 wx (extend2 6 wy)
    | N3 wy =>
       f9 wx (extend3 5 wy)
    | N4 wy =>
       f9 wx (extend4 4 wy)
    | N5 wy =>
       f9 wx (extend5 3 wy)
    | N6 wy =>
       f9 wx (extend6 2 wy)
    | N7 wy =>
       f9 wx (extend7 1 wy)
    | N8 wy =>
       f9 wx (extend8 0 wy)
    | N9 wy => f9 wx wy
    | N10 wy => f10 (extend9 0 wx) wy
    | N11 wy => f11 (extend9 1 wx) wy
    | N12 wy => f12 (extend9 2 wx) wy
    | N13 wy => f13 (extend9 3 wx) wy
    | Nn m wy => fnn m (extend13 m (extend9 3 wx)) wy
    end
  | N10 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       f10 wx (extend0 9 wy)
    | N1 wy =>
       f10 wx (extend1 8 wy)
    | N2 wy =>
       f10 wx (extend2 7 wy)
    | N3 wy =>
       f10 wx (extend3 6 wy)
    | N4 wy =>
       f10 wx (extend4 5 wy)
    | N5 wy =>
       f10 wx (extend5 4 wy)
    | N6 wy =>
       f10 wx (extend6 3 wy)
    | N7 wy =>
       f10 wx (extend7 2 wy)
    | N8 wy =>
       f10 wx (extend8 1 wy)
    | N9 wy =>
       f10 wx (extend9 0 wy)
    | N10 wy => f10 wx wy
    | N11 wy => f11 (extend10 0 wx) wy
    | N12 wy => f12 (extend10 1 wx) wy
    | N13 wy => f13 (extend10 2 wx) wy
    | Nn m wy => fnn m (extend13 m (extend10 2 wx)) wy
    end
  | N11 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       f11 wx (extend0 10 wy)
    | N1 wy =>
       f11 wx (extend1 9 wy)
    | N2 wy =>
       f11 wx (extend2 8 wy)
    | N3 wy =>
       f11 wx (extend3 7 wy)
    | N4 wy =>
       f11 wx (extend4 6 wy)
    | N5 wy =>
       f11 wx (extend5 5 wy)
    | N6 wy =>
       f11 wx (extend6 4 wy)
    | N7 wy =>
       f11 wx (extend7 3 wy)
    | N8 wy =>
       f11 wx (extend8 2 wy)
    | N9 wy =>
       f11 wx (extend9 1 wy)
    | N10 wy =>
       f11 wx (extend10 0 wy)
    | N11 wy => f11 wx wy
    | N12 wy => f12 (extend11 0 wx) wy
    | N13 wy => f13 (extend11 1 wx) wy
    | Nn m wy => fnn m (extend13 m (extend11 1 wx)) wy
    end
  | N12 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       f12 wx (extend0 11 wy)
    | N1 wy =>
       f12 wx (extend1 10 wy)
    | N2 wy =>
       f12 wx (extend2 9 wy)
    | N3 wy =>
       f12 wx (extend3 8 wy)
    | N4 wy =>
       f12 wx (extend4 7 wy)
    | N5 wy =>
       f12 wx (extend5 6 wy)
    | N6 wy =>
       f12 wx (extend6 5 wy)
    | N7 wy =>
       f12 wx (extend7 4 wy)
    | N8 wy =>
       f12 wx (extend8 3 wy)
    | N9 wy =>
       f12 wx (extend9 2 wy)
    | N10 wy =>
       f12 wx (extend10 1 wy)
    | N11 wy =>
       f12 wx (extend11 0 wy)
    | N12 wy => f12 wx wy
    | N13 wy => f13 (extend12 0 wx) wy
    | Nn m wy => fnn m (extend13 m (extend12 0 wx)) wy
    end
  | N13 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       f13 wx (extend0 12 wy)
    | N1 wy =>
       f13 wx (extend1 11 wy)
    | N2 wy =>
       f13 wx (extend2 10 wy)
    | N3 wy =>
       f13 wx (extend3 9 wy)
    | N4 wy =>
       f13 wx (extend4 8 wy)
    | N5 wy =>
       f13 wx (extend5 7 wy)
    | N6 wy =>
       f13 wx (extend6 6 wy)
    | N7 wy =>
       f13 wx (extend7 5 wy)
    | N8 wy =>
       f13 wx (extend8 4 wy)
    | N9 wy =>
       f13 wx (extend9 3 wy)
    | N10 wy =>
       f13 wx (extend10 2 wy)
    | N11 wy =>
       f13 wx (extend11 1 wy)
    | N12 wy =>
       f13 wx (extend12 0 wy)
    | N13 wy => f13 wx wy
    | Nn m wy => fnn m (extend13 m wx) wy
    end
  |  Nn n wx =>
     match y with
     | N0 wy =>
      if w0_eq0 wy then ft0 x else
      fnn n wx (extend13 n (extend0 12 wy))
     | N1 wy =>
      fnn n wx (extend13 n (extend1 11 wy))
     | N2 wy =>
      fnn n wx (extend13 n (extend2 10 wy))
     | N3 wy =>
      fnn n wx (extend13 n (extend3 9 wy))
     | N4 wy =>
      fnn n wx (extend13 n (extend4 8 wy))
     | N5 wy =>
      fnn n wx (extend13 n (extend5 7 wy))
     | N6 wy =>
      fnn n wx (extend13 n (extend6 6 wy))
     | N7 wy =>
      fnn n wx (extend13 n (extend7 5 wy))
     | N8 wy =>
      fnn n wx (extend13 n (extend8 4 wy))
     | N9 wy =>
      fnn n wx (extend13 n (extend9 3 wy))
     | N10 wy =>
      fnn n wx (extend13 n (extend10 2 wy))
     | N11 wy =>
      fnn n wx (extend13 n (extend11 1 wy))
     | N12 wy =>
      fnn n wx (extend13 n (extend12 0 wy))
     | N13 wy =>
      fnn n wx (extend13 n wy)
        | Nn m wy =>
            let mn := Max.max n m in
            let d := diff n m in
              fnn mn
              (castm (diff_r n m) (extend_tr wx (snd d)))
              (castm (diff_l n m) (extend_tr wy (fst d)))
    end
  end.

  (* We iter the smaller argument with the bigger  *)
  Definition iter (x y: t_): res := 
    Eval lazy zeta beta iota delta [extend0 extend1 extend2 extend3 extend4 extend5 extend6 extend7 extend8 extend9 extend10 extend11 extend12 extend13 
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
  | N0 wx, N7 wy => f0n 6 wx wy
  | N0 wx, N8 wy => f0n 7 wx wy
  | N0 wx, N9 wy => f0n 8 wx wy
  | N0 wx, N10 wy => f0n 9 wx wy
  | N0 wx, N11 wy => f0n 10 wx wy
  | N0 wx, N12 wy => f0n 11 wx wy
  | N0 wx, N13 wy => f0n 12 wx wy
  | N0 wx, Nn m wy => f13n m (extend0 12 wx) wy
  | N1 wx, N0 wy => fn0 0 wx wy
  | N1 wx, N1 wy => f1 wx wy
  | N1 wx, N2 wy => f1n 0 wx wy
  | N1 wx, N3 wy => f1n 1 wx wy
  | N1 wx, N4 wy => f1n 2 wx wy
  | N1 wx, N5 wy => f1n 3 wx wy
  | N1 wx, N6 wy => f1n 4 wx wy
  | N1 wx, N7 wy => f1n 5 wx wy
  | N1 wx, N8 wy => f1n 6 wx wy
  | N1 wx, N9 wy => f1n 7 wx wy
  | N1 wx, N10 wy => f1n 8 wx wy
  | N1 wx, N11 wy => f1n 9 wx wy
  | N1 wx, N12 wy => f1n 10 wx wy
  | N1 wx, N13 wy => f1n 11 wx wy
  | N1 wx, Nn m wy => f13n m (extend1 11 wx) wy
  | N2 wx, N0 wy => fn0 1 wx wy
  | N2 wx, N1 wy => fn1 0 wx wy
  | N2 wx, N2 wy => f2 wx wy
  | N2 wx, N3 wy => f2n 0 wx wy
  | N2 wx, N4 wy => f2n 1 wx wy
  | N2 wx, N5 wy => f2n 2 wx wy
  | N2 wx, N6 wy => f2n 3 wx wy
  | N2 wx, N7 wy => f2n 4 wx wy
  | N2 wx, N8 wy => f2n 5 wx wy
  | N2 wx, N9 wy => f2n 6 wx wy
  | N2 wx, N10 wy => f2n 7 wx wy
  | N2 wx, N11 wy => f2n 8 wx wy
  | N2 wx, N12 wy => f2n 9 wx wy
  | N2 wx, N13 wy => f2n 10 wx wy
  | N2 wx, Nn m wy => f13n m (extend2 10 wx) wy
  | N3 wx, N0 wy => fn0 2 wx wy
  | N3 wx, N1 wy => fn1 1 wx wy
  | N3 wx, N2 wy => fn2 0 wx wy
  | N3 wx, N3 wy => f3 wx wy
  | N3 wx, N4 wy => f3n 0 wx wy
  | N3 wx, N5 wy => f3n 1 wx wy
  | N3 wx, N6 wy => f3n 2 wx wy
  | N3 wx, N7 wy => f3n 3 wx wy
  | N3 wx, N8 wy => f3n 4 wx wy
  | N3 wx, N9 wy => f3n 5 wx wy
  | N3 wx, N10 wy => f3n 6 wx wy
  | N3 wx, N11 wy => f3n 7 wx wy
  | N3 wx, N12 wy => f3n 8 wx wy
  | N3 wx, N13 wy => f3n 9 wx wy
  | N3 wx, Nn m wy => f13n m (extend3 9 wx) wy
  | N4 wx, N0 wy => fn0 3 wx wy
  | N4 wx, N1 wy => fn1 2 wx wy
  | N4 wx, N2 wy => fn2 1 wx wy
  | N4 wx, N3 wy => fn3 0 wx wy
  | N4 wx, N4 wy => f4 wx wy
  | N4 wx, N5 wy => f4n 0 wx wy
  | N4 wx, N6 wy => f4n 1 wx wy
  | N4 wx, N7 wy => f4n 2 wx wy
  | N4 wx, N8 wy => f4n 3 wx wy
  | N4 wx, N9 wy => f4n 4 wx wy
  | N4 wx, N10 wy => f4n 5 wx wy
  | N4 wx, N11 wy => f4n 6 wx wy
  | N4 wx, N12 wy => f4n 7 wx wy
  | N4 wx, N13 wy => f4n 8 wx wy
  | N4 wx, Nn m wy => f13n m (extend4 8 wx) wy
  | N5 wx, N0 wy => fn0 4 wx wy
  | N5 wx, N1 wy => fn1 3 wx wy
  | N5 wx, N2 wy => fn2 2 wx wy
  | N5 wx, N3 wy => fn3 1 wx wy
  | N5 wx, N4 wy => fn4 0 wx wy
  | N5 wx, N5 wy => f5 wx wy
  | N5 wx, N6 wy => f5n 0 wx wy
  | N5 wx, N7 wy => f5n 1 wx wy
  | N5 wx, N8 wy => f5n 2 wx wy
  | N5 wx, N9 wy => f5n 3 wx wy
  | N5 wx, N10 wy => f5n 4 wx wy
  | N5 wx, N11 wy => f5n 5 wx wy
  | N5 wx, N12 wy => f5n 6 wx wy
  | N5 wx, N13 wy => f5n 7 wx wy
  | N5 wx, Nn m wy => f13n m (extend5 7 wx) wy
  | N6 wx, N0 wy => fn0 5 wx wy
  | N6 wx, N1 wy => fn1 4 wx wy
  | N6 wx, N2 wy => fn2 3 wx wy
  | N6 wx, N3 wy => fn3 2 wx wy
  | N6 wx, N4 wy => fn4 1 wx wy
  | N6 wx, N5 wy => fn5 0 wx wy
  | N6 wx, N6 wy => f6 wx wy
  | N6 wx, N7 wy => f6n 0 wx wy
  | N6 wx, N8 wy => f6n 1 wx wy
  | N6 wx, N9 wy => f6n 2 wx wy
  | N6 wx, N10 wy => f6n 3 wx wy
  | N6 wx, N11 wy => f6n 4 wx wy
  | N6 wx, N12 wy => f6n 5 wx wy
  | N6 wx, N13 wy => f6n 6 wx wy
  | N6 wx, Nn m wy => f13n m (extend6 6 wx) wy
  | N7 wx, N0 wy => fn0 6 wx wy
  | N7 wx, N1 wy => fn1 5 wx wy
  | N7 wx, N2 wy => fn2 4 wx wy
  | N7 wx, N3 wy => fn3 3 wx wy
  | N7 wx, N4 wy => fn4 2 wx wy
  | N7 wx, N5 wy => fn5 1 wx wy
  | N7 wx, N6 wy => fn6 0 wx wy
  | N7 wx, N7 wy => f7 wx wy
  | N7 wx, N8 wy => f7n 0 wx wy
  | N7 wx, N9 wy => f7n 1 wx wy
  | N7 wx, N10 wy => f7n 2 wx wy
  | N7 wx, N11 wy => f7n 3 wx wy
  | N7 wx, N12 wy => f7n 4 wx wy
  | N7 wx, N13 wy => f7n 5 wx wy
  | N7 wx, Nn m wy => f13n m (extend7 5 wx) wy
  | N8 wx, N0 wy => fn0 7 wx wy
  | N8 wx, N1 wy => fn1 6 wx wy
  | N8 wx, N2 wy => fn2 5 wx wy
  | N8 wx, N3 wy => fn3 4 wx wy
  | N8 wx, N4 wy => fn4 3 wx wy
  | N8 wx, N5 wy => fn5 2 wx wy
  | N8 wx, N6 wy => fn6 1 wx wy
  | N8 wx, N7 wy => fn7 0 wx wy
  | N8 wx, N8 wy => f8 wx wy
  | N8 wx, N9 wy => f8n 0 wx wy
  | N8 wx, N10 wy => f8n 1 wx wy
  | N8 wx, N11 wy => f8n 2 wx wy
  | N8 wx, N12 wy => f8n 3 wx wy
  | N8 wx, N13 wy => f8n 4 wx wy
  | N8 wx, Nn m wy => f13n m (extend8 4 wx) wy
  | N9 wx, N0 wy => fn0 8 wx wy
  | N9 wx, N1 wy => fn1 7 wx wy
  | N9 wx, N2 wy => fn2 6 wx wy
  | N9 wx, N3 wy => fn3 5 wx wy
  | N9 wx, N4 wy => fn4 4 wx wy
  | N9 wx, N5 wy => fn5 3 wx wy
  | N9 wx, N6 wy => fn6 2 wx wy
  | N9 wx, N7 wy => fn7 1 wx wy
  | N9 wx, N8 wy => fn8 0 wx wy
  | N9 wx, N9 wy => f9 wx wy
  | N9 wx, N10 wy => f9n 0 wx wy
  | N9 wx, N11 wy => f9n 1 wx wy
  | N9 wx, N12 wy => f9n 2 wx wy
  | N9 wx, N13 wy => f9n 3 wx wy
  | N9 wx, Nn m wy => f13n m (extend9 3 wx) wy
  | N10 wx, N0 wy => fn0 9 wx wy
  | N10 wx, N1 wy => fn1 8 wx wy
  | N10 wx, N2 wy => fn2 7 wx wy
  | N10 wx, N3 wy => fn3 6 wx wy
  | N10 wx, N4 wy => fn4 5 wx wy
  | N10 wx, N5 wy => fn5 4 wx wy
  | N10 wx, N6 wy => fn6 3 wx wy
  | N10 wx, N7 wy => fn7 2 wx wy
  | N10 wx, N8 wy => fn8 1 wx wy
  | N10 wx, N9 wy => fn9 0 wx wy
  | N10 wx, N10 wy => f10 wx wy
  | N10 wx, N11 wy => f10n 0 wx wy
  | N10 wx, N12 wy => f10n 1 wx wy
  | N10 wx, N13 wy => f10n 2 wx wy
  | N10 wx, Nn m wy => f13n m (extend10 2 wx) wy
  | N11 wx, N0 wy => fn0 10 wx wy
  | N11 wx, N1 wy => fn1 9 wx wy
  | N11 wx, N2 wy => fn2 8 wx wy
  | N11 wx, N3 wy => fn3 7 wx wy
  | N11 wx, N4 wy => fn4 6 wx wy
  | N11 wx, N5 wy => fn5 5 wx wy
  | N11 wx, N6 wy => fn6 4 wx wy
  | N11 wx, N7 wy => fn7 3 wx wy
  | N11 wx, N8 wy => fn8 2 wx wy
  | N11 wx, N9 wy => fn9 1 wx wy
  | N11 wx, N10 wy => fn10 0 wx wy
  | N11 wx, N11 wy => f11 wx wy
  | N11 wx, N12 wy => f11n 0 wx wy
  | N11 wx, N13 wy => f11n 1 wx wy
  | N11 wx, Nn m wy => f13n m (extend11 1 wx) wy
  | N12 wx, N0 wy => fn0 11 wx wy
  | N12 wx, N1 wy => fn1 10 wx wy
  | N12 wx, N2 wy => fn2 9 wx wy
  | N12 wx, N3 wy => fn3 8 wx wy
  | N12 wx, N4 wy => fn4 7 wx wy
  | N12 wx, N5 wy => fn5 6 wx wy
  | N12 wx, N6 wy => fn6 5 wx wy
  | N12 wx, N7 wy => fn7 4 wx wy
  | N12 wx, N8 wy => fn8 3 wx wy
  | N12 wx, N9 wy => fn9 2 wx wy
  | N12 wx, N10 wy => fn10 1 wx wy
  | N12 wx, N11 wy => fn11 0 wx wy
  | N12 wx, N12 wy => f12 wx wy
  | N12 wx, N13 wy => f12n 0 wx wy
  | N12 wx, Nn m wy => f13n m (extend12 0 wx) wy
  | N13 wx, N0 wy => fn0 12 wx wy
  | N13 wx, N1 wy => fn1 11 wx wy
  | N13 wx, N2 wy => fn2 10 wx wy
  | N13 wx, N3 wy => fn3 9 wx wy
  | N13 wx, N4 wy => fn4 8 wx wy
  | N13 wx, N5 wy => fn5 7 wx wy
  | N13 wx, N6 wy => fn6 6 wx wy
  | N13 wx, N7 wy => fn7 5 wx wy
  | N13 wx, N8 wy => fn8 4 wx wy
  | N13 wx, N9 wy => fn9 3 wx wy
  | N13 wx, N10 wy => fn10 2 wx wy
  | N13 wx, N11 wy => fn11 1 wx wy
  | N13 wx, N12 wy => fn12 0 wx wy
  | N13 wx, N13 wy => f13 wx wy
  | N13 wx, Nn m wy => f13n m wx wy
  | Nn n wx, N0 wy => fn13 n wx (extend0 12 wy)
  | Nn n wx, N1 wy => fn13 n wx (extend1 11 wy)
  | Nn n wx, N2 wy => fn13 n wx (extend2 10 wy)
  | Nn n wx, N3 wy => fn13 n wx (extend3 9 wy)
  | Nn n wx, N4 wy => fn13 n wx (extend4 8 wy)
  | Nn n wx, N5 wy => fn13 n wx (extend5 7 wy)
  | Nn n wx, N6 wy => fn13 n wx (extend6 6 wy)
  | Nn n wx, N7 wy => fn13 n wx (extend7 5 wy)
  | Nn n wx, N8 wy => fn13 n wx (extend8 4 wy)
  | Nn n wx, N9 wy => fn13 n wx (extend9 3 wy)
  | Nn n wx, N10 wy => fn13 n wx (extend10 2 wy)
  | Nn n wx, N11 wy => fn13 n wx (extend11 1 wy)
  | Nn n wx, N12 wy => fn13 n wx (extend12 0 wy)
  | Nn n wx, N13 wy => fn13 n wx wy
  | Nn n wx, Nn m wy => fnm n m wx wy
  end.

  (* We iter the smaller argument with the bigger  (zero case) *)
  Definition iter0 (x y: t_): res :=
    Eval lazy zeta beta iota delta [extend0 extend1 extend2 extend3 extend4 extend5 extend6 extend7 extend8 extend9 extend10 extend11 extend12 extend13 
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
    | N7 wy => f0n 6 wx wy
    | N8 wy => f0n 7 wx wy
    | N9 wy => f0n 8 wx wy
    | N10 wy => f0n 9 wx wy
    | N11 wy => f0n 10 wx wy
    | N12 wy => f0n 11 wx wy
    | N13 wy => f0n 12 wx wy
    | Nn m wy => f13n m (extend0 12 wx) wy
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
    | N7 wy => f1n 5 wx wy
    | N8 wy => f1n 6 wx wy
    | N9 wy => f1n 7 wx wy
    | N10 wy => f1n 8 wx wy
    | N11 wy => f1n 9 wx wy
    | N12 wy => f1n 10 wx wy
    | N13 wy => f1n 11 wx wy
    | Nn m wy => f13n m (extend1 11 wx) wy
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
    | N7 wy => f2n 4 wx wy
    | N8 wy => f2n 5 wx wy
    | N9 wy => f2n 6 wx wy
    | N10 wy => f2n 7 wx wy
    | N11 wy => f2n 8 wx wy
    | N12 wy => f2n 9 wx wy
    | N13 wy => f2n 10 wx wy
    | Nn m wy => f13n m (extend2 10 wx) wy
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
    | N7 wy => f3n 3 wx wy
    | N8 wy => f3n 4 wx wy
    | N9 wy => f3n 5 wx wy
    | N10 wy => f3n 6 wx wy
    | N11 wy => f3n 7 wx wy
    | N12 wy => f3n 8 wx wy
    | N13 wy => f3n 9 wx wy
    | Nn m wy => f13n m (extend3 9 wx) wy
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
    | N7 wy => f4n 2 wx wy
    | N8 wy => f4n 3 wx wy
    | N9 wy => f4n 4 wx wy
    | N10 wy => f4n 5 wx wy
    | N11 wy => f4n 6 wx wy
    | N12 wy => f4n 7 wx wy
    | N13 wy => f4n 8 wx wy
    | Nn m wy => f13n m (extend4 8 wx) wy
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
    | N7 wy => f5n 1 wx wy
    | N8 wy => f5n 2 wx wy
    | N9 wy => f5n 3 wx wy
    | N10 wy => f5n 4 wx wy
    | N11 wy => f5n 5 wx wy
    | N12 wy => f5n 6 wx wy
    | N13 wy => f5n 7 wx wy
    | Nn m wy => f13n m (extend5 7 wx) wy
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
    | N7 wy => f6n 0 wx wy
    | N8 wy => f6n 1 wx wy
    | N9 wy => f6n 2 wx wy
    | N10 wy => f6n 3 wx wy
    | N11 wy => f6n 4 wx wy
    | N12 wy => f6n 5 wx wy
    | N13 wy => f6n 6 wx wy
    | Nn m wy => f13n m (extend6 6 wx) wy
    end
  | N7 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       fn0 6 wx wy
    | N1 wy =>
       fn1 5 wx wy
    | N2 wy =>
       fn2 4 wx wy
    | N3 wy =>
       fn3 3 wx wy
    | N4 wy =>
       fn4 2 wx wy
    | N5 wy =>
       fn5 1 wx wy
    | N6 wy =>
       fn6 0 wx wy
    | N7 wy => f7 wx wy
    | N8 wy => f7n 0 wx wy
    | N9 wy => f7n 1 wx wy
    | N10 wy => f7n 2 wx wy
    | N11 wy => f7n 3 wx wy
    | N12 wy => f7n 4 wx wy
    | N13 wy => f7n 5 wx wy
    | Nn m wy => f13n m (extend7 5 wx) wy
    end
  | N8 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       fn0 7 wx wy
    | N1 wy =>
       fn1 6 wx wy
    | N2 wy =>
       fn2 5 wx wy
    | N3 wy =>
       fn3 4 wx wy
    | N4 wy =>
       fn4 3 wx wy
    | N5 wy =>
       fn5 2 wx wy
    | N6 wy =>
       fn6 1 wx wy
    | N7 wy =>
       fn7 0 wx wy
    | N8 wy => f8 wx wy
    | N9 wy => f8n 0 wx wy
    | N10 wy => f8n 1 wx wy
    | N11 wy => f8n 2 wx wy
    | N12 wy => f8n 3 wx wy
    | N13 wy => f8n 4 wx wy
    | Nn m wy => f13n m (extend8 4 wx) wy
    end
  | N9 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       fn0 8 wx wy
    | N1 wy =>
       fn1 7 wx wy
    | N2 wy =>
       fn2 6 wx wy
    | N3 wy =>
       fn3 5 wx wy
    | N4 wy =>
       fn4 4 wx wy
    | N5 wy =>
       fn5 3 wx wy
    | N6 wy =>
       fn6 2 wx wy
    | N7 wy =>
       fn7 1 wx wy
    | N8 wy =>
       fn8 0 wx wy
    | N9 wy => f9 wx wy
    | N10 wy => f9n 0 wx wy
    | N11 wy => f9n 1 wx wy
    | N12 wy => f9n 2 wx wy
    | N13 wy => f9n 3 wx wy
    | Nn m wy => f13n m (extend9 3 wx) wy
    end
  | N10 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       fn0 9 wx wy
    | N1 wy =>
       fn1 8 wx wy
    | N2 wy =>
       fn2 7 wx wy
    | N3 wy =>
       fn3 6 wx wy
    | N4 wy =>
       fn4 5 wx wy
    | N5 wy =>
       fn5 4 wx wy
    | N6 wy =>
       fn6 3 wx wy
    | N7 wy =>
       fn7 2 wx wy
    | N8 wy =>
       fn8 1 wx wy
    | N9 wy =>
       fn9 0 wx wy
    | N10 wy => f10 wx wy
    | N11 wy => f10n 0 wx wy
    | N12 wy => f10n 1 wx wy
    | N13 wy => f10n 2 wx wy
    | Nn m wy => f13n m (extend10 2 wx) wy
    end
  | N11 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       fn0 10 wx wy
    | N1 wy =>
       fn1 9 wx wy
    | N2 wy =>
       fn2 8 wx wy
    | N3 wy =>
       fn3 7 wx wy
    | N4 wy =>
       fn4 6 wx wy
    | N5 wy =>
       fn5 5 wx wy
    | N6 wy =>
       fn6 4 wx wy
    | N7 wy =>
       fn7 3 wx wy
    | N8 wy =>
       fn8 2 wx wy
    | N9 wy =>
       fn9 1 wx wy
    | N10 wy =>
       fn10 0 wx wy
    | N11 wy => f11 wx wy
    | N12 wy => f11n 0 wx wy
    | N13 wy => f11n 1 wx wy
    | Nn m wy => f13n m (extend11 1 wx) wy
    end
  | N12 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       fn0 11 wx wy
    | N1 wy =>
       fn1 10 wx wy
    | N2 wy =>
       fn2 9 wx wy
    | N3 wy =>
       fn3 8 wx wy
    | N4 wy =>
       fn4 7 wx wy
    | N5 wy =>
       fn5 6 wx wy
    | N6 wy =>
       fn6 5 wx wy
    | N7 wy =>
       fn7 4 wx wy
    | N8 wy =>
       fn8 3 wx wy
    | N9 wy =>
       fn9 2 wx wy
    | N10 wy =>
       fn10 1 wx wy
    | N11 wy =>
       fn11 0 wx wy
    | N12 wy => f12 wx wy
    | N13 wy => f12n 0 wx wy
    | Nn m wy => f13n m (extend12 0 wx) wy
    end
  | N13 wx =>
    match y with
    | N0 wy =>
       if w0_eq0 wy then ft0 x else
       fn0 12 wx wy
    | N1 wy =>
       fn1 11 wx wy
    | N2 wy =>
       fn2 10 wx wy
    | N3 wy =>
       fn3 9 wx wy
    | N4 wy =>
       fn4 8 wx wy
    | N5 wy =>
       fn5 7 wx wy
    | N6 wy =>
       fn6 6 wx wy
    | N7 wy =>
       fn7 5 wx wy
    | N8 wy =>
       fn8 4 wx wy
    | N9 wy =>
       fn9 3 wx wy
    | N10 wy =>
       fn10 2 wx wy
    | N11 wy =>
       fn11 1 wx wy
    | N12 wy =>
       fn12 0 wx wy
    | N13 wy => f13 wx wy
    | Nn m wy => f13n m wx wy
    end
  | Nn n wx =>
    match y with
    | N0 wy =>
      if w0_eq0 wy then ft0 x else
      fn13 n wx (extend0 12 wy)
    | N1 wy =>
      fn13 n wx (extend1 11 wy)
    | N2 wy =>
      fn13 n wx (extend2 10 wy)
    | N3 wy =>
      fn13 n wx (extend3 9 wy)
    | N4 wy =>
      fn13 n wx (extend4 8 wy)
    | N5 wy =>
      fn13 n wx (extend5 7 wy)
    | N6 wy =>
      fn13 n wx (extend6 6 wy)
    | N7 wy =>
      fn13 n wx (extend7 5 wy)
    | N8 wy =>
      fn13 n wx (extend8 4 wy)
    | N9 wy =>
      fn13 n wx (extend9 3 wy)
    | N10 wy =>
      fn13 n wx (extend10 2 wy)
    | N11 wy =>
      fn13 n wx (extend11 1 wy)
    | N12 wy =>
      fn13 n wx (extend12 0 wy)
    | N13 wy =>
      fn13 n wx wy
    | Nn m wy => fnm n m wx wy
    end
  end.

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
   reduce_n1 _ _ zero w6_eq0 reduce_6 N7.
 Definition reduce_8 :=
  Eval lazy beta iota delta[reduce_n1] in
   reduce_n1 _ _ zero w7_eq0 reduce_7 N8.
 Definition reduce_9 :=
  Eval lazy beta iota delta[reduce_n1] in
   reduce_n1 _ _ zero w8_eq0 reduce_8 N9.
 Definition reduce_10 :=
  Eval lazy beta iota delta[reduce_n1] in
   reduce_n1 _ _ zero w9_eq0 reduce_9 N10.
 Definition reduce_11 :=
  Eval lazy beta iota delta[reduce_n1] in
   reduce_n1 _ _ zero w10_eq0 reduce_10 N11.
 Definition reduce_12 :=
  Eval lazy beta iota delta[reduce_n1] in
   reduce_n1 _ _ zero w11_eq0 reduce_11 N12.
 Definition reduce_13 :=
  Eval lazy beta iota delta[reduce_n1] in
   reduce_n1 _ _ zero w12_eq0 reduce_12 N13.
 Definition reduce_14 :=
  Eval lazy beta iota delta[reduce_n1] in
   reduce_n1 _ _ zero w13_eq0 reduce_13 (Nn 0).
 Definition reduce_n n := 
  Eval lazy beta iota delta[reduce_n] in
   reduce_n _ _ zero reduce_14 Nn n.

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
 Definition w7_succ_c := w7_op.(znz_succ_c).
 Definition w8_succ_c := w8_op.(znz_succ_c).
 Definition w9_succ_c := w9_op.(znz_succ_c).
 Definition w10_succ_c := w10_op.(znz_succ_c).
 Definition w11_succ_c := w11_op.(znz_succ_c).
 Definition w12_succ_c := w12_op.(znz_succ_c).
 Definition w13_succ_c := w13_op.(znz_succ_c).

 Definition w0_succ := w0_op.(znz_succ).
 Definition w1_succ := w1_op.(znz_succ).
 Definition w2_succ := w2_op.(znz_succ).
 Definition w3_succ := w3_op.(znz_succ).
 Definition w4_succ := w4_op.(znz_succ).
 Definition w5_succ := w5_op.(znz_succ).
 Definition w6_succ := w6_op.(znz_succ).
 Definition w7_succ := w7_op.(znz_succ).
 Definition w8_succ := w8_op.(znz_succ).
 Definition w9_succ := w9_op.(znz_succ).
 Definition w10_succ := w10_op.(znz_succ).
 Definition w11_succ := w11_op.(znz_succ).
 Definition w12_succ := w12_op.(znz_succ).
 Definition w13_succ := w13_op.(znz_succ).

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
    | C1 r => N7 (WW one6 r)
    end
  | N7 wx =>
    match w7_succ_c wx with
    | C0 r => N7 r
    | C1 r => N8 (WW one7 r)
    end
  | N8 wx =>
    match w8_succ_c wx with
    | C0 r => N8 r
    | C1 r => N9 (WW one8 r)
    end
  | N9 wx =>
    match w9_succ_c wx with
    | C0 r => N9 r
    | C1 r => N10 (WW one9 r)
    end
  | N10 wx =>
    match w10_succ_c wx with
    | C0 r => N10 r
    | C1 r => N11 (WW one10 r)
    end
  | N11 wx =>
    match w11_succ_c wx with
    | C0 r => N11 r
    | C1 r => N12 (WW one11 r)
    end
  | N12 wx =>
    match w12_succ_c wx with
    | C0 r => N12 r
    | C1 r => N13 (WW one12 r)
    end
  | N13 wx =>
    match w13_succ_c wx with
    | C0 r => N13 r
    | C1 r => Nn 0 (WW one13 r)
    end
  | Nn n wx =>
    let op := make_op n in
    match op.(znz_succ_c) wx with
    | C0 r => Nn n r
    | C1 r => Nn (S n) (WW op.(znz_1) r)
    end
  end.

 Theorem spec_succ: forall n, [succ n] = [n] + 1.
 Admitted.

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
  | C1 r => N7 (WW one6 r)
  end.

 Definition w7_add_c := znz_add_c w7_op.
 Definition w7_add x y :=
  match w7_add_c x y with
  | C0 r => N7 r
  | C1 r => N8 (WW one7 r)
  end.

 Definition w8_add_c := znz_add_c w8_op.
 Definition w8_add x y :=
  match w8_add_c x y with
  | C0 r => N8 r
  | C1 r => N9 (WW one8 r)
  end.

 Definition w9_add_c := znz_add_c w9_op.
 Definition w9_add x y :=
  match w9_add_c x y with
  | C0 r => N9 r
  | C1 r => N10 (WW one9 r)
  end.

 Definition w10_add_c := znz_add_c w10_op.
 Definition w10_add x y :=
  match w10_add_c x y with
  | C0 r => N10 r
  | C1 r => N11 (WW one10 r)
  end.

 Definition w11_add_c := znz_add_c w11_op.
 Definition w11_add x y :=
  match w11_add_c x y with
  | C0 r => N11 r
  | C1 r => N12 (WW one11 r)
  end.

 Definition w12_add_c := znz_add_c w12_op.
 Definition w12_add x y :=
  match w12_add_c x y with
  | C0 r => N12 r
  | C1 r => N13 (WW one12 r)
  end.

 Definition w13_add_c := znz_add_c w13_op.
 Definition w13_add x y :=
  match w13_add_c x y with
  | C0 r => N13 r
  | C1 r => Nn 0 (WW one13 r)
  end.

 Definition addn n (x y : word w13 (S n)) :=
  let op := make_op n in
  match op.(znz_add_c) x y with
  | C0 r => Nn n r
  | C1 r => Nn (S n) (WW op.(znz_1) r)  end.

 Definition add := Eval lazy beta delta [same_level] in
   (same_level t_ w0_add w1_add w2_add w3_add w4_add w5_add w6_add w7_add w8_add w9_add w10_add w11_add w12_add w13_add addn).

 Theorem spec_add: forall x y, [add x y] = [x] + [y].
 Admitted.

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
 Definition w7_pred_c := w7_op.(znz_pred_c).
 Definition w8_pred_c := w8_op.(znz_pred_c).
 Definition w9_pred_c := w9_op.(znz_pred_c).
 Definition w10_pred_c := w10_op.(znz_pred_c).
 Definition w11_pred_c := w11_op.(znz_pred_c).
 Definition w12_pred_c := w12_op.(znz_pred_c).
 Definition w13_pred_c := w13_op.(znz_pred_c).

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
  | N7 wx =>
    match w7_pred_c wx with
    | C0 r => reduce_7 r
    | C1 r => zero
    end
  | N8 wx =>
    match w8_pred_c wx with
    | C0 r => reduce_8 r
    | C1 r => zero
    end
  | N9 wx =>
    match w9_pred_c wx with
    | C0 r => reduce_9 r
    | C1 r => zero
    end
  | N10 wx =>
    match w10_pred_c wx with
    | C0 r => reduce_10 r
    | C1 r => zero
    end
  | N11 wx =>
    match w11_pred_c wx with
    | C0 r => reduce_11 r
    | C1 r => zero
    end
  | N12 wx =>
    match w12_pred_c wx with
    | C0 r => reduce_12 r
    | C1 r => zero
    end
  | N13 wx =>
    match w13_pred_c wx with
    | C0 r => reduce_13 r
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
 Admitted.
 
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
 Definition w7_sub_c := w7_op.(znz_sub_c).
 Definition w8_sub_c := w8_op.(znz_sub_c).
 Definition w9_sub_c := w9_op.(znz_sub_c).
 Definition w10_sub_c := w10_op.(znz_sub_c).
 Definition w11_sub_c := w11_op.(znz_sub_c).
 Definition w12_sub_c := w12_op.(znz_sub_c).
 Definition w13_sub_c := w13_op.(znz_sub_c).

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
 Definition w7_sub x y :=
  match w7_sub_c x y with
  | C0 r => reduce_7 r
  | C1 r => zero
  end.
 Definition w8_sub x y :=
  match w8_sub_c x y with
  | C0 r => reduce_8 r
  | C1 r => zero
  end.
 Definition w9_sub x y :=
  match w9_sub_c x y with
  | C0 r => reduce_9 r
  | C1 r => zero
  end.
 Definition w10_sub x y :=
  match w10_sub_c x y with
  | C0 r => reduce_10 r
  | C1 r => zero
  end.
 Definition w11_sub x y :=
  match w11_sub_c x y with
  | C0 r => reduce_11 r
  | C1 r => zero
  end.
 Definition w12_sub x y :=
  match w12_sub_c x y with
  | C0 r => reduce_12 r
  | C1 r => zero
  end.
 Definition w13_sub x y :=
  match w13_sub_c x y with
  | C0 r => reduce_13 r
  | C1 r => zero
  end.

 Definition subn n (x y : word w13 (S n)) :=
  let op := make_op n in
  match op.(znz_sub_c) x y with
  | C0 r => Nn n r
  | C1 r => N0 w_0  end.

 Definition sub := Eval lazy beta delta [same_level] in
   (same_level t_ w0_sub w1_sub w2_sub w3_sub w4_sub w5_sub w6_sub w7_sub w8_sub w9_sub w10_sub w11_sub w12_sub w13_sub subn).

 Theorem spec_sub: forall x y, [y] <= [x] -> [sub x y] = [x] - [y].
 Admitted.

 Theorem spec_sub0: forall x y, [x] < [y] -> [sub x y] = 0.
 Admitted.

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
 Definition compare_7 := w7_op.(znz_compare).
 Definition comparen_7 :=
  compare_mn_1 w7 w7 W0 compare_7 (compare_7 W0) compare_7.
 Definition compare_8 := w8_op.(znz_compare).
 Definition comparen_8 :=
  compare_mn_1 w8 w8 W0 compare_8 (compare_8 W0) compare_8.
 Definition compare_9 := w9_op.(znz_compare).
 Definition comparen_9 :=
  compare_mn_1 w9 w9 W0 compare_9 (compare_9 W0) compare_9.
 Definition compare_10 := w10_op.(znz_compare).
 Definition comparen_10 :=
  compare_mn_1 w10 w10 W0 compare_10 (compare_10 W0) compare_10.
 Definition compare_11 := w11_op.(znz_compare).
 Definition comparen_11 :=
  compare_mn_1 w11 w11 W0 compare_11 (compare_11 W0) compare_11.
 Definition compare_12 := w12_op.(znz_compare).
 Definition comparen_12 :=
  compare_mn_1 w12 w12 W0 compare_12 (compare_12 W0) compare_12.
 Definition compare_13 := w13_op.(znz_compare).
 Definition comparen_13 :=
  compare_mn_1 w13 w13 W0 compare_13 (compare_13 W0) compare_13.

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
      compare_7
      (fun n x y => opp_compare (comparen_7 (S n) y x))
      (fun n => comparen_7 (S n))
      compare_8
      (fun n x y => opp_compare (comparen_8 (S n) y x))
      (fun n => comparen_8 (S n))
      compare_9
      (fun n x y => opp_compare (comparen_9 (S n) y x))
      (fun n => comparen_9 (S n))
      compare_10
      (fun n x y => opp_compare (comparen_10 (S n) y x))
      (fun n => comparen_10 (S n))
      compare_11
      (fun n x y => opp_compare (comparen_11 (S n) y x))
      (fun n => comparen_11 (S n))
      compare_12
      (fun n x y => opp_compare (comparen_12 (S n) y x))
      (fun n => comparen_12 (S n))
      compare_13
      (fun n x y => opp_compare (comparen_13 (S n) y x))
      (fun n => comparen_13 (S n))
      comparenm).

 Theorem spec_compare: forall x y,
    match compare x y with 
      Eq => [x] = [y]
    | Lt => [x] < [y]
    | Gt => [x] > [y]
    end.
 Admitted.

 Definition eq_bool x y :=
  match compare x y with
  | Eq => true
  | _  => false
  end.

 Theorem spec_eq_bool: forall x y,
    if eq_bool x y then [x] = [y] else [x] <> [y].
 Admitted.

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
 Definition w7_mul_c := w7_op.(znz_mul_c).
 Definition w8_mul_c := w8_op.(znz_mul_c).
 Definition w9_mul_c := w9_op.(znz_mul_c).
 Definition w10_mul_c := w10_op.(znz_mul_c).
 Definition w11_mul_c := w11_op.(znz_mul_c).
 Definition w12_mul_c := w12_op.(znz_mul_c).
 Definition w13_mul_c := w13_op.(znz_mul_c).

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
 Definition w7_mul_add :=
   Eval lazy beta delta [w_mul_add] in
     @w_mul_add w7 W0 w7_succ w7_add_c w7_mul_c.
 Definition w8_mul_add :=
   Eval lazy beta delta [w_mul_add] in
     @w_mul_add w8 W0 w8_succ w8_add_c w8_mul_c.
 Definition w9_mul_add :=
   Eval lazy beta delta [w_mul_add] in
     @w_mul_add w9 W0 w9_succ w9_add_c w9_mul_c.
 Definition w10_mul_add :=
   Eval lazy beta delta [w_mul_add] in
     @w_mul_add w10 W0 w10_succ w10_add_c w10_mul_c.
 Definition w11_mul_add :=
   Eval lazy beta delta [w_mul_add] in
     @w_mul_add w11 W0 w11_succ w11_add_c w11_mul_c.
 Definition w12_mul_add :=
   Eval lazy beta delta [w_mul_add] in
     @w_mul_add w12 W0 w12_succ w12_add_c w12_mul_c.
 Definition w13_mul_add :=
   Eval lazy beta delta [w_mul_add] in
     @w_mul_add w13 W0 w13_succ w13_add_c w13_mul_c.

 Definition w0_0W := w0_op.(znz_0W).
 Definition w1_0W := w1_op.(znz_0W).
 Definition w2_0W := w2_op.(znz_0W).
 Definition w3_0W := w3_op.(znz_0W).
 Definition w4_0W := w4_op.(znz_0W).
 Definition w5_0W := w5_op.(znz_0W).
 Definition w6_0W := w6_op.(znz_0W).
 Definition w7_0W := w7_op.(znz_0W).
 Definition w8_0W := w8_op.(znz_0W).
 Definition w9_0W := w9_op.(znz_0W).
 Definition w10_0W := w10_op.(znz_0W).
 Definition w11_0W := w11_op.(znz_0W).
 Definition w12_0W := w12_op.(znz_0W).
 Definition w13_0W := w13_op.(znz_0W).

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
 Definition w7_mul_add_n1 :=
  @gen_mul_add_n1 w7 W0 w7_op.(znz_WW) w7_0W w7_mul_add.
 Definition w8_mul_add_n1 :=
  @gen_mul_add_n1 w8 W0 w8_op.(znz_WW) w8_0W w8_mul_add.
 Definition w9_mul_add_n1 :=
  @gen_mul_add_n1 w9 W0 w9_op.(znz_WW) w9_0W w9_mul_add.
 Definition w10_mul_add_n1 :=
  @gen_mul_add_n1 w10 W0 w10_op.(znz_WW) w10_0W w10_mul_add.
 Definition w11_mul_add_n1 :=
  @gen_mul_add_n1 w11 W0 w11_op.(znz_WW) w11_0W w11_mul_add.
 Definition w12_mul_add_n1 :=
  @gen_mul_add_n1 w12 W0 w12_op.(znz_WW) w12_0W w12_mul_add.
 Definition w13_mul_add_n1 :=
  @gen_mul_add_n1 w13 W0 w13_op.(znz_WW) w13_0W w13_mul_add.

  Let to_Z0 n :=
  match n return word w0 (S n) -> t_ with
  | 0%nat => fun x => N1 x
  | 1%nat => fun x => N2 x
  | 2%nat => fun x => N3 x
  | 3%nat => fun x => N4 x
  | 4%nat => fun x => N5 x
  | 5%nat => fun x => N6 x
  | 6%nat => fun x => N7 x
  | 7%nat => fun x => N8 x
  | 8%nat => fun x => N9 x
  | 9%nat => fun x => N10 x
  | 10%nat => fun x => N11 x
  | 11%nat => fun x => N12 x
  | 12%nat => fun x => N13 x
  | 13%nat => fun x => Nn 0 x
  | 14%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z1 n :=
  match n return word w1 (S n) -> t_ with
  | 0%nat => fun x => N2 x
  | 1%nat => fun x => N3 x
  | 2%nat => fun x => N4 x
  | 3%nat => fun x => N5 x
  | 4%nat => fun x => N6 x
  | 5%nat => fun x => N7 x
  | 6%nat => fun x => N8 x
  | 7%nat => fun x => N9 x
  | 8%nat => fun x => N10 x
  | 9%nat => fun x => N11 x
  | 10%nat => fun x => N12 x
  | 11%nat => fun x => N13 x
  | 12%nat => fun x => Nn 0 x
  | 13%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z2 n :=
  match n return word w2 (S n) -> t_ with
  | 0%nat => fun x => N3 x
  | 1%nat => fun x => N4 x
  | 2%nat => fun x => N5 x
  | 3%nat => fun x => N6 x
  | 4%nat => fun x => N7 x
  | 5%nat => fun x => N8 x
  | 6%nat => fun x => N9 x
  | 7%nat => fun x => N10 x
  | 8%nat => fun x => N11 x
  | 9%nat => fun x => N12 x
  | 10%nat => fun x => N13 x
  | 11%nat => fun x => Nn 0 x
  | 12%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z3 n :=
  match n return word w3 (S n) -> t_ with
  | 0%nat => fun x => N4 x
  | 1%nat => fun x => N5 x
  | 2%nat => fun x => N6 x
  | 3%nat => fun x => N7 x
  | 4%nat => fun x => N8 x
  | 5%nat => fun x => N9 x
  | 6%nat => fun x => N10 x
  | 7%nat => fun x => N11 x
  | 8%nat => fun x => N12 x
  | 9%nat => fun x => N13 x
  | 10%nat => fun x => Nn 0 x
  | 11%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z4 n :=
  match n return word w4 (S n) -> t_ with
  | 0%nat => fun x => N5 x
  | 1%nat => fun x => N6 x
  | 2%nat => fun x => N7 x
  | 3%nat => fun x => N8 x
  | 4%nat => fun x => N9 x
  | 5%nat => fun x => N10 x
  | 6%nat => fun x => N11 x
  | 7%nat => fun x => N12 x
  | 8%nat => fun x => N13 x
  | 9%nat => fun x => Nn 0 x
  | 10%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z5 n :=
  match n return word w5 (S n) -> t_ with
  | 0%nat => fun x => N6 x
  | 1%nat => fun x => N7 x
  | 2%nat => fun x => N8 x
  | 3%nat => fun x => N9 x
  | 4%nat => fun x => N10 x
  | 5%nat => fun x => N11 x
  | 6%nat => fun x => N12 x
  | 7%nat => fun x => N13 x
  | 8%nat => fun x => Nn 0 x
  | 9%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z6 n :=
  match n return word w6 (S n) -> t_ with
  | 0%nat => fun x => N7 x
  | 1%nat => fun x => N8 x
  | 2%nat => fun x => N9 x
  | 3%nat => fun x => N10 x
  | 4%nat => fun x => N11 x
  | 5%nat => fun x => N12 x
  | 6%nat => fun x => N13 x
  | 7%nat => fun x => Nn 0 x
  | 8%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z7 n :=
  match n return word w7 (S n) -> t_ with
  | 0%nat => fun x => N8 x
  | 1%nat => fun x => N9 x
  | 2%nat => fun x => N10 x
  | 3%nat => fun x => N11 x
  | 4%nat => fun x => N12 x
  | 5%nat => fun x => N13 x
  | 6%nat => fun x => Nn 0 x
  | 7%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z8 n :=
  match n return word w8 (S n) -> t_ with
  | 0%nat => fun x => N9 x
  | 1%nat => fun x => N10 x
  | 2%nat => fun x => N11 x
  | 3%nat => fun x => N12 x
  | 4%nat => fun x => N13 x
  | 5%nat => fun x => Nn 0 x
  | 6%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z9 n :=
  match n return word w9 (S n) -> t_ with
  | 0%nat => fun x => N10 x
  | 1%nat => fun x => N11 x
  | 2%nat => fun x => N12 x
  | 3%nat => fun x => N13 x
  | 4%nat => fun x => Nn 0 x
  | 5%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z10 n :=
  match n return word w10 (S n) -> t_ with
  | 0%nat => fun x => N11 x
  | 1%nat => fun x => N12 x
  | 2%nat => fun x => N13 x
  | 3%nat => fun x => Nn 0 x
  | 4%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z11 n :=
  match n return word w11 (S n) -> t_ with
  | 0%nat => fun x => N12 x
  | 1%nat => fun x => N13 x
  | 2%nat => fun x => Nn 0 x
  | 3%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

  Let to_Z12 n :=
  match n return word w12 (S n) -> t_ with
  | 0%nat => fun x => N13 x
  | 1%nat => fun x => Nn 0 x
  | 2%nat => fun x => Nn 1 x
  | _   => fun _ => N0 w_0
  end.

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
 if w6_eq0 w then to_Z6 n r
 else to_Z6 (S n) (WW (extend6 n w) r).

 Definition w7_mul n x y :=
 let (w,r) := w7_mul_add_n1 (S n) x y W0 in
 if w7_eq0 w then to_Z7 n r
 else to_Z7 (S n) (WW (extend7 n w) r).

 Definition w8_mul n x y :=
 let (w,r) := w8_mul_add_n1 (S n) x y W0 in
 if w8_eq0 w then to_Z8 n r
 else to_Z8 (S n) (WW (extend8 n w) r).

 Definition w9_mul n x y :=
 let (w,r) := w9_mul_add_n1 (S n) x y W0 in
 if w9_eq0 w then to_Z9 n r
 else to_Z9 (S n) (WW (extend9 n w) r).

 Definition w10_mul n x y :=
 let (w,r) := w10_mul_add_n1 (S n) x y W0 in
 if w10_eq0 w then to_Z10 n r
 else to_Z10 (S n) (WW (extend10 n w) r).

 Definition w11_mul n x y :=
 let (w,r) := w11_mul_add_n1 (S n) x y W0 in
 if w11_eq0 w then to_Z11 n r
 else to_Z11 (S n) (WW (extend11 n w) r).

 Definition w12_mul n x y :=
 let (w,r) := w12_mul_add_n1 (S n) x y W0 in
 if w12_eq0 w then to_Z12 n r
 else to_Z12 (S n) (WW (extend12 n w) r).

 Definition w13_mul n x y :=
 let (w,r) := w13_mul_add_n1 (S n) x y W0 in
 if w13_eq0 w then Nn n r
 else Nn (S n) (WW (extend13 n w) r).

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
    (fun x y => reduce_8 (w7_mul_c x y)) 
    (fun n x y => w7_mul n y x)
    w7_mul
    (fun x y => reduce_9 (w8_mul_c x y)) 
    (fun n x y => w8_mul n y x)
    w8_mul
    (fun x y => reduce_10 (w9_mul_c x y)) 
    (fun n x y => w9_mul n y x)
    w9_mul
    (fun x y => reduce_11 (w10_mul_c x y)) 
    (fun n x y => w10_mul n y x)
    w10_mul
    (fun x y => reduce_12 (w11_mul_c x y)) 
    (fun n x y => w11_mul n y x)
    w11_mul
    (fun x y => reduce_13 (w12_mul_c x y)) 
    (fun n x y => w12_mul n y x)
    w12_mul
    (fun x y => reduce_14 (w13_mul_c x y)) 
    (fun n x y => w13_mul n y x)
    w13_mul
    mulnm
    (fun _ => N0 w_0)
    (fun _ => N0 w_0)
  ).

  Theorem spec_mul: forall x y, [mul x y] = [x] * [y].
  Admitted.

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
 Definition w7_square_c := w7_op.(znz_square_c).
 Definition w8_square_c := w8_op.(znz_square_c).
 Definition w9_square_c := w9_op.(znz_square_c).
 Definition w10_square_c := w10_op.(znz_square_c).
 Definition w11_square_c := w11_op.(znz_square_c).
 Definition w12_square_c := w12_op.(znz_square_c).
 Definition w13_square_c := w13_op.(znz_square_c).

 Definition square x :=
  match x with
  | N0 wx => reduce_1 (w0_square_c wx)
  | N1 wx => N2 (w1_square_c wx)
  | N2 wx => N3 (w2_square_c wx)
  | N3 wx => N4 (w3_square_c wx)
  | N4 wx => N5 (w4_square_c wx)
  | N5 wx => N6 (w5_square_c wx)
  | N6 wx => N7 (w6_square_c wx)
  | N7 wx => N8 (w7_square_c wx)
  | N8 wx => N9 (w8_square_c wx)
  | N9 wx => N10 (w9_square_c wx)
  | N10 wx => N11 (w10_square_c wx)
  | N11 wx => N12 (w11_square_c wx)
  | N12 wx => N13 (w12_square_c wx)
  | N13 wx => Nn 0 (w13_square_c wx)
  | Nn n wx =>
    let op := make_op n in
    Nn (S n) (op.(znz_square_c) wx)
  end.

 Theorem spec_square: forall x, [square x] = [x] * [x].
Admitted.

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
 Admitted.

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
 Definition w7_sqrt := w7_op.(znz_sqrt).
 Definition w8_sqrt := w8_op.(znz_sqrt).
 Definition w9_sqrt := w9_op.(znz_sqrt).
 Definition w10_sqrt := w10_op.(znz_sqrt).
 Definition w11_sqrt := w11_op.(znz_sqrt).
 Definition w12_sqrt := w12_op.(znz_sqrt).
 Definition w13_sqrt := w13_op.(znz_sqrt).

 Definition sqrt x :=
  match x with
  | N0 wx => reduce_0 (w0_sqrt wx)
  | N1 wx => reduce_1 (w1_sqrt wx)
  | N2 wx => reduce_2 (w2_sqrt wx)
  | N3 wx => reduce_3 (w3_sqrt wx)
  | N4 wx => reduce_4 (w4_sqrt wx)
  | N5 wx => reduce_5 (w5_sqrt wx)
  | N6 wx => reduce_6 (w6_sqrt wx)
  | N7 wx => reduce_7 (w7_sqrt wx)
  | N8 wx => reduce_8 (w8_sqrt wx)
  | N9 wx => reduce_9 (w9_sqrt wx)
  | N10 wx => reduce_10 (w10_sqrt wx)
  | N11 wx => reduce_11 (w11_sqrt wx)
  | N12 wx => reduce_12 (w12_sqrt wx)
  | N13 wx => reduce_13 (w13_sqrt wx)
  | Nn n wx =>
    let op := make_op n in
    reduce_n n (op.(znz_sqrt) wx)
  end.

 Theorem spec_sqrt: forall x, [sqrt x] ^ 2 <= [x] < ([sqrt x] + 1) ^ 2.
Admitted.

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
 Definition w7_div_gt := w7_op.(znz_div_gt).
 Definition w8_div_gt := w8_op.(znz_div_gt).
 Definition w9_div_gt := w9_op.(znz_div_gt).
 Definition w10_div_gt := w10_op.(znz_div_gt).
 Definition w11_div_gt := w11_op.(znz_div_gt).
 Definition w12_div_gt := w12_op.(znz_div_gt).
 Definition w13_div_gt := w13_op.(znz_div_gt).

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
   (to_Z6 _ u, N6 v).
 Definition w7_divn1 n x y :=
  let (u, v) :=
  gen_divn1 w7_op.(znz_zdigits) w7_op.(znz_0)
    w7_op.(znz_WW) w7_op.(znz_head0)
    w7_op.(znz_add_mul_div) w7_op.(znz_div21)
    w7_op.(znz_compare) w7_op.(znz_sub) (S n) x y in
   (to_Z7 _ u, N7 v).
 Definition w8_divn1 n x y :=
  let (u, v) :=
  gen_divn1 w8_op.(znz_zdigits) w8_op.(znz_0)
    w8_op.(znz_WW) w8_op.(znz_head0)
    w8_op.(znz_add_mul_div) w8_op.(znz_div21)
    w8_op.(znz_compare) w8_op.(znz_sub) (S n) x y in
   (to_Z8 _ u, N8 v).
 Definition w9_divn1 n x y :=
  let (u, v) :=
  gen_divn1 w9_op.(znz_zdigits) w9_op.(znz_0)
    w9_op.(znz_WW) w9_op.(znz_head0)
    w9_op.(znz_add_mul_div) w9_op.(znz_div21)
    w9_op.(znz_compare) w9_op.(znz_sub) (S n) x y in
   (to_Z9 _ u, N9 v).
 Definition w10_divn1 n x y :=
  let (u, v) :=
  gen_divn1 w10_op.(znz_zdigits) w10_op.(znz_0)
    w10_op.(znz_WW) w10_op.(znz_head0)
    w10_op.(znz_add_mul_div) w10_op.(znz_div21)
    w10_op.(znz_compare) w10_op.(znz_sub) (S n) x y in
   (to_Z10 _ u, N10 v).
 Definition w11_divn1 n x y :=
  let (u, v) :=
  gen_divn1 w11_op.(znz_zdigits) w11_op.(znz_0)
    w11_op.(znz_WW) w11_op.(znz_head0)
    w11_op.(znz_add_mul_div) w11_op.(znz_div21)
    w11_op.(znz_compare) w11_op.(znz_sub) (S n) x y in
   (to_Z11 _ u, N11 v).
 Definition w12_divn1 n x y :=
  let (u, v) :=
  gen_divn1 w12_op.(znz_zdigits) w12_op.(znz_0)
    w12_op.(znz_WW) w12_op.(znz_head0)
    w12_op.(znz_add_mul_div) w12_op.(znz_div21)
    w12_op.(znz_compare) w12_op.(znz_sub) (S n) x y in
   (to_Z12 _ u, N12 v).
 Definition w13_divn1 n x y :=
  let (u, v) :=
  gen_divn1 w13_op.(znz_zdigits) w13_op.(znz_0)
    w13_op.(znz_WW) w13_op.(znz_head0)
    w13_op.(znz_add_mul_div) w13_op.(znz_div21)
    w13_op.(znz_compare) w13_op.(znz_sub) (S n) x y in
   (Nn _ u, N13 v).

 Let div_gt0 x y := let (u,v) := (w0_div_gt x y) in (reduce_0 u, reduce_0 v).
 Let div_gt1 x y := let (u,v) := (w1_div_gt x y) in (reduce_1 u, reduce_1 v).
 Let div_gt2 x y := let (u,v) := (w2_div_gt x y) in (reduce_2 u, reduce_2 v).
 Let div_gt3 x y := let (u,v) := (w3_div_gt x y) in (reduce_3 u, reduce_3 v).
 Let div_gt4 x y := let (u,v) := (w4_div_gt x y) in (reduce_4 u, reduce_4 v).
 Let div_gt5 x y := let (u,v) := (w5_div_gt x y) in (reduce_5 u, reduce_5 v).
 Let div_gt6 x y := let (u,v) := (w6_div_gt x y) in (reduce_6 u, reduce_6 v).
 Let div_gt7 x y := let (u,v) := (w7_div_gt x y) in (reduce_7 u, reduce_7 v).
 Let div_gt8 x y := let (u,v) := (w8_div_gt x y) in (reduce_8 u, reduce_8 v).
 Let div_gt9 x y := let (u,v) := (w9_div_gt x y) in (reduce_9 u, reduce_9 v).
 Let div_gt10 x y := let (u,v) := (w10_div_gt x y) in (reduce_10 u, reduce_10 v).
 Let div_gt11 x y := let (u,v) := (w11_div_gt x y) in (reduce_11 u, reduce_11 v).
 Let div_gt12 x y := let (u,v) := (w12_div_gt x y) in (reduce_12 u, reduce_12 v).
 Let div_gt13 x y := let (u,v) := (w13_div_gt x y) in (reduce_13 u, reduce_13 v).

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
      div_gt7
      (fun n x y => div_gt7 x (GenBase.get_low W0 (S n) y))
      w7_divn1
      div_gt8
      (fun n x y => div_gt8 x (GenBase.get_low W0 (S n) y))
      w8_divn1
      div_gt9
      (fun n x y => div_gt9 x (GenBase.get_low W0 (S n) y))
      w9_divn1
      div_gt10
      (fun n x y => div_gt10 x (GenBase.get_low W0 (S n) y))
      w10_divn1
      div_gt11
      (fun n x y => div_gt11 x (GenBase.get_low W0 (S n) y))
      w11_divn1
      div_gt12
      (fun n x y => div_gt12 x (GenBase.get_low W0 (S n) y))
      w12_divn1
      div_gt13
      (fun n x y => div_gt13 x (GenBase.get_low W0 (S n) y))
      w13_divn1
      div_gtnm).

 Theorem spec_div_gt: forall x y,
       [x] > [y] -> 0 < [y] ->
      let (q,r) := div_gt x y in
      [q] = [x] / [y] /\ [r] = [x] mod [y].
  Admitted.

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
 Admitted.

 Definition div x y := fst (div_eucl x y).

 Theorem spec_div:
   forall x y, 0 < [y] -> [div x y] = [x] / [y].
 Admitted.

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
 Definition w7_mod_gt := w7_op.(znz_mod_gt).
 Definition w8_mod_gt := w8_op.(znz_mod_gt).
 Definition w9_mod_gt := w9_op.(znz_mod_gt).
 Definition w10_mod_gt := w10_op.(znz_mod_gt).
 Definition w11_mod_gt := w11_op.(znz_mod_gt).
 Definition w12_mod_gt := w12_op.(znz_mod_gt).
 Definition w13_mod_gt := w13_op.(znz_mod_gt).

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
 Definition w7_modn1 :=
  gen_modn1 w7_op.(znz_zdigits) w7_op.(znz_0)
    w7_op.(znz_head0) w7_op.(znz_add_mul_div) w7_op.(znz_div21)
    w7_op.(znz_compare) w7_op.(znz_sub).
 Definition w8_modn1 :=
  gen_modn1 w8_op.(znz_zdigits) w8_op.(znz_0)
    w8_op.(znz_head0) w8_op.(znz_add_mul_div) w8_op.(znz_div21)
    w8_op.(znz_compare) w8_op.(znz_sub).
 Definition w9_modn1 :=
  gen_modn1 w9_op.(znz_zdigits) w9_op.(znz_0)
    w9_op.(znz_head0) w9_op.(znz_add_mul_div) w9_op.(znz_div21)
    w9_op.(znz_compare) w9_op.(znz_sub).
 Definition w10_modn1 :=
  gen_modn1 w10_op.(znz_zdigits) w10_op.(znz_0)
    w10_op.(znz_head0) w10_op.(znz_add_mul_div) w10_op.(znz_div21)
    w10_op.(znz_compare) w10_op.(znz_sub).
 Definition w11_modn1 :=
  gen_modn1 w11_op.(znz_zdigits) w11_op.(znz_0)
    w11_op.(znz_head0) w11_op.(znz_add_mul_div) w11_op.(znz_div21)
    w11_op.(znz_compare) w11_op.(znz_sub).
 Definition w12_modn1 :=
  gen_modn1 w12_op.(znz_zdigits) w12_op.(znz_0)
    w12_op.(znz_head0) w12_op.(znz_add_mul_div) w12_op.(znz_div21)
    w12_op.(znz_compare) w12_op.(znz_sub).
 Definition w13_modn1 :=
  gen_modn1 w13_op.(znz_zdigits) w13_op.(znz_0)
    w13_op.(znz_head0) w13_op.(znz_add_mul_div) w13_op.(znz_div21)
    w13_op.(znz_compare) w13_op.(znz_sub).

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
      (fun x y => reduce_7 (w7_mod_gt x y))
      (fun n x y => reduce_7 (w7_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_7 (w7_modn1 (S n) x y))
      (fun x y => reduce_8 (w8_mod_gt x y))
      (fun n x y => reduce_8 (w8_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_8 (w8_modn1 (S n) x y))
      (fun x y => reduce_9 (w9_mod_gt x y))
      (fun n x y => reduce_9 (w9_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_9 (w9_modn1 (S n) x y))
      (fun x y => reduce_10 (w10_mod_gt x y))
      (fun n x y => reduce_10 (w10_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_10 (w10_modn1 (S n) x y))
      (fun x y => reduce_11 (w11_mod_gt x y))
      (fun n x y => reduce_11 (w11_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_11 (w11_modn1 (S n) x y))
      (fun x y => reduce_12 (w12_mod_gt x y))
      (fun n x y => reduce_12 (w12_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_12 (w12_modn1 (S n) x y))
      (fun x y => reduce_13 (w13_mod_gt x y))
      (fun n x y => reduce_13 (w13_mod_gt x (GenBase.get_low W0 (S n) y)))
      (fun n x y => reduce_13 (w13_modn1 (S n) x y))
      mod_gtnm).

 Theorem spec_mod_gt:
   forall x y, [x] > [y] -> 0 < [y] -> [mod_gt x y] = [x] mod [y].
 Admitted.

 Definition modulo x y := 
  match compare x y with
  | Eq => zero
  | Lt => x
  | Gt => mod_gt x y
  end.

 Theorem spec_modulo:
   forall x y, 0 < [y] -> [modulo x y] = [x] mod [y].
 Admitted.

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
  | N7 _ => w7_op.(znz_digits)
  | N8 _ => w8_op.(znz_digits)
  | N9 _ => w9_op.(znz_digits)
  | N10 _ => w10_op.(znz_digits)
  | N11 _ => w11_op.(znz_digits)
  | N12 _ => w12_op.(znz_digits)
  | N13 _ => w13_op.(znz_digits)
  | Nn n _ => (make_op n).(znz_digits)
  end.

 Theorem spec_digits: forall x, 0 <= [x] < 2 ^  Zpos (digits x).
 Admitted.

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

 Fixpoint gcd_gt_aux (p:positive) (cont:t->t->t) (a b:t) {struct p} : t :=
  gcd_gt_body a b
    (fun a b =>
       match p with
       | xH => cont a b
       | xO p => gcd_gt_aux p (gcd_gt_aux p cont) a b
       | xI p => gcd_gt_aux p (gcd_gt_aux p cont) a b
       end).

 Definition gcd_cont a b :=
  match compare one b with
  | Eq => one
  | _ => a
  end.

 Definition gcd_gt a b := gcd_gt_aux (digits a) gcd_cont a b.

 Theorem spec_gcd_gt: forall a b,
   [a] > [b] -> [gcd_gt a b] = Zgcd [a] [b].
 Admitted.

 Definition gcd a b :=
  match compare a b with
  | Eq => a
  | Lt => gcd_gt b a
  | Gt => gcd_gt a b
  end.

 Theorem spec_gcd: forall a b, [gcd a b] = Zgcd [a] [b].
 Admitted.

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
  | 7%nat => reduce_7 (snd (w7_op.(znz_of_pos) x))
  | 8%nat => reduce_8 (snd (w8_op.(znz_of_pos) x))
  | 9%nat => reduce_9 (snd (w9_op.(znz_of_pos) x))
  | 10%nat => reduce_10 (snd (w10_op.(znz_of_pos) x))
  | 11%nat => reduce_11 (snd (w11_op.(znz_of_pos) x))
  | 12%nat => reduce_12 (snd (w12_op.(znz_of_pos) x))
  | 13%nat => reduce_13 (snd (w13_op.(znz_of_pos) x))
  | _ =>
    let n := minus h 14 in
    reduce_n n (snd ((make_op n).(znz_of_pos) x))
  end.

 Theorem spec_of_pos: forall x,
   [of_pos x] = Zpos x.
  Admitted.

 Definition of_N x :=
  match x with
  | BinNat.N0 => zero
  | Npos p => of_pos p
  end.

 Theorem spec_of_N: forall x,
   [of_N x] = Z_of_N x.
  Admitted.

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
 | N7 w=> reduce_7 (w7_op.(znz_head0) w)
 | N8 w=> reduce_8 (w8_op.(znz_head0) w)
 | N9 w=> reduce_9 (w9_op.(znz_head0) w)
 | N10 w=> reduce_10 (w10_op.(znz_head0) w)
 | N11 w=> reduce_11 (w11_op.(znz_head0) w)
 | N12 w=> reduce_12 (w12_op.(znz_head0) w)
 | N13 w=> reduce_13 (w13_op.(znz_head0) w)
 | Nn n w=> reduce_n n ((make_op n).(znz_head0) w)
 end.

 Theorem spec_head00: forall x, [x] = 0 ->[head0 x] = Zpos (digits x).
 Admitted.
  
 Theorem spec_head0: forall x, 0 < [x] ->
   2 ^ (Zpos (digits x) - 1) <= 2 ^ [head0 x] * [x] < 2 ^ Zpos (digits x).
 Admitted.

 Definition tail0 w := match w with
 | N0 w=> reduce_0 (w0_op.(znz_tail0) w)
 | N1 w=> reduce_1 (w1_op.(znz_tail0) w)
 | N2 w=> reduce_2 (w2_op.(znz_tail0) w)
 | N3 w=> reduce_3 (w3_op.(znz_tail0) w)
 | N4 w=> reduce_4 (w4_op.(znz_tail0) w)
 | N5 w=> reduce_5 (w5_op.(znz_tail0) w)
 | N6 w=> reduce_6 (w6_op.(znz_tail0) w)
 | N7 w=> reduce_7 (w7_op.(znz_tail0) w)
 | N8 w=> reduce_8 (w8_op.(znz_tail0) w)
 | N9 w=> reduce_9 (w9_op.(znz_tail0) w)
 | N10 w=> reduce_10 (w10_op.(znz_tail0) w)
 | N11 w=> reduce_11 (w11_op.(znz_tail0) w)
 | N12 w=> reduce_12 (w12_op.(znz_tail0) w)
 | N13 w=> reduce_13 (w13_op.(znz_tail0) w)
 | Nn n w=> reduce_n n ((make_op n).(znz_tail0) w)
 end.

 Theorem spec_tail00: forall x, [x] = 0 ->[tail0 x] = Zpos (digits x).
 Admitted.
  
 Theorem spec_tail0: forall x,
   0 < [x] -> exists y, 0 <= y /\ [x] = (2 * y + 1) * 2 ^ [tail0 x].
 Admitted.

 Definition Ndigits x :=
  match x with
  | N0 _ => N0 w0_op.(znz_zdigits)
  | N1 _ => reduce_1 w1_op.(znz_zdigits)
  | N2 _ => reduce_2 w2_op.(znz_zdigits)
  | N3 _ => reduce_3 w3_op.(znz_zdigits)
  | N4 _ => reduce_4 w4_op.(znz_zdigits)
  | N5 _ => reduce_5 w5_op.(znz_zdigits)
  | N6 _ => reduce_6 w6_op.(znz_zdigits)
  | N7 _ => reduce_7 w7_op.(znz_zdigits)
  | N8 _ => reduce_8 w8_op.(znz_zdigits)
  | N9 _ => reduce_9 w9_op.(znz_zdigits)
  | N10 _ => reduce_10 w10_op.(znz_zdigits)
  | N11 _ => reduce_11 w11_op.(znz_zdigits)
  | N12 _ => reduce_12 w12_op.(znz_zdigits)
  | N13 _ => reduce_13 w13_op.(znz_zdigits)
  | Nn n _ => reduce_n n (make_op n).(znz_zdigits)
  end.

 Theorem spec_Ndigits: forall x, [Ndigits x] = Zpos (digits x).
 Admitted.

 Definition shiftr0 n x := w0_op.(znz_add_mul_div) (w0_op.(znz_sub) w0_op.(znz_zdigits) n) w0_op.(znz_0) x.
 Definition shiftr1 n x := w1_op.(znz_add_mul_div) (w1_op.(znz_sub) w1_op.(znz_zdigits) n) w1_op.(znz_0) x.
 Definition shiftr2 n x := w2_op.(znz_add_mul_div) (w2_op.(znz_sub) w2_op.(znz_zdigits) n) w2_op.(znz_0) x.
 Definition shiftr3 n x := w3_op.(znz_add_mul_div) (w3_op.(znz_sub) w3_op.(znz_zdigits) n) w3_op.(znz_0) x.
 Definition shiftr4 n x := w4_op.(znz_add_mul_div) (w4_op.(znz_sub) w4_op.(znz_zdigits) n) w4_op.(znz_0) x.
 Definition shiftr5 n x := w5_op.(znz_add_mul_div) (w5_op.(znz_sub) w5_op.(znz_zdigits) n) w5_op.(znz_0) x.
 Definition shiftr6 n x := w6_op.(znz_add_mul_div) (w6_op.(znz_sub) w6_op.(znz_zdigits) n) w6_op.(znz_0) x.
 Definition shiftr7 n x := w7_op.(znz_add_mul_div) (w7_op.(znz_sub) w7_op.(znz_zdigits) n) w7_op.(znz_0) x.
 Definition shiftr8 n x := w8_op.(znz_add_mul_div) (w8_op.(znz_sub) w8_op.(znz_zdigits) n) w8_op.(znz_0) x.
 Definition shiftr9 n x := w9_op.(znz_add_mul_div) (w9_op.(znz_sub) w9_op.(znz_zdigits) n) w9_op.(znz_0) x.
 Definition shiftr10 n x := w10_op.(znz_add_mul_div) (w10_op.(znz_sub) w10_op.(znz_zdigits) n) w10_op.(znz_0) x.
 Definition shiftr11 n x := w11_op.(znz_add_mul_div) (w11_op.(znz_sub) w11_op.(znz_zdigits) n) w11_op.(znz_0) x.
 Definition shiftr12 n x := w12_op.(znz_add_mul_div) (w12_op.(znz_sub) w12_op.(znz_zdigits) n) w12_op.(znz_0) x.
 Definition shiftr13 n x := w13_op.(znz_add_mul_div) (w13_op.(znz_sub) w13_op.(znz_zdigits) n) w13_op.(znz_0) x.
 Definition shiftrn n p x := (make_op n).(znz_add_mul_div) ((make_op n).(znz_sub) (make_op n).(znz_zdigits) p) (make_op n).(znz_0) x.

 Definition shiftr := Eval lazy beta delta [same_level] in 
     same_level _ (fun n x => N0 (shiftr0 n x))
           (fun n x => reduce_1 (shiftr1 n x))
           (fun n x => reduce_2 (shiftr2 n x))
           (fun n x => reduce_3 (shiftr3 n x))
           (fun n x => reduce_4 (shiftr4 n x))
           (fun n x => reduce_5 (shiftr5 n x))
           (fun n x => reduce_6 (shiftr6 n x))
           (fun n x => reduce_7 (shiftr7 n x))
           (fun n x => reduce_8 (shiftr8 n x))
           (fun n x => reduce_9 (shiftr9 n x))
           (fun n x => reduce_10 (shiftr10 n x))
           (fun n x => reduce_11 (shiftr11 n x))
           (fun n x => reduce_12 (shiftr12 n x))
           (fun n x => reduce_13 (shiftr13 n x))
           (fun n p x => reduce_n n (shiftrn n p x)).

 Theorem spec_shiftr: forall n x,
  [n] <= [Ndigits x] -> [shiftr n x] = [x] / 2 ^ [n].
 Admitted.

 Definition safe_shiftr n x := 
   match compare n (Ndigits x) with
    |  Lt => shiftr n x 
   | _ => N0 w_0
   end.

 Theorem spec_safe_shiftr: forall n x,
   [safe_shiftr n x] = [x] / 2 ^ [n].
 Admitted.


 Definition shiftl0 n x := w0_op.(znz_add_mul_div) n x w0_op.(znz_0).
 Definition shiftl1 n x := w1_op.(znz_add_mul_div) n x w1_op.(znz_0).
 Definition shiftl2 n x := w2_op.(znz_add_mul_div) n x w2_op.(znz_0).
 Definition shiftl3 n x := w3_op.(znz_add_mul_div) n x w3_op.(znz_0).
 Definition shiftl4 n x := w4_op.(znz_add_mul_div) n x w4_op.(znz_0).
 Definition shiftl5 n x := w5_op.(znz_add_mul_div) n x w5_op.(znz_0).
 Definition shiftl6 n x := w6_op.(znz_add_mul_div) n x w6_op.(znz_0).
 Definition shiftl7 n x := w7_op.(znz_add_mul_div) n x w7_op.(znz_0).
 Definition shiftl8 n x := w8_op.(znz_add_mul_div) n x w8_op.(znz_0).
 Definition shiftl9 n x := w9_op.(znz_add_mul_div) n x w9_op.(znz_0).
 Definition shiftl10 n x := w10_op.(znz_add_mul_div) n x w10_op.(znz_0).
 Definition shiftl11 n x := w11_op.(znz_add_mul_div) n x w11_op.(znz_0).
 Definition shiftl12 n x := w12_op.(znz_add_mul_div) n x w12_op.(znz_0).
 Definition shiftl13 n x := w13_op.(znz_add_mul_div) n x w13_op.(znz_0).
 Definition shiftln n p x := (make_op n).(znz_add_mul_div) p x (make_op n).(znz_0).
 Definition shiftl := Eval lazy beta delta [same_level] in
    same_level _ (fun n x => N0 (shiftl0 n x))
           (fun n x => reduce_1 (shiftl1 n x))
           (fun n x => reduce_2 (shiftl2 n x))
           (fun n x => reduce_3 (shiftl3 n x))
           (fun n x => reduce_4 (shiftl4 n x))
           (fun n x => reduce_5 (shiftl5 n x))
           (fun n x => reduce_6 (shiftl6 n x))
           (fun n x => reduce_7 (shiftl7 n x))
           (fun n x => reduce_8 (shiftl8 n x))
           (fun n x => reduce_9 (shiftl9 n x))
           (fun n x => reduce_10 (shiftl10 n x))
           (fun n x => reduce_11 (shiftl11 n x))
           (fun n x => reduce_12 (shiftl12 n x))
           (fun n x => reduce_13 (shiftl13 n x))
           (fun n p x => reduce_n n (shiftln n p x)).


 Theorem spec_shiftl: forall n x,
  [n] <= [head0 x] -> [shiftl n x] = [x] * 2 ^ [n].
 Admitted.

 Definition double_size w := match w with
 | N0 x => N1 (WW (znz_0 w0_op) x)
 | N1 x => N2 (WW (znz_0 w1_op) x)
 | N2 x => N3 (WW (znz_0 w2_op) x)
 | N3 x => N4 (WW (znz_0 w3_op) x)
 | N4 x => N5 (WW (znz_0 w4_op) x)
 | N5 x => N6 (WW (znz_0 w5_op) x)
 | N6 x => N7 (WW (znz_0 w6_op) x)
 | N7 x => N8 (WW (znz_0 w7_op) x)
 | N8 x => N9 (WW (znz_0 w8_op) x)
 | N9 x => N10 (WW (znz_0 w9_op) x)
 | N10 x => N11 (WW (znz_0 w10_op) x)
 | N11 x => N12 (WW (znz_0 w11_op) x)
 | N12 x => N13 (WW (znz_0 w12_op) x)
 | N13 x => Nn 0 (WW (znz_0 w13_op) x)
 | Nn n x => Nn (S n) (WW (znz_0 (make_op n)) x)
 end.

 Theorem spec_double_size_digits: 
   forall x, digits (double_size x) = xO (digits x).
 Admitted.

 Theorem spec_double_size: forall x, [double_size x] = [x].
 Admitted.

 Theorem spec_double_size_head0: 
   forall x, 2 * [head0 x] <= [head0 (double_size x)].
 Admitted.

 Theorem spec_double_size_head0_pos: 
   forall x, 0 < [head0 (double_size x)].
 Admitted.

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
 Admitted.

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
 Admitted.

 Definition safe_shiftl n x :=
  safe_shiftl_aux_body
   (safe_shiftl_aux_body
    (safe_shiftl_aux (digits n) shiftl)) n x.

 Theorem spec_safe_shift: forall n x,
   [safe_shiftl n x] = [x] * 2 ^ [n].
 Admitted.

 Definition is_even x :=
  match x with
  | N0 wx => w0_op.(znz_is_even) wx
  | N1 wx => w1_op.(znz_is_even) wx
  | N2 wx => w2_op.(znz_is_even) wx
  | N3 wx => w3_op.(znz_is_even) wx
  | N4 wx => w4_op.(znz_is_even) wx
  | N5 wx => w5_op.(znz_is_even) wx
  | N6 wx => w6_op.(znz_is_even) wx
  | N7 wx => w7_op.(znz_is_even) wx
  | N8 wx => w8_op.(znz_is_even) wx
  | N9 wx => w9_op.(znz_is_even) wx
  | N10 wx => w10_op.(znz_is_even) wx
  | N11 wx => w11_op.(znz_is_even) wx
  | N12 wx => w12_op.(znz_is_even) wx
  | N13 wx => w13_op.(znz_is_even) wx
  | Nn n wx => (make_op n).(znz_is_even) wx
  end.

 Theorem spec_is_even: forall x,
   if is_even x then [x] mod 2 = 0 else [x] mod 2 = 1.
 Admitted.

 Theorem spec_0: [zero] = 0.
 Admitted.

 Theorem spec_1: [one] = 1.
 Admitted.

End Make.

