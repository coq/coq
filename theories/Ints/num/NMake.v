Require Import ZArith.
Require Import Basic_type.
Require Import ZnZ.
Require Import Zn2Z.
Require Import Nbasic.
Require Import GenMul.
Require Import GenDivn1.
Require Import Wf_nat.

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

 Definition extend1 :=
  Eval lazy beta zeta iota delta [extend]in extend 1.
 Definition extend2 :=
  Eval lazy beta zeta iota delta [extend]in extend 2.
 Definition extend3 :=
  Eval lazy beta zeta iota delta [extend]in extend 3.
 Definition extend4 :=
  Eval lazy beta zeta iota delta [extend]in extend 4.
 Definition extend5 :=
  Eval lazy beta zeta iota delta [extend]in extend 5.
 Definition extend6 :=
  Eval lazy beta zeta iota delta [extend]in extend 6.
 Definition extend7 :=
  Eval lazy beta zeta iota delta [extend]in extend 7.
 Definition extend8 :=
  Eval lazy beta zeta iota delta [extend]in extend 8.
 Definition extend9 :=
  Eval lazy beta zeta iota delta [extend]in extend 9.
 Definition extend10 :=
  Eval lazy beta zeta iota delta [extend]in extend 10.
 Definition extend11 :=
  Eval lazy beta zeta iota delta [extend]in extend 11.
 Definition extend12 :=
  Eval lazy beta zeta iota delta [extend]in extend 12.
 Definition extend13 :=
  Eval lazy beta zeta iota delta [extend]in extend 13.

 Definition w0_eq0 := w0_op.(znz_eq0).
 Definition w1_eq0 := w1_op.(znz_eq0).
 Definition w2_eq0 := w2_op.(znz_eq0).
 Definition w3_eq0 := w3_op.(znz_eq0).
 Definition w4_eq0 := w4_op.(znz_eq0).
 Definition w5_eq0 := w5_op.(znz_eq0).
 Definition w6_eq0 := w6_op.(znz_eq0).
 Definition w7_eq0 := w7_op.(znz_eq0).
 Definition w8_eq0 := w8_op.(znz_eq0).
 Definition w9_eq0 := w9_op.(znz_eq0).
 Definition w10_eq0 := w10_op.(znz_eq0).
 Definition w11_eq0 := w11_op.(znz_eq0).
 Definition w12_eq0 := w12_op.(znz_eq0).
 Definition w13_eq0 := w13_op.(znz_eq0).

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

 Definition w0_WW := w0_op.(znz_WW).

 Definition w0_add_c := w0_op.(znz_add_c).
 Definition w1_add_c := w1_op.(znz_add_c).
 Definition w2_add_c := w2_op.(znz_add_c).
 Definition w3_add_c := w3_op.(znz_add_c).
 Definition w4_add_c := w4_op.(znz_add_c).
 Definition w5_add_c := w5_op.(znz_add_c).
 Definition w6_add_c := w6_op.(znz_add_c).
 Definition w7_add_c := w7_op.(znz_add_c).
 Definition w8_add_c := w8_op.(znz_add_c).
 Definition w9_add_c := w9_op.(znz_add_c).
 Definition w10_add_c := w10_op.(znz_add_c).
 Definition w11_add_c := w11_op.(znz_add_c).
 Definition w12_add_c := w12_op.(znz_add_c).
 Definition w13_add_c := w13_op.(znz_add_c).

 Definition w0_add x y :=
  match w0_add_c x y with
  | C0 r => N0 r
  | C1 r => N1 (WW one0 r)
  end.
 Definition w1_add x y :=
  match w1_add_c x y with
  | C0 r => N1 r
  | C1 r => N2 (WW one1 r)
  end.
 Definition w2_add x y :=
  match w2_add_c x y with
  | C0 r => N2 r
  | C1 r => N3 (WW one2 r)
  end.
 Definition w3_add x y :=
  match w3_add_c x y with
  | C0 r => N3 r
  | C1 r => N4 (WW one3 r)
  end.
 Definition w4_add x y :=
  match w4_add_c x y with
  | C0 r => N4 r
  | C1 r => N5 (WW one4 r)
  end.
 Definition w5_add x y :=
  match w5_add_c x y with
  | C0 r => N5 r
  | C1 r => N6 (WW one5 r)
  end.
 Definition w6_add x y :=
  match w6_add_c x y with
  | C0 r => N6 r
  | C1 r => N7 (WW one6 r)
  end.
 Definition w7_add x y :=
  match w7_add_c x y with
  | C0 r => N7 r
  | C1 r => N8 (WW one7 r)
  end.
 Definition w8_add x y :=
  match w8_add_c x y with
  | C0 r => N8 r
  | C1 r => N9 (WW one8 r)
  end.
 Definition w9_add x y :=
  match w9_add_c x y with
  | C0 r => N9 r
  | C1 r => N10 (WW one9 r)
  end.
 Definition w10_add x y :=
  match w10_add_c x y with
  | C0 r => N10 r
  | C1 r => N11 (WW one10 r)
  end.
 Definition w11_add x y :=
  match w11_add_c x y with
  | C0 r => N11 r
  | C1 r => N12 (WW one11 r)
  end.
 Definition w12_add x y :=
  match w12_add_c x y with
  | C0 r => N12 r
  | C1 r => N13 (WW one12 r)
  end.
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

 Definition add x y :=
  match x, y with
  | N0 wx, N0 wy => w0_add wx wy 
  | N0 wx, N1 wy =>
    if w0_eq0 wx then y else w1_add (WW w_0 wx) wy
  | N0 wx, N2 wy =>
    if w0_eq0 wx then y else w2_add (extend1 w0 (WW w_0 wx)) wy
  | N0 wx, N3 wy =>
    if w0_eq0 wx then y else w3_add (extend2 w0 (WW w_0 wx)) wy
  | N0 wx, N4 wy =>
    if w0_eq0 wx then y else w4_add (extend3 w0 (WW w_0 wx)) wy
  | N0 wx, N5 wy =>
    if w0_eq0 wx then y else w5_add (extend4 w0 (WW w_0 wx)) wy
  | N0 wx, N6 wy =>
    if w0_eq0 wx then y else w6_add (extend5 w0 (WW w_0 wx)) wy
  | N0 wx, N7 wy =>
    if w0_eq0 wx then y else w7_add (extend6 w0 (WW w_0 wx)) wy
  | N0 wx, N8 wy =>
    if w0_eq0 wx then y else w8_add (extend7 w0 (WW w_0 wx)) wy
  | N0 wx, N9 wy =>
    if w0_eq0 wx then y else w9_add (extend8 w0 (WW w_0 wx)) wy
  | N0 wx, N10 wy =>
    if w0_eq0 wx then y else w10_add (extend9 w0 (WW w_0 wx)) wy
  | N0 wx, N11 wy =>
    if w0_eq0 wx then y else w11_add (extend10 w0 (WW w_0 wx)) wy
  | N0 wx, N12 wy =>
    if w0_eq0 wx then y else w12_add (extend11 w0 (WW w_0 wx)) wy
  | N0 wx, N13 wy =>
    if w0_eq0 wx then y else w13_add (extend12 w0 (WW w_0 wx)) wy
  | N0 wx, Nn n wy =>
    if w0_eq0 wx then y
    else addn n (extend n w13 (extend13 w0 (WW w_0 wx))) wy
  | N1 wx, N0 wy =>
    if w0_eq0 wy then x else w1_add wx (WW w_0 wy)
  | N1 wx, N1 wy => w1_add wx wy
  | N1 wx, N2 wy => w2_add (extend1 w0 wx) wy
  | N1 wx, N3 wy => w3_add (extend2 w0 wx) wy
  | N1 wx, N4 wy => w4_add (extend3 w0 wx) wy
  | N1 wx, N5 wy => w5_add (extend4 w0 wx) wy
  | N1 wx, N6 wy => w6_add (extend5 w0 wx) wy
  | N1 wx, N7 wy => w7_add (extend6 w0 wx) wy
  | N1 wx, N8 wy => w8_add (extend7 w0 wx) wy
  | N1 wx, N9 wy => w9_add (extend8 w0 wx) wy
  | N1 wx, N10 wy => w10_add (extend9 w0 wx) wy
  | N1 wx, N11 wy => w11_add (extend10 w0 wx) wy
  | N1 wx, N12 wy => w12_add (extend11 w0 wx) wy
  | N1 wx, N13 wy => w13_add (extend12 w0 wx) wy
  | N1 wx, Nn n wy => addn n (extend n w13 (extend13 w0 wx)) wy
  | N2 wx, N0 wy =>
    if w0_eq0 wy then x else w2_add wx (extend1 w0 (WW w_0 wy))
  | N2 wx, N1 wy => w2_add wx (extend1 w0 wy)
  | N2 wx, N2 wy => w2_add wx wy
  | N2 wx, N3 wy => w3_add (extend1 w1 wx) wy
  | N2 wx, N4 wy => w4_add (extend2 w1 wx) wy
  | N2 wx, N5 wy => w5_add (extend3 w1 wx) wy
  | N2 wx, N6 wy => w6_add (extend4 w1 wx) wy
  | N2 wx, N7 wy => w7_add (extend5 w1 wx) wy
  | N2 wx, N8 wy => w8_add (extend6 w1 wx) wy
  | N2 wx, N9 wy => w9_add (extend7 w1 wx) wy
  | N2 wx, N10 wy => w10_add (extend8 w1 wx) wy
  | N2 wx, N11 wy => w11_add (extend9 w1 wx) wy
  | N2 wx, N12 wy => w12_add (extend10 w1 wx) wy
  | N2 wx, N13 wy => w13_add (extend11 w1 wx) wy
  | N2 wx, Nn n wy => addn n (extend n w13 (extend12 w1 wx)) wy
  | N3 wx, N0 wy =>
    if w0_eq0 wy then x else w3_add wx (extend2 w0 (WW w_0 wy))
  | N3 wx, N1 wy => w3_add wx (extend2 w0 wy)
  | N3 wx, N2 wy => w3_add wx (extend1 w1 wy)
  | N3 wx, N3 wy => w3_add wx wy
  | N3 wx, N4 wy => w4_add (extend1 w2 wx) wy
  | N3 wx, N5 wy => w5_add (extend2 w2 wx) wy
  | N3 wx, N6 wy => w6_add (extend3 w2 wx) wy
  | N3 wx, N7 wy => w7_add (extend4 w2 wx) wy
  | N3 wx, N8 wy => w8_add (extend5 w2 wx) wy
  | N3 wx, N9 wy => w9_add (extend6 w2 wx) wy
  | N3 wx, N10 wy => w10_add (extend7 w2 wx) wy
  | N3 wx, N11 wy => w11_add (extend8 w2 wx) wy
  | N3 wx, N12 wy => w12_add (extend9 w2 wx) wy
  | N3 wx, N13 wy => w13_add (extend10 w2 wx) wy
  | N3 wx, Nn n wy => addn n (extend n w13 (extend11 w2 wx)) wy
  | N4 wx, N0 wy =>
    if w0_eq0 wy then x else w4_add wx (extend3 w0 (WW w_0 wy))
  | N4 wx, N1 wy => w4_add wx (extend3 w0 wy)
  | N4 wx, N2 wy => w4_add wx (extend2 w1 wy)
  | N4 wx, N3 wy => w4_add wx (extend1 w2 wy)
  | N4 wx, N4 wy => w4_add wx wy
  | N4 wx, N5 wy => w5_add (extend1 w3 wx) wy
  | N4 wx, N6 wy => w6_add (extend2 w3 wx) wy
  | N4 wx, N7 wy => w7_add (extend3 w3 wx) wy
  | N4 wx, N8 wy => w8_add (extend4 w3 wx) wy
  | N4 wx, N9 wy => w9_add (extend5 w3 wx) wy
  | N4 wx, N10 wy => w10_add (extend6 w3 wx) wy
  | N4 wx, N11 wy => w11_add (extend7 w3 wx) wy
  | N4 wx, N12 wy => w12_add (extend8 w3 wx) wy
  | N4 wx, N13 wy => w13_add (extend9 w3 wx) wy
  | N4 wx, Nn n wy => addn n (extend n w13 (extend10 w3 wx)) wy
  | N5 wx, N0 wy =>
    if w0_eq0 wy then x else w5_add wx (extend4 w0 (WW w_0 wy))
  | N5 wx, N1 wy => w5_add wx (extend4 w0 wy)
  | N5 wx, N2 wy => w5_add wx (extend3 w1 wy)
  | N5 wx, N3 wy => w5_add wx (extend2 w2 wy)
  | N5 wx, N4 wy => w5_add wx (extend1 w3 wy)
  | N5 wx, N5 wy => w5_add wx wy
  | N5 wx, N6 wy => w6_add (extend1 w4 wx) wy
  | N5 wx, N7 wy => w7_add (extend2 w4 wx) wy
  | N5 wx, N8 wy => w8_add (extend3 w4 wx) wy
  | N5 wx, N9 wy => w9_add (extend4 w4 wx) wy
  | N5 wx, N10 wy => w10_add (extend5 w4 wx) wy
  | N5 wx, N11 wy => w11_add (extend6 w4 wx) wy
  | N5 wx, N12 wy => w12_add (extend7 w4 wx) wy
  | N5 wx, N13 wy => w13_add (extend8 w4 wx) wy
  | N5 wx, Nn n wy => addn n (extend n w13 (extend9 w4 wx)) wy
  | N6 wx, N0 wy =>
    if w0_eq0 wy then x else w6_add wx (extend5 w0 (WW w_0 wy))
  | N6 wx, N1 wy => w6_add wx (extend5 w0 wy)
  | N6 wx, N2 wy => w6_add wx (extend4 w1 wy)
  | N6 wx, N3 wy => w6_add wx (extend3 w2 wy)
  | N6 wx, N4 wy => w6_add wx (extend2 w3 wy)
  | N6 wx, N5 wy => w6_add wx (extend1 w4 wy)
  | N6 wx, N6 wy => w6_add wx wy
  | N6 wx, N7 wy => w7_add (extend1 w5 wx) wy
  | N6 wx, N8 wy => w8_add (extend2 w5 wx) wy
  | N6 wx, N9 wy => w9_add (extend3 w5 wx) wy
  | N6 wx, N10 wy => w10_add (extend4 w5 wx) wy
  | N6 wx, N11 wy => w11_add (extend5 w5 wx) wy
  | N6 wx, N12 wy => w12_add (extend6 w5 wx) wy
  | N6 wx, N13 wy => w13_add (extend7 w5 wx) wy
  | N6 wx, Nn n wy => addn n (extend n w13 (extend8 w5 wx)) wy
  | N7 wx, N0 wy =>
    if w0_eq0 wy then x else w7_add wx (extend6 w0 (WW w_0 wy))
  | N7 wx, N1 wy => w7_add wx (extend6 w0 wy)
  | N7 wx, N2 wy => w7_add wx (extend5 w1 wy)
  | N7 wx, N3 wy => w7_add wx (extend4 w2 wy)
  | N7 wx, N4 wy => w7_add wx (extend3 w3 wy)
  | N7 wx, N5 wy => w7_add wx (extend2 w4 wy)
  | N7 wx, N6 wy => w7_add wx (extend1 w5 wy)
  | N7 wx, N7 wy => w7_add wx wy
  | N7 wx, N8 wy => w8_add (extend1 w6 wx) wy
  | N7 wx, N9 wy => w9_add (extend2 w6 wx) wy
  | N7 wx, N10 wy => w10_add (extend3 w6 wx) wy
  | N7 wx, N11 wy => w11_add (extend4 w6 wx) wy
  | N7 wx, N12 wy => w12_add (extend5 w6 wx) wy
  | N7 wx, N13 wy => w13_add (extend6 w6 wx) wy
  | N7 wx, Nn n wy => addn n (extend n w13 (extend7 w6 wx)) wy
  | N8 wx, N0 wy =>
    if w0_eq0 wy then x else w8_add wx (extend7 w0 (WW w_0 wy))
  | N8 wx, N1 wy => w8_add wx (extend7 w0 wy)
  | N8 wx, N2 wy => w8_add wx (extend6 w1 wy)
  | N8 wx, N3 wy => w8_add wx (extend5 w2 wy)
  | N8 wx, N4 wy => w8_add wx (extend4 w3 wy)
  | N8 wx, N5 wy => w8_add wx (extend3 w4 wy)
  | N8 wx, N6 wy => w8_add wx (extend2 w5 wy)
  | N8 wx, N7 wy => w8_add wx (extend1 w6 wy)
  | N8 wx, N8 wy => w8_add wx wy
  | N8 wx, N9 wy => w9_add (extend1 w7 wx) wy
  | N8 wx, N10 wy => w10_add (extend2 w7 wx) wy
  | N8 wx, N11 wy => w11_add (extend3 w7 wx) wy
  | N8 wx, N12 wy => w12_add (extend4 w7 wx) wy
  | N8 wx, N13 wy => w13_add (extend5 w7 wx) wy
  | N8 wx, Nn n wy => addn n (extend n w13 (extend6 w7 wx)) wy
  | N9 wx, N0 wy =>
    if w0_eq0 wy then x else w9_add wx (extend8 w0 (WW w_0 wy))
  | N9 wx, N1 wy => w9_add wx (extend8 w0 wy)
  | N9 wx, N2 wy => w9_add wx (extend7 w1 wy)
  | N9 wx, N3 wy => w9_add wx (extend6 w2 wy)
  | N9 wx, N4 wy => w9_add wx (extend5 w3 wy)
  | N9 wx, N5 wy => w9_add wx (extend4 w4 wy)
  | N9 wx, N6 wy => w9_add wx (extend3 w5 wy)
  | N9 wx, N7 wy => w9_add wx (extend2 w6 wy)
  | N9 wx, N8 wy => w9_add wx (extend1 w7 wy)
  | N9 wx, N9 wy => w9_add wx wy
  | N9 wx, N10 wy => w10_add (extend1 w8 wx) wy
  | N9 wx, N11 wy => w11_add (extend2 w8 wx) wy
  | N9 wx, N12 wy => w12_add (extend3 w8 wx) wy
  | N9 wx, N13 wy => w13_add (extend4 w8 wx) wy
  | N9 wx, Nn n wy => addn n (extend n w13 (extend5 w8 wx)) wy
  | N10 wx, N0 wy =>
    if w0_eq0 wy then x else w10_add wx (extend9 w0 (WW w_0 wy))
  | N10 wx, N1 wy => w10_add wx (extend9 w0 wy)
  | N10 wx, N2 wy => w10_add wx (extend8 w1 wy)
  | N10 wx, N3 wy => w10_add wx (extend7 w2 wy)
  | N10 wx, N4 wy => w10_add wx (extend6 w3 wy)
  | N10 wx, N5 wy => w10_add wx (extend5 w4 wy)
  | N10 wx, N6 wy => w10_add wx (extend4 w5 wy)
  | N10 wx, N7 wy => w10_add wx (extend3 w6 wy)
  | N10 wx, N8 wy => w10_add wx (extend2 w7 wy)
  | N10 wx, N9 wy => w10_add wx (extend1 w8 wy)
  | N10 wx, N10 wy => w10_add wx wy
  | N10 wx, N11 wy => w11_add (extend1 w9 wx) wy
  | N10 wx, N12 wy => w12_add (extend2 w9 wx) wy
  | N10 wx, N13 wy => w13_add (extend3 w9 wx) wy
  | N10 wx, Nn n wy => addn n (extend n w13 (extend4 w9 wx)) wy
  | N11 wx, N0 wy =>
    if w0_eq0 wy then x else w11_add wx (extend10 w0 (WW w_0 wy))
  | N11 wx, N1 wy => w11_add wx (extend10 w0 wy)
  | N11 wx, N2 wy => w11_add wx (extend9 w1 wy)
  | N11 wx, N3 wy => w11_add wx (extend8 w2 wy)
  | N11 wx, N4 wy => w11_add wx (extend7 w3 wy)
  | N11 wx, N5 wy => w11_add wx (extend6 w4 wy)
  | N11 wx, N6 wy => w11_add wx (extend5 w5 wy)
  | N11 wx, N7 wy => w11_add wx (extend4 w6 wy)
  | N11 wx, N8 wy => w11_add wx (extend3 w7 wy)
  | N11 wx, N9 wy => w11_add wx (extend2 w8 wy)
  | N11 wx, N10 wy => w11_add wx (extend1 w9 wy)
  | N11 wx, N11 wy => w11_add wx wy
  | N11 wx, N12 wy => w12_add (extend1 w10 wx) wy
  | N11 wx, N13 wy => w13_add (extend2 w10 wx) wy
  | N11 wx, Nn n wy => addn n (extend n w13 (extend3 w10 wx)) wy
  | N12 wx, N0 wy =>
    if w0_eq0 wy then x else w12_add wx (extend11 w0 (WW w_0 wy))
  | N12 wx, N1 wy => w12_add wx (extend11 w0 wy)
  | N12 wx, N2 wy => w12_add wx (extend10 w1 wy)
  | N12 wx, N3 wy => w12_add wx (extend9 w2 wy)
  | N12 wx, N4 wy => w12_add wx (extend8 w3 wy)
  | N12 wx, N5 wy => w12_add wx (extend7 w4 wy)
  | N12 wx, N6 wy => w12_add wx (extend6 w5 wy)
  | N12 wx, N7 wy => w12_add wx (extend5 w6 wy)
  | N12 wx, N8 wy => w12_add wx (extend4 w7 wy)
  | N12 wx, N9 wy => w12_add wx (extend3 w8 wy)
  | N12 wx, N10 wy => w12_add wx (extend2 w9 wy)
  | N12 wx, N11 wy => w12_add wx (extend1 w10 wy)
  | N12 wx, N12 wy => w12_add wx wy
  | N12 wx, N13 wy => w13_add (extend1 w11 wx) wy
  | N12 wx, Nn n wy => addn n (extend n w13 (extend2 w11 wx)) wy
  | N13 wx, N0 wy =>
    if w0_eq0 wy then x else w13_add wx (extend12 w0 (WW w_0 wy))
  | N13 wx, N1 wy => w13_add wx (extend12 w0 wy)
  | N13 wx, N2 wy => w13_add wx (extend11 w1 wy)
  | N13 wx, N3 wy => w13_add wx (extend10 w2 wy)
  | N13 wx, N4 wy => w13_add wx (extend9 w3 wy)
  | N13 wx, N5 wy => w13_add wx (extend8 w4 wy)
  | N13 wx, N6 wy => w13_add wx (extend7 w5 wy)
  | N13 wx, N7 wy => w13_add wx (extend6 w6 wy)
  | N13 wx, N8 wy => w13_add wx (extend5 w7 wy)
  | N13 wx, N9 wy => w13_add wx (extend4 w8 wy)
  | N13 wx, N10 wy => w13_add wx (extend3 w9 wy)
  | N13 wx, N11 wy => w13_add wx (extend2 w10 wy)
  | N13 wx, N12 wy => w13_add wx (extend1 w11 wy)
  | N13 wx, N13 wy => w13_add wx wy
  | N13 wx, Nn n wy => addn n (extend n w13 (extend1 w12 wx)) wy
  | Nn n wx, N0 wy =>
    if w0_eq0 wy then x
    else addn n wx (extend n w13 (extend13 w0 (WW w_0 wy)))
  | Nn n wx, N1 wy => addn n wx (extend n w13 (extend13 w0 wy))
  | Nn n wx, N2 wy => addn n wx (extend n w13 (extend12 w1 wy))
  | Nn n wx, N3 wy => addn n wx (extend n w13 (extend11 w2 wy))
  | Nn n wx, N4 wy => addn n wx (extend n w13 (extend10 w3 wy))
  | Nn n wx, N5 wy => addn n wx (extend n w13 (extend9 w4 wy))
  | Nn n wx, N6 wy => addn n wx (extend n w13 (extend8 w5 wy))
  | Nn n wx, N7 wy => addn n wx (extend n w13 (extend7 w6 wy))
  | Nn n wx, N8 wy => addn n wx (extend n w13 (extend6 w7 wy))
  | Nn n wx, N9 wy => addn n wx (extend n w13 (extend5 w8 wy))
  | Nn n wx, N10 wy => addn n wx (extend n w13 (extend4 w9 wy))
  | Nn n wx, N11 wy => addn n wx (extend n w13 (extend3 w10 wy))
  | Nn n wx, N12 wy => addn n wx (extend n w13 (extend2 w11 wy))
  | Nn n wx, N13 wy => addn n wx (extend n w13 (extend1 w12 wy))
  | Nn n wx, Nn m wy =>
    let mn := Max.max n m in
    let d := diff n m in
     addn mn
       (castm (diff_r n m) (extend_tr wx (snd d)))
       (castm (diff_l n m) (extend_tr wy (fst d)))
  end.

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

 Definition sub x y :=
  match x, y with
  | N0 wx, N0 wy => w0_sub wx wy 
  | N0 wx, N1 wy =>
    if w0_eq0 wx then zero else w1_sub (WW w_0 wx) wy
  | N0 wx, N2 wy =>
    if w0_eq0 wx then zero else w2_sub (extend1 w0 (WW w_0 wx)) wy
  | N0 wx, N3 wy =>
    if w0_eq0 wx then zero else w3_sub (extend2 w0 (WW w_0 wx)) wy
  | N0 wx, N4 wy =>
    if w0_eq0 wx then zero else w4_sub (extend3 w0 (WW w_0 wx)) wy
  | N0 wx, N5 wy =>
    if w0_eq0 wx then zero else w5_sub (extend4 w0 (WW w_0 wx)) wy
  | N0 wx, N6 wy =>
    if w0_eq0 wx then zero else w6_sub (extend5 w0 (WW w_0 wx)) wy
  | N0 wx, N7 wy =>
    if w0_eq0 wx then zero else w7_sub (extend6 w0 (WW w_0 wx)) wy
  | N0 wx, N8 wy =>
    if w0_eq0 wx then zero else w8_sub (extend7 w0 (WW w_0 wx)) wy
  | N0 wx, N9 wy =>
    if w0_eq0 wx then zero else w9_sub (extend8 w0 (WW w_0 wx)) wy
  | N0 wx, N10 wy =>
    if w0_eq0 wx then zero else w10_sub (extend9 w0 (WW w_0 wx)) wy
  | N0 wx, N11 wy =>
    if w0_eq0 wx then zero else w11_sub (extend10 w0 (WW w_0 wx)) wy
  | N0 wx, N12 wy =>
    if w0_eq0 wx then zero else w12_sub (extend11 w0 (WW w_0 wx)) wy
  | N0 wx, N13 wy =>
    if w0_eq0 wx then zero else w13_sub (extend12 w0 (WW w_0 wx)) wy
  | N0 wx, Nn n wy =>
    if w0_eq0 wx then zero
    else subn n (extend n w13 (extend13 w0 (WW w_0 wx))) wy
  | N1 wx, N0 wy =>
    if w0_eq0 wy then x
    else w1_sub wx (WW w_0 wy)
  | N1 wx, N1 wy => w1_sub wx wy
  | N1 wx, N2 wy => w2_sub (extend1 w0 wx) wy
  | N1 wx, N3 wy => w3_sub (extend2 w0 wx) wy
  | N1 wx, N4 wy => w4_sub (extend3 w0 wx) wy
  | N1 wx, N5 wy => w5_sub (extend4 w0 wx) wy
  | N1 wx, N6 wy => w6_sub (extend5 w0 wx) wy
  | N1 wx, N7 wy => w7_sub (extend6 w0 wx) wy
  | N1 wx, N8 wy => w8_sub (extend7 w0 wx) wy
  | N1 wx, N9 wy => w9_sub (extend8 w0 wx) wy
  | N1 wx, N10 wy => w10_sub (extend9 w0 wx) wy
  | N1 wx, N11 wy => w11_sub (extend10 w0 wx) wy
  | N1 wx, N12 wy => w12_sub (extend11 w0 wx) wy
  | N1 wx, N13 wy => w13_sub (extend12 w0 wx) wy
  | N1 wx, Nn n wy => subn n (extend n w13 (extend13 w0 wx)) wy
  | N2 wx, N0 wy =>
    if w0_eq0 wy then x
    else w2_sub wx (extend1 w0 (WW w_0 wy))
  | N2 wx, N1 wy => w2_sub wx (extend1 w0 wy)
  | N2 wx, N2 wy => w2_sub wx wy
  | N2 wx, N3 wy => w3_sub (extend1 w1 wx) wy
  | N2 wx, N4 wy => w4_sub (extend2 w1 wx) wy
  | N2 wx, N5 wy => w5_sub (extend3 w1 wx) wy
  | N2 wx, N6 wy => w6_sub (extend4 w1 wx) wy
  | N2 wx, N7 wy => w7_sub (extend5 w1 wx) wy
  | N2 wx, N8 wy => w8_sub (extend6 w1 wx) wy
  | N2 wx, N9 wy => w9_sub (extend7 w1 wx) wy
  | N2 wx, N10 wy => w10_sub (extend8 w1 wx) wy
  | N2 wx, N11 wy => w11_sub (extend9 w1 wx) wy
  | N2 wx, N12 wy => w12_sub (extend10 w1 wx) wy
  | N2 wx, N13 wy => w13_sub (extend11 w1 wx) wy
  | N2 wx, Nn n wy => subn n (extend n w13 (extend12 w1 wx)) wy
  | N3 wx, N0 wy =>
    if w0_eq0 wy then x
    else w3_sub wx (extend2 w0 (WW w_0 wy))
  | N3 wx, N1 wy => w3_sub wx (extend2 w0 wy)
  | N3 wx, N2 wy => w3_sub wx (extend1 w1 wy)
  | N3 wx, N3 wy => w3_sub wx wy
  | N3 wx, N4 wy => w4_sub (extend1 w2 wx) wy
  | N3 wx, N5 wy => w5_sub (extend2 w2 wx) wy
  | N3 wx, N6 wy => w6_sub (extend3 w2 wx) wy
  | N3 wx, N7 wy => w7_sub (extend4 w2 wx) wy
  | N3 wx, N8 wy => w8_sub (extend5 w2 wx) wy
  | N3 wx, N9 wy => w9_sub (extend6 w2 wx) wy
  | N3 wx, N10 wy => w10_sub (extend7 w2 wx) wy
  | N3 wx, N11 wy => w11_sub (extend8 w2 wx) wy
  | N3 wx, N12 wy => w12_sub (extend9 w2 wx) wy
  | N3 wx, N13 wy => w13_sub (extend10 w2 wx) wy
  | N3 wx, Nn n wy => subn n (extend n w13 (extend11 w2 wx)) wy
  | N4 wx, N0 wy =>
    if w0_eq0 wy then x
    else w4_sub wx (extend3 w0 (WW w_0 wy))
  | N4 wx, N1 wy => w4_sub wx (extend3 w0 wy)
  | N4 wx, N2 wy => w4_sub wx (extend2 w1 wy)
  | N4 wx, N3 wy => w4_sub wx (extend1 w2 wy)
  | N4 wx, N4 wy => w4_sub wx wy
  | N4 wx, N5 wy => w5_sub (extend1 w3 wx) wy
  | N4 wx, N6 wy => w6_sub (extend2 w3 wx) wy
  | N4 wx, N7 wy => w7_sub (extend3 w3 wx) wy
  | N4 wx, N8 wy => w8_sub (extend4 w3 wx) wy
  | N4 wx, N9 wy => w9_sub (extend5 w3 wx) wy
  | N4 wx, N10 wy => w10_sub (extend6 w3 wx) wy
  | N4 wx, N11 wy => w11_sub (extend7 w3 wx) wy
  | N4 wx, N12 wy => w12_sub (extend8 w3 wx) wy
  | N4 wx, N13 wy => w13_sub (extend9 w3 wx) wy
  | N4 wx, Nn n wy => subn n (extend n w13 (extend10 w3 wx)) wy
  | N5 wx, N0 wy =>
    if w0_eq0 wy then x
    else w5_sub wx (extend4 w0 (WW w_0 wy))
  | N5 wx, N1 wy => w5_sub wx (extend4 w0 wy)
  | N5 wx, N2 wy => w5_sub wx (extend3 w1 wy)
  | N5 wx, N3 wy => w5_sub wx (extend2 w2 wy)
  | N5 wx, N4 wy => w5_sub wx (extend1 w3 wy)
  | N5 wx, N5 wy => w5_sub wx wy
  | N5 wx, N6 wy => w6_sub (extend1 w4 wx) wy
  | N5 wx, N7 wy => w7_sub (extend2 w4 wx) wy
  | N5 wx, N8 wy => w8_sub (extend3 w4 wx) wy
  | N5 wx, N9 wy => w9_sub (extend4 w4 wx) wy
  | N5 wx, N10 wy => w10_sub (extend5 w4 wx) wy
  | N5 wx, N11 wy => w11_sub (extend6 w4 wx) wy
  | N5 wx, N12 wy => w12_sub (extend7 w4 wx) wy
  | N5 wx, N13 wy => w13_sub (extend8 w4 wx) wy
  | N5 wx, Nn n wy => subn n (extend n w13 (extend9 w4 wx)) wy
  | N6 wx, N0 wy =>
    if w0_eq0 wy then x
    else w6_sub wx (extend5 w0 (WW w_0 wy))
  | N6 wx, N1 wy => w6_sub wx (extend5 w0 wy)
  | N6 wx, N2 wy => w6_sub wx (extend4 w1 wy)
  | N6 wx, N3 wy => w6_sub wx (extend3 w2 wy)
  | N6 wx, N4 wy => w6_sub wx (extend2 w3 wy)
  | N6 wx, N5 wy => w6_sub wx (extend1 w4 wy)
  | N6 wx, N6 wy => w6_sub wx wy
  | N6 wx, N7 wy => w7_sub (extend1 w5 wx) wy
  | N6 wx, N8 wy => w8_sub (extend2 w5 wx) wy
  | N6 wx, N9 wy => w9_sub (extend3 w5 wx) wy
  | N6 wx, N10 wy => w10_sub (extend4 w5 wx) wy
  | N6 wx, N11 wy => w11_sub (extend5 w5 wx) wy
  | N6 wx, N12 wy => w12_sub (extend6 w5 wx) wy
  | N6 wx, N13 wy => w13_sub (extend7 w5 wx) wy
  | N6 wx, Nn n wy => subn n (extend n w13 (extend8 w5 wx)) wy
  | N7 wx, N0 wy =>
    if w0_eq0 wy then x
    else w7_sub wx (extend6 w0 (WW w_0 wy))
  | N7 wx, N1 wy => w7_sub wx (extend6 w0 wy)
  | N7 wx, N2 wy => w7_sub wx (extend5 w1 wy)
  | N7 wx, N3 wy => w7_sub wx (extend4 w2 wy)
  | N7 wx, N4 wy => w7_sub wx (extend3 w3 wy)
  | N7 wx, N5 wy => w7_sub wx (extend2 w4 wy)
  | N7 wx, N6 wy => w7_sub wx (extend1 w5 wy)
  | N7 wx, N7 wy => w7_sub wx wy
  | N7 wx, N8 wy => w8_sub (extend1 w6 wx) wy
  | N7 wx, N9 wy => w9_sub (extend2 w6 wx) wy
  | N7 wx, N10 wy => w10_sub (extend3 w6 wx) wy
  | N7 wx, N11 wy => w11_sub (extend4 w6 wx) wy
  | N7 wx, N12 wy => w12_sub (extend5 w6 wx) wy
  | N7 wx, N13 wy => w13_sub (extend6 w6 wx) wy
  | N7 wx, Nn n wy => subn n (extend n w13 (extend7 w6 wx)) wy
  | N8 wx, N0 wy =>
    if w0_eq0 wy then x
    else w8_sub wx (extend7 w0 (WW w_0 wy))
  | N8 wx, N1 wy => w8_sub wx (extend7 w0 wy)
  | N8 wx, N2 wy => w8_sub wx (extend6 w1 wy)
  | N8 wx, N3 wy => w8_sub wx (extend5 w2 wy)
  | N8 wx, N4 wy => w8_sub wx (extend4 w3 wy)
  | N8 wx, N5 wy => w8_sub wx (extend3 w4 wy)
  | N8 wx, N6 wy => w8_sub wx (extend2 w5 wy)
  | N8 wx, N7 wy => w8_sub wx (extend1 w6 wy)
  | N8 wx, N8 wy => w8_sub wx wy
  | N8 wx, N9 wy => w9_sub (extend1 w7 wx) wy
  | N8 wx, N10 wy => w10_sub (extend2 w7 wx) wy
  | N8 wx, N11 wy => w11_sub (extend3 w7 wx) wy
  | N8 wx, N12 wy => w12_sub (extend4 w7 wx) wy
  | N8 wx, N13 wy => w13_sub (extend5 w7 wx) wy
  | N8 wx, Nn n wy => subn n (extend n w13 (extend6 w7 wx)) wy
  | N9 wx, N0 wy =>
    if w0_eq0 wy then x
    else w9_sub wx (extend8 w0 (WW w_0 wy))
  | N9 wx, N1 wy => w9_sub wx (extend8 w0 wy)
  | N9 wx, N2 wy => w9_sub wx (extend7 w1 wy)
  | N9 wx, N3 wy => w9_sub wx (extend6 w2 wy)
  | N9 wx, N4 wy => w9_sub wx (extend5 w3 wy)
  | N9 wx, N5 wy => w9_sub wx (extend4 w4 wy)
  | N9 wx, N6 wy => w9_sub wx (extend3 w5 wy)
  | N9 wx, N7 wy => w9_sub wx (extend2 w6 wy)
  | N9 wx, N8 wy => w9_sub wx (extend1 w7 wy)
  | N9 wx, N9 wy => w9_sub wx wy
  | N9 wx, N10 wy => w10_sub (extend1 w8 wx) wy
  | N9 wx, N11 wy => w11_sub (extend2 w8 wx) wy
  | N9 wx, N12 wy => w12_sub (extend3 w8 wx) wy
  | N9 wx, N13 wy => w13_sub (extend4 w8 wx) wy
  | N9 wx, Nn n wy => subn n (extend n w13 (extend5 w8 wx)) wy
  | N10 wx, N0 wy =>
    if w0_eq0 wy then x
    else w10_sub wx (extend9 w0 (WW w_0 wy))
  | N10 wx, N1 wy => w10_sub wx (extend9 w0 wy)
  | N10 wx, N2 wy => w10_sub wx (extend8 w1 wy)
  | N10 wx, N3 wy => w10_sub wx (extend7 w2 wy)
  | N10 wx, N4 wy => w10_sub wx (extend6 w3 wy)
  | N10 wx, N5 wy => w10_sub wx (extend5 w4 wy)
  | N10 wx, N6 wy => w10_sub wx (extend4 w5 wy)
  | N10 wx, N7 wy => w10_sub wx (extend3 w6 wy)
  | N10 wx, N8 wy => w10_sub wx (extend2 w7 wy)
  | N10 wx, N9 wy => w10_sub wx (extend1 w8 wy)
  | N10 wx, N10 wy => w10_sub wx wy
  | N10 wx, N11 wy => w11_sub (extend1 w9 wx) wy
  | N10 wx, N12 wy => w12_sub (extend2 w9 wx) wy
  | N10 wx, N13 wy => w13_sub (extend3 w9 wx) wy
  | N10 wx, Nn n wy => subn n (extend n w13 (extend4 w9 wx)) wy
  | N11 wx, N0 wy =>
    if w0_eq0 wy then x
    else w11_sub wx (extend10 w0 (WW w_0 wy))
  | N11 wx, N1 wy => w11_sub wx (extend10 w0 wy)
  | N11 wx, N2 wy => w11_sub wx (extend9 w1 wy)
  | N11 wx, N3 wy => w11_sub wx (extend8 w2 wy)
  | N11 wx, N4 wy => w11_sub wx (extend7 w3 wy)
  | N11 wx, N5 wy => w11_sub wx (extend6 w4 wy)
  | N11 wx, N6 wy => w11_sub wx (extend5 w5 wy)
  | N11 wx, N7 wy => w11_sub wx (extend4 w6 wy)
  | N11 wx, N8 wy => w11_sub wx (extend3 w7 wy)
  | N11 wx, N9 wy => w11_sub wx (extend2 w8 wy)
  | N11 wx, N10 wy => w11_sub wx (extend1 w9 wy)
  | N11 wx, N11 wy => w11_sub wx wy
  | N11 wx, N12 wy => w12_sub (extend1 w10 wx) wy
  | N11 wx, N13 wy => w13_sub (extend2 w10 wx) wy
  | N11 wx, Nn n wy => subn n (extend n w13 (extend3 w10 wx)) wy
  | N12 wx, N0 wy =>
    if w0_eq0 wy then x
    else w12_sub wx (extend11 w0 (WW w_0 wy))
  | N12 wx, N1 wy => w12_sub wx (extend11 w0 wy)
  | N12 wx, N2 wy => w12_sub wx (extend10 w1 wy)
  | N12 wx, N3 wy => w12_sub wx (extend9 w2 wy)
  | N12 wx, N4 wy => w12_sub wx (extend8 w3 wy)
  | N12 wx, N5 wy => w12_sub wx (extend7 w4 wy)
  | N12 wx, N6 wy => w12_sub wx (extend6 w5 wy)
  | N12 wx, N7 wy => w12_sub wx (extend5 w6 wy)
  | N12 wx, N8 wy => w12_sub wx (extend4 w7 wy)
  | N12 wx, N9 wy => w12_sub wx (extend3 w8 wy)
  | N12 wx, N10 wy => w12_sub wx (extend2 w9 wy)
  | N12 wx, N11 wy => w12_sub wx (extend1 w10 wy)
  | N12 wx, N12 wy => w12_sub wx wy
  | N12 wx, N13 wy => w13_sub (extend1 w11 wx) wy
  | N12 wx, Nn n wy => subn n (extend n w13 (extend2 w11 wx)) wy
  | N13 wx, N0 wy =>
    if w0_eq0 wy then x
    else w13_sub wx (extend12 w0 (WW w_0 wy))
  | N13 wx, N1 wy => w13_sub wx (extend12 w0 wy)
  | N13 wx, N2 wy => w13_sub wx (extend11 w1 wy)
  | N13 wx, N3 wy => w13_sub wx (extend10 w2 wy)
  | N13 wx, N4 wy => w13_sub wx (extend9 w3 wy)
  | N13 wx, N5 wy => w13_sub wx (extend8 w4 wy)
  | N13 wx, N6 wy => w13_sub wx (extend7 w5 wy)
  | N13 wx, N7 wy => w13_sub wx (extend6 w6 wy)
  | N13 wx, N8 wy => w13_sub wx (extend5 w7 wy)
  | N13 wx, N9 wy => w13_sub wx (extend4 w8 wy)
  | N13 wx, N10 wy => w13_sub wx (extend3 w9 wy)
  | N13 wx, N11 wy => w13_sub wx (extend2 w10 wy)
  | N13 wx, N12 wy => w13_sub wx (extend1 w11 wy)
  | N13 wx, N13 wy => w13_sub wx wy
  | N13 wx, Nn n wy => subn n (extend n w13 (extend1 w12 wx)) wy
  | Nn n wx, N0 wy =>
    if w0_eq0 wy then x
    else subn n wx (extend n w13 (extend13 w0 (WW w_0 wy)))
  | Nn n wx, N1 wy => subn n wx (extend n w13 (extend13 w0 wy))
  | Nn n wx, N2 wy => subn n wx (extend n w13 (extend12 w1 wy))
  | Nn n wx, N3 wy => subn n wx (extend n w13 (extend11 w2 wy))
  | Nn n wx, N4 wy => subn n wx (extend n w13 (extend10 w3 wy))
  | Nn n wx, N5 wy => subn n wx (extend n w13 (extend9 w4 wy))
  | Nn n wx, N6 wy => subn n wx (extend n w13 (extend8 w5 wy))
  | Nn n wx, N7 wy => subn n wx (extend n w13 (extend7 w6 wy))
  | Nn n wx, N8 wy => subn n wx (extend n w13 (extend6 w7 wy))
  | Nn n wx, N9 wy => subn n wx (extend n w13 (extend5 w8 wy))
  | Nn n wx, N10 wy => subn n wx (extend n w13 (extend4 w9 wy))
  | Nn n wx, N11 wy => subn n wx (extend n w13 (extend3 w10 wy))
  | Nn n wx, N12 wy => subn n wx (extend n w13 (extend2 w11 wy))
  | Nn n wx, N13 wy => subn n wx (extend n w13 (extend1 w12 wy))
  | Nn n wx, Nn m wy =>
    let mn := Max.max n m in
    let d := diff n m in
     subn mn
       (castm (diff_r n m) (extend_tr wx (snd d)))
       (castm (diff_l n m) (extend_tr wy (fst d)))
  end.

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

 Definition compare x y :=
  match x, y with
  | N0 wx, N0 wy => compare_0 wx wy
  | N0 wx, N1 wy => opp_compare (comparen_0 1 wy wx)
  | N0 wx, N2 wy => opp_compare (comparen_0 2 wy wx)
  | N0 wx, N3 wy => opp_compare (comparen_0 3 wy wx)
  | N0 wx, N4 wy => opp_compare (comparen_0 4 wy wx)
  | N0 wx, N5 wy => opp_compare (comparen_0 5 wy wx)
  | N0 wx, N6 wy => opp_compare (comparen_0 6 wy wx)
  | N0 wx, N7 wy => opp_compare (comparen_0 7 wy wx)
  | N0 wx, N8 wy => opp_compare (comparen_0 8 wy wx)
  | N0 wx, N9 wy => opp_compare (comparen_0 9 wy wx)
  | N0 wx, N10 wy => opp_compare (comparen_0 10 wy wx)
  | N0 wx, N11 wy => opp_compare (comparen_0 11 wy wx)
  | N0 wx, N12 wy => opp_compare (comparen_0 12 wy wx)
  | N0 wx, N13 wy => opp_compare (comparen_0 13 wy wx)
  | N0 wx, Nn n wy =>
    opp_compare (compare_mn_1 w13 w0 w_0 compare_0 (compare_13 W0) (comparen_0 13) (S n) wy wx)
  | N1 wx, N0 wy => comparen_0 1 wx wy
  | N1 wx, N1 wy => compare_1 wx wy
  | N1 wx, N2 wy => opp_compare (comparen_1 1 wy wx)
  | N1 wx, N3 wy => opp_compare (comparen_1 2 wy wx)
  | N1 wx, N4 wy => opp_compare (comparen_1 3 wy wx)
  | N1 wx, N5 wy => opp_compare (comparen_1 4 wy wx)
  | N1 wx, N6 wy => opp_compare (comparen_1 5 wy wx)
  | N1 wx, N7 wy => opp_compare (comparen_1 6 wy wx)
  | N1 wx, N8 wy => opp_compare (comparen_1 7 wy wx)
  | N1 wx, N9 wy => opp_compare (comparen_1 8 wy wx)
  | N1 wx, N10 wy => opp_compare (comparen_1 9 wy wx)
  | N1 wx, N11 wy => opp_compare (comparen_1 10 wy wx)
  | N1 wx, N12 wy => opp_compare (comparen_1 11 wy wx)
  | N1 wx, N13 wy => opp_compare (comparen_1 12 wy wx)
  | N1 wx, Nn n wy =>
    opp_compare (compare_mn_1 w13 w1 W0 compare_1 (compare_13 W0) (comparen_1 12) (S n) wy wx)
  | N2 wx, N0 wy => comparen_0 2 wx wy
  | N2 wx, N1 wy => comparen_1 1 wx wy
  | N2 wx, N2 wy => compare_2 wx wy
  | N2 wx, N3 wy => opp_compare (comparen_2 1 wy wx)
  | N2 wx, N4 wy => opp_compare (comparen_2 2 wy wx)
  | N2 wx, N5 wy => opp_compare (comparen_2 3 wy wx)
  | N2 wx, N6 wy => opp_compare (comparen_2 4 wy wx)
  | N2 wx, N7 wy => opp_compare (comparen_2 5 wy wx)
  | N2 wx, N8 wy => opp_compare (comparen_2 6 wy wx)
  | N2 wx, N9 wy => opp_compare (comparen_2 7 wy wx)
  | N2 wx, N10 wy => opp_compare (comparen_2 8 wy wx)
  | N2 wx, N11 wy => opp_compare (comparen_2 9 wy wx)
  | N2 wx, N12 wy => opp_compare (comparen_2 10 wy wx)
  | N2 wx, N13 wy => opp_compare (comparen_2 11 wy wx)
  | N2 wx, Nn n wy =>
    opp_compare (compare_mn_1 w13 w2 W0 compare_2 (compare_13 W0) (comparen_2 11) (S n) wy wx)
  | N3 wx, N0 wy => comparen_0 3 wx wy
  | N3 wx, N1 wy => comparen_1 2 wx wy
  | N3 wx, N2 wy => comparen_2 1 wx wy
  | N3 wx, N3 wy => compare_3 wx wy
  | N3 wx, N4 wy => opp_compare (comparen_3 1 wy wx)
  | N3 wx, N5 wy => opp_compare (comparen_3 2 wy wx)
  | N3 wx, N6 wy => opp_compare (comparen_3 3 wy wx)
  | N3 wx, N7 wy => opp_compare (comparen_3 4 wy wx)
  | N3 wx, N8 wy => opp_compare (comparen_3 5 wy wx)
  | N3 wx, N9 wy => opp_compare (comparen_3 6 wy wx)
  | N3 wx, N10 wy => opp_compare (comparen_3 7 wy wx)
  | N3 wx, N11 wy => opp_compare (comparen_3 8 wy wx)
  | N3 wx, N12 wy => opp_compare (comparen_3 9 wy wx)
  | N3 wx, N13 wy => opp_compare (comparen_3 10 wy wx)
  | N3 wx, Nn n wy =>
    opp_compare (compare_mn_1 w13 w3 W0 compare_3 (compare_13 W0) (comparen_3 10) (S n) wy wx)
  | N4 wx, N0 wy => comparen_0 4 wx wy
  | N4 wx, N1 wy => comparen_1 3 wx wy
  | N4 wx, N2 wy => comparen_2 2 wx wy
  | N4 wx, N3 wy => comparen_3 1 wx wy
  | N4 wx, N4 wy => compare_4 wx wy
  | N4 wx, N5 wy => opp_compare (comparen_4 1 wy wx)
  | N4 wx, N6 wy => opp_compare (comparen_4 2 wy wx)
  | N4 wx, N7 wy => opp_compare (comparen_4 3 wy wx)
  | N4 wx, N8 wy => opp_compare (comparen_4 4 wy wx)
  | N4 wx, N9 wy => opp_compare (comparen_4 5 wy wx)
  | N4 wx, N10 wy => opp_compare (comparen_4 6 wy wx)
  | N4 wx, N11 wy => opp_compare (comparen_4 7 wy wx)
  | N4 wx, N12 wy => opp_compare (comparen_4 8 wy wx)
  | N4 wx, N13 wy => opp_compare (comparen_4 9 wy wx)
  | N4 wx, Nn n wy =>
    opp_compare (compare_mn_1 w13 w4 W0 compare_4 (compare_13 W0) (comparen_4 9) (S n) wy wx)
  | N5 wx, N0 wy => comparen_0 5 wx wy
  | N5 wx, N1 wy => comparen_1 4 wx wy
  | N5 wx, N2 wy => comparen_2 3 wx wy
  | N5 wx, N3 wy => comparen_3 2 wx wy
  | N5 wx, N4 wy => comparen_4 1 wx wy
  | N5 wx, N5 wy => compare_5 wx wy
  | N5 wx, N6 wy => opp_compare (comparen_5 1 wy wx)
  | N5 wx, N7 wy => opp_compare (comparen_5 2 wy wx)
  | N5 wx, N8 wy => opp_compare (comparen_5 3 wy wx)
  | N5 wx, N9 wy => opp_compare (comparen_5 4 wy wx)
  | N5 wx, N10 wy => opp_compare (comparen_5 5 wy wx)
  | N5 wx, N11 wy => opp_compare (comparen_5 6 wy wx)
  | N5 wx, N12 wy => opp_compare (comparen_5 7 wy wx)
  | N5 wx, N13 wy => opp_compare (comparen_5 8 wy wx)
  | N5 wx, Nn n wy =>
    opp_compare (compare_mn_1 w13 w5 W0 compare_5 (compare_13 W0) (comparen_5 8) (S n) wy wx)
  | N6 wx, N0 wy => comparen_0 6 wx wy
  | N6 wx, N1 wy => comparen_1 5 wx wy
  | N6 wx, N2 wy => comparen_2 4 wx wy
  | N6 wx, N3 wy => comparen_3 3 wx wy
  | N6 wx, N4 wy => comparen_4 2 wx wy
  | N6 wx, N5 wy => comparen_5 1 wx wy
  | N6 wx, N6 wy => compare_6 wx wy
  | N6 wx, N7 wy => opp_compare (comparen_6 1 wy wx)
  | N6 wx, N8 wy => opp_compare (comparen_6 2 wy wx)
  | N6 wx, N9 wy => opp_compare (comparen_6 3 wy wx)
  | N6 wx, N10 wy => opp_compare (comparen_6 4 wy wx)
  | N6 wx, N11 wy => opp_compare (comparen_6 5 wy wx)
  | N6 wx, N12 wy => opp_compare (comparen_6 6 wy wx)
  | N6 wx, N13 wy => opp_compare (comparen_6 7 wy wx)
  | N6 wx, Nn n wy =>
    opp_compare (compare_mn_1 w13 w6 W0 compare_6 (compare_13 W0) (comparen_6 7) (S n) wy wx)
  | N7 wx, N0 wy => comparen_0 7 wx wy
  | N7 wx, N1 wy => comparen_1 6 wx wy
  | N7 wx, N2 wy => comparen_2 5 wx wy
  | N7 wx, N3 wy => comparen_3 4 wx wy
  | N7 wx, N4 wy => comparen_4 3 wx wy
  | N7 wx, N5 wy => comparen_5 2 wx wy
  | N7 wx, N6 wy => comparen_6 1 wx wy
  | N7 wx, N7 wy => compare_7 wx wy
  | N7 wx, N8 wy => opp_compare (comparen_7 1 wy wx)
  | N7 wx, N9 wy => opp_compare (comparen_7 2 wy wx)
  | N7 wx, N10 wy => opp_compare (comparen_7 3 wy wx)
  | N7 wx, N11 wy => opp_compare (comparen_7 4 wy wx)
  | N7 wx, N12 wy => opp_compare (comparen_7 5 wy wx)
  | N7 wx, N13 wy => opp_compare (comparen_7 6 wy wx)
  | N7 wx, Nn n wy =>
    opp_compare (compare_mn_1 w13 w7 W0 compare_7 (compare_13 W0) (comparen_7 6) (S n) wy wx)
  | N8 wx, N0 wy => comparen_0 8 wx wy
  | N8 wx, N1 wy => comparen_1 7 wx wy
  | N8 wx, N2 wy => comparen_2 6 wx wy
  | N8 wx, N3 wy => comparen_3 5 wx wy
  | N8 wx, N4 wy => comparen_4 4 wx wy
  | N8 wx, N5 wy => comparen_5 3 wx wy
  | N8 wx, N6 wy => comparen_6 2 wx wy
  | N8 wx, N7 wy => comparen_7 1 wx wy
  | N8 wx, N8 wy => compare_8 wx wy
  | N8 wx, N9 wy => opp_compare (comparen_8 1 wy wx)
  | N8 wx, N10 wy => opp_compare (comparen_8 2 wy wx)
  | N8 wx, N11 wy => opp_compare (comparen_8 3 wy wx)
  | N8 wx, N12 wy => opp_compare (comparen_8 4 wy wx)
  | N8 wx, N13 wy => opp_compare (comparen_8 5 wy wx)
  | N8 wx, Nn n wy =>
    opp_compare (compare_mn_1 w13 w8 W0 compare_8 (compare_13 W0) (comparen_8 5) (S n) wy wx)
  | N9 wx, N0 wy => comparen_0 9 wx wy
  | N9 wx, N1 wy => comparen_1 8 wx wy
  | N9 wx, N2 wy => comparen_2 7 wx wy
  | N9 wx, N3 wy => comparen_3 6 wx wy
  | N9 wx, N4 wy => comparen_4 5 wx wy
  | N9 wx, N5 wy => comparen_5 4 wx wy
  | N9 wx, N6 wy => comparen_6 3 wx wy
  | N9 wx, N7 wy => comparen_7 2 wx wy
  | N9 wx, N8 wy => comparen_8 1 wx wy
  | N9 wx, N9 wy => compare_9 wx wy
  | N9 wx, N10 wy => opp_compare (comparen_9 1 wy wx)
  | N9 wx, N11 wy => opp_compare (comparen_9 2 wy wx)
  | N9 wx, N12 wy => opp_compare (comparen_9 3 wy wx)
  | N9 wx, N13 wy => opp_compare (comparen_9 4 wy wx)
  | N9 wx, Nn n wy =>
    opp_compare (compare_mn_1 w13 w9 W0 compare_9 (compare_13 W0) (comparen_9 4) (S n) wy wx)
  | N10 wx, N0 wy => comparen_0 10 wx wy
  | N10 wx, N1 wy => comparen_1 9 wx wy
  | N10 wx, N2 wy => comparen_2 8 wx wy
  | N10 wx, N3 wy => comparen_3 7 wx wy
  | N10 wx, N4 wy => comparen_4 6 wx wy
  | N10 wx, N5 wy => comparen_5 5 wx wy
  | N10 wx, N6 wy => comparen_6 4 wx wy
  | N10 wx, N7 wy => comparen_7 3 wx wy
  | N10 wx, N8 wy => comparen_8 2 wx wy
  | N10 wx, N9 wy => comparen_9 1 wx wy
  | N10 wx, N10 wy => compare_10 wx wy
  | N10 wx, N11 wy => opp_compare (comparen_10 1 wy wx)
  | N10 wx, N12 wy => opp_compare (comparen_10 2 wy wx)
  | N10 wx, N13 wy => opp_compare (comparen_10 3 wy wx)
  | N10 wx, Nn n wy =>
    opp_compare (compare_mn_1 w13 w10 W0 compare_10 (compare_13 W0) (comparen_10 3) (S n) wy wx)
  | N11 wx, N0 wy => comparen_0 11 wx wy
  | N11 wx, N1 wy => comparen_1 10 wx wy
  | N11 wx, N2 wy => comparen_2 9 wx wy
  | N11 wx, N3 wy => comparen_3 8 wx wy
  | N11 wx, N4 wy => comparen_4 7 wx wy
  | N11 wx, N5 wy => comparen_5 6 wx wy
  | N11 wx, N6 wy => comparen_6 5 wx wy
  | N11 wx, N7 wy => comparen_7 4 wx wy
  | N11 wx, N8 wy => comparen_8 3 wx wy
  | N11 wx, N9 wy => comparen_9 2 wx wy
  | N11 wx, N10 wy => comparen_10 1 wx wy
  | N11 wx, N11 wy => compare_11 wx wy
  | N11 wx, N12 wy => opp_compare (comparen_11 1 wy wx)
  | N11 wx, N13 wy => opp_compare (comparen_11 2 wy wx)
  | N11 wx, Nn n wy =>
    opp_compare (compare_mn_1 w13 w11 W0 compare_11 (compare_13 W0) (comparen_11 2) (S n) wy wx)
  | N12 wx, N0 wy => comparen_0 12 wx wy
  | N12 wx, N1 wy => comparen_1 11 wx wy
  | N12 wx, N2 wy => comparen_2 10 wx wy
  | N12 wx, N3 wy => comparen_3 9 wx wy
  | N12 wx, N4 wy => comparen_4 8 wx wy
  | N12 wx, N5 wy => comparen_5 7 wx wy
  | N12 wx, N6 wy => comparen_6 6 wx wy
  | N12 wx, N7 wy => comparen_7 5 wx wy
  | N12 wx, N8 wy => comparen_8 4 wx wy
  | N12 wx, N9 wy => comparen_9 3 wx wy
  | N12 wx, N10 wy => comparen_10 2 wx wy
  | N12 wx, N11 wy => comparen_11 1 wx wy
  | N12 wx, N12 wy => compare_12 wx wy
  | N12 wx, N13 wy => opp_compare (comparen_12 1 wy wx)
  | N12 wx, Nn n wy =>
    opp_compare (compare_mn_1 w13 w12 W0 compare_12 (compare_13 W0) (comparen_12 1) (S n) wy wx)
  | N13 wx, N0 wy => comparen_0 13 wx wy
  | N13 wx, N1 wy => comparen_1 12 wx wy
  | N13 wx, N2 wy => comparen_2 11 wx wy
  | N13 wx, N3 wy => comparen_3 10 wx wy
  | N13 wx, N4 wy => comparen_4 9 wx wy
  | N13 wx, N5 wy => comparen_5 8 wx wy
  | N13 wx, N6 wy => comparen_6 7 wx wy
  | N13 wx, N7 wy => comparen_7 6 wx wy
  | N13 wx, N8 wy => comparen_8 5 wx wy
  | N13 wx, N9 wy => comparen_9 4 wx wy
  | N13 wx, N10 wy => comparen_10 3 wx wy
  | N13 wx, N11 wy => comparen_11 2 wx wy
  | N13 wx, N12 wy => comparen_12 1 wx wy
  | N13 wx, N13 wy => compare_13 wx wy
  | N13 wx, Nn n wy =>
    opp_compare (compare_mn_1 w13 w13 W0 compare_13 (compare_13 W0) (comparen_13 0) (S n) wy wx)
  | Nn n wx, N0 wy =>
    compare_mn_1 w13 w0 w_0 compare_0 (compare_13 W0) (comparen_0 13) (S n) wx wy
  | Nn n wx, N1 wy =>
    compare_mn_1 w13 w1 W0 compare_1 (compare_13 W0) (comparen_1 12) (S n) wx wy
  | Nn n wx, N2 wy =>
    compare_mn_1 w13 w2 W0 compare_2 (compare_13 W0) (comparen_2 11) (S n) wx wy
  | Nn n wx, N3 wy =>
    compare_mn_1 w13 w3 W0 compare_3 (compare_13 W0) (comparen_3 10) (S n) wx wy
  | Nn n wx, N4 wy =>
    compare_mn_1 w13 w4 W0 compare_4 (compare_13 W0) (comparen_4 9) (S n) wx wy
  | Nn n wx, N5 wy =>
    compare_mn_1 w13 w5 W0 compare_5 (compare_13 W0) (comparen_5 8) (S n) wx wy
  | Nn n wx, N6 wy =>
    compare_mn_1 w13 w6 W0 compare_6 (compare_13 W0) (comparen_6 7) (S n) wx wy
  | Nn n wx, N7 wy =>
    compare_mn_1 w13 w7 W0 compare_7 (compare_13 W0) (comparen_7 6) (S n) wx wy
  | Nn n wx, N8 wy =>
    compare_mn_1 w13 w8 W0 compare_8 (compare_13 W0) (comparen_8 5) (S n) wx wy
  | Nn n wx, N9 wy =>
    compare_mn_1 w13 w9 W0 compare_9 (compare_13 W0) (comparen_9 4) (S n) wx wy
  | Nn n wx, N10 wy =>
    compare_mn_1 w13 w10 W0 compare_10 (compare_13 W0) (comparen_10 3) (S n) wx wy
  | Nn n wx, N11 wy =>
    compare_mn_1 w13 w11 W0 compare_11 (compare_13 W0) (comparen_11 2) (S n) wx wy
  | Nn n wx, N12 wy =>
    compare_mn_1 w13 w12 W0 compare_12 (compare_13 W0) (comparen_12 1) (S n) wx wy
  | Nn n wx, N13 wy =>
    compare_mn_1 w13 w13 W0 compare_13 (compare_13 W0) (comparen_13 0) (S n) wx wy
  | Nn n wx, Nn m wy =>
    let mn := Max.max n m in
    let d := diff n m in
    let op := make_op mn in
     op.(znz_compare)
       (castm (diff_r n m) (extend_tr wx (snd d)))
       (castm (diff_l n m) (extend_tr wy (fst d)))
  end.

 Definition eq_bool x y :=
  match compare x y with
  | Eq => true
  | _  => false
  end.

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

 Definition mul x y :=
  match x, y with
  | N0 wx, N0 wy =>
    reduce_1 (w0_mul_c wx wy)
  | N0 wx, N1 wy =>
    if w0_eq0 wx then zero
    else
      let (w,r) := w0_mul_add_n1 1 wy wx w_0 in
      if w0_eq0 w then N1 r
      else N2 (WW (WW w_0 w) r)
  | N0 wx, N2 wy =>
    if w0_eq0 wx then zero
    else
      let (w,r) := w0_mul_add_n1 2 wy wx w_0 in
      if w0_eq0 w then N2 r
      else N3 (WW (extend1 w0 (WW w_0 w)) r)
  | N0 wx, N3 wy =>
    if w0_eq0 wx then zero
    else
      let (w,r) := w0_mul_add_n1 3 wy wx w_0 in
      if w0_eq0 w then N3 r
      else N4 (WW (extend2 w0 (WW w_0 w)) r)
  | N0 wx, N4 wy =>
    if w0_eq0 wx then zero
    else
      let (w,r) := w0_mul_add_n1 4 wy wx w_0 in
      if w0_eq0 w then N4 r
      else N5 (WW (extend3 w0 (WW w_0 w)) r)
  | N0 wx, N5 wy =>
    if w0_eq0 wx then zero
    else
      let (w,r) := w0_mul_add_n1 5 wy wx w_0 in
      if w0_eq0 w then N5 r
      else N6 (WW (extend4 w0 (WW w_0 w)) r)
  | N0 wx, N6 wy =>
    if w0_eq0 wx then zero
    else
      let (w,r) := w0_mul_add_n1 6 wy wx w_0 in
      if w0_eq0 w then N6 r
      else N7 (WW (extend5 w0 (WW w_0 w)) r)
  | N0 wx, N7 wy =>
    if w0_eq0 wx then zero
    else
      let (w,r) := w0_mul_add_n1 7 wy wx w_0 in
      if w0_eq0 w then N7 r
      else N8 (WW (extend6 w0 (WW w_0 w)) r)
  | N0 wx, N8 wy =>
    if w0_eq0 wx then zero
    else
      let (w,r) := w0_mul_add_n1 8 wy wx w_0 in
      if w0_eq0 w then N8 r
      else N9 (WW (extend7 w0 (WW w_0 w)) r)
  | N0 wx, N9 wy =>
    if w0_eq0 wx then zero
    else
      let (w,r) := w0_mul_add_n1 9 wy wx w_0 in
      if w0_eq0 w then N9 r
      else N10 (WW (extend8 w0 (WW w_0 w)) r)
  | N0 wx, N10 wy =>
    if w0_eq0 wx then zero
    else
      let (w,r) := w0_mul_add_n1 10 wy wx w_0 in
      if w0_eq0 w then N10 r
      else N11 (WW (extend9 w0 (WW w_0 w)) r)
  | N0 wx, N11 wy =>
    if w0_eq0 wx then zero
    else
      let (w,r) := w0_mul_add_n1 11 wy wx w_0 in
      if w0_eq0 w then N11 r
      else N12 (WW (extend10 w0 (WW w_0 w)) r)
  | N0 wx, N12 wy =>
    if w0_eq0 wx then zero
    else
      let (w,r) := w0_mul_add_n1 12 wy wx w_0 in
      if w0_eq0 w then N12 r
      else N13 (WW (extend11 w0 (WW w_0 w)) r)
  | N0 wx, N13 wy =>
    if w0_eq0 wx then zero
    else
      let (w,r) := w0_mul_add_n1 13 wy wx w_0 in
      if w0_eq0 w then N13 r
      else Nn 0 (WW (extend12 w0 (WW w_0 w)) r)
  | N0 wx, Nn n wy =>
    if w0_eq0 wx then zero
    else
    let (w,r) := w13_mul_add_n1 (S n) wy (extend12 w0 (WW w_0 wx)) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | N1 wx, N0 wy =>
    if w0_eq0 wy then zero
    else
      let (w,r) := w0_mul_add_n1 1 wx wy w_0 in
      if w0_eq0 w then N1 r
      else N2 (WW (WW w_0 w) r)
  | N1 wx, N1 wy =>
    N2 (w1_mul_c wx wy)
  | N1 wx, N2 wy =>
    let (w,r) := w1_mul_add_n1 1 wy wx W0 in
    if w1_eq0 w then N2 r
    else N3 (WW (extend1 w0 w) r)
  | N1 wx, N3 wy =>
    let (w,r) := w1_mul_add_n1 2 wy wx W0 in
    if w1_eq0 w then N3 r
    else N4 (WW (extend2 w0 w) r)
  | N1 wx, N4 wy =>
    let (w,r) := w1_mul_add_n1 3 wy wx W0 in
    if w1_eq0 w then N4 r
    else N5 (WW (extend3 w0 w) r)
  | N1 wx, N5 wy =>
    let (w,r) := w1_mul_add_n1 4 wy wx W0 in
    if w1_eq0 w then N5 r
    else N6 (WW (extend4 w0 w) r)
  | N1 wx, N6 wy =>
    let (w,r) := w1_mul_add_n1 5 wy wx W0 in
    if w1_eq0 w then N6 r
    else N7 (WW (extend5 w0 w) r)
  | N1 wx, N7 wy =>
    let (w,r) := w1_mul_add_n1 6 wy wx W0 in
    if w1_eq0 w then N7 r
    else N8 (WW (extend6 w0 w) r)
  | N1 wx, N8 wy =>
    let (w,r) := w1_mul_add_n1 7 wy wx W0 in
    if w1_eq0 w then N8 r
    else N9 (WW (extend7 w0 w) r)
  | N1 wx, N9 wy =>
    let (w,r) := w1_mul_add_n1 8 wy wx W0 in
    if w1_eq0 w then N9 r
    else N10 (WW (extend8 w0 w) r)
  | N1 wx, N10 wy =>
    let (w,r) := w1_mul_add_n1 9 wy wx W0 in
    if w1_eq0 w then N10 r
    else N11 (WW (extend9 w0 w) r)
  | N1 wx, N11 wy =>
    let (w,r) := w1_mul_add_n1 10 wy wx W0 in
    if w1_eq0 w then N11 r
    else N12 (WW (extend10 w0 w) r)
  | N1 wx, N12 wy =>
    let (w,r) := w1_mul_add_n1 11 wy wx W0 in
    if w1_eq0 w then N12 r
    else N13 (WW (extend11 w0 w) r)
  | N1 wx, N13 wy =>
    let (w,r) := w1_mul_add_n1 12 wy wx W0 in
    if w1_eq0 w then N13 r
    else Nn 0 (WW (extend12 w0 w) r)
  | N1 wx, Nn n wy =>
    let (w,r) := w13_mul_add_n1 (S n) wy (extend12 w0 wx) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | N2 wx, N0 wy =>
    if w0_eq0 wy then zero
    else
      let (w,r) := w0_mul_add_n1 2 wx wy w_0 in
      if w0_eq0 w then N2 r
      else N3 (WW (extend1 w0 (WW w_0 w)) r)
  | N2 wx, N1 wy =>
    let (w,r) := w1_mul_add_n1 1 wx wy W0 in
    if w1_eq0 w then N2 r
    else N3 (WW (extend1 w0 w) r)
  | N2 wx, N2 wy =>
    N3 (w2_mul_c wx wy)
  | N2 wx, N3 wy =>
    let (w,r) := w2_mul_add_n1 1 wy wx W0 in
    if w2_eq0 w then N3 r
    else N4 (WW (extend1 w1 w) r)
  | N2 wx, N4 wy =>
    let (w,r) := w2_mul_add_n1 2 wy wx W0 in
    if w2_eq0 w then N4 r
    else N5 (WW (extend2 w1 w) r)
  | N2 wx, N5 wy =>
    let (w,r) := w2_mul_add_n1 3 wy wx W0 in
    if w2_eq0 w then N5 r
    else N6 (WW (extend3 w1 w) r)
  | N2 wx, N6 wy =>
    let (w,r) := w2_mul_add_n1 4 wy wx W0 in
    if w2_eq0 w then N6 r
    else N7 (WW (extend4 w1 w) r)
  | N2 wx, N7 wy =>
    let (w,r) := w2_mul_add_n1 5 wy wx W0 in
    if w2_eq0 w then N7 r
    else N8 (WW (extend5 w1 w) r)
  | N2 wx, N8 wy =>
    let (w,r) := w2_mul_add_n1 6 wy wx W0 in
    if w2_eq0 w then N8 r
    else N9 (WW (extend6 w1 w) r)
  | N2 wx, N9 wy =>
    let (w,r) := w2_mul_add_n1 7 wy wx W0 in
    if w2_eq0 w then N9 r
    else N10 (WW (extend7 w1 w) r)
  | N2 wx, N10 wy =>
    let (w,r) := w2_mul_add_n1 8 wy wx W0 in
    if w2_eq0 w then N10 r
    else N11 (WW (extend8 w1 w) r)
  | N2 wx, N11 wy =>
    let (w,r) := w2_mul_add_n1 9 wy wx W0 in
    if w2_eq0 w then N11 r
    else N12 (WW (extend9 w1 w) r)
  | N2 wx, N12 wy =>
    let (w,r) := w2_mul_add_n1 10 wy wx W0 in
    if w2_eq0 w then N12 r
    else N13 (WW (extend10 w1 w) r)
  | N2 wx, N13 wy =>
    let (w,r) := w2_mul_add_n1 11 wy wx W0 in
    if w2_eq0 w then N13 r
    else Nn 0 (WW (extend11 w1 w) r)
  | N2 wx, Nn n wy =>
    let (w,r) := w13_mul_add_n1 (S n) wy (extend11 w1 wx) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | N3 wx, N0 wy =>
    if w0_eq0 wy then zero
    else
      let (w,r) := w0_mul_add_n1 3 wx wy w_0 in
      if w0_eq0 w then N3 r
      else N4 (WW (extend2 w0 (WW w_0 w)) r)
  | N3 wx, N1 wy =>
    let (w,r) := w1_mul_add_n1 2 wx wy W0 in
    if w1_eq0 w then N3 r
    else N4 (WW (extend2 w0 w) r)
  | N3 wx, N2 wy =>
    let (w,r) := w2_mul_add_n1 1 wx wy W0 in
    if w2_eq0 w then N3 r
    else N4 (WW (extend1 w1 w) r)
  | N3 wx, N3 wy =>
    N4 (w3_mul_c wx wy)
  | N3 wx, N4 wy =>
    let (w,r) := w3_mul_add_n1 1 wy wx W0 in
    if w3_eq0 w then N4 r
    else N5 (WW (extend1 w2 w) r)
  | N3 wx, N5 wy =>
    let (w,r) := w3_mul_add_n1 2 wy wx W0 in
    if w3_eq0 w then N5 r
    else N6 (WW (extend2 w2 w) r)
  | N3 wx, N6 wy =>
    let (w,r) := w3_mul_add_n1 3 wy wx W0 in
    if w3_eq0 w then N6 r
    else N7 (WW (extend3 w2 w) r)
  | N3 wx, N7 wy =>
    let (w,r) := w3_mul_add_n1 4 wy wx W0 in
    if w3_eq0 w then N7 r
    else N8 (WW (extend4 w2 w) r)
  | N3 wx, N8 wy =>
    let (w,r) := w3_mul_add_n1 5 wy wx W0 in
    if w3_eq0 w then N8 r
    else N9 (WW (extend5 w2 w) r)
  | N3 wx, N9 wy =>
    let (w,r) := w3_mul_add_n1 6 wy wx W0 in
    if w3_eq0 w then N9 r
    else N10 (WW (extend6 w2 w) r)
  | N3 wx, N10 wy =>
    let (w,r) := w3_mul_add_n1 7 wy wx W0 in
    if w3_eq0 w then N10 r
    else N11 (WW (extend7 w2 w) r)
  | N3 wx, N11 wy =>
    let (w,r) := w3_mul_add_n1 8 wy wx W0 in
    if w3_eq0 w then N11 r
    else N12 (WW (extend8 w2 w) r)
  | N3 wx, N12 wy =>
    let (w,r) := w3_mul_add_n1 9 wy wx W0 in
    if w3_eq0 w then N12 r
    else N13 (WW (extend9 w2 w) r)
  | N3 wx, N13 wy =>
    let (w,r) := w3_mul_add_n1 10 wy wx W0 in
    if w3_eq0 w then N13 r
    else Nn 0 (WW (extend10 w2 w) r)
  | N3 wx, Nn n wy =>
    let (w,r) := w13_mul_add_n1 (S n) wy (extend10 w2 wx) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | N4 wx, N0 wy =>
    if w0_eq0 wy then zero
    else
      let (w,r) := w0_mul_add_n1 4 wx wy w_0 in
      if w0_eq0 w then N4 r
      else N5 (WW (extend3 w0 (WW w_0 w)) r)
  | N4 wx, N1 wy =>
    let (w,r) := w1_mul_add_n1 3 wx wy W0 in
    if w1_eq0 w then N4 r
    else N5 (WW (extend3 w0 w) r)
  | N4 wx, N2 wy =>
    let (w,r) := w2_mul_add_n1 2 wx wy W0 in
    if w2_eq0 w then N4 r
    else N5 (WW (extend2 w1 w) r)
  | N4 wx, N3 wy =>
    let (w,r) := w3_mul_add_n1 1 wx wy W0 in
    if w3_eq0 w then N4 r
    else N5 (WW (extend1 w2 w) r)
  | N4 wx, N4 wy =>
    N5 (w4_mul_c wx wy)
  | N4 wx, N5 wy =>
    let (w,r) := w4_mul_add_n1 1 wy wx W0 in
    if w4_eq0 w then N5 r
    else N6 (WW (extend1 w3 w) r)
  | N4 wx, N6 wy =>
    let (w,r) := w4_mul_add_n1 2 wy wx W0 in
    if w4_eq0 w then N6 r
    else N7 (WW (extend2 w3 w) r)
  | N4 wx, N7 wy =>
    let (w,r) := w4_mul_add_n1 3 wy wx W0 in
    if w4_eq0 w then N7 r
    else N8 (WW (extend3 w3 w) r)
  | N4 wx, N8 wy =>
    let (w,r) := w4_mul_add_n1 4 wy wx W0 in
    if w4_eq0 w then N8 r
    else N9 (WW (extend4 w3 w) r)
  | N4 wx, N9 wy =>
    let (w,r) := w4_mul_add_n1 5 wy wx W0 in
    if w4_eq0 w then N9 r
    else N10 (WW (extend5 w3 w) r)
  | N4 wx, N10 wy =>
    let (w,r) := w4_mul_add_n1 6 wy wx W0 in
    if w4_eq0 w then N10 r
    else N11 (WW (extend6 w3 w) r)
  | N4 wx, N11 wy =>
    let (w,r) := w4_mul_add_n1 7 wy wx W0 in
    if w4_eq0 w then N11 r
    else N12 (WW (extend7 w3 w) r)
  | N4 wx, N12 wy =>
    let (w,r) := w4_mul_add_n1 8 wy wx W0 in
    if w4_eq0 w then N12 r
    else N13 (WW (extend8 w3 w) r)
  | N4 wx, N13 wy =>
    let (w,r) := w4_mul_add_n1 9 wy wx W0 in
    if w4_eq0 w then N13 r
    else Nn 0 (WW (extend9 w3 w) r)
  | N4 wx, Nn n wy =>
    let (w,r) := w13_mul_add_n1 (S n) wy (extend9 w3 wx) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | N5 wx, N0 wy =>
    if w0_eq0 wy then zero
    else
      let (w,r) := w0_mul_add_n1 5 wx wy w_0 in
      if w0_eq0 w then N5 r
      else N6 (WW (extend4 w0 (WW w_0 w)) r)
  | N5 wx, N1 wy =>
    let (w,r) := w1_mul_add_n1 4 wx wy W0 in
    if w1_eq0 w then N5 r
    else N6 (WW (extend4 w0 w) r)
  | N5 wx, N2 wy =>
    let (w,r) := w2_mul_add_n1 3 wx wy W0 in
    if w2_eq0 w then N5 r
    else N6 (WW (extend3 w1 w) r)
  | N5 wx, N3 wy =>
    let (w,r) := w3_mul_add_n1 2 wx wy W0 in
    if w3_eq0 w then N5 r
    else N6 (WW (extend2 w2 w) r)
  | N5 wx, N4 wy =>
    let (w,r) := w4_mul_add_n1 1 wx wy W0 in
    if w4_eq0 w then N5 r
    else N6 (WW (extend1 w3 w) r)
  | N5 wx, N5 wy =>
    N6 (w5_mul_c wx wy)
  | N5 wx, N6 wy =>
    let (w,r) := w5_mul_add_n1 1 wy wx W0 in
    if w5_eq0 w then N6 r
    else N7 (WW (extend1 w4 w) r)
  | N5 wx, N7 wy =>
    let (w,r) := w5_mul_add_n1 2 wy wx W0 in
    if w5_eq0 w then N7 r
    else N8 (WW (extend2 w4 w) r)
  | N5 wx, N8 wy =>
    let (w,r) := w5_mul_add_n1 3 wy wx W0 in
    if w5_eq0 w then N8 r
    else N9 (WW (extend3 w4 w) r)
  | N5 wx, N9 wy =>
    let (w,r) := w5_mul_add_n1 4 wy wx W0 in
    if w5_eq0 w then N9 r
    else N10 (WW (extend4 w4 w) r)
  | N5 wx, N10 wy =>
    let (w,r) := w5_mul_add_n1 5 wy wx W0 in
    if w5_eq0 w then N10 r
    else N11 (WW (extend5 w4 w) r)
  | N5 wx, N11 wy =>
    let (w,r) := w5_mul_add_n1 6 wy wx W0 in
    if w5_eq0 w then N11 r
    else N12 (WW (extend6 w4 w) r)
  | N5 wx, N12 wy =>
    let (w,r) := w5_mul_add_n1 7 wy wx W0 in
    if w5_eq0 w then N12 r
    else N13 (WW (extend7 w4 w) r)
  | N5 wx, N13 wy =>
    let (w,r) := w5_mul_add_n1 8 wy wx W0 in
    if w5_eq0 w then N13 r
    else Nn 0 (WW (extend8 w4 w) r)
  | N5 wx, Nn n wy =>
    let (w,r) := w13_mul_add_n1 (S n) wy (extend8 w4 wx) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | N6 wx, N0 wy =>
    if w0_eq0 wy then zero
    else
      let (w,r) := w0_mul_add_n1 6 wx wy w_0 in
      if w0_eq0 w then N6 r
      else N7 (WW (extend5 w0 (WW w_0 w)) r)
  | N6 wx, N1 wy =>
    let (w,r) := w1_mul_add_n1 5 wx wy W0 in
    if w1_eq0 w then N6 r
    else N7 (WW (extend5 w0 w) r)
  | N6 wx, N2 wy =>
    let (w,r) := w2_mul_add_n1 4 wx wy W0 in
    if w2_eq0 w then N6 r
    else N7 (WW (extend4 w1 w) r)
  | N6 wx, N3 wy =>
    let (w,r) := w3_mul_add_n1 3 wx wy W0 in
    if w3_eq0 w then N6 r
    else N7 (WW (extend3 w2 w) r)
  | N6 wx, N4 wy =>
    let (w,r) := w4_mul_add_n1 2 wx wy W0 in
    if w4_eq0 w then N6 r
    else N7 (WW (extend2 w3 w) r)
  | N6 wx, N5 wy =>
    let (w,r) := w5_mul_add_n1 1 wx wy W0 in
    if w5_eq0 w then N6 r
    else N7 (WW (extend1 w4 w) r)
  | N6 wx, N6 wy =>
    N7 (w6_mul_c wx wy)
  | N6 wx, N7 wy =>
    let (w,r) := w6_mul_add_n1 1 wy wx W0 in
    if w6_eq0 w then N7 r
    else N8 (WW (extend1 w5 w) r)
  | N6 wx, N8 wy =>
    let (w,r) := w6_mul_add_n1 2 wy wx W0 in
    if w6_eq0 w then N8 r
    else N9 (WW (extend2 w5 w) r)
  | N6 wx, N9 wy =>
    let (w,r) := w6_mul_add_n1 3 wy wx W0 in
    if w6_eq0 w then N9 r
    else N10 (WW (extend3 w5 w) r)
  | N6 wx, N10 wy =>
    let (w,r) := w6_mul_add_n1 4 wy wx W0 in
    if w6_eq0 w then N10 r
    else N11 (WW (extend4 w5 w) r)
  | N6 wx, N11 wy =>
    let (w,r) := w6_mul_add_n1 5 wy wx W0 in
    if w6_eq0 w then N11 r
    else N12 (WW (extend5 w5 w) r)
  | N6 wx, N12 wy =>
    let (w,r) := w6_mul_add_n1 6 wy wx W0 in
    if w6_eq0 w then N12 r
    else N13 (WW (extend6 w5 w) r)
  | N6 wx, N13 wy =>
    let (w,r) := w6_mul_add_n1 7 wy wx W0 in
    if w6_eq0 w then N13 r
    else Nn 0 (WW (extend7 w5 w) r)
  | N6 wx, Nn n wy =>
    let (w,r) := w13_mul_add_n1 (S n) wy (extend7 w5 wx) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | N7 wx, N0 wy =>
    if w0_eq0 wy then zero
    else
      let (w,r) := w0_mul_add_n1 7 wx wy w_0 in
      if w0_eq0 w then N7 r
      else N8 (WW (extend6 w0 (WW w_0 w)) r)
  | N7 wx, N1 wy =>
    let (w,r) := w1_mul_add_n1 6 wx wy W0 in
    if w1_eq0 w then N7 r
    else N8 (WW (extend6 w0 w) r)
  | N7 wx, N2 wy =>
    let (w,r) := w2_mul_add_n1 5 wx wy W0 in
    if w2_eq0 w then N7 r
    else N8 (WW (extend5 w1 w) r)
  | N7 wx, N3 wy =>
    let (w,r) := w3_mul_add_n1 4 wx wy W0 in
    if w3_eq0 w then N7 r
    else N8 (WW (extend4 w2 w) r)
  | N7 wx, N4 wy =>
    let (w,r) := w4_mul_add_n1 3 wx wy W0 in
    if w4_eq0 w then N7 r
    else N8 (WW (extend3 w3 w) r)
  | N7 wx, N5 wy =>
    let (w,r) := w5_mul_add_n1 2 wx wy W0 in
    if w5_eq0 w then N7 r
    else N8 (WW (extend2 w4 w) r)
  | N7 wx, N6 wy =>
    let (w,r) := w6_mul_add_n1 1 wx wy W0 in
    if w6_eq0 w then N7 r
    else N8 (WW (extend1 w5 w) r)
  | N7 wx, N7 wy =>
    N8 (w7_mul_c wx wy)
  | N7 wx, N8 wy =>
    let (w,r) := w7_mul_add_n1 1 wy wx W0 in
    if w7_eq0 w then N8 r
    else N9 (WW (extend1 w6 w) r)
  | N7 wx, N9 wy =>
    let (w,r) := w7_mul_add_n1 2 wy wx W0 in
    if w7_eq0 w then N9 r
    else N10 (WW (extend2 w6 w) r)
  | N7 wx, N10 wy =>
    let (w,r) := w7_mul_add_n1 3 wy wx W0 in
    if w7_eq0 w then N10 r
    else N11 (WW (extend3 w6 w) r)
  | N7 wx, N11 wy =>
    let (w,r) := w7_mul_add_n1 4 wy wx W0 in
    if w7_eq0 w then N11 r
    else N12 (WW (extend4 w6 w) r)
  | N7 wx, N12 wy =>
    let (w,r) := w7_mul_add_n1 5 wy wx W0 in
    if w7_eq0 w then N12 r
    else N13 (WW (extend5 w6 w) r)
  | N7 wx, N13 wy =>
    let (w,r) := w7_mul_add_n1 6 wy wx W0 in
    if w7_eq0 w then N13 r
    else Nn 0 (WW (extend6 w6 w) r)
  | N7 wx, Nn n wy =>
    let (w,r) := w13_mul_add_n1 (S n) wy (extend6 w6 wx) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | N8 wx, N0 wy =>
    if w0_eq0 wy then zero
    else
      let (w,r) := w0_mul_add_n1 8 wx wy w_0 in
      if w0_eq0 w then N8 r
      else N9 (WW (extend7 w0 (WW w_0 w)) r)
  | N8 wx, N1 wy =>
    let (w,r) := w1_mul_add_n1 7 wx wy W0 in
    if w1_eq0 w then N8 r
    else N9 (WW (extend7 w0 w) r)
  | N8 wx, N2 wy =>
    let (w,r) := w2_mul_add_n1 6 wx wy W0 in
    if w2_eq0 w then N8 r
    else N9 (WW (extend6 w1 w) r)
  | N8 wx, N3 wy =>
    let (w,r) := w3_mul_add_n1 5 wx wy W0 in
    if w3_eq0 w then N8 r
    else N9 (WW (extend5 w2 w) r)
  | N8 wx, N4 wy =>
    let (w,r) := w4_mul_add_n1 4 wx wy W0 in
    if w4_eq0 w then N8 r
    else N9 (WW (extend4 w3 w) r)
  | N8 wx, N5 wy =>
    let (w,r) := w5_mul_add_n1 3 wx wy W0 in
    if w5_eq0 w then N8 r
    else N9 (WW (extend3 w4 w) r)
  | N8 wx, N6 wy =>
    let (w,r) := w6_mul_add_n1 2 wx wy W0 in
    if w6_eq0 w then N8 r
    else N9 (WW (extend2 w5 w) r)
  | N8 wx, N7 wy =>
    let (w,r) := w7_mul_add_n1 1 wx wy W0 in
    if w7_eq0 w then N8 r
    else N9 (WW (extend1 w6 w) r)
  | N8 wx, N8 wy =>
    N9 (w8_mul_c wx wy)
  | N8 wx, N9 wy =>
    let (w,r) := w8_mul_add_n1 1 wy wx W0 in
    if w8_eq0 w then N9 r
    else N10 (WW (extend1 w7 w) r)
  | N8 wx, N10 wy =>
    let (w,r) := w8_mul_add_n1 2 wy wx W0 in
    if w8_eq0 w then N10 r
    else N11 (WW (extend2 w7 w) r)
  | N8 wx, N11 wy =>
    let (w,r) := w8_mul_add_n1 3 wy wx W0 in
    if w8_eq0 w then N11 r
    else N12 (WW (extend3 w7 w) r)
  | N8 wx, N12 wy =>
    let (w,r) := w8_mul_add_n1 4 wy wx W0 in
    if w8_eq0 w then N12 r
    else N13 (WW (extend4 w7 w) r)
  | N8 wx, N13 wy =>
    let (w,r) := w8_mul_add_n1 5 wy wx W0 in
    if w8_eq0 w then N13 r
    else Nn 0 (WW (extend5 w7 w) r)
  | N8 wx, Nn n wy =>
    let (w,r) := w13_mul_add_n1 (S n) wy (extend5 w7 wx) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | N9 wx, N0 wy =>
    if w0_eq0 wy then zero
    else
      let (w,r) := w0_mul_add_n1 9 wx wy w_0 in
      if w0_eq0 w then N9 r
      else N10 (WW (extend8 w0 (WW w_0 w)) r)
  | N9 wx, N1 wy =>
    let (w,r) := w1_mul_add_n1 8 wx wy W0 in
    if w1_eq0 w then N9 r
    else N10 (WW (extend8 w0 w) r)
  | N9 wx, N2 wy =>
    let (w,r) := w2_mul_add_n1 7 wx wy W0 in
    if w2_eq0 w then N9 r
    else N10 (WW (extend7 w1 w) r)
  | N9 wx, N3 wy =>
    let (w,r) := w3_mul_add_n1 6 wx wy W0 in
    if w3_eq0 w then N9 r
    else N10 (WW (extend6 w2 w) r)
  | N9 wx, N4 wy =>
    let (w,r) := w4_mul_add_n1 5 wx wy W0 in
    if w4_eq0 w then N9 r
    else N10 (WW (extend5 w3 w) r)
  | N9 wx, N5 wy =>
    let (w,r) := w5_mul_add_n1 4 wx wy W0 in
    if w5_eq0 w then N9 r
    else N10 (WW (extend4 w4 w) r)
  | N9 wx, N6 wy =>
    let (w,r) := w6_mul_add_n1 3 wx wy W0 in
    if w6_eq0 w then N9 r
    else N10 (WW (extend3 w5 w) r)
  | N9 wx, N7 wy =>
    let (w,r) := w7_mul_add_n1 2 wx wy W0 in
    if w7_eq0 w then N9 r
    else N10 (WW (extend2 w6 w) r)
  | N9 wx, N8 wy =>
    let (w,r) := w8_mul_add_n1 1 wx wy W0 in
    if w8_eq0 w then N9 r
    else N10 (WW (extend1 w7 w) r)
  | N9 wx, N9 wy =>
    N10 (w9_mul_c wx wy)
  | N9 wx, N10 wy =>
    let (w,r) := w9_mul_add_n1 1 wy wx W0 in
    if w9_eq0 w then N10 r
    else N11 (WW (extend1 w8 w) r)
  | N9 wx, N11 wy =>
    let (w,r) := w9_mul_add_n1 2 wy wx W0 in
    if w9_eq0 w then N11 r
    else N12 (WW (extend2 w8 w) r)
  | N9 wx, N12 wy =>
    let (w,r) := w9_mul_add_n1 3 wy wx W0 in
    if w9_eq0 w then N12 r
    else N13 (WW (extend3 w8 w) r)
  | N9 wx, N13 wy =>
    let (w,r) := w9_mul_add_n1 4 wy wx W0 in
    if w9_eq0 w then N13 r
    else Nn 0 (WW (extend4 w8 w) r)
  | N9 wx, Nn n wy =>
    let (w,r) := w13_mul_add_n1 (S n) wy (extend4 w8 wx) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | N10 wx, N0 wy =>
    if w0_eq0 wy then zero
    else
      let (w,r) := w0_mul_add_n1 10 wx wy w_0 in
      if w0_eq0 w then N10 r
      else N11 (WW (extend9 w0 (WW w_0 w)) r)
  | N10 wx, N1 wy =>
    let (w,r) := w1_mul_add_n1 9 wx wy W0 in
    if w1_eq0 w then N10 r
    else N11 (WW (extend9 w0 w) r)
  | N10 wx, N2 wy =>
    let (w,r) := w2_mul_add_n1 8 wx wy W0 in
    if w2_eq0 w then N10 r
    else N11 (WW (extend8 w1 w) r)
  | N10 wx, N3 wy =>
    let (w,r) := w3_mul_add_n1 7 wx wy W0 in
    if w3_eq0 w then N10 r
    else N11 (WW (extend7 w2 w) r)
  | N10 wx, N4 wy =>
    let (w,r) := w4_mul_add_n1 6 wx wy W0 in
    if w4_eq0 w then N10 r
    else N11 (WW (extend6 w3 w) r)
  | N10 wx, N5 wy =>
    let (w,r) := w5_mul_add_n1 5 wx wy W0 in
    if w5_eq0 w then N10 r
    else N11 (WW (extend5 w4 w) r)
  | N10 wx, N6 wy =>
    let (w,r) := w6_mul_add_n1 4 wx wy W0 in
    if w6_eq0 w then N10 r
    else N11 (WW (extend4 w5 w) r)
  | N10 wx, N7 wy =>
    let (w,r) := w7_mul_add_n1 3 wx wy W0 in
    if w7_eq0 w then N10 r
    else N11 (WW (extend3 w6 w) r)
  | N10 wx, N8 wy =>
    let (w,r) := w8_mul_add_n1 2 wx wy W0 in
    if w8_eq0 w then N10 r
    else N11 (WW (extend2 w7 w) r)
  | N10 wx, N9 wy =>
    let (w,r) := w9_mul_add_n1 1 wx wy W0 in
    if w9_eq0 w then N10 r
    else N11 (WW (extend1 w8 w) r)
  | N10 wx, N10 wy =>
    N11 (w10_mul_c wx wy)
  | N10 wx, N11 wy =>
    let (w,r) := w10_mul_add_n1 1 wy wx W0 in
    if w10_eq0 w then N11 r
    else N12 (WW (extend1 w9 w) r)
  | N10 wx, N12 wy =>
    let (w,r) := w10_mul_add_n1 2 wy wx W0 in
    if w10_eq0 w then N12 r
    else N13 (WW (extend2 w9 w) r)
  | N10 wx, N13 wy =>
    let (w,r) := w10_mul_add_n1 3 wy wx W0 in
    if w10_eq0 w then N13 r
    else Nn 0 (WW (extend3 w9 w) r)
  | N10 wx, Nn n wy =>
    let (w,r) := w13_mul_add_n1 (S n) wy (extend3 w9 wx) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | N11 wx, N0 wy =>
    if w0_eq0 wy then zero
    else
      let (w,r) := w0_mul_add_n1 11 wx wy w_0 in
      if w0_eq0 w then N11 r
      else N12 (WW (extend10 w0 (WW w_0 w)) r)
  | N11 wx, N1 wy =>
    let (w,r) := w1_mul_add_n1 10 wx wy W0 in
    if w1_eq0 w then N11 r
    else N12 (WW (extend10 w0 w) r)
  | N11 wx, N2 wy =>
    let (w,r) := w2_mul_add_n1 9 wx wy W0 in
    if w2_eq0 w then N11 r
    else N12 (WW (extend9 w1 w) r)
  | N11 wx, N3 wy =>
    let (w,r) := w3_mul_add_n1 8 wx wy W0 in
    if w3_eq0 w then N11 r
    else N12 (WW (extend8 w2 w) r)
  | N11 wx, N4 wy =>
    let (w,r) := w4_mul_add_n1 7 wx wy W0 in
    if w4_eq0 w then N11 r
    else N12 (WW (extend7 w3 w) r)
  | N11 wx, N5 wy =>
    let (w,r) := w5_mul_add_n1 6 wx wy W0 in
    if w5_eq0 w then N11 r
    else N12 (WW (extend6 w4 w) r)
  | N11 wx, N6 wy =>
    let (w,r) := w6_mul_add_n1 5 wx wy W0 in
    if w6_eq0 w then N11 r
    else N12 (WW (extend5 w5 w) r)
  | N11 wx, N7 wy =>
    let (w,r) := w7_mul_add_n1 4 wx wy W0 in
    if w7_eq0 w then N11 r
    else N12 (WW (extend4 w6 w) r)
  | N11 wx, N8 wy =>
    let (w,r) := w8_mul_add_n1 3 wx wy W0 in
    if w8_eq0 w then N11 r
    else N12 (WW (extend3 w7 w) r)
  | N11 wx, N9 wy =>
    let (w,r) := w9_mul_add_n1 2 wx wy W0 in
    if w9_eq0 w then N11 r
    else N12 (WW (extend2 w8 w) r)
  | N11 wx, N10 wy =>
    let (w,r) := w10_mul_add_n1 1 wx wy W0 in
    if w10_eq0 w then N11 r
    else N12 (WW (extend1 w9 w) r)
  | N11 wx, N11 wy =>
    N12 (w11_mul_c wx wy)
  | N11 wx, N12 wy =>
    let (w,r) := w11_mul_add_n1 1 wy wx W0 in
    if w11_eq0 w then N12 r
    else N13 (WW (extend1 w10 w) r)
  | N11 wx, N13 wy =>
    let (w,r) := w11_mul_add_n1 2 wy wx W0 in
    if w11_eq0 w then N13 r
    else Nn 0 (WW (extend2 w10 w) r)
  | N11 wx, Nn n wy =>
    let (w,r) := w13_mul_add_n1 (S n) wy (extend2 w10 wx) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | N12 wx, N0 wy =>
    if w0_eq0 wy then zero
    else
      let (w,r) := w0_mul_add_n1 12 wx wy w_0 in
      if w0_eq0 w then N12 r
      else N13 (WW (extend11 w0 (WW w_0 w)) r)
  | N12 wx, N1 wy =>
    let (w,r) := w1_mul_add_n1 11 wx wy W0 in
    if w1_eq0 w then N12 r
    else N13 (WW (extend11 w0 w) r)
  | N12 wx, N2 wy =>
    let (w,r) := w2_mul_add_n1 10 wx wy W0 in
    if w2_eq0 w then N12 r
    else N13 (WW (extend10 w1 w) r)
  | N12 wx, N3 wy =>
    let (w,r) := w3_mul_add_n1 9 wx wy W0 in
    if w3_eq0 w then N12 r
    else N13 (WW (extend9 w2 w) r)
  | N12 wx, N4 wy =>
    let (w,r) := w4_mul_add_n1 8 wx wy W0 in
    if w4_eq0 w then N12 r
    else N13 (WW (extend8 w3 w) r)
  | N12 wx, N5 wy =>
    let (w,r) := w5_mul_add_n1 7 wx wy W0 in
    if w5_eq0 w then N12 r
    else N13 (WW (extend7 w4 w) r)
  | N12 wx, N6 wy =>
    let (w,r) := w6_mul_add_n1 6 wx wy W0 in
    if w6_eq0 w then N12 r
    else N13 (WW (extend6 w5 w) r)
  | N12 wx, N7 wy =>
    let (w,r) := w7_mul_add_n1 5 wx wy W0 in
    if w7_eq0 w then N12 r
    else N13 (WW (extend5 w6 w) r)
  | N12 wx, N8 wy =>
    let (w,r) := w8_mul_add_n1 4 wx wy W0 in
    if w8_eq0 w then N12 r
    else N13 (WW (extend4 w7 w) r)
  | N12 wx, N9 wy =>
    let (w,r) := w9_mul_add_n1 3 wx wy W0 in
    if w9_eq0 w then N12 r
    else N13 (WW (extend3 w8 w) r)
  | N12 wx, N10 wy =>
    let (w,r) := w10_mul_add_n1 2 wx wy W0 in
    if w10_eq0 w then N12 r
    else N13 (WW (extend2 w9 w) r)
  | N12 wx, N11 wy =>
    let (w,r) := w11_mul_add_n1 1 wx wy W0 in
    if w11_eq0 w then N12 r
    else N13 (WW (extend1 w10 w) r)
  | N12 wx, N12 wy =>
    N13 (w12_mul_c wx wy)
  | N12 wx, N13 wy =>
    let (w,r) := w12_mul_add_n1 1 wy wx W0 in
    if w12_eq0 w then N13 r
    else Nn 0 (WW (extend1 w11 w) r)
  | N12 wx, Nn n wy =>
    let (w,r) := w13_mul_add_n1 (S n) wy (extend1 w11 wx) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | N13 wx, N0 wy =>
    if w0_eq0 wy then zero
    else
      let (w,r) := w0_mul_add_n1 13 wx wy w_0 in
      if w0_eq0 w then N13 r
      else Nn 0 (WW (extend12 w0 (WW w_0 w)) r)
  | N13 wx, N1 wy =>
    let (w,r) := w1_mul_add_n1 12 wx wy W0 in
    if w1_eq0 w then N13 r
    else Nn 0 (WW (extend12 w0 w) r)
  | N13 wx, N2 wy =>
    let (w,r) := w2_mul_add_n1 11 wx wy W0 in
    if w2_eq0 w then N13 r
    else Nn 0 (WW (extend11 w1 w) r)
  | N13 wx, N3 wy =>
    let (w,r) := w3_mul_add_n1 10 wx wy W0 in
    if w3_eq0 w then N13 r
    else Nn 0 (WW (extend10 w2 w) r)
  | N13 wx, N4 wy =>
    let (w,r) := w4_mul_add_n1 9 wx wy W0 in
    if w4_eq0 w then N13 r
    else Nn 0 (WW (extend9 w3 w) r)
  | N13 wx, N5 wy =>
    let (w,r) := w5_mul_add_n1 8 wx wy W0 in
    if w5_eq0 w then N13 r
    else Nn 0 (WW (extend8 w4 w) r)
  | N13 wx, N6 wy =>
    let (w,r) := w6_mul_add_n1 7 wx wy W0 in
    if w6_eq0 w then N13 r
    else Nn 0 (WW (extend7 w5 w) r)
  | N13 wx, N7 wy =>
    let (w,r) := w7_mul_add_n1 6 wx wy W0 in
    if w7_eq0 w then N13 r
    else Nn 0 (WW (extend6 w6 w) r)
  | N13 wx, N8 wy =>
    let (w,r) := w8_mul_add_n1 5 wx wy W0 in
    if w8_eq0 w then N13 r
    else Nn 0 (WW (extend5 w7 w) r)
  | N13 wx, N9 wy =>
    let (w,r) := w9_mul_add_n1 4 wx wy W0 in
    if w9_eq0 w then N13 r
    else Nn 0 (WW (extend4 w8 w) r)
  | N13 wx, N10 wy =>
    let (w,r) := w10_mul_add_n1 3 wx wy W0 in
    if w10_eq0 w then N13 r
    else Nn 0 (WW (extend3 w9 w) r)
  | N13 wx, N11 wy =>
    let (w,r) := w11_mul_add_n1 2 wx wy W0 in
    if w11_eq0 w then N13 r
    else Nn 0 (WW (extend2 w10 w) r)
  | N13 wx, N12 wy =>
    let (w,r) := w12_mul_add_n1 1 wx wy W0 in
    if w12_eq0 w then N13 r
    else Nn 0 (WW (extend1 w11 w) r)
  | N13 wx, N13 wy =>
    Nn 0 (w13_mul_c wx wy)
  | N13 wx, Nn n wy =>
    let (w,r) := w13_mul_add_n1 (S n) wy wx W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | Nn n wx, N0 wy =>
    if w0_eq0 wy then zero
    else
    let (w,r) := w13_mul_add_n1 (S n) wx (extend12 w0 (WW w_0 wy)) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | Nn n wx, N1 wy =>
    let (w,r) := w13_mul_add_n1 (S n) wx (extend12 w0 wy) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | Nn n wx, N2 wy =>
    let (w,r) := w13_mul_add_n1 (S n) wx (extend11 w1 wy) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | Nn n wx, N3 wy =>
    let (w,r) := w13_mul_add_n1 (S n) wx (extend10 w2 wy) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | Nn n wx, N4 wy =>
    let (w,r) := w13_mul_add_n1 (S n) wx (extend9 w3 wy) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | Nn n wx, N5 wy =>
    let (w,r) := w13_mul_add_n1 (S n) wx (extend8 w4 wy) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | Nn n wx, N6 wy =>
    let (w,r) := w13_mul_add_n1 (S n) wx (extend7 w5 wy) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | Nn n wx, N7 wy =>
    let (w,r) := w13_mul_add_n1 (S n) wx (extend6 w6 wy) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | Nn n wx, N8 wy =>
    let (w,r) := w13_mul_add_n1 (S n) wx (extend5 w7 wy) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | Nn n wx, N9 wy =>
    let (w,r) := w13_mul_add_n1 (S n) wx (extend4 w8 wy) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | Nn n wx, N10 wy =>
    let (w,r) := w13_mul_add_n1 (S n) wx (extend3 w9 wy) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | Nn n wx, N11 wy =>
    let (w,r) := w13_mul_add_n1 (S n) wx (extend2 w10 wy) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | Nn n wx, N12 wy =>
    let (w,r) := w13_mul_add_n1 (S n) wx (extend1 w11 wy) W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | Nn n wx, N13 wy =>
    let (w,r) := w13_mul_add_n1 (S n) wx wy W0 in
    if w13_eq0 w then Nn n r
    else Nn (S n) (WW (extend n w13 (WW W0 w)) r)
  | Nn n wx, Nn m wy =>
    let mn := Max.max n m in
    let d := diff n m in
    let op := make_op mn in
     reduce_n (S mn) (op.(znz_mul_c)
       (castm (diff_r n m) (extend_tr wx (snd d)))
       (castm (diff_l n m) (extend_tr wy (fst d))))
  end.

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

 Fixpoint power_pos (x:t) (p:positive) {struct p} : t :=
  match p with
  | xH => x
  | xO p => square (power_pos x p)
  | xI p => mul (square (power_pos x p)) x
  end.

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

 Definition w0_divn1 :=
  gen_divn1 w0_op.(znz_zdigits) w0_op.(znz_0)
    w0_op.(znz_WW) w0_op.(znz_head0)
    w0_op.(znz_add_mul_div) w0_op.(znz_div21)
    w0_op.(znz_compare) w0_op.(znz_sub).
 Definition w1_divn1 :=
  gen_divn1 w1_op.(znz_zdigits) w1_op.(znz_0)
    w1_op.(znz_WW) w1_op.(znz_head0)
    w1_op.(znz_add_mul_div) w1_op.(znz_div21)
    w1_op.(znz_compare) w1_op.(znz_sub).
 Definition w2_divn1 :=
  gen_divn1 w2_op.(znz_zdigits) w2_op.(znz_0)
    w2_op.(znz_WW) w2_op.(znz_head0)
    w2_op.(znz_add_mul_div) w2_op.(znz_div21)
    w2_op.(znz_compare) w2_op.(znz_sub).
 Definition w3_divn1 :=
  gen_divn1 w3_op.(znz_zdigits) w3_op.(znz_0)
    w3_op.(znz_WW) w3_op.(znz_head0)
    w3_op.(znz_add_mul_div) w3_op.(znz_div21)
    w3_op.(znz_compare) w3_op.(znz_sub).
 Definition w4_divn1 :=
  gen_divn1 w4_op.(znz_zdigits) w4_op.(znz_0)
    w4_op.(znz_WW) w4_op.(znz_head0)
    w4_op.(znz_add_mul_div) w4_op.(znz_div21)
    w4_op.(znz_compare) w4_op.(znz_sub).
 Definition w5_divn1 :=
  gen_divn1 w5_op.(znz_zdigits) w5_op.(znz_0)
    w5_op.(znz_WW) w5_op.(znz_head0)
    w5_op.(znz_add_mul_div) w5_op.(znz_div21)
    w5_op.(znz_compare) w5_op.(znz_sub).
 Definition w6_divn1 :=
  gen_divn1 w6_op.(znz_zdigits) w6_op.(znz_0)
    w6_op.(znz_WW) w6_op.(znz_head0)
    w6_op.(znz_add_mul_div) w6_op.(znz_div21)
    w6_op.(znz_compare) w6_op.(znz_sub).
 Definition w7_divn1 :=
  gen_divn1 w7_op.(znz_zdigits) w7_op.(znz_0)
    w7_op.(znz_WW) w7_op.(znz_head0)
    w7_op.(znz_add_mul_div) w7_op.(znz_div21)
    w7_op.(znz_compare) w7_op.(znz_sub).
 Definition w8_divn1 :=
  gen_divn1 w8_op.(znz_zdigits) w8_op.(znz_0)
    w8_op.(znz_WW) w8_op.(znz_head0)
    w8_op.(znz_add_mul_div) w8_op.(znz_div21)
    w8_op.(znz_compare) w8_op.(znz_sub).
 Definition w9_divn1 :=
  gen_divn1 w9_op.(znz_zdigits) w9_op.(znz_0)
    w9_op.(znz_WW) w9_op.(znz_head0)
    w9_op.(znz_add_mul_div) w9_op.(znz_div21)
    w9_op.(znz_compare) w9_op.(znz_sub).
 Definition w10_divn1 :=
  gen_divn1 w10_op.(znz_zdigits) w10_op.(znz_0)
    w10_op.(znz_WW) w10_op.(znz_head0)
    w10_op.(znz_add_mul_div) w10_op.(znz_div21)
    w10_op.(znz_compare) w10_op.(znz_sub).
 Definition w11_divn1 :=
  gen_divn1 w11_op.(znz_zdigits) w11_op.(znz_0)
    w11_op.(znz_WW) w11_op.(znz_head0)
    w11_op.(znz_add_mul_div) w11_op.(znz_div21)
    w11_op.(znz_compare) w11_op.(znz_sub).
 Definition w12_divn1 :=
  gen_divn1 w12_op.(znz_zdigits) w12_op.(znz_0)
    w12_op.(znz_WW) w12_op.(znz_head0)
    w12_op.(znz_add_mul_div) w12_op.(znz_div21)
    w12_op.(znz_compare) w12_op.(znz_sub).
 Definition w13_divn1 :=
  gen_divn1 w13_op.(znz_zdigits) w13_op.(znz_0)
    w13_op.(znz_WW) w13_op.(znz_head0)
    w13_op.(znz_add_mul_div) w13_op.(znz_div21)
    w13_op.(znz_compare) w13_op.(znz_sub).

 Definition div_gt x y :=
  match x, y with
  | N0 wx, N0 wy => let (q, r):= w0_div_gt wx wy in (reduce_0 q, reduce_0 r)
  | N0 wx, N1 wy =>
    let wx':= GenBase.extend w0_0W 0 wx in
    let (q, r):= w1_div_gt wx' wy in
    (reduce_1 q, reduce_1 r)
  | N0 wx, N2 wy =>
    let wx':= GenBase.extend w0_0W 1 wx in
    let (q, r):= w2_div_gt wx' wy in
    (reduce_2 q, reduce_2 r)
  | N0 wx, N3 wy =>
    let wx':= GenBase.extend w0_0W 2 wx in
    let (q, r):= w3_div_gt wx' wy in
    (reduce_3 q, reduce_3 r)
  | N0 wx, N4 wy =>
    let wx':= GenBase.extend w0_0W 3 wx in
    let (q, r):= w4_div_gt wx' wy in
    (reduce_4 q, reduce_4 r)
  | N0 wx, N5 wy =>
    let wx':= GenBase.extend w0_0W 4 wx in
    let (q, r):= w5_div_gt wx' wy in
    (reduce_5 q, reduce_5 r)
  | N0 wx, N6 wy =>
    let wx':= GenBase.extend w0_0W 5 wx in
    let (q, r):= w6_div_gt wx' wy in
    (reduce_6 q, reduce_6 r)
  | N0 wx, N7 wy =>
    let wx':= GenBase.extend w0_0W 6 wx in
    let (q, r):= w7_div_gt wx' wy in
    (reduce_7 q, reduce_7 r)
  | N0 wx, N8 wy =>
    let wx':= GenBase.extend w0_0W 7 wx in
    let (q, r):= w8_div_gt wx' wy in
    (reduce_8 q, reduce_8 r)
  | N0 wx, N9 wy =>
    let wx':= GenBase.extend w0_0W 8 wx in
    let (q, r):= w9_div_gt wx' wy in
    (reduce_9 q, reduce_9 r)
  | N0 wx, N10 wy =>
    let wx':= GenBase.extend w0_0W 9 wx in
    let (q, r):= w10_div_gt wx' wy in
    (reduce_10 q, reduce_10 r)
  | N0 wx, N11 wy =>
    let wx':= GenBase.extend w0_0W 10 wx in
    let (q, r):= w11_div_gt wx' wy in
    (reduce_11 q, reduce_11 r)
  | N0 wx, N12 wy =>
    let wx':= GenBase.extend w0_0W 11 wx in
    let (q, r):= w12_div_gt wx' wy in
    (reduce_12 q, reduce_12 r)
  | N0 wx, N13 wy =>
    let wx':= GenBase.extend w0_0W 12 wx in
    let (q, r):= w13_div_gt wx' wy in
    (reduce_13 q, reduce_13 r)
  | N0 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w0_0W 13 wx) in
    let (q, r):= (make_op n).(znz_div_gt) wx' wy in
    (reduce_n n q, reduce_n n r)
  | N1 wx, N0 wy => let (q, r):= w0_divn1 1 wx wy in (reduce_1 q, reduce_0 r)
  | N1 wx, N1 wy => let (q, r):= w1_div_gt wx wy in (reduce_1 q, reduce_1 r)
  | N1 wx, N2 wy =>
    let wx':= GenBase.extend w1_0W 0 wx in
    let (q, r):= w2_div_gt wx' wy in
    (reduce_2 q, reduce_2 r)
  | N1 wx, N3 wy =>
    let wx':= GenBase.extend w1_0W 1 wx in
    let (q, r):= w3_div_gt wx' wy in
    (reduce_3 q, reduce_3 r)
  | N1 wx, N4 wy =>
    let wx':= GenBase.extend w1_0W 2 wx in
    let (q, r):= w4_div_gt wx' wy in
    (reduce_4 q, reduce_4 r)
  | N1 wx, N5 wy =>
    let wx':= GenBase.extend w1_0W 3 wx in
    let (q, r):= w5_div_gt wx' wy in
    (reduce_5 q, reduce_5 r)
  | N1 wx, N6 wy =>
    let wx':= GenBase.extend w1_0W 4 wx in
    let (q, r):= w6_div_gt wx' wy in
    (reduce_6 q, reduce_6 r)
  | N1 wx, N7 wy =>
    let wx':= GenBase.extend w1_0W 5 wx in
    let (q, r):= w7_div_gt wx' wy in
    (reduce_7 q, reduce_7 r)
  | N1 wx, N8 wy =>
    let wx':= GenBase.extend w1_0W 6 wx in
    let (q, r):= w8_div_gt wx' wy in
    (reduce_8 q, reduce_8 r)
  | N1 wx, N9 wy =>
    let wx':= GenBase.extend w1_0W 7 wx in
    let (q, r):= w9_div_gt wx' wy in
    (reduce_9 q, reduce_9 r)
  | N1 wx, N10 wy =>
    let wx':= GenBase.extend w1_0W 8 wx in
    let (q, r):= w10_div_gt wx' wy in
    (reduce_10 q, reduce_10 r)
  | N1 wx, N11 wy =>
    let wx':= GenBase.extend w1_0W 9 wx in
    let (q, r):= w11_div_gt wx' wy in
    (reduce_11 q, reduce_11 r)
  | N1 wx, N12 wy =>
    let wx':= GenBase.extend w1_0W 10 wx in
    let (q, r):= w12_div_gt wx' wy in
    (reduce_12 q, reduce_12 r)
  | N1 wx, N13 wy =>
    let wx':= GenBase.extend w1_0W 11 wx in
    let (q, r):= w13_div_gt wx' wy in
    (reduce_13 q, reduce_13 r)
  | N1 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w1_0W 12 wx) in
    let (q, r):= (make_op n).(znz_div_gt) wx' wy in
    (reduce_n n q, reduce_n n r)
  | N2 wx, N0 wy => let (q, r):= w0_divn1 2 wx wy in (reduce_2 q, reduce_0 r)
  | N2 wx, N1 wy => let (q, r):= w1_divn1 1 wx wy in (reduce_2 q, reduce_1 r)
  | N2 wx, N2 wy => let (q, r):= w2_div_gt wx wy in (reduce_2 q, reduce_2 r)
  | N2 wx, N3 wy =>
    let wx':= GenBase.extend w2_0W 0 wx in
    let (q, r):= w3_div_gt wx' wy in
    (reduce_3 q, reduce_3 r)
  | N2 wx, N4 wy =>
    let wx':= GenBase.extend w2_0W 1 wx in
    let (q, r):= w4_div_gt wx' wy in
    (reduce_4 q, reduce_4 r)
  | N2 wx, N5 wy =>
    let wx':= GenBase.extend w2_0W 2 wx in
    let (q, r):= w5_div_gt wx' wy in
    (reduce_5 q, reduce_5 r)
  | N2 wx, N6 wy =>
    let wx':= GenBase.extend w2_0W 3 wx in
    let (q, r):= w6_div_gt wx' wy in
    (reduce_6 q, reduce_6 r)
  | N2 wx, N7 wy =>
    let wx':= GenBase.extend w2_0W 4 wx in
    let (q, r):= w7_div_gt wx' wy in
    (reduce_7 q, reduce_7 r)
  | N2 wx, N8 wy =>
    let wx':= GenBase.extend w2_0W 5 wx in
    let (q, r):= w8_div_gt wx' wy in
    (reduce_8 q, reduce_8 r)
  | N2 wx, N9 wy =>
    let wx':= GenBase.extend w2_0W 6 wx in
    let (q, r):= w9_div_gt wx' wy in
    (reduce_9 q, reduce_9 r)
  | N2 wx, N10 wy =>
    let wx':= GenBase.extend w2_0W 7 wx in
    let (q, r):= w10_div_gt wx' wy in
    (reduce_10 q, reduce_10 r)
  | N2 wx, N11 wy =>
    let wx':= GenBase.extend w2_0W 8 wx in
    let (q, r):= w11_div_gt wx' wy in
    (reduce_11 q, reduce_11 r)
  | N2 wx, N12 wy =>
    let wx':= GenBase.extend w2_0W 9 wx in
    let (q, r):= w12_div_gt wx' wy in
    (reduce_12 q, reduce_12 r)
  | N2 wx, N13 wy =>
    let wx':= GenBase.extend w2_0W 10 wx in
    let (q, r):= w13_div_gt wx' wy in
    (reduce_13 q, reduce_13 r)
  | N2 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w2_0W 11 wx) in
    let (q, r):= (make_op n).(znz_div_gt) wx' wy in
    (reduce_n n q, reduce_n n r)
  | N3 wx, N0 wy => let (q, r):= w0_divn1 3 wx wy in (reduce_3 q, reduce_0 r)
  | N3 wx, N1 wy => let (q, r):= w1_divn1 2 wx wy in (reduce_3 q, reduce_1 r)
  | N3 wx, N2 wy => let (q, r):= w2_divn1 1 wx wy in (reduce_3 q, reduce_2 r)
  | N3 wx, N3 wy => let (q, r):= w3_div_gt wx wy in (reduce_3 q, reduce_3 r)
  | N3 wx, N4 wy =>
    let wx':= GenBase.extend w3_0W 0 wx in
    let (q, r):= w4_div_gt wx' wy in
    (reduce_4 q, reduce_4 r)
  | N3 wx, N5 wy =>
    let wx':= GenBase.extend w3_0W 1 wx in
    let (q, r):= w5_div_gt wx' wy in
    (reduce_5 q, reduce_5 r)
  | N3 wx, N6 wy =>
    let wx':= GenBase.extend w3_0W 2 wx in
    let (q, r):= w6_div_gt wx' wy in
    (reduce_6 q, reduce_6 r)
  | N3 wx, N7 wy =>
    let wx':= GenBase.extend w3_0W 3 wx in
    let (q, r):= w7_div_gt wx' wy in
    (reduce_7 q, reduce_7 r)
  | N3 wx, N8 wy =>
    let wx':= GenBase.extend w3_0W 4 wx in
    let (q, r):= w8_div_gt wx' wy in
    (reduce_8 q, reduce_8 r)
  | N3 wx, N9 wy =>
    let wx':= GenBase.extend w3_0W 5 wx in
    let (q, r):= w9_div_gt wx' wy in
    (reduce_9 q, reduce_9 r)
  | N3 wx, N10 wy =>
    let wx':= GenBase.extend w3_0W 6 wx in
    let (q, r):= w10_div_gt wx' wy in
    (reduce_10 q, reduce_10 r)
  | N3 wx, N11 wy =>
    let wx':= GenBase.extend w3_0W 7 wx in
    let (q, r):= w11_div_gt wx' wy in
    (reduce_11 q, reduce_11 r)
  | N3 wx, N12 wy =>
    let wx':= GenBase.extend w3_0W 8 wx in
    let (q, r):= w12_div_gt wx' wy in
    (reduce_12 q, reduce_12 r)
  | N3 wx, N13 wy =>
    let wx':= GenBase.extend w3_0W 9 wx in
    let (q, r):= w13_div_gt wx' wy in
    (reduce_13 q, reduce_13 r)
  | N3 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w3_0W 10 wx) in
    let (q, r):= (make_op n).(znz_div_gt) wx' wy in
    (reduce_n n q, reduce_n n r)
  | N4 wx, N0 wy => let (q, r):= w0_divn1 4 wx wy in (reduce_4 q, reduce_0 r)
  | N4 wx, N1 wy => let (q, r):= w1_divn1 3 wx wy in (reduce_4 q, reduce_1 r)
  | N4 wx, N2 wy => let (q, r):= w2_divn1 2 wx wy in (reduce_4 q, reduce_2 r)
  | N4 wx, N3 wy => let (q, r):= w3_divn1 1 wx wy in (reduce_4 q, reduce_3 r)
  | N4 wx, N4 wy => let (q, r):= w4_div_gt wx wy in (reduce_4 q, reduce_4 r)
  | N4 wx, N5 wy =>
    let wx':= GenBase.extend w4_0W 0 wx in
    let (q, r):= w5_div_gt wx' wy in
    (reduce_5 q, reduce_5 r)
  | N4 wx, N6 wy =>
    let wx':= GenBase.extend w4_0W 1 wx in
    let (q, r):= w6_div_gt wx' wy in
    (reduce_6 q, reduce_6 r)
  | N4 wx, N7 wy =>
    let wx':= GenBase.extend w4_0W 2 wx in
    let (q, r):= w7_div_gt wx' wy in
    (reduce_7 q, reduce_7 r)
  | N4 wx, N8 wy =>
    let wx':= GenBase.extend w4_0W 3 wx in
    let (q, r):= w8_div_gt wx' wy in
    (reduce_8 q, reduce_8 r)
  | N4 wx, N9 wy =>
    let wx':= GenBase.extend w4_0W 4 wx in
    let (q, r):= w9_div_gt wx' wy in
    (reduce_9 q, reduce_9 r)
  | N4 wx, N10 wy =>
    let wx':= GenBase.extend w4_0W 5 wx in
    let (q, r):= w10_div_gt wx' wy in
    (reduce_10 q, reduce_10 r)
  | N4 wx, N11 wy =>
    let wx':= GenBase.extend w4_0W 6 wx in
    let (q, r):= w11_div_gt wx' wy in
    (reduce_11 q, reduce_11 r)
  | N4 wx, N12 wy =>
    let wx':= GenBase.extend w4_0W 7 wx in
    let (q, r):= w12_div_gt wx' wy in
    (reduce_12 q, reduce_12 r)
  | N4 wx, N13 wy =>
    let wx':= GenBase.extend w4_0W 8 wx in
    let (q, r):= w13_div_gt wx' wy in
    (reduce_13 q, reduce_13 r)
  | N4 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w4_0W 9 wx) in
    let (q, r):= (make_op n).(znz_div_gt) wx' wy in
    (reduce_n n q, reduce_n n r)
  | N5 wx, N0 wy => let (q, r):= w0_divn1 5 wx wy in (reduce_5 q, reduce_0 r)
  | N5 wx, N1 wy => let (q, r):= w1_divn1 4 wx wy in (reduce_5 q, reduce_1 r)
  | N5 wx, N2 wy => let (q, r):= w2_divn1 3 wx wy in (reduce_5 q, reduce_2 r)
  | N5 wx, N3 wy => let (q, r):= w3_divn1 2 wx wy in (reduce_5 q, reduce_3 r)
  | N5 wx, N4 wy => let (q, r):= w4_divn1 1 wx wy in (reduce_5 q, reduce_4 r)
  | N5 wx, N5 wy => let (q, r):= w5_div_gt wx wy in (reduce_5 q, reduce_5 r)
  | N5 wx, N6 wy =>
    let wx':= GenBase.extend w5_0W 0 wx in
    let (q, r):= w6_div_gt wx' wy in
    (reduce_6 q, reduce_6 r)
  | N5 wx, N7 wy =>
    let wx':= GenBase.extend w5_0W 1 wx in
    let (q, r):= w7_div_gt wx' wy in
    (reduce_7 q, reduce_7 r)
  | N5 wx, N8 wy =>
    let wx':= GenBase.extend w5_0W 2 wx in
    let (q, r):= w8_div_gt wx' wy in
    (reduce_8 q, reduce_8 r)
  | N5 wx, N9 wy =>
    let wx':= GenBase.extend w5_0W 3 wx in
    let (q, r):= w9_div_gt wx' wy in
    (reduce_9 q, reduce_9 r)
  | N5 wx, N10 wy =>
    let wx':= GenBase.extend w5_0W 4 wx in
    let (q, r):= w10_div_gt wx' wy in
    (reduce_10 q, reduce_10 r)
  | N5 wx, N11 wy =>
    let wx':= GenBase.extend w5_0W 5 wx in
    let (q, r):= w11_div_gt wx' wy in
    (reduce_11 q, reduce_11 r)
  | N5 wx, N12 wy =>
    let wx':= GenBase.extend w5_0W 6 wx in
    let (q, r):= w12_div_gt wx' wy in
    (reduce_12 q, reduce_12 r)
  | N5 wx, N13 wy =>
    let wx':= GenBase.extend w5_0W 7 wx in
    let (q, r):= w13_div_gt wx' wy in
    (reduce_13 q, reduce_13 r)
  | N5 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w5_0W 8 wx) in
    let (q, r):= (make_op n).(znz_div_gt) wx' wy in
    (reduce_n n q, reduce_n n r)
  | N6 wx, N0 wy => let (q, r):= w0_divn1 6 wx wy in (reduce_6 q, reduce_0 r)
  | N6 wx, N1 wy => let (q, r):= w1_divn1 5 wx wy in (reduce_6 q, reduce_1 r)
  | N6 wx, N2 wy => let (q, r):= w2_divn1 4 wx wy in (reduce_6 q, reduce_2 r)
  | N6 wx, N3 wy => let (q, r):= w3_divn1 3 wx wy in (reduce_6 q, reduce_3 r)
  | N6 wx, N4 wy => let (q, r):= w4_divn1 2 wx wy in (reduce_6 q, reduce_4 r)
  | N6 wx, N5 wy => let (q, r):= w5_divn1 1 wx wy in (reduce_6 q, reduce_5 r)
  | N6 wx, N6 wy => let (q, r):= w6_div_gt wx wy in (reduce_6 q, reduce_6 r)
  | N6 wx, N7 wy =>
    let wx':= GenBase.extend w6_0W 0 wx in
    let (q, r):= w7_div_gt wx' wy in
    (reduce_7 q, reduce_7 r)
  | N6 wx, N8 wy =>
    let wx':= GenBase.extend w6_0W 1 wx in
    let (q, r):= w8_div_gt wx' wy in
    (reduce_8 q, reduce_8 r)
  | N6 wx, N9 wy =>
    let wx':= GenBase.extend w6_0W 2 wx in
    let (q, r):= w9_div_gt wx' wy in
    (reduce_9 q, reduce_9 r)
  | N6 wx, N10 wy =>
    let wx':= GenBase.extend w6_0W 3 wx in
    let (q, r):= w10_div_gt wx' wy in
    (reduce_10 q, reduce_10 r)
  | N6 wx, N11 wy =>
    let wx':= GenBase.extend w6_0W 4 wx in
    let (q, r):= w11_div_gt wx' wy in
    (reduce_11 q, reduce_11 r)
  | N6 wx, N12 wy =>
    let wx':= GenBase.extend w6_0W 5 wx in
    let (q, r):= w12_div_gt wx' wy in
    (reduce_12 q, reduce_12 r)
  | N6 wx, N13 wy =>
    let wx':= GenBase.extend w6_0W 6 wx in
    let (q, r):= w13_div_gt wx' wy in
    (reduce_13 q, reduce_13 r)
  | N6 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w6_0W 7 wx) in
    let (q, r):= (make_op n).(znz_div_gt) wx' wy in
    (reduce_n n q, reduce_n n r)
  | N7 wx, N0 wy => let (q, r):= w0_divn1 7 wx wy in (reduce_7 q, reduce_0 r)
  | N7 wx, N1 wy => let (q, r):= w1_divn1 6 wx wy in (reduce_7 q, reduce_1 r)
  | N7 wx, N2 wy => let (q, r):= w2_divn1 5 wx wy in (reduce_7 q, reduce_2 r)
  | N7 wx, N3 wy => let (q, r):= w3_divn1 4 wx wy in (reduce_7 q, reduce_3 r)
  | N7 wx, N4 wy => let (q, r):= w4_divn1 3 wx wy in (reduce_7 q, reduce_4 r)
  | N7 wx, N5 wy => let (q, r):= w5_divn1 2 wx wy in (reduce_7 q, reduce_5 r)
  | N7 wx, N6 wy => let (q, r):= w6_divn1 1 wx wy in (reduce_7 q, reduce_6 r)
  | N7 wx, N7 wy => let (q, r):= w7_div_gt wx wy in (reduce_7 q, reduce_7 r)
  | N7 wx, N8 wy =>
    let wx':= GenBase.extend w7_0W 0 wx in
    let (q, r):= w8_div_gt wx' wy in
    (reduce_8 q, reduce_8 r)
  | N7 wx, N9 wy =>
    let wx':= GenBase.extend w7_0W 1 wx in
    let (q, r):= w9_div_gt wx' wy in
    (reduce_9 q, reduce_9 r)
  | N7 wx, N10 wy =>
    let wx':= GenBase.extend w7_0W 2 wx in
    let (q, r):= w10_div_gt wx' wy in
    (reduce_10 q, reduce_10 r)
  | N7 wx, N11 wy =>
    let wx':= GenBase.extend w7_0W 3 wx in
    let (q, r):= w11_div_gt wx' wy in
    (reduce_11 q, reduce_11 r)
  | N7 wx, N12 wy =>
    let wx':= GenBase.extend w7_0W 4 wx in
    let (q, r):= w12_div_gt wx' wy in
    (reduce_12 q, reduce_12 r)
  | N7 wx, N13 wy =>
    let wx':= GenBase.extend w7_0W 5 wx in
    let (q, r):= w13_div_gt wx' wy in
    (reduce_13 q, reduce_13 r)
  | N7 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w7_0W 6 wx) in
    let (q, r):= (make_op n).(znz_div_gt) wx' wy in
    (reduce_n n q, reduce_n n r)
  | N8 wx, N0 wy => let (q, r):= w0_divn1 8 wx wy in (reduce_8 q, reduce_0 r)
  | N8 wx, N1 wy => let (q, r):= w1_divn1 7 wx wy in (reduce_8 q, reduce_1 r)
  | N8 wx, N2 wy => let (q, r):= w2_divn1 6 wx wy in (reduce_8 q, reduce_2 r)
  | N8 wx, N3 wy => let (q, r):= w3_divn1 5 wx wy in (reduce_8 q, reduce_3 r)
  | N8 wx, N4 wy => let (q, r):= w4_divn1 4 wx wy in (reduce_8 q, reduce_4 r)
  | N8 wx, N5 wy => let (q, r):= w5_divn1 3 wx wy in (reduce_8 q, reduce_5 r)
  | N8 wx, N6 wy => let (q, r):= w6_divn1 2 wx wy in (reduce_8 q, reduce_6 r)
  | N8 wx, N7 wy => let (q, r):= w7_divn1 1 wx wy in (reduce_8 q, reduce_7 r)
  | N8 wx, N8 wy => let (q, r):= w8_div_gt wx wy in (reduce_8 q, reduce_8 r)
  | N8 wx, N9 wy =>
    let wx':= GenBase.extend w8_0W 0 wx in
    let (q, r):= w9_div_gt wx' wy in
    (reduce_9 q, reduce_9 r)
  | N8 wx, N10 wy =>
    let wx':= GenBase.extend w8_0W 1 wx in
    let (q, r):= w10_div_gt wx' wy in
    (reduce_10 q, reduce_10 r)
  | N8 wx, N11 wy =>
    let wx':= GenBase.extend w8_0W 2 wx in
    let (q, r):= w11_div_gt wx' wy in
    (reduce_11 q, reduce_11 r)
  | N8 wx, N12 wy =>
    let wx':= GenBase.extend w8_0W 3 wx in
    let (q, r):= w12_div_gt wx' wy in
    (reduce_12 q, reduce_12 r)
  | N8 wx, N13 wy =>
    let wx':= GenBase.extend w8_0W 4 wx in
    let (q, r):= w13_div_gt wx' wy in
    (reduce_13 q, reduce_13 r)
  | N8 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w8_0W 5 wx) in
    let (q, r):= (make_op n).(znz_div_gt) wx' wy in
    (reduce_n n q, reduce_n n r)
  | N9 wx, N0 wy => let (q, r):= w0_divn1 9 wx wy in (reduce_9 q, reduce_0 r)
  | N9 wx, N1 wy => let (q, r):= w1_divn1 8 wx wy in (reduce_9 q, reduce_1 r)
  | N9 wx, N2 wy => let (q, r):= w2_divn1 7 wx wy in (reduce_9 q, reduce_2 r)
  | N9 wx, N3 wy => let (q, r):= w3_divn1 6 wx wy in (reduce_9 q, reduce_3 r)
  | N9 wx, N4 wy => let (q, r):= w4_divn1 5 wx wy in (reduce_9 q, reduce_4 r)
  | N9 wx, N5 wy => let (q, r):= w5_divn1 4 wx wy in (reduce_9 q, reduce_5 r)
  | N9 wx, N6 wy => let (q, r):= w6_divn1 3 wx wy in (reduce_9 q, reduce_6 r)
  | N9 wx, N7 wy => let (q, r):= w7_divn1 2 wx wy in (reduce_9 q, reduce_7 r)
  | N9 wx, N8 wy => let (q, r):= w8_divn1 1 wx wy in (reduce_9 q, reduce_8 r)
  | N9 wx, N9 wy => let (q, r):= w9_div_gt wx wy in (reduce_9 q, reduce_9 r)
  | N9 wx, N10 wy =>
    let wx':= GenBase.extend w9_0W 0 wx in
    let (q, r):= w10_div_gt wx' wy in
    (reduce_10 q, reduce_10 r)
  | N9 wx, N11 wy =>
    let wx':= GenBase.extend w9_0W 1 wx in
    let (q, r):= w11_div_gt wx' wy in
    (reduce_11 q, reduce_11 r)
  | N9 wx, N12 wy =>
    let wx':= GenBase.extend w9_0W 2 wx in
    let (q, r):= w12_div_gt wx' wy in
    (reduce_12 q, reduce_12 r)
  | N9 wx, N13 wy =>
    let wx':= GenBase.extend w9_0W 3 wx in
    let (q, r):= w13_div_gt wx' wy in
    (reduce_13 q, reduce_13 r)
  | N9 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w9_0W 4 wx) in
    let (q, r):= (make_op n).(znz_div_gt) wx' wy in
    (reduce_n n q, reduce_n n r)
  | N10 wx, N0 wy => let (q, r):= w0_divn1 10 wx wy in (reduce_10 q, reduce_0 r)
  | N10 wx, N1 wy => let (q, r):= w1_divn1 9 wx wy in (reduce_10 q, reduce_1 r)
  | N10 wx, N2 wy => let (q, r):= w2_divn1 8 wx wy in (reduce_10 q, reduce_2 r)
  | N10 wx, N3 wy => let (q, r):= w3_divn1 7 wx wy in (reduce_10 q, reduce_3 r)
  | N10 wx, N4 wy => let (q, r):= w4_divn1 6 wx wy in (reduce_10 q, reduce_4 r)
  | N10 wx, N5 wy => let (q, r):= w5_divn1 5 wx wy in (reduce_10 q, reduce_5 r)
  | N10 wx, N6 wy => let (q, r):= w6_divn1 4 wx wy in (reduce_10 q, reduce_6 r)
  | N10 wx, N7 wy => let (q, r):= w7_divn1 3 wx wy in (reduce_10 q, reduce_7 r)
  | N10 wx, N8 wy => let (q, r):= w8_divn1 2 wx wy in (reduce_10 q, reduce_8 r)
  | N10 wx, N9 wy => let (q, r):= w9_divn1 1 wx wy in (reduce_10 q, reduce_9 r)
  | N10 wx, N10 wy => let (q, r):= w10_div_gt wx wy in (reduce_10 q, reduce_10 r)
  | N10 wx, N11 wy =>
    let wx':= GenBase.extend w10_0W 0 wx in
    let (q, r):= w11_div_gt wx' wy in
    (reduce_11 q, reduce_11 r)
  | N10 wx, N12 wy =>
    let wx':= GenBase.extend w10_0W 1 wx in
    let (q, r):= w12_div_gt wx' wy in
    (reduce_12 q, reduce_12 r)
  | N10 wx, N13 wy =>
    let wx':= GenBase.extend w10_0W 2 wx in
    let (q, r):= w13_div_gt wx' wy in
    (reduce_13 q, reduce_13 r)
  | N10 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w10_0W 3 wx) in
    let (q, r):= (make_op n).(znz_div_gt) wx' wy in
    (reduce_n n q, reduce_n n r)
  | N11 wx, N0 wy => let (q, r):= w0_divn1 11 wx wy in (reduce_11 q, reduce_0 r)
  | N11 wx, N1 wy => let (q, r):= w1_divn1 10 wx wy in (reduce_11 q, reduce_1 r)
  | N11 wx, N2 wy => let (q, r):= w2_divn1 9 wx wy in (reduce_11 q, reduce_2 r)
  | N11 wx, N3 wy => let (q, r):= w3_divn1 8 wx wy in (reduce_11 q, reduce_3 r)
  | N11 wx, N4 wy => let (q, r):= w4_divn1 7 wx wy in (reduce_11 q, reduce_4 r)
  | N11 wx, N5 wy => let (q, r):= w5_divn1 6 wx wy in (reduce_11 q, reduce_5 r)
  | N11 wx, N6 wy => let (q, r):= w6_divn1 5 wx wy in (reduce_11 q, reduce_6 r)
  | N11 wx, N7 wy => let (q, r):= w7_divn1 4 wx wy in (reduce_11 q, reduce_7 r)
  | N11 wx, N8 wy => let (q, r):= w8_divn1 3 wx wy in (reduce_11 q, reduce_8 r)
  | N11 wx, N9 wy => let (q, r):= w9_divn1 2 wx wy in (reduce_11 q, reduce_9 r)
  | N11 wx, N10 wy => let (q, r):= w10_divn1 1 wx wy in (reduce_11 q, reduce_10 r)
  | N11 wx, N11 wy => let (q, r):= w11_div_gt wx wy in (reduce_11 q, reduce_11 r)
  | N11 wx, N12 wy =>
    let wx':= GenBase.extend w11_0W 0 wx in
    let (q, r):= w12_div_gt wx' wy in
    (reduce_12 q, reduce_12 r)
  | N11 wx, N13 wy =>
    let wx':= GenBase.extend w11_0W 1 wx in
    let (q, r):= w13_div_gt wx' wy in
    (reduce_13 q, reduce_13 r)
  | N11 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w11_0W 2 wx) in
    let (q, r):= (make_op n).(znz_div_gt) wx' wy in
    (reduce_n n q, reduce_n n r)
  | N12 wx, N0 wy => let (q, r):= w0_divn1 12 wx wy in (reduce_12 q, reduce_0 r)
  | N12 wx, N1 wy => let (q, r):= w1_divn1 11 wx wy in (reduce_12 q, reduce_1 r)
  | N12 wx, N2 wy => let (q, r):= w2_divn1 10 wx wy in (reduce_12 q, reduce_2 r)
  | N12 wx, N3 wy => let (q, r):= w3_divn1 9 wx wy in (reduce_12 q, reduce_3 r)
  | N12 wx, N4 wy => let (q, r):= w4_divn1 8 wx wy in (reduce_12 q, reduce_4 r)
  | N12 wx, N5 wy => let (q, r):= w5_divn1 7 wx wy in (reduce_12 q, reduce_5 r)
  | N12 wx, N6 wy => let (q, r):= w6_divn1 6 wx wy in (reduce_12 q, reduce_6 r)
  | N12 wx, N7 wy => let (q, r):= w7_divn1 5 wx wy in (reduce_12 q, reduce_7 r)
  | N12 wx, N8 wy => let (q, r):= w8_divn1 4 wx wy in (reduce_12 q, reduce_8 r)
  | N12 wx, N9 wy => let (q, r):= w9_divn1 3 wx wy in (reduce_12 q, reduce_9 r)
  | N12 wx, N10 wy => let (q, r):= w10_divn1 2 wx wy in (reduce_12 q, reduce_10 r)
  | N12 wx, N11 wy => let (q, r):= w11_divn1 1 wx wy in (reduce_12 q, reduce_11 r)
  | N12 wx, N12 wy => let (q, r):= w12_div_gt wx wy in (reduce_12 q, reduce_12 r)
  | N12 wx, N13 wy =>
    let wx':= GenBase.extend w12_0W 0 wx in
    let (q, r):= w13_div_gt wx' wy in
    (reduce_13 q, reduce_13 r)
  | N12 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w12_0W 1 wx) in
    let (q, r):= (make_op n).(znz_div_gt) wx' wy in
    (reduce_n n q, reduce_n n r)
  | N13 wx, N0 wy => let (q, r):= w0_divn1 13 wx wy in (reduce_13 q, reduce_0 r)
  | N13 wx, N1 wy => let (q, r):= w1_divn1 12 wx wy in (reduce_13 q, reduce_1 r)
  | N13 wx, N2 wy => let (q, r):= w2_divn1 11 wx wy in (reduce_13 q, reduce_2 r)
  | N13 wx, N3 wy => let (q, r):= w3_divn1 10 wx wy in (reduce_13 q, reduce_3 r)
  | N13 wx, N4 wy => let (q, r):= w4_divn1 9 wx wy in (reduce_13 q, reduce_4 r)
  | N13 wx, N5 wy => let (q, r):= w5_divn1 8 wx wy in (reduce_13 q, reduce_5 r)
  | N13 wx, N6 wy => let (q, r):= w6_divn1 7 wx wy in (reduce_13 q, reduce_6 r)
  | N13 wx, N7 wy => let (q, r):= w7_divn1 6 wx wy in (reduce_13 q, reduce_7 r)
  | N13 wx, N8 wy => let (q, r):= w8_divn1 5 wx wy in (reduce_13 q, reduce_8 r)
  | N13 wx, N9 wy => let (q, r):= w9_divn1 4 wx wy in (reduce_13 q, reduce_9 r)
  | N13 wx, N10 wy => let (q, r):= w10_divn1 3 wx wy in (reduce_13 q, reduce_10 r)
  | N13 wx, N11 wy => let (q, r):= w11_divn1 2 wx wy in (reduce_13 q, reduce_11 r)
  | N13 wx, N12 wy => let (q, r):= w12_divn1 1 wx wy in (reduce_13 q, reduce_12 r)
  | N13 wx, N13 wy => let (q, r):= w13_div_gt wx wy in (reduce_13 q, reduce_13 r)
  | N13 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w13_0W 0 wx) in
    let (q, r):= (make_op n).(znz_div_gt) wx' wy in
    (reduce_n n q, reduce_n n r)
  | Nn n wx, N0 wy =>
    let wy':= GenBase.extend w0_0W 12 wy in
    let (q, r):= w13_divn1 (S n) wx wy' in
    (reduce_n n q, reduce_13 r)
  | Nn n wx, N1 wy =>
    let wy':= GenBase.extend w1_0W 11 wy in
    let (q, r):= w13_divn1 (S n) wx wy' in
    (reduce_n n q, reduce_13 r)
  | Nn n wx, N2 wy =>
    let wy':= GenBase.extend w2_0W 10 wy in
    let (q, r):= w13_divn1 (S n) wx wy' in
    (reduce_n n q, reduce_13 r)
  | Nn n wx, N3 wy =>
    let wy':= GenBase.extend w3_0W 9 wy in
    let (q, r):= w13_divn1 (S n) wx wy' in
    (reduce_n n q, reduce_13 r)
  | Nn n wx, N4 wy =>
    let wy':= GenBase.extend w4_0W 8 wy in
    let (q, r):= w13_divn1 (S n) wx wy' in
    (reduce_n n q, reduce_13 r)
  | Nn n wx, N5 wy =>
    let wy':= GenBase.extend w5_0W 7 wy in
    let (q, r):= w13_divn1 (S n) wx wy' in
    (reduce_n n q, reduce_13 r)
  | Nn n wx, N6 wy =>
    let wy':= GenBase.extend w6_0W 6 wy in
    let (q, r):= w13_divn1 (S n) wx wy' in
    (reduce_n n q, reduce_13 r)
  | Nn n wx, N7 wy =>
    let wy':= GenBase.extend w7_0W 5 wy in
    let (q, r):= w13_divn1 (S n) wx wy' in
    (reduce_n n q, reduce_13 r)
  | Nn n wx, N8 wy =>
    let wy':= GenBase.extend w8_0W 4 wy in
    let (q, r):= w13_divn1 (S n) wx wy' in
    (reduce_n n q, reduce_13 r)
  | Nn n wx, N9 wy =>
    let wy':= GenBase.extend w9_0W 3 wy in
    let (q, r):= w13_divn1 (S n) wx wy' in
    (reduce_n n q, reduce_13 r)
  | Nn n wx, N10 wy =>
    let wy':= GenBase.extend w10_0W 2 wy in
    let (q, r):= w13_divn1 (S n) wx wy' in
    (reduce_n n q, reduce_13 r)
  | Nn n wx, N11 wy =>
    let wy':= GenBase.extend w11_0W 1 wy in
    let (q, r):= w13_divn1 (S n) wx wy' in
    (reduce_n n q, reduce_13 r)
  | Nn n wx, N12 wy =>
    let wy':= GenBase.extend w12_0W 0 wy in
    let (q, r):= w13_divn1 (S n) wx wy' in
    (reduce_n n q, reduce_13 r)
  | Nn n wx, N13 wy =>
    let wy':= wy in
    let (q, r):= w13_divn1 (S n) wx wy' in
    (reduce_n n q, reduce_13 r)
  | Nn n wx, Nn m wy =>
    let mn := Max.max n m in
    let d := diff n m in
    let op := make_op mn in
    let (q, r):= op.(znz_div)
         (castm (diff_r n m) (extend_tr wx (snd d)))
         (castm (diff_l n m) (extend_tr wy (fst d))) in
    (reduce_n mn q, reduce_n mn r)
  end.

 Definition div_eucl x y :=
  match compare x y with
  | Eq => (one, zero)
  | Lt => (zero, x)
  | Gt => div_gt x y
  end.

 Definition div x y := fst (div_eucl x y).

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

 Definition mod_gt x y :=
  match x, y with
  | N0 wx, N0 wy => reduce_0 (w0_mod_gt wx wy)
  | N0 wx, N1 wy =>
    let wx':= GenBase.extend w0_0W 0 wx in
    reduce_1 (w1_mod_gt wx' wy)
  | N0 wx, N2 wy =>
    let wx':= GenBase.extend w0_0W 1 wx in
    reduce_2 (w2_mod_gt wx' wy)
  | N0 wx, N3 wy =>
    let wx':= GenBase.extend w0_0W 2 wx in
    reduce_3 (w3_mod_gt wx' wy)
  | N0 wx, N4 wy =>
    let wx':= GenBase.extend w0_0W 3 wx in
    reduce_4 (w4_mod_gt wx' wy)
  | N0 wx, N5 wy =>
    let wx':= GenBase.extend w0_0W 4 wx in
    reduce_5 (w5_mod_gt wx' wy)
  | N0 wx, N6 wy =>
    let wx':= GenBase.extend w0_0W 5 wx in
    reduce_6 (w6_mod_gt wx' wy)
  | N0 wx, N7 wy =>
    let wx':= GenBase.extend w0_0W 6 wx in
    reduce_7 (w7_mod_gt wx' wy)
  | N0 wx, N8 wy =>
    let wx':= GenBase.extend w0_0W 7 wx in
    reduce_8 (w8_mod_gt wx' wy)
  | N0 wx, N9 wy =>
    let wx':= GenBase.extend w0_0W 8 wx in
    reduce_9 (w9_mod_gt wx' wy)
  | N0 wx, N10 wy =>
    let wx':= GenBase.extend w0_0W 9 wx in
    reduce_10 (w10_mod_gt wx' wy)
  | N0 wx, N11 wy =>
    let wx':= GenBase.extend w0_0W 10 wx in
    reduce_11 (w11_mod_gt wx' wy)
  | N0 wx, N12 wy =>
    let wx':= GenBase.extend w0_0W 11 wx in
    reduce_12 (w12_mod_gt wx' wy)
  | N0 wx, N13 wy =>
    let wx':= GenBase.extend w0_0W 12 wx in
    reduce_13 (w13_mod_gt wx' wy)
  | N0 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w0_0W 13 wx) in
    reduce_n n ((make_op n).(znz_mod_gt) wx' wy)
  | N1 wx, N0 wy => reduce_0 (w0_modn1 1 wx wy)
  | N1 wx, N1 wy => reduce_1 (w1_mod_gt wx wy)
  | N1 wx, N2 wy =>
    let wx':= GenBase.extend w1_0W 0 wx in
    reduce_2 (w2_mod_gt wx' wy)
  | N1 wx, N3 wy =>
    let wx':= GenBase.extend w1_0W 1 wx in
    reduce_3 (w3_mod_gt wx' wy)
  | N1 wx, N4 wy =>
    let wx':= GenBase.extend w1_0W 2 wx in
    reduce_4 (w4_mod_gt wx' wy)
  | N1 wx, N5 wy =>
    let wx':= GenBase.extend w1_0W 3 wx in
    reduce_5 (w5_mod_gt wx' wy)
  | N1 wx, N6 wy =>
    let wx':= GenBase.extend w1_0W 4 wx in
    reduce_6 (w6_mod_gt wx' wy)
  | N1 wx, N7 wy =>
    let wx':= GenBase.extend w1_0W 5 wx in
    reduce_7 (w7_mod_gt wx' wy)
  | N1 wx, N8 wy =>
    let wx':= GenBase.extend w1_0W 6 wx in
    reduce_8 (w8_mod_gt wx' wy)
  | N1 wx, N9 wy =>
    let wx':= GenBase.extend w1_0W 7 wx in
    reduce_9 (w9_mod_gt wx' wy)
  | N1 wx, N10 wy =>
    let wx':= GenBase.extend w1_0W 8 wx in
    reduce_10 (w10_mod_gt wx' wy)
  | N1 wx, N11 wy =>
    let wx':= GenBase.extend w1_0W 9 wx in
    reduce_11 (w11_mod_gt wx' wy)
  | N1 wx, N12 wy =>
    let wx':= GenBase.extend w1_0W 10 wx in
    reduce_12 (w12_mod_gt wx' wy)
  | N1 wx, N13 wy =>
    let wx':= GenBase.extend w1_0W 11 wx in
    reduce_13 (w13_mod_gt wx' wy)
  | N1 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w1_0W 12 wx) in
    reduce_n n ((make_op n).(znz_mod_gt) wx' wy)
  | N2 wx, N0 wy => reduce_0 (w0_modn1 2 wx wy)
  | N2 wx, N1 wy => reduce_1 (w1_modn1 1 wx wy)
  | N2 wx, N2 wy => reduce_2 (w2_mod_gt wx wy)
  | N2 wx, N3 wy =>
    let wx':= GenBase.extend w2_0W 0 wx in
    reduce_3 (w3_mod_gt wx' wy)
  | N2 wx, N4 wy =>
    let wx':= GenBase.extend w2_0W 1 wx in
    reduce_4 (w4_mod_gt wx' wy)
  | N2 wx, N5 wy =>
    let wx':= GenBase.extend w2_0W 2 wx in
    reduce_5 (w5_mod_gt wx' wy)
  | N2 wx, N6 wy =>
    let wx':= GenBase.extend w2_0W 3 wx in
    reduce_6 (w6_mod_gt wx' wy)
  | N2 wx, N7 wy =>
    let wx':= GenBase.extend w2_0W 4 wx in
    reduce_7 (w7_mod_gt wx' wy)
  | N2 wx, N8 wy =>
    let wx':= GenBase.extend w2_0W 5 wx in
    reduce_8 (w8_mod_gt wx' wy)
  | N2 wx, N9 wy =>
    let wx':= GenBase.extend w2_0W 6 wx in
    reduce_9 (w9_mod_gt wx' wy)
  | N2 wx, N10 wy =>
    let wx':= GenBase.extend w2_0W 7 wx in
    reduce_10 (w10_mod_gt wx' wy)
  | N2 wx, N11 wy =>
    let wx':= GenBase.extend w2_0W 8 wx in
    reduce_11 (w11_mod_gt wx' wy)
  | N2 wx, N12 wy =>
    let wx':= GenBase.extend w2_0W 9 wx in
    reduce_12 (w12_mod_gt wx' wy)
  | N2 wx, N13 wy =>
    let wx':= GenBase.extend w2_0W 10 wx in
    reduce_13 (w13_mod_gt wx' wy)
  | N2 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w2_0W 11 wx) in
    reduce_n n ((make_op n).(znz_mod_gt) wx' wy)
  | N3 wx, N0 wy => reduce_0 (w0_modn1 3 wx wy)
  | N3 wx, N1 wy => reduce_1 (w1_modn1 2 wx wy)
  | N3 wx, N2 wy => reduce_2 (w2_modn1 1 wx wy)
  | N3 wx, N3 wy => reduce_3 (w3_mod_gt wx wy)
  | N3 wx, N4 wy =>
    let wx':= GenBase.extend w3_0W 0 wx in
    reduce_4 (w4_mod_gt wx' wy)
  | N3 wx, N5 wy =>
    let wx':= GenBase.extend w3_0W 1 wx in
    reduce_5 (w5_mod_gt wx' wy)
  | N3 wx, N6 wy =>
    let wx':= GenBase.extend w3_0W 2 wx in
    reduce_6 (w6_mod_gt wx' wy)
  | N3 wx, N7 wy =>
    let wx':= GenBase.extend w3_0W 3 wx in
    reduce_7 (w7_mod_gt wx' wy)
  | N3 wx, N8 wy =>
    let wx':= GenBase.extend w3_0W 4 wx in
    reduce_8 (w8_mod_gt wx' wy)
  | N3 wx, N9 wy =>
    let wx':= GenBase.extend w3_0W 5 wx in
    reduce_9 (w9_mod_gt wx' wy)
  | N3 wx, N10 wy =>
    let wx':= GenBase.extend w3_0W 6 wx in
    reduce_10 (w10_mod_gt wx' wy)
  | N3 wx, N11 wy =>
    let wx':= GenBase.extend w3_0W 7 wx in
    reduce_11 (w11_mod_gt wx' wy)
  | N3 wx, N12 wy =>
    let wx':= GenBase.extend w3_0W 8 wx in
    reduce_12 (w12_mod_gt wx' wy)
  | N3 wx, N13 wy =>
    let wx':= GenBase.extend w3_0W 9 wx in
    reduce_13 (w13_mod_gt wx' wy)
  | N3 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w3_0W 10 wx) in
    reduce_n n ((make_op n).(znz_mod_gt) wx' wy)
  | N4 wx, N0 wy => reduce_0 (w0_modn1 4 wx wy)
  | N4 wx, N1 wy => reduce_1 (w1_modn1 3 wx wy)
  | N4 wx, N2 wy => reduce_2 (w2_modn1 2 wx wy)
  | N4 wx, N3 wy => reduce_3 (w3_modn1 1 wx wy)
  | N4 wx, N4 wy => reduce_4 (w4_mod_gt wx wy)
  | N4 wx, N5 wy =>
    let wx':= GenBase.extend w4_0W 0 wx in
    reduce_5 (w5_mod_gt wx' wy)
  | N4 wx, N6 wy =>
    let wx':= GenBase.extend w4_0W 1 wx in
    reduce_6 (w6_mod_gt wx' wy)
  | N4 wx, N7 wy =>
    let wx':= GenBase.extend w4_0W 2 wx in
    reduce_7 (w7_mod_gt wx' wy)
  | N4 wx, N8 wy =>
    let wx':= GenBase.extend w4_0W 3 wx in
    reduce_8 (w8_mod_gt wx' wy)
  | N4 wx, N9 wy =>
    let wx':= GenBase.extend w4_0W 4 wx in
    reduce_9 (w9_mod_gt wx' wy)
  | N4 wx, N10 wy =>
    let wx':= GenBase.extend w4_0W 5 wx in
    reduce_10 (w10_mod_gt wx' wy)
  | N4 wx, N11 wy =>
    let wx':= GenBase.extend w4_0W 6 wx in
    reduce_11 (w11_mod_gt wx' wy)
  | N4 wx, N12 wy =>
    let wx':= GenBase.extend w4_0W 7 wx in
    reduce_12 (w12_mod_gt wx' wy)
  | N4 wx, N13 wy =>
    let wx':= GenBase.extend w4_0W 8 wx in
    reduce_13 (w13_mod_gt wx' wy)
  | N4 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w4_0W 9 wx) in
    reduce_n n ((make_op n).(znz_mod_gt) wx' wy)
  | N5 wx, N0 wy => reduce_0 (w0_modn1 5 wx wy)
  | N5 wx, N1 wy => reduce_1 (w1_modn1 4 wx wy)
  | N5 wx, N2 wy => reduce_2 (w2_modn1 3 wx wy)
  | N5 wx, N3 wy => reduce_3 (w3_modn1 2 wx wy)
  | N5 wx, N4 wy => reduce_4 (w4_modn1 1 wx wy)
  | N5 wx, N5 wy => reduce_5 (w5_mod_gt wx wy)
  | N5 wx, N6 wy =>
    let wx':= GenBase.extend w5_0W 0 wx in
    reduce_6 (w6_mod_gt wx' wy)
  | N5 wx, N7 wy =>
    let wx':= GenBase.extend w5_0W 1 wx in
    reduce_7 (w7_mod_gt wx' wy)
  | N5 wx, N8 wy =>
    let wx':= GenBase.extend w5_0W 2 wx in
    reduce_8 (w8_mod_gt wx' wy)
  | N5 wx, N9 wy =>
    let wx':= GenBase.extend w5_0W 3 wx in
    reduce_9 (w9_mod_gt wx' wy)
  | N5 wx, N10 wy =>
    let wx':= GenBase.extend w5_0W 4 wx in
    reduce_10 (w10_mod_gt wx' wy)
  | N5 wx, N11 wy =>
    let wx':= GenBase.extend w5_0W 5 wx in
    reduce_11 (w11_mod_gt wx' wy)
  | N5 wx, N12 wy =>
    let wx':= GenBase.extend w5_0W 6 wx in
    reduce_12 (w12_mod_gt wx' wy)
  | N5 wx, N13 wy =>
    let wx':= GenBase.extend w5_0W 7 wx in
    reduce_13 (w13_mod_gt wx' wy)
  | N5 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w5_0W 8 wx) in
    reduce_n n ((make_op n).(znz_mod_gt) wx' wy)
  | N6 wx, N0 wy => reduce_0 (w0_modn1 6 wx wy)
  | N6 wx, N1 wy => reduce_1 (w1_modn1 5 wx wy)
  | N6 wx, N2 wy => reduce_2 (w2_modn1 4 wx wy)
  | N6 wx, N3 wy => reduce_3 (w3_modn1 3 wx wy)
  | N6 wx, N4 wy => reduce_4 (w4_modn1 2 wx wy)
  | N6 wx, N5 wy => reduce_5 (w5_modn1 1 wx wy)
  | N6 wx, N6 wy => reduce_6 (w6_mod_gt wx wy)
  | N6 wx, N7 wy =>
    let wx':= GenBase.extend w6_0W 0 wx in
    reduce_7 (w7_mod_gt wx' wy)
  | N6 wx, N8 wy =>
    let wx':= GenBase.extend w6_0W 1 wx in
    reduce_8 (w8_mod_gt wx' wy)
  | N6 wx, N9 wy =>
    let wx':= GenBase.extend w6_0W 2 wx in
    reduce_9 (w9_mod_gt wx' wy)
  | N6 wx, N10 wy =>
    let wx':= GenBase.extend w6_0W 3 wx in
    reduce_10 (w10_mod_gt wx' wy)
  | N6 wx, N11 wy =>
    let wx':= GenBase.extend w6_0W 4 wx in
    reduce_11 (w11_mod_gt wx' wy)
  | N6 wx, N12 wy =>
    let wx':= GenBase.extend w6_0W 5 wx in
    reduce_12 (w12_mod_gt wx' wy)
  | N6 wx, N13 wy =>
    let wx':= GenBase.extend w6_0W 6 wx in
    reduce_13 (w13_mod_gt wx' wy)
  | N6 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w6_0W 7 wx) in
    reduce_n n ((make_op n).(znz_mod_gt) wx' wy)
  | N7 wx, N0 wy => reduce_0 (w0_modn1 7 wx wy)
  | N7 wx, N1 wy => reduce_1 (w1_modn1 6 wx wy)
  | N7 wx, N2 wy => reduce_2 (w2_modn1 5 wx wy)
  | N7 wx, N3 wy => reduce_3 (w3_modn1 4 wx wy)
  | N7 wx, N4 wy => reduce_4 (w4_modn1 3 wx wy)
  | N7 wx, N5 wy => reduce_5 (w5_modn1 2 wx wy)
  | N7 wx, N6 wy => reduce_6 (w6_modn1 1 wx wy)
  | N7 wx, N7 wy => reduce_7 (w7_mod_gt wx wy)
  | N7 wx, N8 wy =>
    let wx':= GenBase.extend w7_0W 0 wx in
    reduce_8 (w8_mod_gt wx' wy)
  | N7 wx, N9 wy =>
    let wx':= GenBase.extend w7_0W 1 wx in
    reduce_9 (w9_mod_gt wx' wy)
  | N7 wx, N10 wy =>
    let wx':= GenBase.extend w7_0W 2 wx in
    reduce_10 (w10_mod_gt wx' wy)
  | N7 wx, N11 wy =>
    let wx':= GenBase.extend w7_0W 3 wx in
    reduce_11 (w11_mod_gt wx' wy)
  | N7 wx, N12 wy =>
    let wx':= GenBase.extend w7_0W 4 wx in
    reduce_12 (w12_mod_gt wx' wy)
  | N7 wx, N13 wy =>
    let wx':= GenBase.extend w7_0W 5 wx in
    reduce_13 (w13_mod_gt wx' wy)
  | N7 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w7_0W 6 wx) in
    reduce_n n ((make_op n).(znz_mod_gt) wx' wy)
  | N8 wx, N0 wy => reduce_0 (w0_modn1 8 wx wy)
  | N8 wx, N1 wy => reduce_1 (w1_modn1 7 wx wy)
  | N8 wx, N2 wy => reduce_2 (w2_modn1 6 wx wy)
  | N8 wx, N3 wy => reduce_3 (w3_modn1 5 wx wy)
  | N8 wx, N4 wy => reduce_4 (w4_modn1 4 wx wy)
  | N8 wx, N5 wy => reduce_5 (w5_modn1 3 wx wy)
  | N8 wx, N6 wy => reduce_6 (w6_modn1 2 wx wy)
  | N8 wx, N7 wy => reduce_7 (w7_modn1 1 wx wy)
  | N8 wx, N8 wy => reduce_8 (w8_mod_gt wx wy)
  | N8 wx, N9 wy =>
    let wx':= GenBase.extend w8_0W 0 wx in
    reduce_9 (w9_mod_gt wx' wy)
  | N8 wx, N10 wy =>
    let wx':= GenBase.extend w8_0W 1 wx in
    reduce_10 (w10_mod_gt wx' wy)
  | N8 wx, N11 wy =>
    let wx':= GenBase.extend w8_0W 2 wx in
    reduce_11 (w11_mod_gt wx' wy)
  | N8 wx, N12 wy =>
    let wx':= GenBase.extend w8_0W 3 wx in
    reduce_12 (w12_mod_gt wx' wy)
  | N8 wx, N13 wy =>
    let wx':= GenBase.extend w8_0W 4 wx in
    reduce_13 (w13_mod_gt wx' wy)
  | N8 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w8_0W 5 wx) in
    reduce_n n ((make_op n).(znz_mod_gt) wx' wy)
  | N9 wx, N0 wy => reduce_0 (w0_modn1 9 wx wy)
  | N9 wx, N1 wy => reduce_1 (w1_modn1 8 wx wy)
  | N9 wx, N2 wy => reduce_2 (w2_modn1 7 wx wy)
  | N9 wx, N3 wy => reduce_3 (w3_modn1 6 wx wy)
  | N9 wx, N4 wy => reduce_4 (w4_modn1 5 wx wy)
  | N9 wx, N5 wy => reduce_5 (w5_modn1 4 wx wy)
  | N9 wx, N6 wy => reduce_6 (w6_modn1 3 wx wy)
  | N9 wx, N7 wy => reduce_7 (w7_modn1 2 wx wy)
  | N9 wx, N8 wy => reduce_8 (w8_modn1 1 wx wy)
  | N9 wx, N9 wy => reduce_9 (w9_mod_gt wx wy)
  | N9 wx, N10 wy =>
    let wx':= GenBase.extend w9_0W 0 wx in
    reduce_10 (w10_mod_gt wx' wy)
  | N9 wx, N11 wy =>
    let wx':= GenBase.extend w9_0W 1 wx in
    reduce_11 (w11_mod_gt wx' wy)
  | N9 wx, N12 wy =>
    let wx':= GenBase.extend w9_0W 2 wx in
    reduce_12 (w12_mod_gt wx' wy)
  | N9 wx, N13 wy =>
    let wx':= GenBase.extend w9_0W 3 wx in
    reduce_13 (w13_mod_gt wx' wy)
  | N9 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w9_0W 4 wx) in
    reduce_n n ((make_op n).(znz_mod_gt) wx' wy)
  | N10 wx, N0 wy => reduce_0 (w0_modn1 10 wx wy)
  | N10 wx, N1 wy => reduce_1 (w1_modn1 9 wx wy)
  | N10 wx, N2 wy => reduce_2 (w2_modn1 8 wx wy)
  | N10 wx, N3 wy => reduce_3 (w3_modn1 7 wx wy)
  | N10 wx, N4 wy => reduce_4 (w4_modn1 6 wx wy)
  | N10 wx, N5 wy => reduce_5 (w5_modn1 5 wx wy)
  | N10 wx, N6 wy => reduce_6 (w6_modn1 4 wx wy)
  | N10 wx, N7 wy => reduce_7 (w7_modn1 3 wx wy)
  | N10 wx, N8 wy => reduce_8 (w8_modn1 2 wx wy)
  | N10 wx, N9 wy => reduce_9 (w9_modn1 1 wx wy)
  | N10 wx, N10 wy => reduce_10 (w10_mod_gt wx wy)
  | N10 wx, N11 wy =>
    let wx':= GenBase.extend w10_0W 0 wx in
    reduce_11 (w11_mod_gt wx' wy)
  | N10 wx, N12 wy =>
    let wx':= GenBase.extend w10_0W 1 wx in
    reduce_12 (w12_mod_gt wx' wy)
  | N10 wx, N13 wy =>
    let wx':= GenBase.extend w10_0W 2 wx in
    reduce_13 (w13_mod_gt wx' wy)
  | N10 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w10_0W 3 wx) in
    reduce_n n ((make_op n).(znz_mod_gt) wx' wy)
  | N11 wx, N0 wy => reduce_0 (w0_modn1 11 wx wy)
  | N11 wx, N1 wy => reduce_1 (w1_modn1 10 wx wy)
  | N11 wx, N2 wy => reduce_2 (w2_modn1 9 wx wy)
  | N11 wx, N3 wy => reduce_3 (w3_modn1 8 wx wy)
  | N11 wx, N4 wy => reduce_4 (w4_modn1 7 wx wy)
  | N11 wx, N5 wy => reduce_5 (w5_modn1 6 wx wy)
  | N11 wx, N6 wy => reduce_6 (w6_modn1 5 wx wy)
  | N11 wx, N7 wy => reduce_7 (w7_modn1 4 wx wy)
  | N11 wx, N8 wy => reduce_8 (w8_modn1 3 wx wy)
  | N11 wx, N9 wy => reduce_9 (w9_modn1 2 wx wy)
  | N11 wx, N10 wy => reduce_10 (w10_modn1 1 wx wy)
  | N11 wx, N11 wy => reduce_11 (w11_mod_gt wx wy)
  | N11 wx, N12 wy =>
    let wx':= GenBase.extend w11_0W 0 wx in
    reduce_12 (w12_mod_gt wx' wy)
  | N11 wx, N13 wy =>
    let wx':= GenBase.extend w11_0W 1 wx in
    reduce_13 (w13_mod_gt wx' wy)
  | N11 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w11_0W 2 wx) in
    reduce_n n ((make_op n).(znz_mod_gt) wx' wy)
  | N12 wx, N0 wy => reduce_0 (w0_modn1 12 wx wy)
  | N12 wx, N1 wy => reduce_1 (w1_modn1 11 wx wy)
  | N12 wx, N2 wy => reduce_2 (w2_modn1 10 wx wy)
  | N12 wx, N3 wy => reduce_3 (w3_modn1 9 wx wy)
  | N12 wx, N4 wy => reduce_4 (w4_modn1 8 wx wy)
  | N12 wx, N5 wy => reduce_5 (w5_modn1 7 wx wy)
  | N12 wx, N6 wy => reduce_6 (w6_modn1 6 wx wy)
  | N12 wx, N7 wy => reduce_7 (w7_modn1 5 wx wy)
  | N12 wx, N8 wy => reduce_8 (w8_modn1 4 wx wy)
  | N12 wx, N9 wy => reduce_9 (w9_modn1 3 wx wy)
  | N12 wx, N10 wy => reduce_10 (w10_modn1 2 wx wy)
  | N12 wx, N11 wy => reduce_11 (w11_modn1 1 wx wy)
  | N12 wx, N12 wy => reduce_12 (w12_mod_gt wx wy)
  | N12 wx, N13 wy =>
    let wx':= GenBase.extend w12_0W 0 wx in
    reduce_13 (w13_mod_gt wx' wy)
  | N12 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w12_0W 1 wx) in
    reduce_n n ((make_op n).(znz_mod_gt) wx' wy)
  | N13 wx, N0 wy => reduce_0 (w0_modn1 13 wx wy)
  | N13 wx, N1 wy => reduce_1 (w1_modn1 12 wx wy)
  | N13 wx, N2 wy => reduce_2 (w2_modn1 11 wx wy)
  | N13 wx, N3 wy => reduce_3 (w3_modn1 10 wx wy)
  | N13 wx, N4 wy => reduce_4 (w4_modn1 9 wx wy)
  | N13 wx, N5 wy => reduce_5 (w5_modn1 8 wx wy)
  | N13 wx, N6 wy => reduce_6 (w6_modn1 7 wx wy)
  | N13 wx, N7 wy => reduce_7 (w7_modn1 6 wx wy)
  | N13 wx, N8 wy => reduce_8 (w8_modn1 5 wx wy)
  | N13 wx, N9 wy => reduce_9 (w9_modn1 4 wx wy)
  | N13 wx, N10 wy => reduce_10 (w10_modn1 3 wx wy)
  | N13 wx, N11 wy => reduce_11 (w11_modn1 2 wx wy)
  | N13 wx, N12 wy => reduce_12 (w12_modn1 1 wx wy)
  | N13 wx, N13 wy => reduce_13 (w13_mod_gt wx wy)
  | N13 wx, Nn n wy =>
    let wx':= extend n w13 (GenBase.extend w13_0W 0 wx) in
    reduce_n n ((make_op n).(znz_mod_gt) wx' wy)
  | Nn n wx, N0 wy =>
    let wy':= GenBase.extend w0_0W 12 wy in
    reduce_13 (w13_modn1 (S n) wx wy')
  | Nn n wx, N1 wy =>
    let wy':= GenBase.extend w1_0W 11 wy in
    reduce_13 (w13_modn1 (S n) wx wy')
  | Nn n wx, N2 wy =>
    let wy':= GenBase.extend w2_0W 10 wy in
    reduce_13 (w13_modn1 (S n) wx wy')
  | Nn n wx, N3 wy =>
    let wy':= GenBase.extend w3_0W 9 wy in
    reduce_13 (w13_modn1 (S n) wx wy')
  | Nn n wx, N4 wy =>
    let wy':= GenBase.extend w4_0W 8 wy in
    reduce_13 (w13_modn1 (S n) wx wy')
  | Nn n wx, N5 wy =>
    let wy':= GenBase.extend w5_0W 7 wy in
    reduce_13 (w13_modn1 (S n) wx wy')
  | Nn n wx, N6 wy =>
    let wy':= GenBase.extend w6_0W 6 wy in
    reduce_13 (w13_modn1 (S n) wx wy')
  | Nn n wx, N7 wy =>
    let wy':= GenBase.extend w7_0W 5 wy in
    reduce_13 (w13_modn1 (S n) wx wy')
  | Nn n wx, N8 wy =>
    let wy':= GenBase.extend w8_0W 4 wy in
    reduce_13 (w13_modn1 (S n) wx wy')
  | Nn n wx, N9 wy =>
    let wy':= GenBase.extend w9_0W 3 wy in
    reduce_13 (w13_modn1 (S n) wx wy')
  | Nn n wx, N10 wy =>
    let wy':= GenBase.extend w10_0W 2 wy in
    reduce_13 (w13_modn1 (S n) wx wy')
  | Nn n wx, N11 wy =>
    let wy':= GenBase.extend w11_0W 1 wy in
    reduce_13 (w13_modn1 (S n) wx wy')
  | Nn n wx, N12 wy =>
    let wy':= GenBase.extend w12_0W 0 wy in
    reduce_13 (w13_modn1 (S n) wx wy')
  | Nn n wx, N13 wy =>
    let wy':= wy in
    reduce_13 (w13_modn1 (S n) wx wy')
  | Nn n wx, Nn m wy =>
    let mn := Max.max n m in
    let d := diff n m in
    let op := make_op mn in
     reduce_n mn (op.(znz_mod_gt)
       (castm (diff_r n m) (extend_tr wx (snd d)))
       (castm (diff_l n m) (extend_tr wy (fst d))))
  end.

 Definition modulo x y := 
  match compare x y with
  | Eq => zero
  | Lt => x
  | Gt => mod_gt x y
  end.

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

 Fixpoint gcd_gt (p:positive) (cont:t->t->t) (a b:t) {struct p} : t :=
  gcd_gt_body a b
    (fun a b =>
       match p with
       | xH => cont a b
       | xO p => gcd_gt p (gcd_gt p cont) a b
       | xI p => gcd_gt p (gcd_gt p cont) a b
       end).

 Definition gcd_cont a b :=
  match compare one b with
  | Eq => one
  | _ => a
  end.

 Definition gcd a b :=
  match compare a b with
  | Eq => a
  | Lt => gcd_gt (digits b) gcd_cont b a
  | Gt => gcd_gt (digits a) gcd_cont a b
  end.

Definition pheight p := Peano.pred (nat_of_P (get_height w0_op.(znz_digits) (plength p))).
 Definition of_pos x :=
  let h := pheight x in
  match h with
  | O => reduce_0 (snd (w0_op.(znz_of_pos) x))
  | (S O) => reduce_1 (snd (w1_op.(znz_of_pos) x))
  | (S (S O)) => reduce_2 (snd (w2_op.(znz_of_pos) x))
  | (S (S (S O))) => reduce_3 (snd (w3_op.(znz_of_pos) x))
  | (S (S (S (S O)))) => reduce_4 (snd (w4_op.(znz_of_pos) x))
  | (S (S (S (S (S O))))) => reduce_5 (snd (w5_op.(znz_of_pos) x))
  | (S (S (S (S (S (S O)))))) => reduce_6 (snd (w6_op.(znz_of_pos) x))
  | (S (S (S (S (S (S (S O))))))) => reduce_7 (snd (w7_op.(znz_of_pos) x))
  | (S (S (S (S (S (S (S (S O)))))))) => reduce_8 (snd (w8_op.(znz_of_pos) x))
  | (S (S (S (S (S (S (S (S (S O))))))))) => reduce_9 (snd (w9_op.(znz_of_pos) x))
  | (S (S (S (S (S (S (S (S (S (S O)))))))))) => reduce_10 (snd (w10_op.(znz_of_pos) x))
  | (S (S (S (S (S (S (S (S (S (S (S O))))))))))) => reduce_11 (snd (w11_op.(znz_of_pos) x))
  | (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))) => reduce_12 (snd (w12_op.(znz_of_pos) x))
  | (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))) => reduce_13 (snd (w13_op.(znz_of_pos) x))
  | _ =>
    let n := minus h 14 in
    reduce_n n (snd ((make_op n).(znz_of_pos) x))
  end.

 Definition of_N x :=
  match x with
  | BinNat.N0 => zero
  | Npos p => of_pos p
  end.

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

 Definition level f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13  fn x y: t_ :=  match x, y with
  | N0 wx, N0 wy => f0 wx wy 
  | N0 wx, N1 wy => f1 (WW w_0 wx) wy
  | N0 wx, N2 wy => f2 (extend1 w0 (WW w_0 wx)) wy
  | N0 wx, N3 wy => f3 (extend2 w0 (WW w_0 wx)) wy
  | N0 wx, N4 wy => f4 (extend3 w0 (WW w_0 wx)) wy
  | N0 wx, N5 wy => f5 (extend4 w0 (WW w_0 wx)) wy
  | N0 wx, N6 wy => f6 (extend5 w0 (WW w_0 wx)) wy
  | N0 wx, N7 wy => f7 (extend6 w0 (WW w_0 wx)) wy
  | N0 wx, N8 wy => f8 (extend7 w0 (WW w_0 wx)) wy
  | N0 wx, N9 wy => f9 (extend8 w0 (WW w_0 wx)) wy
  | N0 wx, N10 wy => f10 (extend9 w0 (WW w_0 wx)) wy
  | N0 wx, N11 wy => f11 (extend10 w0 (WW w_0 wx)) wy
  | N0 wx, N12 wy => f12 (extend11 w0 (WW w_0 wx)) wy
  | N0 wx, N13 wy => f13 (extend12 w0 (WW w_0 wx)) wy
  | N0 wx, Nn n wy =>
    fn n (extend n w13 (extend13 w0 (WW w_0 wx))) wy
  | N1 wx, N0 wy =>
    f1 wx (WW w_0 wy)
  | N1 wx, N1 wy => f1 wx wy
  | N1 wx, N2 wy => f2 (extend1 w0 wx) wy
  | N1 wx, N3 wy => f3 (extend2 w0 wx) wy
  | N1 wx, N4 wy => f4 (extend3 w0 wx) wy
  | N1 wx, N5 wy => f5 (extend4 w0 wx) wy
  | N1 wx, N6 wy => f6 (extend5 w0 wx) wy
  | N1 wx, N7 wy => f7 (extend6 w0 wx) wy
  | N1 wx, N8 wy => f8 (extend7 w0 wx) wy
  | N1 wx, N9 wy => f9 (extend8 w0 wx) wy
  | N1 wx, N10 wy => f10 (extend9 w0 wx) wy
  | N1 wx, N11 wy => f11 (extend10 w0 wx) wy
  | N1 wx, N12 wy => f12 (extend11 w0 wx) wy
  | N1 wx, N13 wy => f13 (extend12 w0 wx) wy
  | N1 wx, Nn n wy => fn n (extend n w13 (extend13 w0 wx)) wy
  | N2 wx, N0 wy =>
    f2 wx (extend1 w0 (WW w_0 wy))
  | N2 wx, N1 wy => f2 wx (extend1 w0 wy)
  | N2 wx, N2 wy => f2 wx wy
  | N2 wx, N3 wy => f3 (extend1 w1 wx) wy
  | N2 wx, N4 wy => f4 (extend2 w1 wx) wy
  | N2 wx, N5 wy => f5 (extend3 w1 wx) wy
  | N2 wx, N6 wy => f6 (extend4 w1 wx) wy
  | N2 wx, N7 wy => f7 (extend5 w1 wx) wy
  | N2 wx, N8 wy => f8 (extend6 w1 wx) wy
  | N2 wx, N9 wy => f9 (extend7 w1 wx) wy
  | N2 wx, N10 wy => f10 (extend8 w1 wx) wy
  | N2 wx, N11 wy => f11 (extend9 w1 wx) wy
  | N2 wx, N12 wy => f12 (extend10 w1 wx) wy
  | N2 wx, N13 wy => f13 (extend11 w1 wx) wy
  | N2 wx, Nn n wy => fn n (extend n w13 (extend12 w1 wx)) wy
  | N3 wx, N0 wy =>
    f3 wx (extend2 w0 (WW w_0 wy))
  | N3 wx, N1 wy => f3 wx (extend2 w0 wy)
  | N3 wx, N2 wy => f3 wx (extend1 w1 wy)
  | N3 wx, N3 wy => f3 wx wy
  | N3 wx, N4 wy => f4 (extend1 w2 wx) wy
  | N3 wx, N5 wy => f5 (extend2 w2 wx) wy
  | N3 wx, N6 wy => f6 (extend3 w2 wx) wy
  | N3 wx, N7 wy => f7 (extend4 w2 wx) wy
  | N3 wx, N8 wy => f8 (extend5 w2 wx) wy
  | N3 wx, N9 wy => f9 (extend6 w2 wx) wy
  | N3 wx, N10 wy => f10 (extend7 w2 wx) wy
  | N3 wx, N11 wy => f11 (extend8 w2 wx) wy
  | N3 wx, N12 wy => f12 (extend9 w2 wx) wy
  | N3 wx, N13 wy => f13 (extend10 w2 wx) wy
  | N3 wx, Nn n wy => fn n (extend n w13 (extend11 w2 wx)) wy
  | N4 wx, N0 wy =>
    f4 wx (extend3 w0 (WW w_0 wy))
  | N4 wx, N1 wy => f4 wx (extend3 w0 wy)
  | N4 wx, N2 wy => f4 wx (extend2 w1 wy)
  | N4 wx, N3 wy => f4 wx (extend1 w2 wy)
  | N4 wx, N4 wy => f4 wx wy
  | N4 wx, N5 wy => f5 (extend1 w3 wx) wy
  | N4 wx, N6 wy => f6 (extend2 w3 wx) wy
  | N4 wx, N7 wy => f7 (extend3 w3 wx) wy
  | N4 wx, N8 wy => f8 (extend4 w3 wx) wy
  | N4 wx, N9 wy => f9 (extend5 w3 wx) wy
  | N4 wx, N10 wy => f10 (extend6 w3 wx) wy
  | N4 wx, N11 wy => f11 (extend7 w3 wx) wy
  | N4 wx, N12 wy => f12 (extend8 w3 wx) wy
  | N4 wx, N13 wy => f13 (extend9 w3 wx) wy
  | N4 wx, Nn n wy => fn n (extend n w13 (extend10 w3 wx)) wy
  | N5 wx, N0 wy =>
    f5 wx (extend4 w0 (WW w_0 wy))
  | N5 wx, N1 wy => f5 wx (extend4 w0 wy)
  | N5 wx, N2 wy => f5 wx (extend3 w1 wy)
  | N5 wx, N3 wy => f5 wx (extend2 w2 wy)
  | N5 wx, N4 wy => f5 wx (extend1 w3 wy)
  | N5 wx, N5 wy => f5 wx wy
  | N5 wx, N6 wy => f6 (extend1 w4 wx) wy
  | N5 wx, N7 wy => f7 (extend2 w4 wx) wy
  | N5 wx, N8 wy => f8 (extend3 w4 wx) wy
  | N5 wx, N9 wy => f9 (extend4 w4 wx) wy
  | N5 wx, N10 wy => f10 (extend5 w4 wx) wy
  | N5 wx, N11 wy => f11 (extend6 w4 wx) wy
  | N5 wx, N12 wy => f12 (extend7 w4 wx) wy
  | N5 wx, N13 wy => f13 (extend8 w4 wx) wy
  | N5 wx, Nn n wy => fn n (extend n w13 (extend9 w4 wx)) wy
  | N6 wx, N0 wy =>
    f6 wx (extend5 w0 (WW w_0 wy))
  | N6 wx, N1 wy => f6 wx (extend5 w0 wy)
  | N6 wx, N2 wy => f6 wx (extend4 w1 wy)
  | N6 wx, N3 wy => f6 wx (extend3 w2 wy)
  | N6 wx, N4 wy => f6 wx (extend2 w3 wy)
  | N6 wx, N5 wy => f6 wx (extend1 w4 wy)
  | N6 wx, N6 wy => f6 wx wy
  | N6 wx, N7 wy => f7 (extend1 w5 wx) wy
  | N6 wx, N8 wy => f8 (extend2 w5 wx) wy
  | N6 wx, N9 wy => f9 (extend3 w5 wx) wy
  | N6 wx, N10 wy => f10 (extend4 w5 wx) wy
  | N6 wx, N11 wy => f11 (extend5 w5 wx) wy
  | N6 wx, N12 wy => f12 (extend6 w5 wx) wy
  | N6 wx, N13 wy => f13 (extend7 w5 wx) wy
  | N6 wx, Nn n wy => fn n (extend n w13 (extend8 w5 wx)) wy
  | N7 wx, N0 wy =>
    f7 wx (extend6 w0 (WW w_0 wy))
  | N7 wx, N1 wy => f7 wx (extend6 w0 wy)
  | N7 wx, N2 wy => f7 wx (extend5 w1 wy)
  | N7 wx, N3 wy => f7 wx (extend4 w2 wy)
  | N7 wx, N4 wy => f7 wx (extend3 w3 wy)
  | N7 wx, N5 wy => f7 wx (extend2 w4 wy)
  | N7 wx, N6 wy => f7 wx (extend1 w5 wy)
  | N7 wx, N7 wy => f7 wx wy
  | N7 wx, N8 wy => f8 (extend1 w6 wx) wy
  | N7 wx, N9 wy => f9 (extend2 w6 wx) wy
  | N7 wx, N10 wy => f10 (extend3 w6 wx) wy
  | N7 wx, N11 wy => f11 (extend4 w6 wx) wy
  | N7 wx, N12 wy => f12 (extend5 w6 wx) wy
  | N7 wx, N13 wy => f13 (extend6 w6 wx) wy
  | N7 wx, Nn n wy => fn n (extend n w13 (extend7 w6 wx)) wy
  | N8 wx, N0 wy =>
    f8 wx (extend7 w0 (WW w_0 wy))
  | N8 wx, N1 wy => f8 wx (extend7 w0 wy)
  | N8 wx, N2 wy => f8 wx (extend6 w1 wy)
  | N8 wx, N3 wy => f8 wx (extend5 w2 wy)
  | N8 wx, N4 wy => f8 wx (extend4 w3 wy)
  | N8 wx, N5 wy => f8 wx (extend3 w4 wy)
  | N8 wx, N6 wy => f8 wx (extend2 w5 wy)
  | N8 wx, N7 wy => f8 wx (extend1 w6 wy)
  | N8 wx, N8 wy => f8 wx wy
  | N8 wx, N9 wy => f9 (extend1 w7 wx) wy
  | N8 wx, N10 wy => f10 (extend2 w7 wx) wy
  | N8 wx, N11 wy => f11 (extend3 w7 wx) wy
  | N8 wx, N12 wy => f12 (extend4 w7 wx) wy
  | N8 wx, N13 wy => f13 (extend5 w7 wx) wy
  | N8 wx, Nn n wy => fn n (extend n w13 (extend6 w7 wx)) wy
  | N9 wx, N0 wy =>
    f9 wx (extend8 w0 (WW w_0 wy))
  | N9 wx, N1 wy => f9 wx (extend8 w0 wy)
  | N9 wx, N2 wy => f9 wx (extend7 w1 wy)
  | N9 wx, N3 wy => f9 wx (extend6 w2 wy)
  | N9 wx, N4 wy => f9 wx (extend5 w3 wy)
  | N9 wx, N5 wy => f9 wx (extend4 w4 wy)
  | N9 wx, N6 wy => f9 wx (extend3 w5 wy)
  | N9 wx, N7 wy => f9 wx (extend2 w6 wy)
  | N9 wx, N8 wy => f9 wx (extend1 w7 wy)
  | N9 wx, N9 wy => f9 wx wy
  | N9 wx, N10 wy => f10 (extend1 w8 wx) wy
  | N9 wx, N11 wy => f11 (extend2 w8 wx) wy
  | N9 wx, N12 wy => f12 (extend3 w8 wx) wy
  | N9 wx, N13 wy => f13 (extend4 w8 wx) wy
  | N9 wx, Nn n wy => fn n (extend n w13 (extend5 w8 wx)) wy
  | N10 wx, N0 wy =>
    f10 wx (extend9 w0 (WW w_0 wy))
  | N10 wx, N1 wy => f10 wx (extend9 w0 wy)
  | N10 wx, N2 wy => f10 wx (extend8 w1 wy)
  | N10 wx, N3 wy => f10 wx (extend7 w2 wy)
  | N10 wx, N4 wy => f10 wx (extend6 w3 wy)
  | N10 wx, N5 wy => f10 wx (extend5 w4 wy)
  | N10 wx, N6 wy => f10 wx (extend4 w5 wy)
  | N10 wx, N7 wy => f10 wx (extend3 w6 wy)
  | N10 wx, N8 wy => f10 wx (extend2 w7 wy)
  | N10 wx, N9 wy => f10 wx (extend1 w8 wy)
  | N10 wx, N10 wy => f10 wx wy
  | N10 wx, N11 wy => f11 (extend1 w9 wx) wy
  | N10 wx, N12 wy => f12 (extend2 w9 wx) wy
  | N10 wx, N13 wy => f13 (extend3 w9 wx) wy
  | N10 wx, Nn n wy => fn n (extend n w13 (extend4 w9 wx)) wy
  | N11 wx, N0 wy =>
    f11 wx (extend10 w0 (WW w_0 wy))
  | N11 wx, N1 wy => f11 wx (extend10 w0 wy)
  | N11 wx, N2 wy => f11 wx (extend9 w1 wy)
  | N11 wx, N3 wy => f11 wx (extend8 w2 wy)
  | N11 wx, N4 wy => f11 wx (extend7 w3 wy)
  | N11 wx, N5 wy => f11 wx (extend6 w4 wy)
  | N11 wx, N6 wy => f11 wx (extend5 w5 wy)
  | N11 wx, N7 wy => f11 wx (extend4 w6 wy)
  | N11 wx, N8 wy => f11 wx (extend3 w7 wy)
  | N11 wx, N9 wy => f11 wx (extend2 w8 wy)
  | N11 wx, N10 wy => f11 wx (extend1 w9 wy)
  | N11 wx, N11 wy => f11 wx wy
  | N11 wx, N12 wy => f12 (extend1 w10 wx) wy
  | N11 wx, N13 wy => f13 (extend2 w10 wx) wy
  | N11 wx, Nn n wy => fn n (extend n w13 (extend3 w10 wx)) wy
  | N12 wx, N0 wy =>
    f12 wx (extend11 w0 (WW w_0 wy))
  | N12 wx, N1 wy => f12 wx (extend11 w0 wy)
  | N12 wx, N2 wy => f12 wx (extend10 w1 wy)
  | N12 wx, N3 wy => f12 wx (extend9 w2 wy)
  | N12 wx, N4 wy => f12 wx (extend8 w3 wy)
  | N12 wx, N5 wy => f12 wx (extend7 w4 wy)
  | N12 wx, N6 wy => f12 wx (extend6 w5 wy)
  | N12 wx, N7 wy => f12 wx (extend5 w6 wy)
  | N12 wx, N8 wy => f12 wx (extend4 w7 wy)
  | N12 wx, N9 wy => f12 wx (extend3 w8 wy)
  | N12 wx, N10 wy => f12 wx (extend2 w9 wy)
  | N12 wx, N11 wy => f12 wx (extend1 w10 wy)
  | N12 wx, N12 wy => f12 wx wy
  | N12 wx, N13 wy => f13 (extend1 w11 wx) wy
  | N12 wx, Nn n wy => fn n (extend n w13 (extend2 w11 wx)) wy
  | N13 wx, N0 wy =>
    f13 wx (extend12 w0 (WW w_0 wy))
  | N13 wx, N1 wy => f13 wx (extend12 w0 wy)
  | N13 wx, N2 wy => f13 wx (extend11 w1 wy)
  | N13 wx, N3 wy => f13 wx (extend10 w2 wy)
  | N13 wx, N4 wy => f13 wx (extend9 w3 wy)
  | N13 wx, N5 wy => f13 wx (extend8 w4 wy)
  | N13 wx, N6 wy => f13 wx (extend7 w5 wy)
  | N13 wx, N7 wy => f13 wx (extend6 w6 wy)
  | N13 wx, N8 wy => f13 wx (extend5 w7 wy)
  | N13 wx, N9 wy => f13 wx (extend4 w8 wy)
  | N13 wx, N10 wy => f13 wx (extend3 w9 wy)
  | N13 wx, N11 wy => f13 wx (extend2 w10 wy)
  | N13 wx, N12 wy => f13 wx (extend1 w11 wy)
  | N13 wx, N13 wy => f13 wx wy
  | N13 wx, Nn n wy => fn n (extend n w13 (extend1 w12 wx)) wy
  | Nn n wx, N0 wy =>
    fn n wx (extend n w13 (extend13 w0 (WW w_0 wy)))
  | Nn n wx, N1 wy => fn n wx (extend n w13 (extend13 w0 wy))
  | Nn n wx, N2 wy => fn n wx (extend n w13 (extend12 w1 wy))
  | Nn n wx, N3 wy => fn n wx (extend n w13 (extend11 w2 wy))
  | Nn n wx, N4 wy => fn n wx (extend n w13 (extend10 w3 wy))
  | Nn n wx, N5 wy => fn n wx (extend n w13 (extend9 w4 wy))
  | Nn n wx, N6 wy => fn n wx (extend n w13 (extend8 w5 wy))
  | Nn n wx, N7 wy => fn n wx (extend n w13 (extend7 w6 wy))
  | Nn n wx, N8 wy => fn n wx (extend n w13 (extend6 w7 wy))
  | Nn n wx, N9 wy => fn n wx (extend n w13 (extend5 w8 wy))
  | Nn n wx, N10 wy => fn n wx (extend n w13 (extend4 w9 wy))
  | Nn n wx, N11 wy => fn n wx (extend n w13 (extend3 w10 wy))
  | Nn n wx, N12 wy => fn n wx (extend n w13 (extend2 w11 wy))
  | Nn n wx, N13 wy => fn n wx (extend n w13 (extend1 w12 wy))
  | Nn n wx, Nn m wy =>
    let mn := Max.max n m in
    let d := diff n m in
     fn mn
       (castm (diff_r n m) (extend_tr wx (snd d)))
       (castm (diff_l n m) (extend_tr wy (fst d)))
  end.

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

 Definition shiftr := 
  Eval lazy beta delta [level] in 
     level (fun n x => N0 (shiftr0 n x))
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

 Definition safe_shiftr n x := 
   match compare n (Ndigits x) with
    |  Lt => shiftr n x 
   | _ => N0 w_0
   end.

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
 Definition shiftl := 
  Eval lazy beta delta [level] in 
     level (fun n x => N0 (shiftl0 n x))
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


 Definition double_size w := match w with
 | N0 w=> N1 (WW w_0 w)
 | N1 w=> N2 (extend1 _ w)
 | N2 w=> N3 (extend1 _ w)
 | N3 w=> N4 (extend1 _ w)
 | N4 w=> N5 (extend1 _ w)
 | N5 w=> N6 (extend1 _ w)
 | N6 w=> N7 (extend1 _ w)
 | N7 w=> N8 (extend1 _ w)
 | N8 w=> N9 (extend1 _ w)
 | N9 w=> N10 (extend1 _ w)
 | N10 w=> N11 (extend1 _ w)
 | N11 w=> N12 (extend1 _ w)
 | N12 w=> N13 (extend1 _ w)
 | N13 w=> Nn 0 (extend1 _ w)
 | Nn n w=> Nn (S n) (extend1 _ w)
 end.

 Definition safe_shiftl_aux_body cont n x :=
   match compare n (head0 x)  with
      Gt => cont n (double_size x)
   |  _ => shiftl n x
   end.

 Fixpoint safe_shiftl_aux p cont n x  {struct p} :=
   safe_shiftl_aux_body 
       (fun n x => match p with
        | xH => cont n x
        | xO p => safe_shiftl_aux p (safe_shiftl_aux p cont) n x
        | xI p => safe_shiftl_aux p (safe_shiftl_aux p cont) n x
        end) n x.

  Definition safe_shiftl n x :=
  safe_shiftl_aux (digits n) (fun n x => N0 w0_op.(znz_0)) n x.
 
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

(* Proof section *)

 Open Scope Z_scope.
 Notation "[ x ]" := (to_Z x).
 
 Theorem succ_spec: forall n, [succ n] = [n] + 1.
 Admitted.

 Theorem spec_add: forall x y, [add x y] = [x] + [y].
 Admitted.

 Theorem spec_sub: forall x y, [y] <= [x] -> [sub x y] = [x] - [y].
 Admitted.

 Theorem spec_sub0: forall x y, [x] < [y] -> [sub x y] = 0.
 Admitted.

 Theorem spec_compare: forall x y,
    match compare x y with 
      Eq => [x] = [y]
    | Lt => [x] < [y]
    | Gt => [x] > [y]
    end.
 Proof.
 Admitted.

 Theorem spec_mul: forall x y, [mul x y] =[x] * [y].
 Proof.
 Admitted.

 Theorem spec_sqrt : forall x,
       [sqrt x] ^ 2 <= [x] < ([sqrt x] + 1) ^ 2.
 Proof.
 Admitted.

End Make.

