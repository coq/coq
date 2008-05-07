(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import ZArith.
Require Import BigNumPrelude.

Open Scope Z_scope.

Module Type NType.

 Parameter t : Set.
 
 Parameter zero : t.
 Parameter one : t.

 Parameter of_N : N -> t.
 Parameter to_Z : t -> Z.
 Parameter spec_pos: forall x, 0 <= to_Z x.
 Parameter spec_0: to_Z zero = 0.
 Parameter spec_1: to_Z one = 1.
 Parameter spec_of_N: forall x, to_Z (of_N x) = Z_of_N x.

 Parameter compare : t -> t -> comparison.

 Parameter spec_compare: forall x y,
    match compare x y with
      Eq => to_Z x = to_Z y
    | Lt => to_Z x < to_Z y
    | Gt => to_Z x > to_Z y
    end.

 Parameter eq_bool : t -> t -> bool.

 Parameter spec_eq_bool: forall x y,
    if eq_bool x y then to_Z x = to_Z y else to_Z x <> to_Z y.
 
 Parameter succ : t -> t.

 Parameter spec_succ: forall n, to_Z (succ n) = to_Z n + 1.

 Parameter add  : t -> t -> t.

 Parameter spec_add: forall x y, to_Z (add x y) = to_Z x +  to_Z y.

 Parameter pred : t -> t.

 Parameter spec_pred: forall x, 0 < to_Z x -> to_Z (pred x) = to_Z x - 1.

 Parameter sub  : t -> t -> t.

 Parameter spec_sub: forall x y, to_Z y <= to_Z x ->
   to_Z (sub x y) = to_Z x - to_Z y.

 Parameter mul       : t -> t -> t.

 Parameter spec_mul: forall x y, to_Z (mul x y) = to_Z x * to_Z y.

 Parameter square    : t -> t.

 Parameter spec_square: forall x, to_Z (square x) = to_Z x *  to_Z x.

 Parameter power_pos : t -> positive -> t.

 Parameter spec_power_pos: forall x n, to_Z (power_pos x n) = to_Z x ^ Zpos n.

 Parameter sqrt      : t -> t.

 Parameter spec_sqrt: forall x, to_Z (sqrt x) ^ 2 <= to_Z x < (to_Z (sqrt x) + 1) ^ 2.

 Parameter div_eucl : t -> t -> t * t.

 Parameter spec_div_eucl: forall x y,
      0 < to_Z y ->
      let (q,r) := div_eucl x y in (to_Z q, to_Z r) = (Zdiv_eucl (to_Z x) (to_Z y)).
 
 Parameter div      : t -> t -> t.

 Parameter spec_div: forall x y,
      0 < to_Z y -> to_Z (div x y) = to_Z x / to_Z y.

 Parameter modulo   : t -> t -> t.

 Parameter spec_modulo:
   forall x y, 0 < to_Z y -> to_Z (modulo x y) = to_Z x mod to_Z y.

 Parameter gcd      : t -> t -> t.

 Parameter spec_gcd: forall a b, to_Z (gcd a b) = Zgcd (to_Z a) (to_Z b).


End NType.

Module Make (N:NType).
 
 Inductive t_ : Set := 
  | Pos : N.t -> t_
  | Neg : N.t -> t_.
 
 Definition t := t_.

 Definition zero := Pos N.zero.
 Definition one  := Pos N.one.
 Definition minus_one := Neg N.one.

 Definition of_Z x := 
  match x with
  | Zpos x => Pos (N.of_N (Npos x))
  | Z0 => zero
  | Zneg x => Neg (N.of_N (Npos x))
  end.
 
 Definition to_Z x :=
  match x with
  | Pos nx => N.to_Z nx
  | Neg nx => Zopp (N.to_Z nx)
  end.

 Theorem spec_of_Z: forall x, to_Z (of_Z x) = x.
 intros x; case x; unfold to_Z, of_Z, zero.
   exact N.spec_0.
   intros; rewrite N.spec_of_N; auto.
   intros; rewrite N.spec_of_N; auto.
 Qed.


 Theorem spec_0: to_Z zero = 0.
 exact N.spec_0.
 Qed.

 Theorem spec_1: to_Z one = 1.
 exact N.spec_1.
 Qed.

 Theorem spec_m1: to_Z minus_one = -1.
 simpl; rewrite N.spec_1; auto.
 Qed.

 Definition compare x y :=
  match x, y with
  | Pos nx, Pos ny => N.compare nx ny
  | Pos nx, Neg ny =>
    match N.compare nx N.zero with
    | Gt => Gt
    | _ => N.compare ny N.zero
    end
  | Neg nx, Pos ny =>
    match N.compare N.zero nx with
    | Lt => Lt
    | _ => N.compare N.zero ny
    end
  | Neg nx, Neg ny => N.compare ny nx
  end.


 Theorem spec_compare: forall x y,
    match compare x y with
      Eq => to_Z x = to_Z y
    | Lt => to_Z x < to_Z y
    | Gt => to_Z x > to_Z y
    end.
  unfold compare, to_Z; intros x y; case x; case y; clear x y;
    intros x y; auto; generalize (N.spec_pos x) (N.spec_pos y).
  generalize (N.spec_compare y x); case N.compare; auto with zarith.
  generalize (N.spec_compare y N.zero); case N.compare; 
     try rewrite N.spec_0; auto with zarith.
  generalize (N.spec_compare x N.zero); case N.compare;
   rewrite N.spec_0; auto with zarith.
  generalize (N.spec_compare x N.zero); case N.compare;
   rewrite N.spec_0; auto with zarith.
  generalize (N.spec_compare N.zero y); case N.compare; 
     try rewrite N.spec_0; auto with zarith.
  generalize (N.spec_compare N.zero x); case N.compare;
   rewrite N.spec_0; auto with zarith.
  generalize (N.spec_compare N.zero x); case N.compare;
   rewrite N.spec_0; auto with zarith.
  generalize (N.spec_compare x y); case N.compare; auto with zarith.
  Qed.

 Definition eq_bool x y := 
  match compare x y with
  | Eq => true
  | _ => false
  end.

 Theorem spec_eq_bool: forall x y,
    if eq_bool x y then to_Z x = to_Z y else to_Z x <> to_Z y.
 intros x y; unfold eq_bool;
   generalize (spec_compare x y); case compare; auto with zarith.
 Qed.

 Definition cmp_sign x y :=
  match x, y with
  | Pos nx, Neg ny => 
    if N.eq_bool ny N.zero then Eq else Gt 
  | Neg nx, Pos ny => 
    if N.eq_bool nx N.zero then Eq else Lt
  | _, _ => Eq
  end.

 Theorem spec_cmp_sign: forall x y,
  match cmp_sign x y with
  | Gt => 0 <= to_Z x /\ to_Z y < 0
  | Lt => to_Z x <  0 /\ 0 <= to_Z y
  | Eq => True
  end.
  Proof.
  intros [x | x] [y | y]; unfold cmp_sign; auto.
  generalize (N.spec_eq_bool y N.zero); case N.eq_bool; auto.
  rewrite N.spec_0; unfold to_Z.
  generalize (N.spec_pos x) (N.spec_pos y); auto with zarith.
  generalize (N.spec_eq_bool x N.zero); case N.eq_bool; auto.
  rewrite N.spec_0; unfold to_Z.
  generalize (N.spec_pos x) (N.spec_pos y); auto with zarith.
  Qed.
 
 Definition to_N x :=
  match x with
  | Pos nx => nx
  | Neg nx => nx
  end.

 Definition abs x := Pos (to_N x).

 Theorem spec_abs: forall x, to_Z (abs x) = Zabs (to_Z x).
 intros x; case x; clear x; intros x; assert (F:=N.spec_pos x).
    simpl; rewrite Zabs_eq; auto.
 simpl; rewrite Zabs_non_eq; simpl; auto with zarith.
 Qed.
 
 Definition opp x := 
  match x with 
  | Pos nx => Neg nx
  | Neg nx => Pos nx
  end.

 Theorem spec_opp: forall x, to_Z (opp x) = - to_Z x.
 intros x; case x; simpl; auto with zarith.
 Qed.
    
 Definition succ x :=
  match x with
  | Pos n => Pos (N.succ n)
  | Neg n =>
    match N.compare N.zero n with
    | Lt => Neg (N.pred n)
    | _ => one
    end
  end.

 Theorem spec_succ: forall n, to_Z (succ n) = to_Z n + 1.
 intros x; case x; clear x; intros x.
   exact (N.spec_succ x).
 simpl; generalize (N.spec_compare N.zero x); case N.compare; 
   rewrite N.spec_0; simpl.
  intros HH; rewrite <- HH; rewrite N.spec_1; ring.
  intros HH; rewrite N.spec_pred; auto with zarith.
 generalize (N.spec_pos x); auto with zarith.
 Qed.

 Definition add x y :=
  match x, y with
  | Pos nx, Pos ny => Pos (N.add nx ny)
  | Pos nx, Neg ny =>
    match N.compare nx ny with
    | Gt => Pos (N.sub nx ny)
    | Eq => zero
    | Lt => Neg (N.sub ny nx)
    end
  | Neg nx, Pos ny =>
    match N.compare nx ny with
    | Gt => Neg (N.sub nx ny)
    | Eq => zero
    | Lt => Pos (N.sub ny nx)
    end
  | Neg nx, Neg ny => Neg (N.add nx ny)
  end.
  
 Theorem spec_add: forall x y, to_Z (add x y) = to_Z x +  to_Z y.
 unfold add, to_Z; intros [x | x] [y | y].
   exact (N.spec_add x y).
 unfold zero; generalize (N.spec_compare x y); case N.compare.
   rewrite N.spec_0; auto with zarith.
 intros; rewrite N.spec_sub; try ring; auto with zarith.
 intros; rewrite N.spec_sub; try ring; auto with zarith.
 unfold zero; generalize (N.spec_compare x y); case N.compare.
   rewrite N.spec_0; auto with zarith.
 intros; rewrite N.spec_sub; try ring; auto with zarith.
 intros; rewrite N.spec_sub; try ring; auto with zarith.
 intros; rewrite N.spec_add; try ring; auto with zarith.
 Qed.

 Definition pred x :=
  match x with
  | Pos nx =>
    match N.compare N.zero nx with
    | Lt => Pos (N.pred nx)
    | _ => minus_one
    end
  | Neg nx => Neg (N.succ nx)
  end.

 Theorem spec_pred: forall x, to_Z (pred x) = to_Z x - 1.
 unfold pred, to_Z, minus_one; intros [x | x].
   generalize (N.spec_compare N.zero x); case N.compare; 
     rewrite N.spec_0; try rewrite N.spec_1; auto with zarith.
   intros H; exact (N.spec_pred _ H).
 generalize (N.spec_pos x); auto with zarith.
 rewrite N.spec_succ; ring.
 Qed.

 Definition sub x y :=
  match x, y with
  | Pos nx, Pos ny => 
    match N.compare nx ny with
    | Gt => Pos (N.sub nx ny)
    | Eq => zero
    | Lt => Neg (N.sub ny nx)
    end
  | Pos nx, Neg ny => Pos (N.add nx ny)
  | Neg nx, Pos ny => Neg (N.add nx ny)
  | Neg nx, Neg ny => 
    match N.compare nx ny with
    | Gt => Neg (N.sub nx ny)
    | Eq => zero
    | Lt => Pos (N.sub ny nx)
    end
  end.

 Theorem spec_sub: forall x y, to_Z (sub x y) = to_Z x - to_Z y.
 unfold sub, to_Z; intros [x | x] [y | y].
 unfold zero; generalize (N.spec_compare x y); case N.compare.
   rewrite N.spec_0; auto with zarith.
 intros; rewrite N.spec_sub; try ring; auto with zarith.
 intros; rewrite N.spec_sub; try ring; auto with zarith.
 rewrite N.spec_add; ring.
 rewrite N.spec_add; ring.
 unfold zero; generalize (N.spec_compare x y); case N.compare.
   rewrite N.spec_0; auto with zarith.
 intros; rewrite N.spec_sub; try ring; auto with zarith.
 intros; rewrite N.spec_sub; try ring; auto with zarith.
 Qed.

 Definition mul x y := 
  match x, y with
  | Pos nx, Pos ny => Pos (N.mul nx ny)
  | Pos nx, Neg ny => Neg (N.mul nx ny)
  | Neg nx, Pos ny => Neg (N.mul nx ny)
  | Neg nx, Neg ny => Pos (N.mul nx ny)
  end.


 Theorem spec_mul: forall x y, to_Z (mul x y) = to_Z x * to_Z y.
 unfold mul, to_Z; intros [x | x] [y | y]; rewrite N.spec_mul; ring.
 Qed.

 Definition square x := 
  match x with
  | Pos nx => Pos (N.square nx)
  | Neg nx => Pos (N.square nx)
  end.

 Theorem spec_square: forall x, to_Z (square x) = to_Z x *  to_Z x.
 unfold square, to_Z; intros [x | x]; rewrite N.spec_square; ring.
 Qed.

 Definition power_pos x p :=
  match x with
  | Pos nx => Pos (N.power_pos nx p)
  | Neg nx => 
    match p with
    | xH => x
    | xO _ => Pos (N.power_pos nx p)
    | xI _ => Neg (N.power_pos nx p)
    end
  end.

 Theorem spec_power_pos: forall x n, to_Z (power_pos x n) = to_Z x ^ Zpos n.
 assert (F0: forall x, (-x)^2 = x^2).
   intros x; rewrite Zpower_2; ring.
 unfold power_pos, to_Z; intros [x | x] [p | p |]; 
   try rewrite N.spec_power_pos; try ring.
 assert (F: 0 <= 2 * Zpos p).
  assert (0 <= Zpos p); auto with zarith.
 rewrite Zpos_xI; repeat rewrite Zpower_exp; auto with zarith.
 repeat rewrite Zpower_mult; auto with zarith.
 rewrite F0; ring.
 assert (F: 0 <= 2 * Zpos p).
  assert (0 <= Zpos p); auto with zarith.
 rewrite Zpos_xO; repeat rewrite Zpower_exp; auto with zarith.
 repeat rewrite Zpower_mult; auto with zarith.
 rewrite F0; ring.
 Qed.

 Definition sqrt x :=
  match x with
  | Pos nx => Pos (N.sqrt nx)
  | Neg nx => Neg N.zero
  end.


 Theorem spec_sqrt: forall x, 0 <= to_Z x -> 
   to_Z (sqrt x) ^ 2 <= to_Z x < (to_Z (sqrt x) + 1) ^ 2.
 unfold to_Z, sqrt; intros [x | x] H.
   exact (N.spec_sqrt x).
 replace (N.to_Z x) with 0.
   rewrite N.spec_0; simpl Zpower; unfold Zpower_pos, iter_pos;
    auto with zarith.
 generalize (N.spec_pos x); auto with zarith.
 Qed.

 Definition div_eucl x y :=
  match x, y with
  | Pos nx, Pos ny =>
    let (q, r) := N.div_eucl nx ny in
    (Pos q, Pos r)
  | Pos nx, Neg ny =>
    let (q, r) := N.div_eucl nx ny in
    match N.compare N.zero r with
    | Eq => (Neg q, zero)
    | _ => (Neg (N.succ q), Neg (N.sub ny r))
    end
  | Neg nx, Pos ny =>
    let (q, r) := N.div_eucl nx ny in
    match N.compare N.zero r with
    | Eq => (Neg q, zero)
    | _ => (Neg (N.succ q), Pos (N.sub ny r))
    end
  | Neg nx, Neg ny =>
    let (q, r) := N.div_eucl nx ny in
    (Pos q, Neg r)
  end.


 Theorem spec_div_eucl: forall x y,
      to_Z y <> 0 ->
      let (q,r) := div_eucl x y in
      (to_Z q, to_Z r) = Zdiv_eucl (to_Z x) (to_Z y).
 unfold div_eucl, to_Z; intros [x | x] [y | y] H.
 assert (H1: 0 < N.to_Z y).
   generalize (N.spec_pos y); auto with zarith.
 generalize (N.spec_div_eucl x y H1); case N.div_eucl; auto.
 assert (HH: 0 < N.to_Z y).
   generalize (N.spec_pos y); auto with zarith.
 generalize (N.spec_div_eucl x y HH); case N.div_eucl; auto.
 intros q r; generalize (N.spec_pos x) HH; unfold Zdiv_eucl;
   case_eq (N.to_Z x); case_eq (N.to_Z y); 
     try (intros; apply False_ind; auto with zarith; fail).
 intros p He1 He2 _ _ H1; injection H1; intros H2 H3.
 generalize (N.spec_compare N.zero r); case N.compare;
   unfold zero; rewrite N.spec_0; try rewrite H3; auto.
 rewrite H2; intros; apply False_ind; auto with zarith.
 rewrite H2; intros; apply False_ind; auto with zarith.
 intros p _ _ _ H1; discriminate H1.
 intros p He p1 He1 H1 _.
 generalize (N.spec_compare N.zero r); case N.compare.
 change (- Zpos p) with (Zneg p).
 unfold zero; lazy zeta.
 rewrite N.spec_0; intros H2; rewrite <- H2.
 intros H3; rewrite <- H3; auto.
 rewrite N.spec_0; intros H2.
 change (- Zpos p) with (Zneg p); lazy iota beta.
 intros H3; rewrite <- H3; auto.
 rewrite N.spec_succ; rewrite N.spec_sub.
 generalize H2; case (N.to_Z r).
 intros; apply False_ind; auto with zarith.
 intros p2 _; rewrite He; auto with zarith.
 change (Zneg p) with (- (Zpos p)); apply f_equal2 with (f := @pair Z Z); ring.
 intros p2 H4; discriminate H4.
 assert (N.to_Z r = (Zpos p1 mod (Zpos p))).
   unfold Zmod, Zdiv_eucl; rewrite <- H3; auto.
 case (Z_mod_lt (Zpos p1) (Zpos p)); auto with zarith.
 rewrite N.spec_0; intros H2; generalize (N.spec_pos r); 
   intros; apply False_ind; auto with zarith.
 assert (HH: 0 < N.to_Z y).
   generalize (N.spec_pos y); auto with zarith.
 generalize (N.spec_div_eucl x y HH); case N.div_eucl; auto.
 intros q r; generalize (N.spec_pos x) HH; unfold Zdiv_eucl;
   case_eq (N.to_Z x); case_eq (N.to_Z y); 
     try (intros; apply False_ind; auto with zarith; fail).
 intros p He1 He2 _ _ H1; injection H1; intros H2 H3.
 generalize (N.spec_compare N.zero r); case N.compare;
   unfold zero; rewrite N.spec_0; try rewrite H3; auto.
 rewrite H2; intros; apply False_ind; auto with zarith.
 rewrite H2; intros; apply False_ind; auto with zarith.
 intros p _ _ _ H1; discriminate H1.
 intros p He p1 He1 H1 _.
 generalize (N.spec_compare N.zero r); case N.compare.
 change (- Zpos p1) with (Zneg p1).
 unfold zero; lazy zeta.
 rewrite N.spec_0; intros H2; rewrite <- H2.
 intros H3; rewrite <- H3; auto.
 rewrite N.spec_0; intros H2.
 change (- Zpos p1) with (Zneg p1); lazy iota beta.
 intros H3; rewrite <- H3; auto.
 rewrite N.spec_succ; rewrite N.spec_sub.
 generalize H2; case (N.to_Z r).
 intros; apply False_ind; auto with zarith.
 intros p2 _; rewrite He; auto with zarith.
 intros p2 H4; discriminate H4.
 assert (N.to_Z r = (Zpos p1 mod (Zpos p))).
   unfold Zmod, Zdiv_eucl; rewrite <- H3; auto.
 case (Z_mod_lt (Zpos p1) (Zpos p)); auto with zarith.
 rewrite N.spec_0; generalize (N.spec_pos r); intros; apply False_ind; auto with zarith.
 assert (H1: 0 < N.to_Z y).
   generalize (N.spec_pos y); auto with zarith.
 generalize (N.spec_div_eucl x y H1); case N.div_eucl; auto.
 intros q r; generalize (N.spec_pos x) H1; unfold Zdiv_eucl;
   case_eq (N.to_Z x); case_eq (N.to_Z y); 
     try (intros; apply False_ind; auto with zarith; fail).
 change (-0) with 0; lazy iota beta; auto.
 intros p _ _ _ _ H2; injection H2.
 intros H3 H4; rewrite H3; rewrite H4; auto.
 intros p _ _ _ H2; discriminate H2.
 intros p He p1 He1 _ _  H2.
 change (- Zpos p1) with (Zneg p1); lazy iota beta.
 change (- Zpos p) with (Zneg p); lazy iota beta.
 rewrite <- H2; auto.
 Qed.

 Definition div x y := fst (div_eucl x y).

 Definition spec_div: forall x y,
     to_Z y <> 0 -> to_Z (div x y) = to_Z x / to_Z y.
 intros x y H1; generalize (spec_div_eucl x y H1); unfold div, Zdiv.
 case div_eucl; case Zdiv_eucl; simpl; auto.
 intros q r q11 r1 H; injection H; auto.
 Qed.

 Definition modulo x y := snd (div_eucl x y).

 Theorem spec_modulo:
   forall x y, to_Z y <> 0  -> to_Z (modulo x y) = to_Z x mod to_Z y.
 intros x y H1; generalize (spec_div_eucl x y H1); unfold modulo, Zmod.
 case div_eucl; case Zdiv_eucl; simpl; auto.
 intros q r q11 r1 H; injection H; auto.
 Qed.

 Definition gcd x y :=
  match x, y with
  | Pos nx, Pos ny => Pos (N.gcd nx ny)
  | Pos nx, Neg ny => Pos (N.gcd nx ny)
  | Neg nx, Pos ny => Pos (N.gcd nx ny)
  | Neg nx, Neg ny => Pos (N.gcd nx ny) 
  end.

 Theorem spec_gcd: forall a b, to_Z (gcd a b) = Zgcd (to_Z a) (to_Z b).
 unfold gcd, Zgcd, to_Z; intros [x | x] [y | y]; rewrite N.spec_gcd; unfold Zgcd;
  auto; case N.to_Z; simpl; auto with zarith;
  try rewrite Zabs_Zopp; auto;
  case N.to_Z; simpl; auto with zarith.
 Qed.

End Make.
