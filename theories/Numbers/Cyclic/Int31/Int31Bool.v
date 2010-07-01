Require Import ZArith.
Require Import BigNumPrelude.
Require Import List.
Require Import NaryFunctions.
Require Export Int31Native.

Local Open Scope Z_scope.

Definition digits31_type t := Eval compute in nfun bool size t.

Inductive Int31 : Type := I31 : digits31_type Int31.

(** Zero is [I31 D0 ... D0] *)
Definition On : Int31 := Eval compute in napply_cst _ _ false size I31.

(** One is [I31 D0 ... D0 D1] *)
Definition In : Int31 := Eval compute in (napply_cst _ _ false (size-1) I31) true.

Definition Zdigit_of_bool (b:bool) := 
  if b then Zdouble_plus_one else Zdouble.

Definition Int31_to_Z :=
  Int31_rect (fun _ => Z) (nfold bool Z Zdigit_of_bool 0%Z size).

Definition sneakr : bool -> Int31 -> Int31 := Eval compute in
 fun b => Int31_rect _ (napply_except_last _ _ (size-1) (I31 b)).

Definition sneakl : bool -> Int31 -> Int31 := Eval compute in
 fun b => Int31_rect _ (fun _ => napply_then_last _ _ b (size-1) I31).

Definition shiftl := sneakl false.
Definition shiftr := sneakr false.
Definition twice := sneakl false.
Definition twice_plus_one := sneakl true.
Definition nshiftl n := iter_nat n _ shiftl.
Definition nshiftr n := iter_nat n _ shiftr.

Lemma Zdouble_mod2 : forall n x, Zdouble x mod 2^(Z_of_nat (S n)) = Zdouble (x mod 2 ^ Z_of_nat n).
Proof.
 intros;rewrite inj_S, Zdouble_mult, Zpower_Zsucc, 
  Zmult_mod_distr_l, <- Zdouble_mult;auto with zarith.
Qed.
 
Lemma Zdouble_plus_one_mod2 : forall n x, (0 <= x)%Z ->
   Zdouble_plus_one x mod 2^(Z_of_nat (S n)) = Zdouble_plus_one (x mod 2 ^ Z_of_nat n).
Proof.
 intros;rewrite Zdouble_plus_one_mult.
 replace (2 * x + 1)%Z with (x * 2 ^ 1 + 1)%Z;[ | ring].
 rewrite Zmod_shift_r, Zmult_comm;change (2^1)%Z with 2%Z;auto with zarith.
 rewrite <- Zdouble_mult, Zdouble_mod2, Zdouble_plus_one_mult, Zdouble_mult;trivial.
 rewrite inj_S;auto with zarith.
Qed.

Lemma Zdigit_of_bool_mod2 : forall n x b, (0<=x)%Z ->
  Zdigit_of_bool b x mod 2^(Z_of_nat (S n)) = Zdigit_of_bool b (x mod 2^(Z_of_nat n)).
Proof.
 intros n x b H;destruct b;auto using Zdouble_mod2, Zdouble_plus_one_mod2.
Qed.

Lemma Zdigit_of_bool_pos : forall x b, (0 <= x)%Z -> (0 <= Zdigit_of_bool b x)%Z.
Proof.
 destruct b;intros;[rewrite Zdouble_plus_one_mult | rewrite Zdouble_mult];auto with zarith.
Qed.

Ltac pos_Zdigit x := 
  match x with 
  | Zdigit_of_bool ?b' ?x' => 
    pos_Zdigit x';
    assert (0 <= x)%Z;[apply Zdigit_of_bool_pos;trivial | ]
  | _ => assert (0 <= x)%Z;[auto with zarith| ]
  end.

Lemma twice_spec : forall x, Int31_to_Z (twice x) = (Int31_to_Z x * 2 mod 2 ^ (Z_of_nat size)) %Z.
Proof.
 assert (H : forall s, s = size -> forall x,Int31_to_Z (twice x) = (Int31_to_Z x * 2 mod 2 ^ (Z_of_nat s)));
   [ | apply H;trivial].
 destruct x;simpl.
 rewrite Zmult_comm.
 match goal with
  |- (_ = (2 * ?p) mod _) => change (2 * p)%Z with (Zdouble p) end.
 rewrite H;unfold size;rewrite Zdouble_mod2.
 match goal with |- _ = Zdouble (?x mod _) => pos_Zdigit x end.
 repeat (rewrite Zdigit_of_bool_mod2;[ | trivial]).
 replace (Zdigit_of_bool b 0 mod 2 ^ Z_of_nat 0)%Z with 0%Z;trivial.
 simpl;rewrite Zmod_1_r;trivial.
Qed.

Lemma twice_plus_one_spec : forall x, Int31_to_Z (twice_plus_one x) = ((Int31_to_Z x * 2 + 1)%Z mod 2 ^ (Z_of_nat size)) %Z.
Proof.
 assert (H : forall s, s = size -> forall x,Int31_to_Z (twice_plus_one x) = ((Int31_to_Z x * 2 + 1)%Z mod 2 ^ (Z_of_nat s)));
   [ | apply H;trivial].
 destruct x;simpl.
 rewrite Zmult_comm.
 rewrite <- Zdouble_plus_one_mult.
 match goal with |- _ = Zdouble_plus_one ?x mod _ => pos_Zdigit x end.
 rewrite H;unfold size;rewrite Zdouble_plus_one_mod2;trivial.
 repeat (rewrite Zdigit_of_bool_mod2;[ | trivial]).
 replace (Zdigit_of_bool b 0 mod 2 ^ Z_of_nat 0)%Z with 0%Z;trivial.
 simpl;rewrite Zmod_1_r;trivial.
Qed.

Lemma Zdigit_fo_bool_div2 : forall b x, (Zdigit_of_bool b x / 2 =  x)%Z.
Proof.
 intros b x;destruct b;simpl.
 rewrite Zdouble_plus_one_mult, Zmult_comm, Z_div_plus_l;[ | reflexivity].
 unfold Zdiv;simpl;rewrite Zplus_0_r;trivial.
 rewrite Zdouble_mult, <- (Zplus_0_r (2 * x)),Zmult_comm,Z_div_plus_l;[ | reflexivity].
 unfold Zdiv;simpl;rewrite Zplus_0_r;trivial.
Qed.

Lemma shiftr_spec : forall x, Int31_to_Z (shiftr x) = (Int31_to_Z x / 2)%Z.
Proof.
 destruct x;simpl.
 rewrite Zdigit_fo_bool_div2;trivial.
Qed.

Fixpoint nprod_map2 (A B C:Type) (f:A->B->C) n : A^n -> B^n -> C^n :=
 match n as n0 return A^n0 -> B^n0 -> C^n0 with
 | O => fun _ _ => tt
 | S n => 
   fun ap bp =>
     let (a,pa) := ap in
     let (b,pb) := bp in
     (f a b, nprod_map2 A B C f n pa pb)
 end.

Definition nfun_map2 (A B C D:Type) (f:A->B->C) n (construct:C^^n --> D) : A^^n --> (B^^n --> D).
apply ncurry; intros pa.
apply ncurry; intros pb .
apply (nuncurry _ _ n construct (nprod_map2 _ _ _ f n pa pb)).
Defined.

Definition Ilor (x y : Int31) :=
 Int31_rect (fun _ => Int31) (Int31_rect _ (nfun_map2 _ _ _ _ orb size I31) x) y.

Definition Iland (x y : Int31) :=
 Int31_rect (fun _ => Int31) (Int31_rect _ (nfun_map2 _ _ _ _ andb size I31) x) y.

Definition Ilxor (x y : Int31) :=
 Int31_rect (fun _ => Int31) (Int31_rect _ (nfun_map2 _ _ _ _ xorb size I31) x) y.

(** Translation to Z *)
Lemma Zdigit_of_bool_inj : forall b1 z1 b2 z2, 
  Zdigit_of_bool b1 z1 = Zdigit_of_bool b2 z2 -> b1 = b2 /\ z1 = z2.
Proof.
 destruct b1;destruct b2;simpl;intros z2;
  repeat (rewrite Zdouble_plus_one_mult || rewrite Zdouble_mult);intros.
 split;[trivial | omega].
 assert (W:= Zdouble_mult z2);elimtype False;omega.
 elimtype False;omega.
 assert (W:= Zdouble_mult z2);split;[trivial | omega].
Qed.

Lemma Int31_to_Z_inj : forall x y, Int31_to_Z x = Int31_to_Z y -> x = y.
Proof.
 destruct x;destruct y;simpl;intros H.
 repeat match goal with [H: Zdigit_of_bool _ _ = Zdigit_of_bool _ _ |- _ ] =>
  apply Zdigit_of_bool_inj in H;destruct H end;subst;trivial.
Qed.

Fixpoint Int31_of_pos (n:nat) (p:positive) :=
  match n, p with 
  | O, _ => On
  | S n, xH => In
  | S n, xO p => twice (Int31_of_pos n p) 
  | S n, xI p => twice_plus_one (Int31_of_pos n p)
  end.

Definition Int31_of_Z z := 
  match z with
  | Zpos p => Int31_of_pos size p
  | _ => On
  end.

Lemma Int31_to_of_pos : forall n p,
  (n <= size)%nat ->
  Int31_to_Z (Int31_of_pos n p) = Zpos p mod 2 ^ (Z_of_nat n).
Proof.
 induction n;intros.
 change (0 = Zpos p mod 1);rewrite Zmod_1_r;trivial.
 simpl Int31_of_pos.
 assert (2 ^ Z_of_nat n > 0) by auto with zarith.
 assert (0 < 2) by auto with zarith.
 assert (0 <= Z_of_nat (S n) <= Z_of_nat size) 
  by (split;auto with zarith;apply inj_le;trivial).
 destruct p.
 rewrite twice_plus_one_spec, IHn;[ | auto with arith].
 rewrite Zmod_small.
 change (Zpos p~1) with (1 + 2*Zpos p);rewrite (Zplus_comm 1).
 rewrite <- Zdouble_plus_one_mult, Zdouble_plus_one_mod2, Zdouble_plus_one_mult.
 ring. auto with zarith.
 assert (W:= Z_mod_lt (Zpos p) (2 ^ Z_of_nat n) H0).
 assert (W1:=Zpower_le_monotone 2 (Z_of_nat (S n)) (Z_of_nat size) H1 H2).
 rewrite inj_S, Zpower_Zsucc in W1;auto with zarith.
 rewrite twice_spec, IHn;[ | auto with arith].
 rewrite Zmod_small.
 change (Zpos p~0) with (2*Zpos p).
 rewrite <- Zdouble_mult, Zdouble_mod2, Zdouble_mult.
 ring.
 assert (W:= Z_mod_lt (Zpos p) (2 ^ Z_of_nat n) H0).
 assert (W1:=Zpower_le_monotone 2 (Z_of_nat (S n)) (Z_of_nat size) H1 H2).
 rewrite inj_S, Zpower_Zsucc in W1;auto with zarith.
 rewrite Zmod_small;[trivial | ].
 split;[auto with zarith | ].
 rewrite inj_S;assert (W:= Zpower2_lt_lin (Zsucc (Z_of_nat n)));auto with zarith.
Qed.

Lemma Int31_to_of_Z_le : forall x, 0 <= x -> Int31_to_Z (Int31_of_Z x) = x mod 2 ^ (Z_of_nat size).
Proof.
 destruct x;intros.
 rewrite Zmod_0_l;trivial.
 unfold Int31_of_Z;intros;rewrite Int31_to_of_pos;trivial.
 elim H;trivial.
Qed.

Lemma Int31_to_of_Z_bound : forall x, 0 <= x < 2^(Z_of_nat size) -> 
  Int31_to_Z (Int31_of_Z x) = x.
Proof.
 intros;rewrite Int31_to_of_Z_le, Zmod_small;auto with zarith.
Qed.

Lemma Zdigit_of_bool_bounded : forall n z b,
  0 <= z < 2 ^ Z_of_nat n -> 
  0 <= Zdigit_of_bool b z < 2 ^ Z_of_nat (S n).
Proof.
 intros;rewrite inj_S, Zpower_Zsucc;[ | auto with zarith].
 destruct b;unfold Zdigit_of_bool;
 [rewrite Zdouble_plus_one_mult | rewrite Zdouble_mult] ;auto with zarith.
Qed.

Lemma Int31_to_Z_bounded : forall x, 0 <= Int31_to_Z x < 2 ^ (Z_of_nat size).
Proof.
 destruct x; simpl Int31_to_Z.
 unfold size;repeat apply Zdigit_of_bool_bounded.
 compute;split;[discriminate | trivial].
Qed.

Lemma Int31_of_to_Z : forall x, Int31_of_Z (Int31_to_Z x) = x.
Proof.
 intros;apply Int31_to_Z_inj.
 rewrite Int31_to_of_Z_bound;auto using Int31_to_Z_bounded.
Qed.

