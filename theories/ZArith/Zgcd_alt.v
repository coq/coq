(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** * Zgcd_alt : an alternate version of Zgcd, based on Euler's algorithm *)

(**
Author: Pierre Letouzey
*)

(** The alternate [Zgcd_alt] given here used to be the main [Zgcd]
    function (see file [Znumtheory]), but this main [Zgcd] is now
    based on a modern binary-efficient algorithm. This earlier
    version, based on Euler's algorithm of iterated modulo, is kept
    here due to both its intrinsic interest and its use as reference
    point when proving gcd on Int31 numbers *)

Require Import ZArith_base.
Require Import ZArithRing.
Require Import Zdiv.
Require Import Znumtheory.

Open Scope Z_scope.

(** In Coq, we need to control the number of iteration of modulo.
   For that, we use an explicit measure in [nat], and we prove later
   that using [2*d] is enough, where [d] is the number of binary
   digits of the first argument. *)

 Fixpoint Zgcdn (n:nat) : Z -> Z -> Z := fun a b =>
   match n with
     | O => 1 (* arbitrary, since n should be big enough *)
     | S n => match a with
  	        | Z0 => Zabs b
  	        | Zpos _ => Zgcdn n (Zmod b a) a
  	        | Zneg a => Zgcdn n (Zmod b (Zpos a)) (Zpos a)
  	      end
   end.

 Definition Zgcd_bound (a:Z) :=
   match a with
     | Z0 => S O
     | Zpos p => let n := Psize p in (n+n)%nat
     | Zneg p => let n := Psize p in (n+n)%nat
   end.

 Definition Zgcd_alt a b := Zgcdn (Zgcd_bound a) a b.

 (** A first obvious fact : [Zgcd a b] is positive. *)

 Lemma Zgcdn_pos : forall n a b,
   0 <= Zgcdn n a b.
 Proof.
   induction n.
   simpl; auto with zarith.
   destruct a; simpl; intros; auto with zarith; auto.
 Qed.

 Lemma Zgcd_alt_pos : forall a b, 0 <= Zgcd_alt a b.
 Proof.
   intros; unfold Zgcd; apply Zgcdn_pos; auto.
 Qed.

 (** We now prove that Zgcd is indeed a gcd. *)

 (** 1) We prove a weaker & easier bound. *)

 Lemma Zgcdn_linear_bound : forall n a b,
   Zabs a < Z_of_nat n -> Zis_gcd a b (Zgcdn n a b).
 Proof.
   induction n.
   simpl; intros.
   exfalso; generalize (Zabs_pos a); omega.
   destruct a; intros; simpl;
     [ generalize (Zis_gcd_0_abs b); intuition | | ];
   unfold Zmod;
   generalize (Z_div_mod b (Zpos p) (refl_equal Gt));
   destruct (Zdiv_eucl b (Zpos p)) as (q,r);
   intros (H0,H1);
   rewrite inj_S in H; simpl Zabs in H;
   (assert (H2: Zabs r < Z_of_nat n) by
    (rewrite Zabs_eq; auto with zarith));
    assert (IH:=IHn r (Zpos p) H2); clear IHn;
    simpl in IH |- *;
    rewrite H0.
   apply Zis_gcd_for_euclid2; auto.
   apply Zis_gcd_minus; apply Zis_gcd_sym.
   apply Zis_gcd_for_euclid2; auto.
 Qed.

 (** 2) For Euclid's algorithm, the worst-case situation corresponds
    to Fibonacci numbers. Let's define them: *)

 Fixpoint fibonacci (n:nat) : Z :=
   match n with
     | O => 1
     | S O => 1
     | S (S n as p) => fibonacci p + fibonacci n
   end.

 Lemma fibonacci_pos : forall n, 0 <= fibonacci n.
 Proof.
   cut (forall N n, (n<N)%nat -> 0<=fibonacci n).
   eauto.
   induction N.
   inversion 1.
   intros.
   destruct n.
   simpl; auto with zarith.
   destruct n.
   simpl; auto with zarith.
   change (0 <= fibonacci (S n) + fibonacci n).
   generalize (IHN n) (IHN (S n)); omega.
 Qed.

 Lemma fibonacci_incr :
   forall n m, (n<=m)%nat -> fibonacci n <= fibonacci m.
 Proof.
   induction 1.
   auto with zarith.
   apply Zle_trans with (fibonacci m); auto.
   clear.
   destruct m.
   simpl; auto with zarith.
   change (fibonacci (S m) <= fibonacci (S m)+fibonacci m).
   generalize (fibonacci_pos m); omega.
 Qed.

 (** 3) We prove that fibonacci numbers are indeed worst-case:
    for a given number [n], if we reach a conclusion about [gcd(a,b)] in
    exactly [n+1] loops, then [fibonacci (n+1)<=a /\ fibonacci(n+2)<=b] *)

 Lemma Zgcdn_worst_is_fibonacci : forall n a b,
   0 < a < b ->
   Zis_gcd a b (Zgcdn (S n) a b) ->
   Zgcdn n a b <> Zgcdn (S n) a b ->
   fibonacci (S n) <= a /\
   fibonacci (S (S n)) <= b.
 Proof.
   induction n.
   simpl; intros.
   destruct a; omega.
   intros.
   destruct a; [simpl in *; omega| | destruct H; discriminate].
   revert H1; revert H0.
   set (m:=S n) in *; (assert (m=S n) by auto); clearbody m.
   pattern m at 2; rewrite H0.
   simpl Zgcdn.
   unfold Zmod; generalize (Z_div_mod b (Zpos p) (refl_equal Gt)).
   destruct (Zdiv_eucl b (Zpos p)) as (q,r).
   intros (H1,H2).
   destruct H2.
   destruct (Zle_lt_or_eq _ _ H2).
   generalize (IHn _ _ (conj H4 H3)).
   intros H5 H6 H7.
   replace (fibonacci (S (S m))) with (fibonacci (S m) + fibonacci m) by auto.
   assert (r = Zpos p * (-q) + b) by (rewrite H1; ring).
   destruct H5; auto.
   pattern r at 1; rewrite H8.
   apply Zis_gcd_sym.
   apply Zis_gcd_for_euclid2; auto.
   apply Zis_gcd_sym; auto.
   split; auto.
   rewrite H1.
   apply Zplus_le_compat; auto.
   apply Zle_trans with (Zpos p * 1); auto.
   ring_simplify (Zpos p * 1); auto.
   apply Zmult_le_compat_l.
   destruct q.
   omega.
   assert (0 < Zpos p0) by (compute; auto).
   omega.
   assert (Zpos p * Zneg p0 < 0) by (compute; auto).
   omega.
   compute; intros; discriminate.
   (* r=0 *)
   subst r.
   simpl; rewrite H0.
   intros.
   simpl in H4.
   simpl in H5.
   destruct n.
   simpl in H5.
   simpl.
   omega.
   simpl in H5.
   elim H5; auto.
 Qed.

 (** 3b) We reformulate the previous result in a more positive way. *)

 Lemma Zgcdn_ok_before_fibonacci : forall n a b,
   0 < a < b -> a < fibonacci (S n) ->
   Zis_gcd a b (Zgcdn n a b).
 Proof.
   destruct a; [ destruct 1; exfalso; omega | | destruct 1; discriminate].
   cut (forall k n b,
     k = (S (nat_of_P p) - n)%nat ->
     0 < Zpos p < b -> Zpos p < fibonacci (S n) ->
     Zis_gcd (Zpos p) b (Zgcdn n (Zpos p) b)).
   destruct 2; eauto.
   clear n; induction k.
   intros.
   assert (nat_of_P p < n)%nat by omega.
   apply Zgcdn_linear_bound.
   simpl.
   generalize (inj_le _ _ H2).
   rewrite inj_S.
   rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; auto.
   omega.
   intros.
   generalize (Zgcdn_worst_is_fibonacci n (Zpos p) b H0); intros.
   assert (Zis_gcd (Zpos p) b (Zgcdn (S n) (Zpos p) b)).
   apply IHk; auto.
   omega.
   replace (fibonacci (S (S n))) with (fibonacci (S n)+fibonacci n) by auto.
   generalize (fibonacci_pos n); omega.
   replace (Zgcdn n (Zpos p) b) with (Zgcdn (S n) (Zpos p) b); auto.
   generalize (H2 H3); clear H2 H3; omega.
 Qed.

 (** 4) The proposed bound leads to a fibonacci number that is big enough. *)

 Lemma Zgcd_bound_fibonacci :
   forall a, 0 < a -> a < fibonacci (Zgcd_bound a).
 Proof.
   destruct a; [omega| | intro H; discriminate].
   intros _.
   induction p; [ | | compute; auto ];
    simpl Zgcd_bound in *;
    rewrite plus_comm; simpl plus;
    set (n:= (Psize p+Psize p)%nat) in *; simpl;
    assert (n <> O) by (unfold n; destruct p; simpl; auto).

   destruct n as [ |m]; [elim H; auto| ].
   generalize (fibonacci_pos m); rewrite Zpos_xI; omega.

   destruct n as [ |m]; [elim H; auto| ].
   generalize (fibonacci_pos m); rewrite Zpos_xO; omega.
 Qed.

 (* 5) the end: we glue everything together and take care of
    situations not corresponding to [0<a<b]. *)

 Lemma Zgcdn_is_gcd :
   forall n a b, (Zgcd_bound a <= n)%nat ->
     Zis_gcd a b (Zgcdn n a b).
 Proof.
   destruct a; intros.
   simpl in H.
   destruct n; [exfalso; omega | ].
   simpl; generalize (Zis_gcd_0_abs b); intuition.
   (*Zpos*)
   generalize (Zgcd_bound_fibonacci (Zpos p)).
   simpl Zgcd_bound in *.
   remember (Psize p+Psize p)%nat as m.
   assert (1 < m)%nat.
     rewrite Heqm; destruct p; simpl; rewrite 1? plus_comm;
       auto with arith.
   destruct m as [ |m]; [inversion H0; auto| ].
   destruct n as [ |n]; [inversion H; auto| ].
   simpl Zgcdn.
   unfold Zmod.
   generalize (Z_div_mod b (Zpos p) (refl_equal Gt)).
   destruct (Zdiv_eucl b (Zpos p)) as (q,r).
   intros (H2,H3) H4.
   rewrite H2.
   apply Zis_gcd_for_euclid2.
   destruct H3.
   destruct (Zle_lt_or_eq _ _ H1).
   apply Zgcdn_ok_before_fibonacci; auto.
   apply Zlt_le_trans with (fibonacci (S m)); [ omega | apply fibonacci_incr; auto].
   subst r; simpl.
   destruct m as [ |m]; [exfalso; omega| ].
   destruct n as [ |n]; [exfalso; omega| ].
   simpl; apply Zis_gcd_sym; apply Zis_gcd_0.
   (*Zneg*)
   generalize (Zgcd_bound_fibonacci (Zpos p)).
   simpl Zgcd_bound in *.
   remember (Psize p+Psize p)%nat as m.
   assert (1 < m)%nat.
     rewrite Heqm; destruct p; simpl; rewrite 1? plus_comm;
       auto with arith.
   destruct m as [ |m]; [inversion H0; auto| ].
   destruct n as [ |n]; [inversion H; auto| ].
   simpl Zgcdn.
   unfold Zmod.
   generalize (Z_div_mod b (Zpos p) (refl_equal Gt)).
   destruct (Zdiv_eucl b (Zpos p)) as (q,r).
   intros (H1,H2) H3.
   rewrite H1.
   apply Zis_gcd_minus.
   apply Zis_gcd_sym.
   apply Zis_gcd_for_euclid2.
   destruct H2.
   destruct (Zle_lt_or_eq _ _ H2).
   apply Zgcdn_ok_before_fibonacci; auto.
   apply Zlt_le_trans with (fibonacci (S m)); [ omega | apply fibonacci_incr; auto].
   subst r; simpl.
   destruct m as [ |m]; [exfalso; omega| ].
   destruct n as [ |n]; [exfalso; omega| ].
   simpl; apply Zis_gcd_sym; apply Zis_gcd_0.
 Qed.

 Lemma Zgcd_is_gcd :
   forall a b, Zis_gcd a b (Zgcd_alt a b).
 Proof.
  unfold Zgcd_alt; intros; apply Zgcdn_is_gcd; auto.
 Qed.


