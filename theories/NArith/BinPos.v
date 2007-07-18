(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Unset Boxed Definitions.

(**********************************************************************)
(** Binary positive numbers *)

(** Original development by Pierre Crégut, CNET, Lannion, France *)

Inductive positive : Set :=
| xI : positive -> positive
| xO : positive -> positive
| xH : positive.

(** Declare binding key for scope positive_scope *)

Delimit Scope positive_scope with positive.

(** Automatically open scope positive_scope for type positive, xO and xI *)

Bind Scope positive_scope with positive.
Arguments Scope xO [positive_scope].
Arguments Scope xI [positive_scope].

(** Successor *)

Fixpoint Psucc (x:positive) : positive :=
  match x with
    | xI x' => xO (Psucc x')
    | xO x' => xI x'
    | xH => xO xH
  end.

(** Addition *)

Set Boxed Definitions.

Fixpoint Pplus (x y:positive) {struct x} : positive :=
  match x, y with
    | xI x', xI y' => xO (Pplus_carry x' y')
    | xI x', xO y' => xI (Pplus x' y')
    | xI x', xH => xO (Psucc x')
    | xO x', xI y' => xI (Pplus x' y')
    | xO x', xO y' => xO (Pplus x' y')
    | xO x', xH => xI x'
    | xH, xI y' => xO (Psucc y')
    | xH, xO y' => xI y'
    | xH, xH => xO xH
  end
  
with Pplus_carry (x y:positive) {struct x} : positive :=
  match x, y with
    | xI x', xI y' => xI (Pplus_carry x' y')
    | xI x', xO y' => xO (Pplus_carry x' y')
    | xI x', xH => xI (Psucc x')
    | xO x', xI y' => xO (Pplus_carry x' y')
    | xO x', xO y' => xI (Pplus x' y')
    | xO x', xH => xO (Psucc x')
    | xH, xI y' => xI (Psucc y')
    | xH, xO y' => xO (Psucc y')
    | xH, xH => xI xH
  end.

Unset Boxed Definitions.

Infix "+" := Pplus : positive_scope.

Open Local Scope positive_scope.

(** From binary positive numbers to Peano natural numbers *)

Fixpoint Pmult_nat (x:positive) (pow2:nat) {struct x} : nat :=
  match x with
    | xI x' => (pow2 + Pmult_nat x' (pow2 + pow2))%nat
    | xO x' => Pmult_nat x' (pow2 + pow2)%nat
    | xH => pow2
  end.

Definition nat_of_P (x:positive) := Pmult_nat x 1.

(** From Peano natural numbers to binary positive numbers *)

Fixpoint P_of_succ_nat (n:nat) : positive :=
  match n with
    | O => xH
    | S x' => Psucc (P_of_succ_nat x')
  end.

(** Operation x -> 2*x-1 *)

Fixpoint Pdouble_minus_one (x:positive) : positive :=
  match x with
    | xI x' => xI (xO x')
    | xO x' => xI (Pdouble_minus_one x')
    | xH => xH
  end.

(** Predecessor *)

Definition Ppred (x:positive) :=
  match x with
    | xI x' => xO x'
    | xO x' => Pdouble_minus_one x'
    | xH => xH
  end.

(** An auxiliary type for subtraction *)

Inductive positive_mask : Set :=
| IsNul : positive_mask
| IsPos : positive -> positive_mask
| IsNeg : positive_mask.

(** Operation x -> 2*x+1 *)

Definition Pdouble_plus_one_mask (x:positive_mask) :=
  match x with
    | IsNul => IsPos xH
    | IsNeg => IsNeg
    | IsPos p => IsPos (xI p)
  end.

(** Operation x -> 2*x *)

Definition Pdouble_mask (x:positive_mask) :=
  match x with
    | IsNul => IsNul
    | IsNeg => IsNeg
    | IsPos p => IsPos (xO p)
  end.

(** Operation x -> 2*x-2 *)

Definition Pdouble_minus_two (x:positive) :=
  match x with
    | xI x' => IsPos (xO (xO x'))
    | xO x' => IsPos (xO (Pdouble_minus_one x'))
    | xH => IsNul
  end.

(** Subtraction of binary positive numbers into a positive numbers mask *)

Fixpoint Pminus_mask (x y:positive) {struct y} : positive_mask :=
  match x, y with
    | xI x', xI y' => Pdouble_mask (Pminus_mask x' y')
    | xI x', xO y' => Pdouble_plus_one_mask (Pminus_mask x' y')
    | xI x', xH => IsPos (xO x')
    | xO x', xI y' => Pdouble_plus_one_mask (Pminus_mask_carry x' y')
    | xO x', xO y' => Pdouble_mask (Pminus_mask x' y')
    | xO x', xH => IsPos (Pdouble_minus_one x')
    | xH, xH => IsNul
    | xH, _ => IsNeg
  end
  
with Pminus_mask_carry (x y:positive) {struct y} : positive_mask :=
  match x, y with
    | xI x', xI y' => Pdouble_plus_one_mask (Pminus_mask_carry x' y')
    | xI x', xO y' => Pdouble_mask (Pminus_mask x' y')
    | xI x', xH => IsPos (Pdouble_minus_one x')
    | xO x', xI y' => Pdouble_mask (Pminus_mask_carry x' y')
    | xO x', xO y' => Pdouble_plus_one_mask (Pminus_mask_carry x' y')
    | xO x', xH => Pdouble_minus_two x'
    | xH, _ => IsNeg
  end.

(** Subtraction of binary positive numbers x and y, returns 1 if x<=y *)

Definition Pminus (x y:positive) :=
  match Pminus_mask x y with
    | IsPos z => z
    | _ => xH
  end.

Infix "-" := Pminus : positive_scope.

(** Multiplication on binary positive numbers *)

Fixpoint Pmult (x y:positive) {struct x} : positive :=
  match x with
    | xI x' => y + xO (Pmult x' y)
    | xO x' => xO (Pmult x' y)
    | xH => y
  end.

Infix "*" := Pmult : positive_scope.

(** Division by 2 rounded below but for 1 *)

Definition Pdiv2 (z:positive) :=
  match z with
    | xH => xH
    | xO p => p
    | xI p => p
  end.

Infix "/" := Pdiv2 : positive_scope.

(** Comparison on binary positive numbers *)

Fixpoint Pcompare (x y:positive) (r:comparison) {struct y} : comparison :=
  match x, y with
    | xI x', xI y' => Pcompare x' y' r
    | xI x', xO y' => Pcompare x' y' Gt
    | xI x', xH => Gt
    | xO x', xI y' => Pcompare x' y' Lt
    | xO x', xO y' => Pcompare x' y' r
    | xO x', xH => Gt
    | xH, xI y' => Lt
    | xH, xO y' => Lt
    | xH, xH => r
  end.

Infix "?=" := Pcompare (at level 70, no associativity) : positive_scope.

Definition Plt (x y:positive) := (Pcompare x y Eq) = Lt.
Definition Pgt (x y:positive) := (Pcompare x y Eq) = Gt.
Definition Ple (x y:positive) := (Pcompare x y Eq) <> Gt.
Definition Pge (x y:positive) := (Pcompare x y Eq) <> Lt.

Infix "<=" := Ple : positive_scope.
Infix "<" := Plt : positive_scope.
Infix ">=" := Pge : positive_scope.
Infix ">" := Pgt : positive_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : positive_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : positive_scope.
Notation "x < y < z" := (x < y /\ y < z) : positive_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : positive_scope.


Definition Pmin (p p' : positive) := match Pcompare p p' Eq with 
 | Lt | Eq => p 
 | Gt => p'
 end.

Definition Pmax (p p' : positive) := match Pcompare p p' Eq with 
 | Lt | Eq => p' 
 | Gt => p
 end.

(**********************************************************************)
(** Miscellaneous properties of binary positive numbers *)

Lemma ZL11 : forall p:positive, p = xH \/ p <> xH.
Proof.
  intros x; case x; intros; (left; reflexivity) || (right; discriminate).
Qed.

(**********************************************************************)
(** Properties of successor on binary positive numbers *)

(** Specification of [xI] in term of [Psucc] and [xO] *)

Lemma xI_succ_xO : forall p:positive, xI p = Psucc (xO p).
Proof.
  reflexivity.
Qed.

Lemma Psucc_discr : forall p:positive, p <> Psucc p.
Proof.
  intro x; destruct x as [p| p| ]; discriminate.
Qed.

(** Successor and double *)

Lemma Psucc_o_double_minus_one_eq_xO :
  forall p:positive, Psucc (Pdouble_minus_one p) = xO p.
Proof.
  intro x; induction x as [x IHx| x| ]; simpl in |- *; try rewrite IHx;
    reflexivity.
Qed.

Lemma Pdouble_minus_one_o_succ_eq_xI :
  forall p:positive, Pdouble_minus_one (Psucc p) = xI p.
Proof.
  intro x; induction x as [x IHx| x| ]; simpl in |- *; try rewrite IHx;
    reflexivity.
Qed.

Lemma xO_succ_permute :
  forall p:positive, xO (Psucc p) = Psucc (Psucc (xO p)).
Proof.
  intro y; induction  y as [y Hrecy| y Hrecy| ]; simpl in |- *; auto.
Qed.

Lemma double_moins_un_xO_discr :
  forall p:positive, Pdouble_minus_one p <> xO p.
Proof.
  intro x; destruct x as [p| p| ]; discriminate.
Qed.

(** Successor and predecessor *)

Lemma Psucc_not_one : forall p:positive, Psucc p <> xH.
Proof.
  intro x; destruct x as [x| x| ]; discriminate.
Qed.

Lemma Ppred_succ : forall p:positive, Ppred (Psucc p) = p.
Proof.
  intro x; destruct x as [p| p| ]; [ idtac | idtac | simpl in |- *; auto ];
    (induction p as [p IHp| | ]; [ idtac | reflexivity | reflexivity ]);
    simpl in |- *; simpl in IHp; try rewrite <- IHp; reflexivity.
Qed.

Lemma Psucc_pred : forall p:positive, p = xH \/ Psucc (Ppred p) = p.
Proof.
  intro x; induction  x as [x Hrecx| x Hrecx| ];
    [ simpl in |- *; auto
      | simpl in |- *; intros; right; apply Psucc_o_double_minus_one_eq_xO
      | auto ].
Qed.

(** Injectivity of successor *)

Lemma Psucc_inj : forall p q:positive, Psucc p = Psucc q -> p = q.
Proof.
  intro x; induction x; intro y; destruct y as [y| y| ]; simpl in |- *; intro H;
    discriminate H || (try (injection H; clear H; intro H)).
  rewrite (IHx y H); reflexivity.
  absurd (Psucc x = xH); [ apply Psucc_not_one | assumption ].
  apply f_equal with (1 := H); assumption.
  absurd (Psucc y = xH);
    [ apply Psucc_not_one | symmetry  in |- *; assumption ].
  reflexivity.
Qed.

(**********************************************************************)
(** Properties of addition on binary positive numbers *)

(** Specification of [Psucc] in term of [Pplus] *)

Lemma Pplus_one_succ_r : forall p:positive, Psucc p = p + xH.
Proof.
  intro q; destruct q as [p| p| ]; reflexivity.
Qed.

Lemma Pplus_one_succ_l : forall p:positive, Psucc p = xH + p.
Proof.
  intro q; destruct q as [p| p| ]; reflexivity.
Qed.

(** Specification of [Pplus_carry] *)

Theorem Pplus_carry_spec :
  forall p q:positive, Pplus_carry p q = Psucc (p + q).
Proof.
  intro x; induction x as [p IHp| p IHp| ]; intro y;
    [ destruct y as [p0| p0| ]
      | destruct y as [p0| p0| ]
      | destruct y as [p| p| ] ]; simpl in |- *; auto; rewrite IHp; 
    auto.
Qed.

(** Commutativity *)

Theorem Pplus_comm : forall p q:positive, p + q = q + p.
Proof.
  intro x; induction x as [p IHp| p IHp| ]; intro y;
    [ destruct y as [p0| p0| ]
      | destruct y as [p0| p0| ]
      | destruct y as [p| p| ] ]; simpl in |- *; auto;
    try do 2 rewrite Pplus_carry_spec; rewrite IHp; auto.
Qed. 

(** Permutation of [Pplus] and [Psucc] *)

Theorem Pplus_succ_permute_r :
  forall p q:positive, p + Psucc q = Psucc (p + q).
Proof.
  intro x; induction x as [p IHp| p IHp| ]; intro y;
    [ destruct y as [p0| p0| ]
      | destruct y as [p0| p0| ]
      | destruct y as [p| p| ] ]; simpl in |- *; auto;
    [ rewrite Pplus_carry_spec; rewrite IHp; auto
      | rewrite Pplus_carry_spec; auto
      | destruct p; simpl in |- *; auto
      | rewrite IHp; auto
      | destruct p; simpl in |- *; auto ].
Qed.

Theorem Pplus_succ_permute_l :
  forall p q:positive, Psucc p + q = Psucc (p + q).
Proof.
  intros x y; rewrite Pplus_comm; rewrite Pplus_comm with (p := x);
    apply Pplus_succ_permute_r.
Qed.

Theorem Pplus_carry_pred_eq_plus :
  forall p q:positive, q <> xH -> Pplus_carry p (Ppred q) = p + q.
Proof.
  intros q z H; elim (Psucc_pred z);
    [ intro; absurd (z = xH); auto
      | intros E; pattern z at 2 in |- *; rewrite <- E;
        rewrite Pplus_succ_permute_r; rewrite Pplus_carry_spec; 
          trivial ].
Qed. 

(** No neutral for addition on strictly positive numbers *)

Lemma Pplus_no_neutral : forall p q:positive, q + p <> p.
Proof.
  intro x; induction x; intro y; destruct y as [y| y| ]; simpl in |- *; intro H;
    discriminate H || injection H; clear H; intro H; apply (IHx y H).
Qed.

Lemma Pplus_carry_no_neutral :
  forall p q:positive, Pplus_carry q p <> Psucc p.
Proof.
  intros x y H; absurd (y + x = x);
    [ apply Pplus_no_neutral
      | apply Psucc_inj; rewrite <- Pplus_carry_spec; assumption ].
Qed.

(** Simplification *)

Lemma Pplus_carry_plus :
  forall p q r s:positive, Pplus_carry p r = Pplus_carry q s -> p + r = q + s.
Proof.
  intros x y z t H; apply Psucc_inj; do 2 rewrite <- Pplus_carry_spec;
    assumption.
Qed.

Lemma Pplus_reg_r : forall p q r:positive, p + r = q + r -> p = q.
Proof.
  intros x y z; generalize x y; clear x y.
  induction z as [z| z| ].
  destruct x as [x| x| ]; intro y; destruct y as [y| y| ]; simpl in |- *;
    intro H; discriminate H || (try (injection H; clear H; intro H)).
  rewrite IHz with (1 := Pplus_carry_plus _ _ _ _ H); reflexivity.
  absurd (Pplus_carry x z = Psucc z);
    [ apply Pplus_carry_no_neutral | assumption ].
  rewrite IHz with (1 := H); reflexivity.
  symmetry  in H; absurd (Pplus_carry y z = Psucc z);
    [ apply Pplus_carry_no_neutral | assumption ].
  reflexivity.
  destruct x as [x| x| ]; intro y; destruct y as [y| y| ]; simpl in |- *;
    intro H; discriminate H || (try (injection H; clear H; intro H)).
  rewrite IHz with (1 := H); reflexivity.
  absurd (x + z = z); [ apply Pplus_no_neutral | assumption ].
  rewrite IHz with (1 := H); reflexivity.
  symmetry  in H; absurd (y + z = z);
    [ apply Pplus_no_neutral | assumption ].
  reflexivity.
  intros H x y; apply Psucc_inj; do 2 rewrite Pplus_one_succ_r; assumption.
Qed.

Lemma Pplus_reg_l : forall p q r:positive, p + q = p + r -> q = r.
Proof.
  intros x y z H; apply Pplus_reg_r with (r := x);
    rewrite Pplus_comm with (p := z); rewrite Pplus_comm with (p := y);
      assumption.
Qed.

Lemma Pplus_carry_reg_r :
  forall p q r:positive, Pplus_carry p r = Pplus_carry q r -> p = q.
Proof.
  intros x y z H; apply Pplus_reg_r with (r := z); apply Pplus_carry_plus;
    assumption.
Qed.

Lemma Pplus_carry_reg_l :
  forall p q r:positive, Pplus_carry p q = Pplus_carry p r -> q = r.
Proof.
  intros x y z H; apply Pplus_reg_r with (r := x);
    rewrite Pplus_comm with (p := z); rewrite Pplus_comm with (p := y);
      apply Pplus_carry_plus; assumption.
Qed.

(** Addition on positive is associative *)

Theorem Pplus_assoc : forall p q r:positive, p + (q + r) = p + q + r.
Proof.
  intros x y; generalize x; clear x.
  induction y as [y| y| ]; intro x.
  destruct x as [x| x| ]; intro z; destruct z as [z| z| ]; simpl in |- *;
    repeat rewrite Pplus_carry_spec; repeat rewrite Pplus_succ_permute_r;
      repeat rewrite Pplus_succ_permute_l;
        reflexivity || (repeat apply f_equal with (A := positive)); 
          apply IHy.
  destruct x as [x| x| ]; intro z; destruct z as [z| z| ]; simpl in |- *;
    repeat rewrite Pplus_carry_spec; repeat rewrite Pplus_succ_permute_r;
      repeat rewrite Pplus_succ_permute_l;
        reflexivity || (repeat apply f_equal with (A := positive)); 
          apply IHy.
  intro z; rewrite Pplus_comm with (p := xH);
    do 2 rewrite <- Pplus_one_succ_r; rewrite Pplus_succ_permute_l;
      rewrite Pplus_succ_permute_r; reflexivity.
Qed.

(** Commutation of addition with the double of a positive number *)

Lemma Pplus_xO : forall m n : positive, xO (m + n) = xO m + xO n.
Proof.
  destruct n; destruct m; simpl; auto.
Qed.

Lemma Pplus_xI_double_minus_one :
  forall p q:positive, xO (p + q) = xI p + Pdouble_minus_one q.
Proof.
  intros; change (xI p) with (xO p + xH) in |- *.
  rewrite <- Pplus_assoc; rewrite <- Pplus_one_succ_l;
    rewrite Psucc_o_double_minus_one_eq_xO.
  reflexivity.
Qed.

Lemma Pplus_xO_double_minus_one :
  forall p q:positive, Pdouble_minus_one (p + q) = xO p + Pdouble_minus_one q.
Proof.
  induction p as [p IHp| p IHp| ]; destruct q as [q| q| ]; simpl in |- *;
    try rewrite Pplus_carry_spec; try rewrite Pdouble_minus_one_o_succ_eq_xI;
      try rewrite IHp; try rewrite Pplus_xI_double_minus_one; 
        try reflexivity.
  rewrite <- Psucc_o_double_minus_one_eq_xO; rewrite Pplus_one_succ_l;
    reflexivity. 
Qed.

(** Misc *)

Lemma Pplus_diag : forall p:positive, p + p = xO p.
Proof.
  intro x; induction x; simpl in |- *; try rewrite Pplus_carry_spec;
    try rewrite IHx; reflexivity.
Qed.

(**********************************************************************)
(** Peano induction and recursion on binary positive positive numbers *)
(** (a nice proof from Conor McBride, see "The view from the left")   *)

Inductive PeanoView : positive -> Type :=
| PeanoOne : PeanoView xH
| PeanoSucc : forall p, PeanoView p -> PeanoView (Psucc p).

Fixpoint peanoView_xO p (q:PeanoView p) {struct q} : PeanoView (xO p) :=
  match q in PeanoView x return PeanoView (xO x) with
    | PeanoOne => PeanoSucc _ PeanoOne
    | PeanoSucc _ q => PeanoSucc _ (PeanoSucc _ (peanoView_xO _ q))
  end.

Fixpoint peanoView_xI p (q:PeanoView p) {struct q} : PeanoView (xI p) :=
  match q in PeanoView x return PeanoView (xI x) with
    | PeanoOne => PeanoSucc _ (PeanoSucc _ PeanoOne)
    | PeanoSucc _ q => PeanoSucc _ (PeanoSucc _ (peanoView_xI _ q))
  end.

Fixpoint peanoView p : PeanoView p :=
  match p return PeanoView p with
    | xH => PeanoOne
    | xO p => peanoView_xO p (peanoView p)
    | xI p => peanoView_xI p (peanoView p)
  end.

Definition PeanoView_iter (P:positive->Type) 
  (a:P xH) (f:forall p, P p -> P (Psucc p)) :=
  (fix iter p (q:PeanoView p) : P p :=
    match q in PeanoView p return P p with 
      | PeanoOne => a
      | PeanoSucc _ q => f _ (iter _ q)
    end).

Require Import Eqdep_dec EqdepFacts.

Theorem eq_dep_eq_positive :
  forall (P:positive->Type) (p:positive) (x y:P p), 
    eq_dep positive P p x p y -> x = y.
Proof.
  apply eq_dep_eq_dec.
  decide equality.
Qed.

Theorem PeanoViewUnique : forall p (q q':PeanoView p), q = q'.  
Proof.
  intros. 
  induction q. 
  apply eq_dep_eq_positive. 
  cut (xH=xH). pattern xH at 1 2 5, q'. destruct q'. trivial.
  destruct p0; intros; discriminate.
  trivial.
  apply eq_dep_eq_positive.
  cut (Psucc p=Psucc p). pattern (Psucc p) at 1 2 5, q'. destruct q'. 
  intro. destruct p; discriminate.
  intro. unfold p0 in H. apply Psucc_inj in H.
  generalize q'. rewrite H. intro.
  rewrite (IHq q'0).
  trivial.
  trivial.
Qed.

Definition Prect (P:positive->Type) (a:P xH) (f:forall p, P p -> P (Psucc p)) 
  (p:positive) :=
  PeanoView_iter P a f p (peanoView p).

Theorem Prect_succ : forall (P:positive->Type) (a:P xH) 
  (f:forall p, P p -> P (Psucc p)) (p:positive), 
  Prect P a f (Psucc p) = f _ (Prect P a f p).
Proof.
  intros.
  unfold Prect.
  rewrite (PeanoViewUnique _ (peanoView (Psucc p)) (PeanoSucc _ (peanoView p))).
  trivial.
Qed.

Theorem Prect_base : forall (P:positive->Type) (a:P xH) 
  (f:forall p, P p -> P (Psucc p)), Prect P a f xH = a.
Proof.
  trivial.
Qed.

Definition Prec (P:positive->Set) := Prect P.

(** Peano induction *)

Definition Pind (P:positive->Prop) := Prect P.

(** Peano case analysis *)

Theorem Pcase :
  forall P:positive -> Prop,
    P xH -> (forall n:positive, P (Psucc n)) -> forall p:positive, P p.
Proof.
  intros; apply Pind; auto.
Qed.

(**********************************************************************)
(** Properties of multiplication on binary positive numbers *)

(** One is right neutral for multiplication *)

Lemma Pmult_1_r : forall p:positive, p * xH = p.
Proof.
  intro x; induction x; simpl in |- *.
  rewrite IHx; reflexivity.
  rewrite IHx; reflexivity.
  reflexivity.
Qed.

(** Successor and multiplication *)

Lemma Pmult_Sn_m : forall n m : positive, (Psucc n) * m = m + n * m.
Proof.
  induction n as [n IH | n IH |]; simpl; intro m.
  rewrite IH; rewrite Pplus_assoc; rewrite Pplus_diag;
    rewrite <- Pplus_xO; reflexivity.
  reflexivity.
  symmetry; apply Pplus_diag.
Qed.

(** Right reduction properties for multiplication *)

Lemma Pmult_xO_permute_r : forall p q:positive, p * xO q = xO (p * q).
Proof.
  intros x y; induction x; simpl in |- *.
  rewrite IHx; reflexivity.
  rewrite IHx; reflexivity.
  reflexivity.
Qed.

Lemma Pmult_xI_permute_r : forall p q:positive, p * xI q = p + xO (p * q).
Proof.
  intros x y; induction x; simpl in |- *.
  rewrite IHx; do 2 rewrite Pplus_assoc; rewrite Pplus_comm with (p := y);
    reflexivity.
  rewrite IHx; reflexivity.
  reflexivity.
Qed.

(** Commutativity of multiplication *)

Theorem Pmult_comm : forall p q:positive, p * q = q * p.
Proof.
  intros x y; induction y; simpl in |- *.
  rewrite <- IHy; apply Pmult_xI_permute_r.
  rewrite <- IHy; apply Pmult_xO_permute_r.
  apply Pmult_1_r.
Qed.

(** Distributivity of multiplication over addition *)

Theorem Pmult_plus_distr_l :
  forall p q r:positive, p * (q + r) = p * q + p * r.
Proof.
  intros x y z; induction x; simpl in |- *.
  rewrite IHx; rewrite <- Pplus_assoc with (q := xO (x * y));
    rewrite Pplus_assoc with (p := xO (x * y));
      rewrite Pplus_comm with (p := xO (x * y));
        rewrite <- Pplus_assoc with (q := xO (x * y));
          rewrite Pplus_assoc with (q := z); reflexivity.
  rewrite IHx; reflexivity.
  reflexivity.
Qed.

Theorem Pmult_plus_distr_r :
  forall p q r:positive, (p + q) * r = p * r + q * r.
Proof.
  intros x y z; do 3 rewrite Pmult_comm with (q := z); apply Pmult_plus_distr_l.
Qed.

(** Associativity of multiplication *)

Theorem Pmult_assoc : forall p q r:positive, p * (q * r) = p * q * r.
Proof.
  intro x; induction x as [x| x| ]; simpl in |- *; intros y z.
  rewrite IHx; rewrite Pmult_plus_distr_r; reflexivity.
  rewrite IHx; reflexivity.
  reflexivity.
Qed.

(** Parity properties of multiplication *)

Lemma Pmult_xI_mult_xO_discr : forall p q r:positive, xI p * r <> xO q * r.
Proof.
  intros x y z; induction z as [| z IHz| ]; try discriminate.
  intro H; apply IHz; clear IHz.
  do 2 rewrite Pmult_xO_permute_r in H.
  injection H; clear H; intro H; exact H.
Qed.

Lemma Pmult_xO_discr : forall p q:positive, xO p * q <> q.
Proof.
  intros x y; induction y; try discriminate.
  rewrite Pmult_xO_permute_r; injection; assumption.
Qed.

(** Simplification properties of multiplication *)

Theorem Pmult_reg_r : forall p q r:positive, p * r = q * r -> p = q.
Proof.
  intro x; induction x as [p IHp| p IHp| ]; intro y; destruct y as [q| q| ];
    intros z H; reflexivity || apply (f_equal (A:=positive)) || apply False_ind.
  simpl in H; apply IHp with (xO z); simpl in |- *;
    do 2 rewrite Pmult_xO_permute_r; apply Pplus_reg_l with (1 := H).
  apply Pmult_xI_mult_xO_discr with (1 := H).
  simpl in H; rewrite Pplus_comm in H; apply Pplus_no_neutral with (1 := H).
  symmetry  in H; apply Pmult_xI_mult_xO_discr with (1 := H).
  apply IHp with (xO z); simpl in |- *; do 2 rewrite Pmult_xO_permute_r;
    assumption.
  apply Pmult_xO_discr with (1 := H).
  simpl in H; symmetry  in H; rewrite Pplus_comm in H;
    apply Pplus_no_neutral with (1 := H).
  symmetry  in H; apply Pmult_xO_discr with (1 := H).
Qed.

Theorem Pmult_reg_l : forall p q r:positive, r * p = r * q -> p = q.
Proof.
  intros x y z H; apply Pmult_reg_r with (r := z).
  rewrite Pmult_comm with (p := x); rewrite Pmult_comm with (p := y);
    assumption.
Qed.

(** Inversion of multiplication *)

Lemma Pmult_1_inversion_l : forall p q:positive, p * q = xH -> p = xH.
Proof.
  intros x y; destruct x as [p| p| ]; simpl in |- *.
  destruct y as [p0| p0| ]; intro; discriminate.
  intro; discriminate.
  reflexivity.
Qed.

(**********************************************************************)
(** Properties of comparison on binary positive numbers *)

Theorem Pcompare_refl : forall p:positive, (p ?= p) Eq = Eq.
  intro x; induction  x as [x Hrecx| x Hrecx| ]; auto.
Qed.

(* A generalization of Pcompare_refl *)

Theorem Pcompare_refl_id : forall (p : positive) (r : comparison), (p ?= p) r = r.
  induction p; auto.
Qed.

Theorem Pcompare_not_Eq :
  forall p q:positive, (p ?= q) Gt <> Eq /\ (p ?= q) Lt <> Eq.
Proof.
  intro x; induction x as [p IHp| p IHp| ]; intro y; destruct y as [q| q| ];
    split; simpl in |- *; auto; discriminate || (elim (IHp q); auto).
Qed.

Theorem Pcompare_Eq_eq : forall p q:positive, (p ?= q) Eq = Eq -> p = q.
Proof.
  intro x; induction x as [p IHp| p IHp| ]; intro y; destruct y as [q| q| ];
    simpl in |- *; auto; intro H;
      [ rewrite (IHp q); trivial
        | absurd ((p ?= q) Gt = Eq);
          [ elim (Pcompare_not_Eq p q); auto | assumption ]
        | discriminate H
        | absurd ((p ?= q) Lt = Eq);
          [ elim (Pcompare_not_Eq p q); auto | assumption ]
        | rewrite (IHp q); auto
        | discriminate H
        | discriminate H
        | discriminate H ].
Qed.

Lemma Pcompare_Gt_Lt :
  forall p q:positive, (p ?= q) Gt = Lt -> (p ?= q) Eq = Lt.
Proof.
  intro x; induction  x as [x Hrecx| x Hrecx| ]; intro y;
    [ induction  y as [y Hrecy| y Hrecy| ]
      | induction  y as [y Hrecy| y Hrecy| ]
      | induction  y as [y Hrecy| y Hrecy| ] ]; simpl in |- *; 
    auto; discriminate || intros H; discriminate H.
Qed.

Lemma Pcompare_eq_Lt :
  forall p q : positive, (p ?= q) Eq = Lt <-> (p ?= q) Gt = Lt.
Proof.
  intros p q; split; [| apply Pcompare_Gt_Lt].
  generalize q; clear q; induction p; induction q; simpl; auto.
  intro; discriminate.
Qed.

Lemma Pcompare_Lt_Gt :
  forall p q:positive, (p ?= q) Lt = Gt -> (p ?= q) Eq = Gt.
Proof.
  intro x; induction  x as [x Hrecx| x Hrecx| ]; intro y;
    [ induction  y as [y Hrecy| y Hrecy| ]
      | induction  y as [y Hrecy| y Hrecy| ]
      | induction  y as [y Hrecy| y Hrecy| ] ]; simpl in |- *; 
    auto; discriminate || intros H; discriminate H.
Qed.

Lemma Pcompare_eq_Gt :
  forall p q : positive, (p ?= q) Eq = Gt <-> (p ?= q) Lt = Gt.
Proof.
  intros p q; split; [| apply Pcompare_Lt_Gt].
  generalize q; clear q; induction p; induction q; simpl; auto.
  intro; discriminate.
Qed.

Lemma Pcompare_Lt_Lt :
  forall p q:positive, (p ?= q) Lt = Lt -> (p ?= q) Eq = Lt \/ p = q.
Proof.
  intro x; induction x as [p IHp| p IHp| ]; intro y; destruct y as [q| q| ];
    simpl in |- *; auto; try discriminate; intro H2; elim (IHp q H2); 
      auto; intros E; rewrite E; auto.
Qed.

Lemma Pcompare_Lt_eq_Lt :
  forall p q:positive, (p ?= q) Lt = Lt <-> (p ?= q) Eq = Lt \/ p = q.
Proof.
  intros p q; split; [apply Pcompare_Lt_Lt |].
  intro H; destruct H as [H | H]; [ | rewrite H; apply Pcompare_refl_id].
  generalize q H. clear q H.
  induction p as [p' IH | p' IH |]; destruct q as [q' | q' |]; simpl; intro H;
    try (reflexivity || assumption || discriminate H); apply IH; assumption.
Qed.

Lemma Pcompare_Gt_Gt :
  forall p q:positive, (p ?= q) Gt = Gt -> (p ?= q) Eq = Gt \/ p = q.
Proof.
  intro x; induction x as [p IHp| p IHp| ]; intro y; destruct y as [q| q| ];
    simpl in |- *; auto; try discriminate; intro H2; elim (IHp q H2); 
      auto; intros E; rewrite E; auto.
Qed.

Lemma Pcompare_Gt_eq_Gt :
  forall p q:positive, (p ?= q) Gt = Gt <-> (p ?= q) Eq = Gt \/ p = q.
Proof.
  intros p q; split; [apply Pcompare_Gt_Gt |].
  intro H; destruct H as [H | H]; [ | rewrite H; apply Pcompare_refl_id].
  generalize q H. clear q H.
  induction p as [p' IH | p' IH |]; destruct q as [q' | q' |]; simpl; intro H;
    try (reflexivity || assumption || discriminate H); apply IH; assumption.
Qed.

Lemma Dcompare : forall r:comparison, r = Eq \/ r = Lt \/ r = Gt.
Proof.
  simple induction r; auto. 
Qed.

Ltac ElimPcompare c1 c2 :=
  elim (Dcompare ((c1 ?= c2) Eq));
    [ idtac | let x := fresh "H" in
      (intro x; case x; clear x) ].

Lemma Pcompare_antisym :
  forall (p q:positive) (r:comparison),
    CompOpp ((p ?= q) r) = (q ?= p) (CompOpp r).
Proof.
  intro x; induction x as [p IHp| p IHp| ]; intro y;
    [ destruct y as [p0| p0| ]
      | destruct y as [p0| p0| ]
      | destruct y as [p| p| ] ]; intro r;
    reflexivity ||
      (symmetry  in |- *; assumption) || discriminate H || simpl in |- *;
        apply IHp || (try rewrite IHp); try reflexivity.
Qed.

Lemma ZC1 : forall p q:positive, (p ?= q) Eq = Gt -> (q ?= p) Eq = Lt.
Proof.
  intros; change Eq with (CompOpp Eq) in |- *.
  rewrite <- Pcompare_antisym; rewrite H; reflexivity.
Qed.

Lemma ZC2 : forall p q:positive, (p ?= q) Eq = Lt -> (q ?= p) Eq = Gt.
Proof.
  intros; change Eq with (CompOpp Eq) in |- *.
  rewrite <- Pcompare_antisym; rewrite H; reflexivity.
Qed.

Lemma ZC3 : forall p q:positive, (p ?= q) Eq = Eq -> (q ?= p) Eq = Eq.
Proof.
  intros; change Eq with (CompOpp Eq) in |- *.
  rewrite <- Pcompare_antisym; rewrite H; reflexivity.
Qed.

Lemma ZC4 : forall p q:positive, (p ?= q) Eq = CompOpp ((q ?= p) Eq).
Proof.
  intros; change Eq at 1 with (CompOpp Eq) in |- *.
  symmetry  in |- *; apply Pcompare_antisym.
Qed.

(** Comparison and the successor *)

Lemma Pcompare_p_Sp : forall p : positive, (p ?= Psucc p) Eq = Lt.
Proof.
  induction p as [p' IH | p' IH |]; simpl in *;
    [ elim (Pcompare_eq_Lt p' (Psucc p')); auto |
      apply Pcompare_refl_id | reflexivity].
Qed.

Theorem Pcompare_p_Sq : forall p q : positive,
  (p ?= Psucc q) Eq = Lt <-> (p ?= q) Eq = Lt \/ p = q.
Proof.
  intros p q; split.
  generalize p q; clear p q.
  induction p as [p' IH | p' IH |]; destruct q as [q' | q' |]; simpl; intro H.
  assert (T : xI p' = xI q' <-> p' = q').
  split; intro HH; [inversion HH; trivial | rewrite HH; reflexivity].
  cut ((p' ?= q') Eq = Lt \/ p' = q'). firstorder.
  apply IH. apply Pcompare_Gt_Lt; assumption.
  left; elim (Pcompare_eq_Lt p' q'); auto.
  destruct p'; discriminate.
  apply IH in H. left.
  destruct H as [H | H]; [elim (Pcompare_Lt_eq_Lt p' q'); auto; left; assumption |
    rewrite H; apply Pcompare_refl_id].
  assert (T : xO p' = xO q' <-> p' = q').
  split; intro HH; [inversion HH; trivial | rewrite HH; reflexivity].
  cut ((p' ?= q') Eq = Lt \/ p' = q'); [firstorder | ].
  elim (Pcompare_Lt_eq_Lt p' q'); auto.
  destruct p'; discriminate.
  left; reflexivity.
  left; reflexivity.
  right; reflexivity.
  intro H; destruct H as [H | H].
  generalize q H; clear q H. induction p as [p' IH | p' IH |];
  destruct q as [q' | q' |]; simpl in *; intro H;
    try (reflexivity || discriminate H).
  elim (Pcompare_eq_Lt p' (Psucc q')); auto;
    apply IH; assumption.
  elim (Pcompare_eq_Lt p' q'); auto.
  assert (H1 : (p' ?= q') Eq = Lt \/ p' = q'); [elim (Pcompare_Lt_eq_Lt p' q'); auto |].
  destruct H1 as [H1 | H1]; [apply IH; assumption | rewrite H1; apply Pcompare_p_Sp].
  elim (Pcompare_Lt_eq_Lt p' q'); auto.
  rewrite H; apply Pcompare_p_Sp.
Qed.

(** 1 is the least positive number *)

Lemma Pcompare_1 : forall p, ~ (p ?= xH) Eq = Lt.
Proof.
  destruct p; discriminate.
Qed.

(**********************************************************************)
(** Properties of subtraction on binary positive numbers *)

Lemma Ppred_minus : forall p, Ppred p = Pminus p xH.
Proof.
  destruct p; compute; auto.
Qed.

Lemma double_eq_zero_inversion :
  forall p:positive_mask, Pdouble_mask p = IsNul -> p = IsNul.
Proof.
  destruct p; simpl in |- *; [ trivial | discriminate 1 | discriminate 1 ].
Qed.

Lemma double_plus_one_zero_discr :
  forall p:positive_mask, Pdouble_plus_one_mask p <> IsNul.
Proof.
  simple induction p; intros; discriminate.
Qed.

Lemma double_plus_one_eq_one_inversion :
  forall p:positive_mask, Pdouble_plus_one_mask p = IsPos xH -> p = IsNul.
Proof.
  destruct p; simpl in |- *; [ trivial | discriminate 1 | discriminate 1 ].
Qed.

Lemma double_eq_one_discr :
  forall p:positive_mask, Pdouble_mask p <> IsPos xH.
Proof.
  simple induction p; intros; discriminate.
Qed.

Theorem Pminus_mask_diag : forall p:positive, Pminus_mask p p = IsNul.
Proof.
  intro x; induction x as [p IHp| p IHp| ];
    [ simpl in |- *; rewrite IHp; simpl in |- *; trivial
      | simpl in |- *; rewrite IHp; auto
      | auto ].
Qed.

Lemma Pminus_mask_carry_diag : forall p, Pminus_mask_carry p p = IsNeg.
Proof.
  induction p; simpl; auto; rewrite IHp; auto.
Qed.

Lemma Pminus_mask_IsNeg : forall p q:positive, 
 Pminus_mask p q = IsNeg -> Pminus_mask_carry p q = IsNeg.
Proof.
  induction p; destruct q; simpl; intros; auto; try discriminate.

  unfold Pdouble_mask in H.
  generalize (IHp q).
  destruct (Pminus_mask p q); try discriminate.
  intro H'; rewrite H'; auto.

  unfold Pdouble_plus_one_mask in H.
  destruct (Pminus_mask p q); simpl; auto; try discriminate.

  unfold Pdouble_plus_one_mask in H.
  destruct (Pminus_mask_carry p q); simpl; auto; try discriminate.

  unfold Pdouble_mask in H.
  generalize (IHp q).
  destruct (Pminus_mask p q); try discriminate.
  intro H'; rewrite H'; auto.
Qed.

Lemma ZL10 :
  forall p q:positive,
    Pminus_mask p q = IsPos xH -> Pminus_mask_carry p q = IsNul.
Proof.
  intro x; induction x as [p| p| ]; intro y; destruct y as [q| q| ];
    simpl in |- *; intro H; try discriminate H;
      [ absurd (Pdouble_mask (Pminus_mask p q) = IsPos xH);
        [ apply double_eq_one_discr | assumption ]
        | assert (Heq : Pminus_mask p q = IsNul);
          [ apply double_plus_one_eq_one_inversion; assumption
            | rewrite Heq; reflexivity ]
        | assert (Heq : Pminus_mask_carry p q = IsNul);
          [ apply double_plus_one_eq_one_inversion; assumption
            | rewrite Heq; reflexivity ]
        | absurd (Pdouble_mask (Pminus_mask p q) = IsPos xH);
          [ apply double_eq_one_discr | assumption ]
        | destruct p; simpl in |- *;
          [ discriminate H | discriminate H | reflexivity ] ].
Qed.

(** Properties of subtraction valid only for x>y *)

Lemma Pminus_mask_Gt :
  forall p q:positive,
    (p ?= q) Eq = Gt ->
    exists h : positive,
      Pminus_mask p q = IsPos h /\
      q + h = p /\ (h = xH \/ Pminus_mask_carry p q = IsPos (Ppred h)).
Proof.
  intro x; induction x as [p| p| ]; intro y; destruct y as [q| q| ];
    simpl in |- *; intro H; try discriminate H.
  destruct (IHp q H) as [z [H4 [H6 H7]]]; exists (xO z); split.
  rewrite H4; reflexivity.
  split.
  simpl in |- *; rewrite H6; reflexivity.
  right; clear H6; destruct (ZL11 z) as [H8| H8];
    [ rewrite H8; rewrite H8 in H4; rewrite ZL10;
      [ reflexivity | assumption ]
      | clear H4; destruct H7 as [H9| H9];
        [ absurd (z = xH); assumption
          | rewrite H9; clear H9; destruct z as [p0| p0| ];
            [ reflexivity | reflexivity | absurd (xH = xH); trivial ] ] ].
  case Pcompare_Gt_Gt with (1 := H);
  [ intros H3; elim (IHp q H3); intros z H4; exists (xI z); elim H4;
    intros H5 H6; elim H6; intros H7 H8; split;
      [ simpl in |- *; rewrite H5; auto
        | split;
          [ simpl in |- *; rewrite H7; trivial
            | right;
              change (Pdouble_mask (Pminus_mask p q) = IsPos (Ppred (xI z)))
                in |- *; rewrite H5; auto ] ]
    | intros H3; exists xH; rewrite H3; split;
      [ simpl in |- *; rewrite Pminus_mask_diag; auto | split; auto ] ].
  exists (xO p); auto.
  destruct (IHp q) as [z [H4 [H6 H7]]].
  apply Pcompare_Lt_Gt; assumption.
  destruct (ZL11 z) as [vZ| ];
    [ exists xH; split;
      [ rewrite ZL10; [ reflexivity | rewrite vZ in H4; assumption ]
        | split;
          [ simpl in |- *; rewrite Pplus_one_succ_r; rewrite <- vZ;
            rewrite H6; trivial
            | auto ] ]
      | exists (xI (Ppred z)); destruct H7 as [| H8];
        [ absurd (z = xH); assumption
          | split;
            [ rewrite H8; trivial
              | split;
                [ simpl in |- *; rewrite Pplus_carry_pred_eq_plus;
                  [ rewrite H6; trivial | assumption ]
                  | right; rewrite H8; reflexivity ] ] ] ].
  destruct (IHp q H) as [z [H4 [H6 H7]]].
  exists (xO z); split;
    [ rewrite H4; auto
      | split;
        [ simpl in |- *; rewrite H6; reflexivity
          | right;
            change
              (Pdouble_plus_one_mask (Pminus_mask_carry p q) =
                IsPos (Pdouble_minus_one z)) in |- *;
              destruct (ZL11 z) as [H8| H8];
                [ rewrite H8; simpl in |- *;
                  assert (H9 : Pminus_mask_carry p q = IsNul);
                    [ apply ZL10; rewrite <- H8; assumption
                      | rewrite H9; reflexivity ]
                  | destruct H7 as [H9| H9];
                    [ absurd (z = xH); auto
                      | rewrite H9; destruct z as [p0| p0| ]; simpl in |- *;
                        [ reflexivity
                          | reflexivity
                          | absurd (xH = xH); [ assumption | reflexivity ] ] ] ] ] ].
  exists (Pdouble_minus_one p); split;
    [ reflexivity
      | clear IHp; split;
        [ destruct p; simpl in |- *;
          [ reflexivity
            | rewrite Psucc_o_double_minus_one_eq_xO; reflexivity
            | reflexivity ]
          | destruct p; [ right | right | left ]; reflexivity ] ].
Qed.

Theorem Pplus_minus :
  forall p q:positive, (p ?= q) Eq = Gt -> q + (p - q) = p.
Proof.
  intros x y H; elim Pminus_mask_Gt with (1 := H); intros z H1; elim H1;
    intros H2 H3; elim H3; intros H4 H5; unfold Pminus in |- *; 
      rewrite H2; exact H4.
Qed.

(* When x<y, the substraction of x by y returns 1 *)

Lemma Pminus_mask_Lt : forall p q:positive, p<q -> Pminus_mask p q = IsNeg.
Proof.
  unfold Plt; induction p; destruct q; simpl; intros; auto; try discriminate.
  rewrite IHp; simpl; auto.
  rewrite IHp; simpl; auto.
  apply Pcompare_Gt_Lt; auto.
  destruct (Pcompare_Lt_Lt _ _ H).
  rewrite Pminus_mask_IsNeg; simpl; auto.
  subst q; rewrite Pminus_mask_carry_diag; auto.
  rewrite IHp; simpl; auto.
Qed. 

Lemma Pminus_Lt : forall p q:positive, p<q -> p-q = xH.
Proof.
  intros; unfold Plt, Pminus; rewrite Pminus_mask_Lt; auto.
Qed.




