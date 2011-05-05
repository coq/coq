(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export BinNums.
Require Import Eqdep_dec EqdepFacts RelationClasses Morphisms Setoid
 Equalities GenericMinMax Le Plus.

(**********************************************************************)
(** * Binary positive numbers, operations and properties *)
(**********************************************************************)

(** Initial development by Pierre Crégut, CNET, Lannion, France *)

(** The type [positive] and its constructors [xI] and [xO] and [xH]
    are now defined in [BinNums.v] *)

(** Postfix notation for positive numbers, allowing to mimic
    the position of bits in a big-endian representation.
    For instance, we can write [1~1~0] instead of [(xO (xI xH))]
    for the number 6 (which is 110 in binary notation).
*)

Notation "p ~ 1" := (xI p)
 (at level 7, left associativity, format "p '~' '1'") : positive_scope.
Notation "p ~ 0" := (xO p)
 (at level 7, left associativity, format "p '~' '0'") : positive_scope.

Local Open Scope positive_scope.
Local Unset Boolean Equality Schemes.
Local Unset Case Analysis Schemes.

(** Every definitions and early properties about positive numbers
    are placed in a module [Pos] for qualification purpose. *)

Module Pos.
Definition t := positive.
Definition eq := @Logic.eq t.
Definition eq_equiv := @eq_equivalence t.
Include BackportEq.

(** * Operations over positive numbers *)

(** ** Successor *)

Fixpoint succ x :=
  match x with
    | p~1 => (succ p)~0
    | p~0 => p~1
    | 1 => 1~0
  end.

(** ** Addition *)

Fixpoint add x y :=
  match x, y with
    | p~1, q~1 => (add_carry p q)~0
    | p~1, q~0 => (add p q)~1
    | p~1, 1 => (succ p)~0
    | p~0, q~1 => (add p q)~1
    | p~0, q~0 => (add p q)~0
    | p~0, 1 => p~1
    | 1, q~1 => (succ q)~0
    | 1, q~0 => q~1
    | 1, 1 => 1~0
  end

with add_carry x y :=
  match x, y with
    | p~1, q~1 => (add_carry p q)~1
    | p~1, q~0 => (add_carry p q)~0
    | p~1, 1 => (succ p)~1
    | p~0, q~1 => (add_carry p q)~0
    | p~0, q~0 => (add p q)~1
    | p~0, 1 => (succ p)~0
    | 1, q~1 => (succ q)~1
    | 1, q~0 => (succ q)~0
    | 1, 1 => 1~1
  end.

Infix "+" := add : positive_scope.

(** ** Operation [x -> 2*x-1] *)

Fixpoint pred_double x :=
  match x with
    | p~1 => p~0~1
    | p~0 => (pred_double p)~1
    | 1 => 1
  end.

(** ** Predecessor *)

Definition pred x :=
  match x with
    | p~1 => p~0
    | p~0 => pred_double p
    | 1 => 1
  end.

(** ** An auxiliary type for subtraction *)

Inductive mask : Set :=
| IsNul : mask
| IsPos : positive -> mask
| IsNeg : mask.

(** ** Operation [x -> 2*x+1] *)

Definition succ_double_mask (x:mask) : mask :=
  match x with
    | IsNul => IsPos 1
    | IsNeg => IsNeg
    | IsPos p => IsPos p~1
  end.

(** ** Operation [x -> 2*x] *)

Definition double_mask (x:mask) : mask :=
  match x with
    | IsNul => IsNul
    | IsNeg => IsNeg
    | IsPos p => IsPos p~0
  end.

(** ** Operation [x -> 2*x-2] *)

Definition double_pred_mask x : mask :=
  match x with
    | p~1 => IsPos p~0~0
    | p~0 => IsPos (pred_double p)~0
    | 1 => IsNul
  end.

(** ** Predecessor with mask *)

Definition pred_mask (p : mask) : mask :=
  match p with
    | IsPos 1 => IsNul
    | IsPos q => IsPos (pred q)
    | IsNul => IsNeg
    | IsNeg => IsNeg
  end.

(** ** Subtraction, result as a mask *)

Fixpoint sub_mask (x y:positive) {struct y} : mask :=
  match x, y with
    | p~1, q~1 => double_mask (sub_mask p q)
    | p~1, q~0 => succ_double_mask (sub_mask p q)
    | p~1, 1 => IsPos p~0
    | p~0, q~1 => succ_double_mask (sub_mask_carry p q)
    | p~0, q~0 => double_mask (sub_mask p q)
    | p~0, 1 => IsPos (pred_double p)
    | 1, 1 => IsNul
    | 1, _ => IsNeg
  end

with sub_mask_carry (x y:positive) {struct y} : mask :=
  match x, y with
    | p~1, q~1 => succ_double_mask (sub_mask_carry p q)
    | p~1, q~0 => double_mask (sub_mask p q)
    | p~1, 1 => IsPos (pred_double p)
    | p~0, q~1 => double_mask (sub_mask_carry p q)
    | p~0, q~0 => succ_double_mask (sub_mask_carry p q)
    | p~0, 1 => double_pred_mask p
    | 1, _ => IsNeg
  end.

(** ** Subtraction, result as a positive, returning 1 if [x<=y] *)

Definition sub x y :=
  match sub_mask x y with
    | IsPos z => z
    | _ => 1
  end.

Infix "-" := sub : positive_scope.

(** ** Multiplication *)

Fixpoint mul x y :=
  match x with
    | p~1 => y + (mul p y)~0
    | p~0 => (mul p y)~0
    | 1 => y
  end.

Infix "*" := mul : positive_scope.

(** ** Iteration over a positive number *)

Fixpoint iter (n:positive) {A} (f:A -> A) (x:A) : A :=
  match n with
    | xH => f x
    | xO n' => iter n' f (iter n' f x)
    | xI n' => f (iter n' f (iter n' f x))
  end.

(** ** Power *)

Definition pow (x y:positive) := iter y (mul x) 1.

Infix "^" := pow : positive_scope.

(** ** Division by 2 rounded below but for 1 *)

Definition div2 p :=
  match p with
    | 1 => 1
    | p~0 => p
    | p~1 => p
  end.

(** Division by 2 rounded up *)

Definition div2_up p :=
 match p with
   | 1 => 1
   | p~0 => p
   | p~1 => succ p
 end.

(** ** Number of digits in a positive number *)

Fixpoint size_nat p : nat :=
  match p with
    | 1 => S O
    | p~1 => S (size_nat p)
    | p~0 => S (size_nat p)
  end.

(** Same, with positive output *)

Fixpoint size p :=
  match p with
    | 1 => 1
    | p~1 => succ (size p)
    | p~0 => succ (size p)
  end.

(** ** Comparison on binary positive numbers *)

Fixpoint compare_cont (x y:positive) (r:comparison) {struct y} : comparison :=
  match x, y with
    | p~1, q~1 => compare_cont p q r
    | p~1, q~0 => compare_cont p q Gt
    | p~1, 1 => Gt
    | p~0, q~1 => compare_cont p q Lt
    | p~0, q~0 => compare_cont p q r
    | p~0, 1 => Gt
    | 1, q~1 => Lt
    | 1, q~0 => Lt
    | 1, 1 => r
  end.

Definition compare x y := compare_cont x y Eq.

Infix "?=" := compare (at level 70, no associativity) : positive_scope.

Definition lt x y := (x ?= y) = Lt.
Definition gt x y := (x ?= y) = Gt.
Definition le x y := (x ?= y) <> Gt.
Definition ge x y := (x ?= y) <> Lt.

Infix "<=" := le : positive_scope.
Infix "<" := lt : positive_scope.
Infix ">=" := ge : positive_scope.
Infix ">" := gt : positive_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : positive_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : positive_scope.
Notation "x < y < z" := (x < y /\ y < z) : positive_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : positive_scope.

Definition min p p' :=
 match p ?= p' with
 | Lt | Eq => p
 | Gt => p'
 end.

Definition max p p' :=
 match p ?= p' with
 | Lt | Eq => p'
 | Gt => p
 end.

(** ** Boolean equality and comparisons *)

(** Nota: this [eqb] is not convertible with the generated [positive_beq], due
    to a different guard argument. We keep this version for compatibility. *)

Fixpoint eqb p q {struct q} :=
  match p, q with
    | p~1, q~1 => eqb p q
    | p~0, q~0 => eqb p q
    | 1, 1 => true
    | _, _ => false
  end.

Definition leb x y :=
 match x ?= y with Gt => false | _ => true end.

Definition ltb x y :=
 match x ?= y with Lt => true | _ => false end.

Infix "=?" := leb (at level 70, no associativity) : positive_scope.
Infix "<=?" := leb (at level 70, no associativity) : positive_scope.
Infix "<?" := ltb (at level 70, no associativity) : positive_scope.

(** ** A Square Root function for positive numbers *)

(** We procede by blocks of two digits : if p is written qbb'
    then sqrt(p) will be sqrt(q)~0 or sqrt(q)~1.
    For deciding easily in which case we are, we store the remainder
    (as a positive_mask, since it can be null).
    Instead of copy-pasting the following code four times, we
    factorize as an auxiliary function, with f and g being either
    xO or xI depending of the initial digits.
    NB: (sub_mask (g (f 1)) 4) is a hack, morally it's g (f 0).
*)

Definition sqrtrem_step (f g:positive->positive) p :=
 match p with
  | (s, IsPos r) =>
    let s' := s~0~1 in
    let r' := g (f r) in
    if s' <=? r' then (s~1, sub_mask r' s')
    else (s~0, IsPos r')
  | (s,_)  => (s~0, sub_mask (g (f 1)) 4)
 end.

Fixpoint sqrtrem p : positive * mask :=
 match p with
  | 1 => (1,IsNul)
  | 2 => (1,IsPos 1)
  | 3 => (1,IsPos 2)
  | p~0~0 => sqrtrem_step xO xO (sqrtrem p)
  | p~0~1 => sqrtrem_step xO xI (sqrtrem p)
  | p~1~0 => sqrtrem_step xI xO (sqrtrem p)
  | p~1~1 => sqrtrem_step xI xI (sqrtrem p)
 end.

Definition sqrt p := fst (sqrtrem p).


(** ** Greatest Common Divisor *)

Definition divide p q := exists r, p*r = q.
Notation "( p | q )" := (divide p q) (at level 0) : positive_scope.

(** Instead of the Euclid algorithm, we use here the Stein binary
   algorithm, which is faster for this representation. This algorithm
   is almost structural, but in the last cases we do some recursive
   calls on subtraction, hence the need for a counter.
*)

Fixpoint gcdn (n : nat) (a b : positive) : positive :=
  match n with
    | O => 1
    | S n =>
      match a,b with
	| 1, _ => 1
	| _, 1 => 1
	| a~0, b~0 => (gcdn n a b)~0
	| _  , b~0 => gcdn n a b
	| a~0, _   => gcdn n a b
	| a'~1, b'~1 =>
          match a' ?= b' with
	    | Eq => a
	    | Lt => gcdn n (b'-a') a
	    | Gt => gcdn n (a'-b') b
          end
      end
  end.

(** We'll show later that we need at most (log2(a.b)) loops *)

Definition gcd (a b : positive) := gcdn (size_nat a + size_nat b)%nat a b.

(** Generalized Gcd, also computing the division of a and b by the gcd *)

Fixpoint ggcdn (n : nat) (a b : positive) : (positive*(positive*positive)) :=
  match n with
    | O => (1,(a,b))
    | S n =>
      match a,b with
	| 1, _ => (1,(1,b))
	| _, 1 => (1,(a,1))
	| a~0, b~0 =>
           let (g,p) := ggcdn n a b in
           (g~0,p)
	| _, b~0 =>
           let '(g,(aa,bb)) := ggcdn n a b in
           (g,(aa, bb~0))
	| a~0, _ =>
           let '(g,(aa,bb)) := ggcdn n a b in
           (g,(aa~0, bb))
	| a'~1, b'~1 =>
           match a' ?= b' with
	     | Eq => (a,(1,1))
	     | Lt =>
	        let '(g,(ba,aa)) := ggcdn n (b'-a') a in
	        (g,(aa, aa + ba~0))
	     | Gt =>
		let '(g,(ab,bb)) := ggcdn n (a'-b') b in
		(g,(bb + ab~0, bb))
	   end
      end
  end.

Definition ggcd (a b: positive) := ggcdn (size_nat a + size_nat b)%nat a b.


(** ** From binary positive numbers to Peano natural numbers *)

Definition iter_op {A}(op:A->A->A) :=
  fix iter (p:positive)(a:A) : A :=
  match p with
    | 1 => a
    | p~0 => iter p (op a a)
    | p~1 => op a (iter p (op a a))
  end.

Definition to_nat (x:positive) : nat := iter_op plus x (S O).

(** ** From Peano natural numbers to binary positive numbers *)

(** A version preserving positive numbers, and sending 0 to 1. *)

Fixpoint of_nat (n:nat) : positive :=
 match n with
   | O => 1
   | S O => 1
   | S x => succ (of_nat x)
 end.

(* Another version that converts [n] into [n+1] *)

Fixpoint of_succ_nat (n:nat) : positive :=
  match n with
    | O => 1
    | S x => succ (of_succ_nat x)
  end.


(**********************************************************************)
(** * Properties of operations over positive numbers *)

(** ** Decidability of equality on binary positive numbers *)

Lemma eq_dec : forall x y:positive, {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

(**********************************************************************)
(** * Properties of successor on binary positive numbers *)

(** ** Specification of [xI] in term of [succ] and [xO] *)

Lemma xI_succ_xO p : p~1 = succ p~0.
Proof.
  reflexivity.
Qed.

Lemma succ_discr p : p <> succ p.
Proof.
  now destruct p.
Qed.

(** ** Successor and double *)

Lemma pred_double_spec p : pred_double p = pred (p~0).
Proof.
  reflexivity.
Qed.

Lemma succ_pred_double p : succ (pred_double p) = p~0.
Proof.
  induction p; simpl; now f_equal.
Qed.

Lemma pred_double_succ p : pred_double (succ p) = p~1.
Proof.
  induction p; simpl; now f_equal.
Qed.

Lemma double_succ p : (succ p)~0 = succ (succ p~0).
Proof.
  now destruct p.
Qed.

Lemma pred_double_xO_discr p : pred_double p <> p~0.
Proof.
  now destruct p.
Qed.

(** ** Successor and predecessor *)

Lemma succ_not_1 p : succ p <> 1.
Proof.
  now destruct p.
Qed.

Lemma pred_succ p : pred (succ p) = p.
Proof.
  destruct p; simpl; trivial. apply pred_double_succ.
Qed.

Lemma succ_pred_or p : p = 1 \/ succ (pred p) = p.
Proof.
  destruct p; simpl; auto.
  right; apply succ_pred_double.
Qed.

Lemma succ_pred p : p <> 1 -> succ (pred p) = p.
Proof.
  destruct p; intros H; simpl; trivial.
  apply succ_pred_double.
  now destruct H.
Qed.

Ltac destr_eq H := discriminate H || (try (injection H; clear H; intro H)).

(** ** Injectivity of successor *)

Lemma succ_inj p q : succ p = succ q -> p = q.
Proof.
  revert q.
  induction p; intros [q|q| ] H; simpl in H; destr_eq H; f_equal; auto.
  elim (succ_not_1 p); auto.
  elim (succ_not_1 q); auto.
Qed.

(**********************************************************************)
(** * Properties of addition on binary positive numbers *)

(** ** Specification of [succ] in term of [add] *)

Lemma add_1_r p : p + 1 = succ p.
Proof.
  now destruct p.
Qed.

Lemma add_1_l p : 1 + p = succ p.
Proof.
  now destruct p.
Qed.

(** ** Specification of [add_carry] *)

Theorem add_carry_spec p q : add_carry p q = succ (p + q).
Proof.
  revert q. induction p; destruct q; simpl; now f_equal.
Qed.

(** ** Commutativity *)

Theorem add_comm p q : p + q = q + p.
Proof.
  revert q. induction p; destruct q; simpl; f_equal; trivial.
  rewrite 2 add_carry_spec; now f_equal.
Qed.

(** ** Permutation of [add] and [succ] *)

Theorem add_succ_r p q : p + succ q = succ (p + q).
Proof.
  revert q.
  induction p; destruct q; simpl; f_equal;
   auto using add_1_r; rewrite add_carry_spec; auto.
Qed.

Theorem add_succ_l p q : succ p + q = succ (p + q).
Proof.
  rewrite add_comm, (add_comm p). apply add_succ_r.
Qed.

(** ** No neutral elements for addition *)

Lemma add_no_neutral p q : q + p <> p.
Proof.
  revert q.
  induction p as [p IHp|p IHp| ]; intros [q|q| ] H;
   destr_eq H; apply (IHp q H).
Qed.

(** ** Simplification *)

Lemma add_carry_add p q r s :
  add_carry p r = add_carry q s -> p + r = q + s.
Proof.
  intros H; apply succ_inj; now rewrite <- 2 add_carry_spec.
Qed.

Lemma add_reg_r p q r : p + r = q + r -> p = q.
Proof.
  revert p q. induction r.
  intros [p|p| ] [q|q| ] H; simpl; destr_eq H; f_equal;
   auto using add_carry_add; contradict H;
   rewrite add_carry_spec, <- add_succ_r; auto using add_no_neutral.
  intros [p|p| ] [q|q| ] H; simpl; destr_eq H; f_equal; auto;
    contradict H; auto using add_no_neutral.
  intros p q H. apply succ_inj. now rewrite <- 2 add_1_r.
Qed.

Lemma add_reg_l p q r : p + q = p + r -> q = r.
Proof.
  rewrite 2 (add_comm p). now apply add_reg_r.
Qed.

Lemma add_cancel_r p q r : p + r = q + r <-> p = q.
Proof.
 split. apply add_reg_r. congruence.
Qed.

Lemma add_cancel_l p q r : r + p = r + q <-> p = q.
Proof.
 split. apply add_reg_l. congruence.
Qed.

Lemma add_carry_reg_r p q r :
  add_carry p r = add_carry q r -> p = q.
Proof.
 intros H. apply add_reg_r with (r:=r); now apply add_carry_add.
Qed.

Lemma add_carry_reg_l p q r :
  add_carry p q = add_carry p r -> q = r.
Proof.
  intros H; apply add_reg_r with (r:=p);
  rewrite (add_comm r), (add_comm q); now apply add_carry_add.
Qed.

(** ** Addition is associative *)

Theorem add_assoc p q r : p + (q + r) = p + q + r.
Proof.
  revert q r. induction p.
  intros [q|q| ] [r|r| ]; simpl; f_equal; trivial;
    rewrite ?add_carry_spec, ?add_succ_r, ?add_succ_l, ?add_1_r;
    f_equal; trivial.
  intros [q|q| ] [r|r| ]; simpl; f_equal; trivial;
    rewrite ?add_carry_spec, ?add_succ_r, ?add_succ_l, ?add_1_r;
    f_equal; trivial.
  intros q r; rewrite 2 add_1_l, add_succ_l; auto.
Qed.

(** ** Commutation of addition and double *)

Lemma add_xO p q : (p + q)~0 = p~0 + q~0.
Proof.
  now destruct p, q.
Qed.

Lemma add_xI_pred_double p q :
  (p + q)~0 = p~1 + pred_double q.
Proof.
  change (p~1) with (p~0 + 1).
  now rewrite <- add_assoc, add_1_l, succ_pred_double.
Qed.

Lemma add_xO_pred_double p q :
  pred_double (p + q) = p~0 + pred_double q.
Proof.
  revert q. induction p as [p IHp| p IHp| ]; destruct q; simpl;
   rewrite ?add_carry_spec, ?pred_double_succ, ?add_xI_pred_double;
   try reflexivity.
  rewrite IHp; auto.
  rewrite <- succ_pred_double, <- add_1_l. reflexivity.
Qed.

(** ** Miscellaneous *)

Lemma add_diag p : p + p = p~0.
Proof.
  induction p as [p IHp| p IHp| ]; simpl;
  now rewrite ?add_carry_spec, ?IHp.
Qed.

(**********************************************************************)
(** * Peano induction and recursion on binary positive positive numbers *)
(** * (a nice proof from Conor McBride, see "The view from the left")   *)

Inductive PeanoView : positive -> Type :=
| PeanoOne : PeanoView 1
| PeanoSucc : forall p, PeanoView p -> PeanoView (succ p).

Fixpoint peanoView_xO p (q:PeanoView p) : PeanoView (p~0) :=
  match q in PeanoView x return PeanoView (x~0) with
    | PeanoOne => PeanoSucc _ PeanoOne
    | PeanoSucc _ q => PeanoSucc _ (PeanoSucc _ (peanoView_xO _ q))
  end.

Fixpoint peanoView_xI p (q:PeanoView p) : PeanoView (p~1) :=
  match q in PeanoView x return PeanoView (x~1) with
    | PeanoOne => PeanoSucc _ (PeanoSucc _ PeanoOne)
    | PeanoSucc _ q => PeanoSucc _ (PeanoSucc _ (peanoView_xI _ q))
  end.

Fixpoint peanoView p : PeanoView p :=
  match p return PeanoView p with
    | 1 => PeanoOne
    | p~0 => peanoView_xO p (peanoView p)
    | p~1 => peanoView_xI p (peanoView p)
  end.

Definition PeanoView_iter (P:positive->Type)
  (a:P 1) (f:forall p, P p -> P (succ p)) :=
  (fix iter p (q:PeanoView p) : P p :=
    match q in PeanoView p return P p with
      | PeanoOne => a
      | PeanoSucc _ q => f _ (iter _ q)
    end).

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
  induction q as [ | p q IHq ].
  apply eq_dep_eq_positive.
  cut (1=1). pattern 1 at 1 2 5, q'. destruct q'. trivial.
  destruct p; intros; discriminate.
  trivial.
  apply eq_dep_eq_positive.
  cut (succ p=succ p). pattern (succ p) at 1 2 5, q'. destruct q'.
  intro. destruct p; discriminate.
  intro. apply succ_inj in H.
  generalize q'. rewrite H. intro.
  rewrite (IHq q'0).
  trivial.
  trivial.
Qed.

Definition peano_rect (P:positive->Type) (a:P 1) (f:forall p, P p -> P (succ p))
  (p:positive) :=
  PeanoView_iter P a f p (peanoView p).

Theorem peano_rect_succ : forall (P:positive->Type) (a:P 1)
  (f:forall p, P p -> P (succ p)) (p:positive),
  peano_rect P a f (succ p) = f _ (peano_rect P a f p).
Proof.
  intros.
  unfold peano_rect.
  rewrite (PeanoViewUnique _ (peanoView (succ p)) (PeanoSucc _ (peanoView p))).
  trivial.
Qed.

Theorem peano_rect_base : forall (P:positive->Type) (a:P 1)
  (f:forall p, P p -> P (succ p)), peano_rect P a f 1 = a.
Proof.
  trivial.
Qed.

Definition peano_rec (P:positive->Set) := peano_rect P.

(** ** Peano induction *)

Definition peano_ind (P:positive->Prop) := peano_rect P.

(** ** Peano case analysis *)

Theorem peano_case :
  forall P:positive -> Prop,
    P 1 -> (forall n:positive, P (succ n)) -> forall p:positive, P p.
Proof.
  intros; apply peano_ind; auto.
Qed.

(**********************************************************************)
(** * Properties of multiplication on binary positive numbers *)

(** ** One is neutral for multiplication *)

Lemma mul_1_l p : 1 * p = p.
Proof.
  reflexivity.
Qed.

Lemma mul_1_r p : p * 1 = p.
Proof.
  induction p; simpl; now f_equal.
Qed.

(** ** Right reduction properties for multiplication *)

Lemma mul_xO_r p q : p * q~0 = (p * q)~0.
Proof.
  induction p; simpl; f_equal; f_equal; trivial.
Qed.

Lemma mul_xI_r p q : p * q~1 = p + (p * q)~0.
Proof.
  induction p as [p IHp|p IHp| ]; simpl; f_equal; trivial.
  now rewrite IHp, 2 add_assoc, (add_comm p).
Qed.

(** ** Commutativity of multiplication *)

Theorem mul_comm p q : p * q = q * p.
Proof.
  induction q as [q IHq|q IHq| ]; simpl; rewrite <- ? IHq;
  auto using mul_xI_r, mul_xO_r, mul_1_r.
Qed.

(** ** Distributivity of multiplication over addition *)

Theorem mul_add_distr_l p q r :
  p * (q + r) = p * q + p * r.
Proof.
  induction p as [p IHp|p IHp| ]; simpl.
  rewrite IHp. set (m:=(p*q)~0). set (n:=(p*r)~0).
  change ((p*q+p*r)~0) with (m+n).
  rewrite 2 add_assoc; f_equal.
  rewrite <- 2 add_assoc; f_equal.
  apply add_comm.
  f_equal; auto.
  reflexivity.
Qed.

Theorem mul_add_distr_r p q r :
  (p + q) * r = p * r + q * r.
Proof.
  rewrite 3 (mul_comm _ r); apply mul_add_distr_l.
Qed.

(** ** Associativity of multiplication *)

Theorem mul_assoc p q r : p * (q * r) = p * q * r.
Proof.
  induction p as [p IHp| p IHp | ]; simpl; rewrite ?IHp; trivial.
  now rewrite mul_add_distr_r.
Qed.

(** ** Successor and multiplication *)

Lemma mul_succ_l p q : (succ p) * q = q + p * q.
Proof.
  induction p as [p IHp | p IHp | ]; simpl; trivial.
  now rewrite IHp, add_assoc, add_diag, <-add_xO.
  symmetry; apply add_diag.
Qed.

Lemma mul_succ_r p q : p * (succ q) = p + p * q.
Proof.
  rewrite mul_comm, mul_succ_l. f_equal. apply mul_comm.
Qed.

(** ** Parity properties of multiplication *)

Lemma mul_xI_mul_xO_discr p q r : p~1 * r <> q~0 * r.
Proof.
  induction r; try discriminate.
  rewrite 2 mul_xO_r; intro H; destr_eq H; auto.
Qed.

Lemma mul_xO_discr p q : p~0 * q <> q.
Proof.
  induction q; try discriminate.
  rewrite mul_xO_r; injection; assumption.
Qed.

(** ** Simplification properties of multiplication *)

Theorem mul_reg_r p q r : p * r = q * r -> p = q.
Proof.
  revert q r.
  induction p as [p IHp| p IHp| ]; intros [q|q| ] r H;
    reflexivity || apply f_equal || exfalso.
  apply IHp with (r~0). simpl in *.
    rewrite 2 mul_xO_r. apply add_reg_l with (1:=H).
  contradict H. apply mul_xI_mul_xO_discr.
  contradict H. simpl. rewrite add_comm. apply add_no_neutral.
  symmetry in H. contradict H. apply mul_xI_mul_xO_discr.
  apply IHp with (r~0). simpl. now rewrite 2 mul_xO_r.
  contradict H. apply mul_xO_discr.
  symmetry in H. contradict H. simpl. rewrite add_comm.
   apply add_no_neutral.
  symmetry in H. contradict H. apply mul_xO_discr.
Qed.

Theorem mul_reg_l p q r : r * p = r * q -> p = q.
Proof.
  rewrite 2 (mul_comm r). apply mul_reg_r.
Qed.

Lemma mul_cancel_r p q r : p * r = q * r <-> p = q.
Proof.
 split. apply mul_reg_r. congruence.
Qed.

Lemma mul_cancel_l p q r : r * p = r * q <-> p = q.
Proof.
 split. apply mul_reg_l. congruence.
Qed.

(** ** Inversion of multiplication *)

Lemma mul_1_inversion_l p q : p * q = 1 -> p = 1.
Proof.
  now destruct p, q.
Qed.

Lemma mul_1_inversion_r p q : p * q = 1 -> q = 1.
Proof.
  now destruct p, q.
Qed.

(** ** Square *)

Lemma square_xO p : p~0 * p~0 = (p*p)~0~0.
Proof.
 simpl. now rewrite mul_comm.
Qed.

Lemma square_xI p : p~1 * p~1 = (p*p+p)~0~1.
Proof.
 simpl. rewrite mul_comm. simpl. f_equal.
 rewrite add_assoc, add_diag. simpl. now rewrite add_comm.
Qed.

(** ** Properties of [iter] *)

Lemma iter_swap_gen : forall A B (f:A->B)(g:A->A)(h:B->B),
 (forall a, f (g a) = h (f a)) -> forall p a,
 f (iter p g a) = iter p h (f a).
Proof.
 induction p; simpl; intros; now rewrite ?H, ?IHp.
Qed.

Theorem iter_swap :
  forall p (A:Type) (f:A -> A) (x:A),
    iter p f (f x) = f (iter p f x).
Proof.
 intros. symmetry. now apply iter_swap_gen.
Qed.

Theorem iter_succ :
  forall p (A:Type) (f:A -> A) (x:A),
    iter (succ p) f x = f (iter p f x).
Proof.
 induction p as [p IHp|p IHp|]; intros; simpl; trivial.
 now rewrite !IHp, iter_swap.
Qed.

Theorem iter_add :
  forall p q (A:Type) (f:A -> A) (x:A),
    iter (p+q) f x = iter p f (iter q f x).
Proof.
 induction p using peano_ind; intros.
 now rewrite add_1_l, iter_succ.
 now rewrite add_succ_l, !iter_succ, IHp.
Qed.

Theorem iter_invariant :
  forall (p:positive) (A:Type) (f:A -> A) (Inv:A -> Prop),
    (forall x:A, Inv x -> Inv (f x)) ->
    forall x:A, Inv x -> Inv (iter p f x).
Proof.
 induction p as [p IHp|p IHp|]; simpl; trivial.
 intros A f Inv H x H0. apply H, IHp, IHp; trivial.
 intros A f Inv H x H0. apply IHp, IHp; trivial.
Qed.

(** ** Properties of power *)

Lemma pow_1_r p : p^1 = p.
Proof.
 unfold pow. simpl. now rewrite mul_comm.
Qed.

Lemma pow_succ_r p q : p^(succ q) = p * p^q.
Proof.
 unfold pow. now rewrite iter_succ.
Qed.

(*********************************************************************)
(** * Properties of boolean equality *)

Theorem eqb_refl x : eqb x x = true.
Proof.
 induction x; auto.
Qed.

Theorem eqb_true_eq x y : eqb x y = true -> x=y.
Proof.
 revert y. induction x; destruct y; simpl; intros;
  try discriminate; f_equal; auto.
Qed.

Theorem eqb_eq x y : eqb x y = true <-> x=y.
Proof.
 split. apply eqb_true_eq.
 intros; subst; apply eqb_refl.
Qed.


(**********************************************************************)
(** * Properties of comparison on binary positive numbers *)

(** First, we express [compare_cont] in term of [compare] *)

Definition switch_Eq c c' :=
 match c' with
  | Eq => c
  | Lt => Lt
  | Gt => Gt
 end.

Lemma compare_cont_spec p q c :
  compare_cont p q c = switch_Eq c (p ?= q).
Proof.
  unfold compare.
  revert q c.
  induction p; destruct q; simpl; trivial.
  intros c.
  rewrite 2 IHp. now destruct (compare_cont p q Eq).
  intros c.
  rewrite 2 IHp. now destruct (compare_cont p q Eq).
Qed.

(** From this general result, we now describe particular cases
    of [compare_cont p q c = c'] :
    - When [c=Eq], this is directly [compare]
    - When [c<>Eq], we'll show first that [c'<>Eq]
    - That leaves only 4 lemmas for [c] and [c'] being [Lt] or [Gt]
*)

Ltac easy' := repeat split; simpl; easy || now destruct 1.

Theorem compare_cont_Eq p q c :
 compare_cont p q c = Eq -> c = Eq.
Proof.
  rewrite compare_cont_spec. now destruct (p ?= q).
Qed.

Lemma compare_cont_Lt_Gt p q :
  compare_cont p q Lt = Gt <-> p > q.
Proof.
  rewrite compare_cont_spec. unfold gt. destruct (p ?= q); now split.
Qed.

Lemma compare_cont_Lt_Lt p q :
  compare_cont p q Lt = Lt <-> p <= q.
Proof.
  rewrite compare_cont_spec. unfold le. destruct (p ?= q); easy'.
Qed.

Lemma compare_cont_Gt_Lt p q :
  compare_cont p q Gt = Lt <-> p < q.
Proof.
  rewrite compare_cont_spec. unfold lt. destruct (p ?= q); now split.
Qed.

Lemma compare_cont_Gt_Gt p q :
  compare_cont p q Gt = Gt <-> p >= q.
Proof.
  rewrite compare_cont_spec. unfold ge. destruct (p ?= q); easy'.
Qed.

(** We can express recursive equations for [compare] *)

Lemma compare_xO_xO p q : (p~0 ?= q~0) = (p ?= q).
Proof. reflexivity. Qed.

Lemma compare_xI_xI p q : (p~1 ?= q~1) = (p ?= q).
Proof. reflexivity. Qed.

Lemma compare_xI_xO p q :
 (p~1 ?= q~0) = switch_Eq Gt (p ?= q).
Proof. exact (compare_cont_spec p q Gt). Qed.

Lemma compare_xO_xI p q :
 (p~0 ?= q~1) = switch_Eq Lt (p ?= q).
Proof. exact (compare_cont_spec p q Lt). Qed.

Hint Rewrite compare_xO_xO compare_xI_xI compare_xI_xO compare_xO_xI : compare.

Ltac simpl_compare := autorewrite with compare.
Ltac simpl_compare_in H := autorewrite with compare in H.

(** Comparison and equality *)

Theorem compare_refl p : (p ?= p) = Eq.
Proof.
  induction p; auto.
Qed.

(* A generalization of the last property *)

Theorem compare_cont_refl p c :
  compare_cont p p c = c.
Proof.
  now rewrite compare_cont_spec, compare_refl.
Qed.

Theorem compare_eq p q : (p ?= q) = Eq -> p = q.
Proof.
  revert q. induction p; destruct q; intros H;
   simpl; try easy; simpl_compare_in H;
   (f_equal; now auto) || (now destruct compare).
Qed.

Lemma compare_eq_iff p q : (p ?= q) = Eq <-> p = q.
Proof.
  split. apply compare_eq.
  intros; subst; apply compare_refl.
Qed.

Lemma compare_lt_iff p q : (p ?= q) = Lt <-> p < q.
Proof. reflexivity. Qed.

Lemma compare_gt_iff p q : (p ?= q) = Gt <-> p > q.
Proof. reflexivity. Qed.

Lemma compare_le_iff p q : (p ?= q) <> Gt <-> p <= q.
Proof. reflexivity. Qed.

Lemma compare_ge_iff p q : (p ?= q) <> Lt <-> p >= q.
Proof. reflexivity. Qed.

Lemma compare_cont_antisym p q c :
  CompOpp (compare_cont p q c) = compare_cont q p (CompOpp c).
Proof.
  revert q c.
  induction p as [p IHp|p IHp| ]; intros [q|q| ] c; simpl;
   trivial; apply IHp.
Qed.

Lemma compare_antisym p q : (q ?= p) = CompOpp (p ?= q).
Proof.
  unfold compare. now rewrite compare_cont_antisym.
Qed.

Lemma gt_lt p q : p > q -> q < p.
Proof.
  unfold lt, gt. intros H. now rewrite compare_antisym, H.
Qed.

Lemma lt_gt p q : p < q -> q > p.
Proof.
  unfold lt, gt. intros H. now rewrite compare_antisym, H.
Qed.

Lemma gt_lt_iff p q : p > q <-> q < p.
Proof.
  split. apply gt_lt. apply lt_gt.
Qed.

Lemma ge_le p q : p >= q -> q <= p.
Proof.
  unfold le, ge. intros H. contradict H. now apply gt_lt.
Qed.

Lemma le_ge p q : p <= q -> q >= p.
Proof.
  unfold le, ge. intros H. contradict H. now apply lt_gt.
Qed.

Lemma ge_le_iff p q : p >= q <-> q <= p.
Proof.
  split. apply ge_le. apply le_ge.
Qed.

Lemma le_nlt p q : p <= q <-> ~ q < p.
Proof.
  now rewrite <- ge_le_iff.
Qed.

Lemma lt_nle p q : p < q <-> ~ q <= p.
Proof.
 intros. unfold lt, le. rewrite compare_antisym.
 destruct compare; split; auto; easy'.
Qed.

Lemma compare_spec p q : CompareSpec (p=q) (p<q) (q<p) (p ?= q).
Proof.
  destruct (p ?= q) as [ ]_eqn; constructor.
  now apply compare_eq.
  trivial.
  now apply gt_lt.
Qed.

Lemma le_lteq p q : p <= q <-> p < q \/ p = q.
Proof.
  unfold le, lt. case compare_spec; split; try easy.
  now right.
  now left.
  now destruct 1.
  destruct 1. discriminate.
  subst. unfold lt in *. now rewrite compare_refl in *.
Qed.

Lemma lt_le_incl p q : p<q -> p<=q.
Proof.
  intros. apply le_lteq. now left.
Qed.

(** ** Boolean comparisons *)

Lemma ltb_lt p q : (p <? q) = true <-> p < q.
Proof.
  unfold ltb, lt. destruct compare; easy'.
Qed.

Lemma leb_le p q : (p <=? q) = true <-> p <= q.
Proof.
  unfold leb, le. destruct compare; easy'.
Qed.

(** ** Comparison and the successor *)

Lemma compare_succ_r p q :
  switch_Eq Gt (p ?= succ q) = switch_Eq Lt (p ?= q).
Proof.
  revert q.
  induction p as [p IH|p IH| ]; intros [q|q| ]; simpl;
   simpl_compare; rewrite ?IH; trivial;
   (now destruct compare) || (now destruct p).
Qed.

Lemma compare_succ_l p q :
  switch_Eq Lt (succ p ?= q) = switch_Eq Gt (p ?= q).
Proof.
  rewrite 2 (compare_antisym q). generalize (compare_succ_r q p).
  now do 2 destruct compare.
Qed.

Theorem lt_succ_r p q : p < succ q <-> p <= q.
Proof.
  unfold lt, le. generalize (compare_succ_r p q).
  do 2 destruct compare; try discriminate; now split.
Qed.

Lemma lt_succ_diag_r p : p < succ p.
Proof.
  rewrite lt_succ_r. apply le_lteq. now right.
Qed.

Lemma compare_succ_succ p q : (succ p ?= succ q) = (p ?= q).
Proof.
 revert q.
 induction p; destruct q; simpl; simpl_compare; trivial;
  apply compare_succ_l || apply compare_succ_r ||
  (now destruct p) || (now destruct q).
Qed.

(** ** 1 is the least positive number *)

Lemma le_1_l p : 1 <= p.
Proof.
  now destruct p.
Qed.

Lemma ge_1_r p : p >= 1.
Proof.
  now destruct p.
Qed.

Lemma nlt_1_r p : ~ p < 1.
Proof.
  exact (ge_1_r p).
Qed.

Lemma lt_1_succ p : 1 < succ p.
Proof.
  apply lt_succ_r, le_1_l.
Qed.

(** ** Properties of the order *)

Lemma lt_lt_succ n m : n < m -> n < succ m.
Proof.
  intros. now apply lt_succ_r, lt_le_incl.
Qed.

Lemma succ_lt_mono n m : n < m <-> succ n < succ m.
Proof.
  unfold lt. now rewrite compare_succ_succ.
Qed.

Lemma succ_le_mono n m : n <= m <-> succ n <= succ m.
Proof.
  unfold le. now rewrite compare_succ_succ.
Qed.

Lemma lt_irrefl p : ~ p < p.
Proof.
  unfold lt. now rewrite compare_refl.
Qed.

Lemma lt_trans n m p : n < m -> m < p -> n < p.
Proof.
  induction p using peano_ind; intros H H'.
  elim (nlt_1_r _ H').
  apply lt_lt_succ.
  apply lt_succ_r, le_lteq in H'. destruct H' as [H'|H']; subst; auto.
Qed.

Theorem lt_ind : forall (A : positive -> Prop) (n : positive),
  A (succ n) ->
    (forall m : positive, n < m -> A m -> A (succ m)) ->
      forall m : positive, n < m -> A m.
Proof.
  intros A n AB AS m. induction m using peano_ind; intros H.
  elim (nlt_1_r _ H).
  apply lt_succ_r, le_lteq in H. destruct H as [H|H]; subst; auto.
Qed.

Instance lt_strorder : StrictOrder lt.
Proof. split. exact lt_irrefl. exact lt_trans. Qed.

Instance lt_compat : Proper (Logic.eq==>Logic.eq==>iff) lt.
Proof. repeat red. intros. subst; auto. Qed.

Lemma lt_total p q : p < q \/ p = q \/ q < p.
Proof.
 case (compare_spec p q); intuition.
Qed.

Lemma le_refl p : p <= p.
Proof.
 intros. unfold le. now rewrite compare_refl.
Qed.

Lemma le_lt_trans n m p : n <= m -> m < p -> n < p.
Proof.
 intros H H'. apply le_lteq in H. destruct H.
 now apply lt_trans with m. now subst.
Qed.

Lemma lt_le_trans n m p : n < m -> m <= p -> n < p.
Proof.
 intros H H'. apply le_lteq in H'. destruct H'.
 now apply lt_trans with m. now subst.
Qed.

Lemma le_trans n m p : n <= m -> m <= p -> n <= p.
Proof.
 intros H H'.
 apply le_lteq in H. destruct H.
 apply le_lteq; left. now apply lt_le_trans with m.
 now subst.
Qed.

Lemma le_succ_l n m : succ n <= m <-> n < m.
Proof.
 rewrite <- lt_succ_r. symmetry. apply succ_lt_mono.
Qed.

Lemma le_antisym p q : p <= q -> q <= p -> p = q.
Proof.
 rewrite le_lteq; destruct 1; auto.
 rewrite le_lteq; destruct 1; auto.
 elim (lt_irrefl p). now transitivity q.
Qed.

Instance le_preorder : PreOrder le.
Proof. split. exact le_refl. exact le_trans. Qed.

Instance le_partorder : PartialOrder Logic.eq le.
Proof.
 intros x y. change (x=y <-> x <= y <= x).
 split. intros; now subst.
 destruct 1; now apply le_antisym.
Qed.

(** ** Comparison and addition *)

Lemma add_compare_mono_l p q r : (p+q ?= p+r) = (q ?= r).
Proof.
 revert p q r. induction p using peano_ind; intros q r.
 rewrite 2 add_1_l. apply compare_succ_succ.
 now rewrite 2 add_succ_l, compare_succ_succ.
Qed.

Lemma add_compare_mono_r p q r : (q+p ?= r+p) = (q ?= r).
Proof.
 rewrite 2 (add_comm _ p). apply add_compare_mono_l.
Qed.

(** ** Order and addition *)

Lemma add_lt_mono_l p q r : q<r <-> p+q < p+r.
Proof.
 unfold lt. rewrite add_compare_mono_l. apply iff_refl.
Qed.

Lemma add_lt_mono_r p q r : q<r <-> q+p < r+p.
Proof.
 unfold lt. rewrite add_compare_mono_r. apply iff_refl.
Qed.

Lemma add_lt_mono p q r s : p<q -> r<s -> p+r<q+s.
Proof.
 intros. apply lt_trans with (p+s).
 now apply add_lt_mono_l.
 now apply add_lt_mono_r.
Qed.

Lemma add_le_mono_l p q r : q<=r <-> p+q<=p+r.
Proof.
 unfold le. rewrite add_compare_mono_l. apply iff_refl.
Qed.

Lemma add_le_mono_r p q r : q<=r <-> q+p<=r+p.
Proof.
 unfold le. rewrite add_compare_mono_r. apply iff_refl.
Qed.

Lemma add_le_mono p q r s : p<=q -> r<=s -> p+r <= q+s.
Proof.
 intros. apply le_trans with (p+s).
 now apply add_le_mono_l.
 now apply add_le_mono_r.
Qed.

(** ** Comparison and multiplication *)

Lemma mul_compare_mono_l p q r : (p*q ?= p*r) = (q ?= r).
Proof.
 revert q r. induction p; simpl; trivial.
 intros q r. specialize (IHp q r).
 destruct (compare_spec q r).
 subst. apply compare_refl.
 now apply add_lt_mono.
 now apply lt_gt, add_lt_mono, gt_lt.
Qed.

Lemma mul_compare_mono_r p q r : (q*p ?= r*p) = (q ?= r).
Proof.
 rewrite 2 (mul_comm _ p). apply mul_compare_mono_l.
Qed.

(** ** Order and multiplication *)

Lemma mul_lt_mono_l p q r : q<r <-> p*q < p*r.
Proof.
 unfold lt. rewrite mul_compare_mono_l. apply iff_refl.
Qed.

Lemma mul_lt_mono_r p q r : q<r <-> q*p < r*p.
Proof.
 unfold lt. rewrite mul_compare_mono_r. apply iff_refl.
Qed.

Lemma mul_lt_mono p q r s : p<q -> r<s -> p*r < q*s.
Proof.
 intros. apply lt_trans with (p*s).
 now apply mul_lt_mono_l.
 now apply mul_lt_mono_r.
Qed.

Lemma mul_le_mono_l p q r : q<=r <-> p*q<=p*r.
Proof.
 unfold le. rewrite mul_compare_mono_l. apply iff_refl.
Qed.

Lemma mul_le_mono_r p q r : q<=r <-> q*p<=r*p.
Proof.
 unfold le. rewrite mul_compare_mono_r. apply iff_refl.
Qed.

Lemma mul_le_mono p q r s : p<=q -> r<=s -> p*r <= q*s.
Proof.
 intros. apply le_trans with (p*s).
 now apply mul_le_mono_l.
 now apply mul_le_mono_r.
Qed.

Lemma lt_add_r p q : p < p+q.
Proof.
 induction q using peano_ind.
 rewrite add_1_r. apply lt_succ_diag_r.
 apply lt_trans with (p+q); auto.
 apply add_lt_mono_l, lt_succ_diag_r.
Qed.

Lemma lt_not_add_l p q : ~ p+q < p.
Proof.
 intro H. elim (lt_irrefl p).
 apply lt_trans with (p+q); auto using lt_add_r.
Qed.

Lemma pow_gt_1 n p : 1<n -> 1<n^p.
Proof.
 intros H. induction p using peano_ind.
 now rewrite pow_1_r.
 rewrite pow_succ_r.
 apply lt_trans with (n*1).
 now rewrite mul_1_r.
 now apply mul_lt_mono_l.
Qed.

(**********************************************************************)
(** * Properties of subtraction on binary positive numbers *)

Lemma sub_1_r p : sub p 1 = pred p.
Proof.
  now destruct p.
Qed.

Lemma pred_sub p : pred p = sub p 1.
Proof.
  symmetry. apply sub_1_r.
Qed.

Lemma sub_mask_succ_r p q :
  sub_mask p (succ q) = sub_mask_carry p q.
Proof.
  revert q. induction p ; destruct q; simpl; f_equal; trivial; now destruct p.
Qed.

Theorem sub_mask_carry_spec p q :
  sub_mask_carry p q = pred_mask (sub_mask p q).
Proof.
  revert q. induction p as [p IHp|p IHp| ]; destruct q; simpl;
   try reflexivity; try rewrite IHp;
   destruct (sub_mask p q) as [|[r|r| ]|] || destruct p; auto.
Qed.

Theorem sub_succ_r p q : p - (succ q) = pred (p - q).
Proof.
  unfold sub; rewrite sub_mask_succ_r, sub_mask_carry_spec.
  destruct (sub_mask p q) as [|[r|r| ]|]; auto.
Qed.

Lemma double_eq_0_inversion (p:mask) :
  double_mask p = IsNul -> p = IsNul.
Proof.
  now destruct p.
Qed.

Lemma succ_double_0_discr (p:mask) : succ_double_mask p <> IsNul.
Proof.
  now destruct p.
Qed.

Lemma succ_double_eq_1_inversion (p:mask) :
  succ_double_mask p = IsPos 1 -> p = IsNul.
Proof.
  now destruct p.
Qed.

Lemma double_eq_1_discr (p:mask) : double_mask p <> IsPos 1.
Proof.
  now destruct p.
Qed.

Definition mask2cmp (p:mask) : comparison :=
 match p with
  | IsNul => Eq
  | IsPos _ => Gt
  | IsNeg => Lt
 end.

Lemma sub_mask_compare p q :
 mask2cmp (sub_mask p q) = (p ?= q).
Proof.
  symmetry. revert q.
  induction p as [p IHp| p IHp| ]; intros [q|q| ]; simpl; trivial;
  specialize (IHp q); rewrite ?sub_mask_carry_spec;
  destruct (sub_mask p q) as [|r|]; simpl in *;
  try clear r; try destruct r; simpl; trivial;
  simpl_compare; now rewrite IHp.
Qed.

Theorem sub_mask_nul_iff p q : sub_mask p q = IsNul <-> p = q.
Proof.
  rewrite <- compare_eq_iff, <- sub_mask_compare.
  destruct (sub_mask p q); now split.
Qed.

Theorem sub_mask_diag p : sub_mask p p = IsNul.
Proof.
  now apply sub_mask_nul_iff.
Qed.

(** ** Properties of subtraction without underflow *)

Lemma sub_mask_carry_pos p q r :
  sub_mask p q = IsPos r ->
  r = 1 \/ sub_mask_carry p q = IsPos (pred r).
Proof.
 intros H.
 destruct (eq_dec r 1) as [EQ|NE]; [now left|right].
 rewrite sub_mask_carry_spec, H. destruct r; trivial. now elim NE.
Qed.

Lemma sub_mask_add p q r :
  sub_mask p q = IsPos r -> q + r = p.
Proof.
 revert q r.
 induction p as [p IHp|p IHp| ]; intros [q|q| ] r H;
  simpl in H; try destr_eq H; try specialize (IHp q);
  rewrite ?sub_mask_carry_spec in H.
 (* p~1 q~1 *)
 destruct (sub_mask p q) as [|r'|]; destr_eq H. subst r; simpl; f_equal; auto.
 (* p~1 q~0 *)
 assert (H' := proj1 (sub_mask_nul_iff p q)).
 destruct (sub_mask p q) as [|r'|]; destr_eq H; subst r; simpl; f_equal; auto.
 symmetry; auto.
 (* p~1 1 *)
 subst r; simpl; f_equal; auto.
 (* p~0 q~1 *)
 destruct (sub_mask p q) as [|[r'|r'| ]|]; destr_eq H; subst r; simpl; f_equal.
 rewrite add_carry_spec, <- add_succ_r. auto.
 rewrite add_carry_spec, <- add_succ_r, succ_pred_double. auto.
 rewrite <- add_1_r. auto.
 (* p~0 q~0 *)
 destruct (sub_mask p q) as [|r'|]; destr_eq H; subst r; simpl; f_equal. auto.
 (* p~0 1 *)
 subst r; now rewrite add_1_l, succ_pred_double.
Qed.

Lemma sub_mask_pos_iff p q :
  (exists r, sub_mask p q = IsPos r) <-> p > q.
Proof.
 unfold gt. rewrite <- sub_mask_compare.
 destruct (sub_mask p q) as [|r|]; split; try easy'. now exists r.
Qed.

Lemma sub_mask_pos p q :
  q < p -> exists r, sub_mask p q = IsPos r.
Proof.
 intros. now apply sub_mask_pos_iff, lt_gt.
Qed.

Lemma sub_mask_pos' p q :
  q < p -> exists r, sub_mask p q = IsPos r /\ q + r = p.
Proof.
 intros H. destruct (sub_mask_pos p q H) as (r,Hr).
 exists r. split; trivial. now apply sub_mask_add.
Qed.

Theorem sub_add p q : q < p -> (p-q)+q = p.
Proof.
  intros H; destruct (sub_mask_pos p q H) as (r,U).
  unfold sub. rewrite U. rewrite add_comm. now apply sub_mask_add.
Qed.

Lemma add_sub p q : (p+q)-q = p.
Proof.
 intros. apply add_reg_r with q.
 rewrite sub_add; trivial.
 rewrite add_comm. apply lt_add_r.
Qed.

Lemma mul_sub_distr_l p q r : r<q -> p*(q-r) = p*q-p*r.
Proof.
 intros H.
 apply add_reg_r with (p*r).
 rewrite <- mul_add_distr_l.
 rewrite sub_add; trivial.
 symmetry. apply sub_add; trivial.
 now apply mul_lt_mono_l.
Qed.

Lemma sub_lt_mono_l p q r: q<p -> p<r -> r-p < r-q.
Proof.
 intros Hqp Hpr.
 apply (add_lt_mono_r p).
 rewrite sub_add by trivial.
 apply le_lt_trans with ((r-q)+q).
 rewrite sub_add by (now apply lt_trans with p).
 apply le_refl.
 now apply add_lt_mono_l.
Qed.

Lemma sub_compare_mono_l p q r :
 q<p -> r<p -> (p-q ?= p-r) = (r ?= q).
Proof.
 intros Hqp Hrp.
 case (compare_spec r q); intros H. subst. apply compare_refl.
 apply sub_lt_mono_l; trivial.
 apply lt_gt, sub_lt_mono_l; trivial.
Qed.

Lemma sub_compare_mono_r p q r :
 p<q -> p<r -> (q-p ?= r-p) = (q ?= r).
Proof.
 intros. rewrite <- (add_compare_mono_r p), 2 sub_add; trivial.
Qed.

Lemma sub_lt_mono_r p q r : q<p -> r<q -> q-r < p-r.
Proof.
 intros. unfold lt. rewrite sub_compare_mono_r; trivial.
 now apply lt_trans with q.
Qed.

Lemma sub_decr n m : m<n -> n-m < n.
Proof.
 intros.
 apply add_lt_mono_r with m.
 rewrite sub_add; trivial.
 apply lt_add_r.
Qed.

Lemma add_sub_assoc p q r : r<q -> p+(q-r) = p+q-r.
Proof.
 intros.
 apply add_reg_r with r.
 rewrite <- add_assoc, !sub_add; trivial.
 rewrite add_comm. apply lt_trans with q; trivial using lt_add_r.
Qed.

Lemma sub_add_distr p q r : q+r < p -> p-(q+r) = p-q-r.
Proof.
 intros.
 assert (q < p)
  by (apply lt_trans with (q+r); trivial using lt_add_r).
 rewrite (add_comm q r) in *.
 apply add_reg_r with (r+q).
 rewrite sub_add by trivial.
 rewrite add_assoc, !sub_add; trivial.
 apply (add_lt_mono_r q). rewrite sub_add; trivial.
Qed.

Lemma sub_sub_distr p q r : r<q -> q-r < p -> p-(q-r) = p+r-q.
Proof.
 intros.
 apply add_reg_r with ((q-r)+r).
 rewrite add_assoc, !sub_add; trivial.
 rewrite <- (sub_add q r); trivial.
 now apply add_lt_mono_r.
Qed.

(** Recursive equations for [sub] *)

Lemma sub_xO_xO n m : m<n -> n~0 - m~0 = (n-m)~0.
Proof.
 intros H. unfold sub. simpl.
 now destruct (sub_mask_pos n m H) as (p, ->).
Qed.

Lemma sub_xI_xI n m : m<n -> n~1 - m~1 = (n-m)~0.
Proof.
 intros H. unfold sub. simpl.
 now destruct (sub_mask_pos n m H) as (p, ->).
Qed.

Lemma sub_xI_xO n m : m<n -> n~1 - m~0 = (n-m)~1.
Proof.
 intros H. unfold sub. simpl.
 now destruct (sub_mask_pos n m) as (p, ->).
Qed.

Lemma sub_xO_xI n m : n~0 - m~1 = pred_double (n-m).
Proof.
 unfold sub. simpl. rewrite sub_mask_carry_spec.
 now destruct (sub_mask n m) as [|[r|r|]|].
Qed.

(** Properties of subtraction with underflow *)

Lemma sub_mask_neg_iff p q : sub_mask p q = IsNeg <-> p < q.
Proof.
  unfold lt. rewrite <- sub_mask_compare.
  destruct sub_mask; now split.
Qed.

Lemma sub_mask_neg p q : p<q -> sub_mask p q = IsNeg.
Proof.
  apply sub_mask_neg_iff.
Qed.

Lemma sub_le p q : p<=q -> p-q = 1.
Proof.
  unfold le, sub. rewrite <- sub_mask_compare.
  destruct sub_mask; easy'.
Qed.

Lemma sub_lt p q : p<q -> p-q = 1.
Proof.
  intros. now apply sub_le, lt_le_incl.
Qed.

Lemma sub_diag p : p-p = 1.
Proof.
  unfold sub. now rewrite sub_mask_diag.
Qed.

(** ** Results concerning [size] and [size_nat] *)

Lemma size_nat_monotone p q : p<q -> (size_nat p <= size_nat q)%nat.
Proof.
  assert (le0 : forall n, (0<=n)%nat) by (induction n; auto).
  assert (leS : forall n m, (n<=m -> S n <= S m)%nat) by (induction 1; auto).
  revert q.
  induction p; destruct q; simpl; intros; auto; easy || apply leS;
   red in H; simpl_compare_in H.
  apply IHp. red. now destruct (p?=q).
  destruct (compare_spec p q); subst; now auto.
Qed.

Lemma size_gt p : p < 2^(size p).
Proof.
 induction p; simpl; try rewrite pow_succ_r; try easy.
 apply le_succ_l in IHp. now apply le_succ_l.
Qed.

Lemma size_le p : 2^(size p) <= p~0.
Proof.
 induction p; simpl; try rewrite pow_succ_r; try easy.
 apply mul_le_mono_l.
 apply le_lteq; left. rewrite xI_succ_xO. apply lt_succ_r, IHp.
Qed.

(** ** Properties of [min] and [max] *)

(** First, the specification *)

Lemma max_l : forall x y, y<=x -> max x y = x.
Proof.
 intros x y H. unfold max. case compare_spec; auto.
 intros H'. apply le_nlt in H. now elim H.
Qed.

Lemma max_r : forall x y, x<=y -> max x y = y.
Proof.
 unfold le, max. intros x y. destruct compare; easy'.
Qed.

Lemma min_l : forall x y, x<=y -> min x y = x.
Proof.
 unfold le, min. intros x y. destruct compare; easy'.
Qed.

Lemma min_r : forall x y, y<=x -> min x y = y.
Proof.
 intros x y H. unfold min. case compare_spec; auto.
 intros H'. apply le_nlt in H. now elim H'.
Qed.

(** We hence obtain all the generic properties of [min] and [max]. *)

Include !UsualMinMaxLogicalProperties.
Include !UsualMinMaxDecProperties.

(** Minimum, maximum and constant one *)

Lemma max_1_l n : max 1 n = n.
Proof.
 unfold max. case compare_spec; auto.
 intros H. apply lt_nle in H. elim H. apply le_1_l.
Qed.

Lemma max_1_r n : max n 1 = n.
Proof. rewrite max_comm. apply max_1_l. Qed.

Lemma min_1_l n : min 1 n = 1.
Proof.
 unfold min. case compare_spec; auto.
 intros H. apply lt_nle in H. elim H. apply le_1_l.
Qed.

Lemma min_1_r n : min n 1 = 1.
Proof. rewrite min_comm. apply min_1_l. Qed.

(** Minimum, maximum and operations (consequences of monotonicity) *)

Lemma succ_max_distr n m : succ (max n m) = max (succ n) (succ m).
Proof.
 symmetry. apply max_monotone.
 intros x x'. apply succ_le_mono.
Qed.

Lemma succ_min_distr n m : succ (min n m) = min (succ n) (succ m).
Proof.
 symmetry. apply min_monotone.
 intros x x'. apply succ_le_mono.
Qed.

Lemma add_max_distr_l n m p : max (p + n) (p + m) = p + max n m.
Proof.
 apply max_monotone. intros x x'. apply add_le_mono_l.
Qed.

Lemma add_max_distr_r n m p : max (n + p) (m + p) = max n m + p.
Proof.
 rewrite 3 (add_comm _ p). apply add_max_distr_l.
Qed.

Lemma add_min_distr_l n m p : min (p + n) (p + m) = p + min n m.
Proof.
 apply min_monotone. intros x x'. apply add_le_mono_l.
Qed.

Lemma add_min_distr_r n m p : min (n + p) (m + p) = min n m + p.
Proof.
 rewrite 3 (add_comm _ p). apply add_min_distr_l.
Qed.

Lemma mul_max_distr_l n m p : max (p * n) (p * m) = p * max n m.
Proof.
 apply max_monotone. intros x x'. apply mul_le_mono_l.
Qed.

Lemma mul_max_distr_r n m p : max (n * p) (m * p) = max n m * p.
Proof.
 rewrite 3 (mul_comm _ p). apply mul_max_distr_l.
Qed.

Lemma mul_min_distr_l n m p : min (p * n) (p * m) = p * min n m.
Proof.
 apply min_monotone. intros x x'. apply mul_le_mono_l.
Qed.

Lemma mul_min_distr_r n m p : min (n * p) (m * p) = min n m * p.
Proof.
 rewrite 3 (mul_comm _ p). apply mul_min_distr_l.
Qed.


(** ** Results concerning [iter_op] *)

Lemma iter_op_succ : forall A (op:A->A->A),
 (forall x y z, op x (op y z) = op (op x y) z) ->
 forall p a,
 iter_op op (succ p) a = op a (iter_op op p a).
Proof.
 induction p; simpl; intros; trivial.
 rewrite H. apply IHp.
Qed.

(** ** Results about [of_nat] and [of_succ_nat] *)

Lemma pred_of_succ_nat (n:nat) : pred (of_succ_nat n) = of_nat n.
Proof.
 induction n. trivial.
 simpl. rewrite pred_succ. rewrite <- IHn.
 destruct n. trivial.
 simpl. now rewrite pred_succ.
Qed.

Lemma succ_of_nat (n:nat) : n<>O -> succ (of_nat n) = of_succ_nat n.
Proof.
 intro H.
 rewrite <- pred_of_succ_nat.
 destruct n. now destruct H.
 simpl. now rewrite pred_succ.
Qed.

(** ** Correctness proofs for the square root function *)

Inductive SqrtSpec : positive*mask -> positive -> Prop :=
 | SqrtExact s x : x=s*s -> SqrtSpec (s,IsNul) x
 | SqrtApprox s r x : x=s*s+r -> r <= s~0 -> SqrtSpec (s,IsPos r) x.

Lemma sqrtrem_step_spec f g p x :
 (f=xO \/ f=xI) -> (g=xO \/ g=xI) ->
 SqrtSpec p x -> SqrtSpec (sqrtrem_step f g p) (g (f x)).
Proof.
intros Hf Hg [ s _ -> | s r _ -> Hr ].
(* exact *)
unfold sqrtrem_step.
destruct Hf,Hg; subst; simpl; constructor; now rewrite ?square_xO.
(* approx *)
assert (Hfg : forall p q, g (f (p+q)) = p~0~0 + g (f q))
 by (intros; destruct Hf, Hg; now subst).
unfold sqrtrem_step, leb.
case compare_spec; [intros EQ | intros LT | intros GT].
(* - EQ *)
rewrite <- EQ, sub_mask_diag. constructor.
destruct Hg; subst g; destr_eq EQ.
destruct Hf; subst f; destr_eq EQ.
subst. now rewrite square_xI.
(* - LT *)
destruct (sub_mask_pos' _ _ LT) as (y & -> & H). constructor.
rewrite Hfg, <- H. now rewrite square_xI, add_assoc. clear Hfg.
rewrite <- lt_succ_r in Hr. change (r < s~1) in Hr.
rewrite <- lt_succ_r, (add_lt_mono_l (s~0~1)), H. simpl.
rewrite add_carry_spec, add_diag. simpl.
destruct Hf,Hg; subst; red; simpl_compare; now rewrite Hr.
(* - GT *)
constructor. now rewrite Hfg, square_xO. apply lt_succ_r, GT.
Qed.

Lemma sqrtrem_spec p : SqrtSpec (sqrtrem p) p.
Proof.
revert p. fix 1.
 destruct p; try destruct p; try (constructor; easy);
  apply sqrtrem_step_spec; auto.
Qed.

Lemma sqrt_spec p :
 let s := sqrt p in s*s <= p < (succ s)*(succ s).
Proof.
 simpl.
 assert (H:=sqrtrem_spec p).
 unfold sqrt in *. destruct sqrtrem as (s,rm); simpl.
 inversion_clear H; subst.
 (* exact *)
 split. reflexivity. apply mul_lt_mono; apply lt_succ_diag_r.
 (* approx *)
 split.
 apply lt_le_incl, lt_add_r.
 rewrite <- add_1_l, mul_add_distr_r, !mul_add_distr_l, !mul_1_r, !mul_1_l.
 rewrite add_assoc, (add_comm _ r). apply add_lt_mono_r.
 now rewrite <- add_assoc, add_diag, add_1_l, lt_succ_r.
Qed.

(** ** Correctness proofs for the gcd function *)

Lemma divide_add_cancel_l p q r : (p | r) -> (p | q + r) -> (p | q).
Proof.
 intros (s,Hs) (t,Ht).
 exists (t-s).
 rewrite mul_sub_distr_l.
 rewrite Hs, Ht.
 apply add_sub.
 apply mul_lt_mono_l with p.
 rewrite Hs, Ht, add_comm.
 apply lt_add_r.
Qed.

Lemma divide_xO_xI p q r : (p | q~0) -> (p | r~1) -> (p | q).
Proof.
 intros (s,Hs) (t,Ht).
 destruct p.
 destruct s; try easy. rewrite mul_xO_r in Hs. destr_eq Hs. now exists s.
 discriminate.
 exists q; auto.
Qed.

Lemma divide_xO_xO p q : (p~0|q~0) <-> (p|q).
Proof.
 split; intros (r,H); simpl in *. destr_eq H. now exists r.
 exists r; simpl; f_equal; auto.
Qed.

Lemma divide_mul_l p q r : (p|q) -> (p|q*r).
Proof.
 intros (s,H). exists (s*r). rewrite mul_assoc; now f_equal.
Qed.

Lemma divide_mul_r p q r : (p|r) -> (p|q*r).
Proof.
 rewrite mul_comm. apply divide_mul_l.
Qed.

(** The first component of ggcd is gcd *)

Lemma ggcdn_gcdn : forall n a b,
  fst (ggcdn n a b) = gcdn n a b.
Proof.
 induction n.
 simpl; auto.
 destruct a, b; simpl; auto; try case compare_spec; simpl; trivial;
  rewrite <- IHn; destruct ggcdn as (g,(u,v)); simpl; auto.
Qed.

Lemma ggcd_gcd : forall a b, fst (ggcd a b) = gcd a b.
Proof.
 unfold ggcd, gcd. intros. apply ggcdn_gcdn.
Qed.

(** The other components of ggcd are indeed the correct factors. *)

Ltac destr_pggcdn IHn :=
 match goal with |- context [ ggcdn _ ?x ?y ] =>
  generalize (IHn x y); destruct ggcdn as (g,(u,v)); simpl
 end.

Lemma ggcdn_correct_divisors : forall n a b,
  let '(g,(aa,bb)) := ggcdn n a b in
  a = g*aa /\ b = g*bb.
Proof.
 induction n.
 simpl; auto.
 destruct a, b; simpl; auto; try case compare_spec; try destr_pggcdn IHn.
 (* Eq *)
 intros ->. now rewrite mul_comm.
 (* Lt *)
 intros (H',H) LT; split; auto.
 rewrite mul_add_distr_l, mul_xO_r, <- H, <- H'.
 simpl. f_equal. symmetry.
 rewrite add_comm. now apply sub_add.
 (* Gt *)
 intros (H',H) LT; split; auto.
 rewrite mul_add_distr_l, mul_xO_r, <- H, <- H'.
 simpl. f_equal. symmetry.
 rewrite add_comm. now apply sub_add.
 (* Then... *)
 intros (H,H'); split; auto. rewrite mul_xO_r, H'; auto.
 intros (H,H'); split; auto. rewrite mul_xO_r, H; auto.
 intros (H,H'); split; subst; auto.
Qed.

Lemma ggcd_correct_divisors : forall a b,
  let '(g,(aa,bb)) := ggcd a b in
  a=g*aa /\ b=g*bb.
Proof.
 unfold ggcd. intros. apply ggcdn_correct_divisors.
Qed.

(** We can use this fact to prove a part of the gcd correctness *)

Lemma gcd_divide_l : forall a b, (gcd a b | a).
Proof.
 intros a b. rewrite <- ggcd_gcd. generalize (ggcd_correct_divisors a b).
 destruct ggcd as (g,(aa,bb)); simpl. intros (H,_). exists aa; auto.
Qed.

Lemma gcd_divide_r : forall a b, (gcd a b | b).
Proof.
 intros a b. rewrite <- ggcd_gcd. generalize (ggcd_correct_divisors a b).
 destruct ggcd as (g,(aa,bb)); simpl. intros (_,H). exists bb; auto.
Qed.

(** We now prove directly that gcd is the greatest amongst common divisors *)

Lemma gcdn_greatest : forall n a b, (size_nat a + size_nat b <= n)%nat ->
 forall p, (p|a) -> (p|b) -> (p|gcdn n a b).
Proof.
 induction n.
 destruct a, b; simpl; inversion 1.
 destruct a, b; simpl; try case compare_spec; simpl; auto.
 (* Lt *)
 intros LT LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
 apply le_S_n in LE. eapply Le.le_trans; [|eapply LE].
 rewrite plus_comm, <- plus_n_Sm, <- plus_Sn_m.
 apply plus_le_compat; trivial.
 apply size_nat_monotone, sub_decr, LT.
 apply divide_xO_xI with a; trivial.
 apply (divide_add_cancel_l p _ a~1); trivial.
 now rewrite <- sub_xI_xI, sub_add.
 (* Gt *)
 intros LT LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
 apply le_S_n in LE. eapply Le.le_trans; [|eapply LE].
 apply plus_le_compat; trivial.
 apply size_nat_monotone, sub_decr, LT.
 apply divide_xO_xI with b; trivial.
 apply (divide_add_cancel_l p _ b~1); trivial.
 now rewrite <- sub_xI_xI, sub_add.
 (* a~1 b~0 *)
 intros LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
 apply le_S_n in LE. simpl. now rewrite plus_n_Sm.
 apply divide_xO_xI with a; trivial.
 (* a~0 b~1 *)
 intros LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
 simpl. now apply le_S_n.
 apply divide_xO_xI with b; trivial.
 (* a~0 b~0 *)
 intros LE p Hp1 Hp2.
 destruct p.
 change (gcdn n a b)~0 with (2*(gcdn n a b)).
 apply divide_mul_r.
 apply IHn; clear IHn.
 apply le_S_n in LE. apply le_Sn_le. now rewrite plus_n_Sm.
 apply divide_xO_xI with p; trivial. exists 1; now rewrite mul_1_r.
 apply divide_xO_xI with p; trivial. exists 1; now rewrite mul_1_r.
 apply divide_xO_xO.
 apply IHn; clear IHn.
 apply le_S_n in LE. apply le_Sn_le. now rewrite plus_n_Sm.
 now apply divide_xO_xO.
 now apply divide_xO_xO.
 exists (gcdn n a b)~0. auto.
Qed.

Lemma gcd_greatest : forall a b p, (p|a) -> (p|b) -> (p|gcd a b).
Proof.
 intros. apply gcdn_greatest; auto.
Qed.

(** As a consequence, the rests after division by gcd are relatively prime *)

Lemma ggcd_greatest : forall a b,
 let (aa,bb) := snd (ggcd a b) in
 forall p, (p|aa) -> (p|bb) -> p=1.
Proof.
 intros. generalize (gcd_greatest a b) (ggcd_correct_divisors a b).
 rewrite <- ggcd_gcd. destruct ggcd as (g,(aa,bb)); simpl.
 intros H (EQa,EQb) p Hp1 Hp2; subst.
 assert (H' : (g*p | g)).
  apply H.
  destruct Hp1 as (r,Hr). exists r. now rewrite <- Hr, mul_assoc.
  destruct Hp2 as (r,Hr). exists r. now rewrite <- Hr, mul_assoc.
 destruct H' as (q,H').
 apply mul_1_inversion_l with q.
 apply mul_reg_l with g. now rewrite mul_assoc, mul_1_r.
Qed.

End Pos.

(** Exportation of notations *)

Infix "+" := Pos.add : positive_scope.
Infix "-" := Pos.sub : positive_scope.
Infix "*" := Pos.mul : positive_scope.
Infix "^" := Pos.pow : positive_scope.
Infix "?=" := Pos.compare (at level 70, no associativity) : positive_scope.
Infix "=?" := Pos.eqb (at level 70, no associativity) : positive_scope.
Infix "<=?" := Pos.leb (at level 70, no associativity) : positive_scope.
Infix "<?" := Pos.ltb (at level 70, no associativity) : positive_scope.
Infix "<=" := Pos.le : positive_scope.
Infix "<" := Pos.lt : positive_scope.
Infix ">=" := Pos.ge : positive_scope.
Infix ">" := Pos.gt : positive_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : positive_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : positive_scope.
Notation "x < y < z" := (x < y /\ y < z) : positive_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : positive_scope.

Notation "( p | q )" := (Pos.divide p q) (at level 0) : positive_scope.

(** Compatibility notations *)

Notation positive := positive (only parsing).
Notation positive_rect := positive_rect (only parsing).
Notation positive_rec := positive_rec (only parsing).
Notation positive_ind := positive_ind (only parsing).
Notation xI := xI (only parsing).
Notation xO := xO (only parsing).
Notation xH := xH (only parsing).

Notation Psucc := Pos.succ (only parsing).
Notation Pplus := Pos.add (only parsing).
Notation Pplus_carry := Pos.add_carry (only parsing).
Notation Ppred := Pos.pred (only parsing).
Notation Piter_op := Pos.iter_op (only parsing).
Notation Piter_op_succ := Pos.iter_op_succ (only parsing).
Notation Pmult_nat := (Pos.iter_op plus) (only parsing).
Notation nat_of_P := Pos.to_nat (only parsing).
Notation P_of_succ_nat := Pos.of_succ_nat (only parsing).
Notation Pdouble_minus_one := Pos.pred_double (only parsing).
Notation positive_mask := Pos.mask (only parsing).
Notation IsNul := Pos.IsNul (only parsing).
Notation IsPos := Pos.IsPos (only parsing).
Notation IsNeg := Pos.IsNeg (only parsing).
Notation positive_mask_rect := Pos.mask_rect (only parsing).
Notation positive_mask_ind := Pos.mask_ind (only parsing).
Notation positive_mask_rec := Pos.mask_rec (only parsing).
Notation Pdouble_plus_one_mask := Pos.succ_double_mask (only parsing).
Notation Pdouble_mask := Pos.double_mask (only parsing).
Notation Pdouble_minus_two := Pos.double_pred_mask (only parsing).
Notation Pminus_mask := Pos.sub_mask (only parsing).
Notation Pminus_mask_carry := Pos.sub_mask_carry (only parsing).
Notation Pminus := Pos.sub (only parsing).
Notation Pmult := Pos.mul (only parsing).
Notation iter_pos p A := (@Pos.iter p A) (only parsing).
Notation Ppow := Pos.pow (only parsing).
Notation Pdiv2 := Pos.div2 (only parsing).
Notation Pdiv2_up := Pos.div2_up (only parsing).
Notation Psize := Pos.size_nat (only parsing).
Notation Psize_pos := Pos.size (only parsing).
Notation Pcompare := Pos.compare_cont (only parsing).
Notation Plt := Pos.lt (only parsing).
Notation Pgt := Pos.gt (only parsing).
Notation Ple := Pos.le (only parsing).
Notation Pge := Pos.ge (only parsing).
Notation Pmin := Pos.min (only parsing).
Notation Pmax := Pos.max (only parsing).
Notation Peqb := Pos.eqb (only parsing).
Notation positive_eq_dec := Pos.eq_dec (only parsing).
Notation xI_succ_xO := Pos.xI_succ_xO (only parsing).
Notation Psucc_discr := Pos.succ_discr (only parsing).
Notation Psucc_o_double_minus_one_eq_xO :=
 Pos.succ_pred_double (only parsing).
Notation Pdouble_minus_one_o_succ_eq_xI :=
 Pos.pred_double_succ (only parsing).
Notation xO_succ_permute := Pos.double_succ (only parsing).
Notation double_moins_un_xO_discr :=
 Pos.pred_double_xO_discr (only parsing).
Notation Psucc_not_one := Pos.succ_not_1 (only parsing).
Notation Ppred_succ := Pos.pred_succ (only parsing).
Notation Psucc_pred := Pos.succ_pred_or (only parsing).
Notation Psucc_inj := Pos.succ_inj (only parsing).
Notation Pplus_carry_spec := Pos.add_carry_spec (only parsing).
Notation Pplus_comm := Pos.add_comm (only parsing).
Notation Pplus_succ_permute_r := Pos.add_succ_r (only parsing).
Notation Pplus_succ_permute_l := Pos.add_succ_l (only parsing).
Notation Pplus_no_neutral := Pos.add_no_neutral (only parsing).
Notation Pplus_carry_plus := Pos.add_carry_add (only parsing).
Notation Pplus_reg_r := Pos.add_reg_r (only parsing).
Notation Pplus_reg_l := Pos.add_reg_l (only parsing).
Notation Pplus_carry_reg_r := Pos.add_carry_reg_r (only parsing).
Notation Pplus_carry_reg_l := Pos.add_carry_reg_l (only parsing).
Notation Pplus_assoc := Pos.add_assoc (only parsing).
Notation Pplus_xO := Pos.add_xO (only parsing).
Notation Pplus_xI_double_minus_one := Pos.add_xI_pred_double (only parsing).
Notation Pplus_xO_double_minus_one := Pos.add_xO_pred_double (only parsing).
Notation Pplus_diag := Pos.add_diag (only parsing).
Notation PeanoView := Pos.PeanoView (only parsing).
Notation PeanoOne := Pos.PeanoOne (only parsing).
Notation PeanoSucc := Pos.PeanoSucc (only parsing).
Notation PeanoView_rect := Pos.PeanoView_rect (only parsing).
Notation PeanoView_ind := Pos.PeanoView_ind (only parsing).
Notation PeanoView_rec := Pos.PeanoView_rec (only parsing).
Notation peanoView_xO := Pos.peanoView_xO (only parsing).
Notation peanoView_xI := Pos.peanoView_xI (only parsing).
Notation peanoView := Pos.peanoView (only parsing).
Notation PeanoView_iter := Pos.PeanoView_iter (only parsing).
Notation eq_dep_eq_positive := Pos.eq_dep_eq_positive (only parsing).
Notation PeanoViewUnique := Pos.PeanoViewUnique (only parsing).
Notation Prect := Pos.peano_rect (only parsing).
Notation Prect_succ := Pos.peano_rect_succ (only parsing).
Notation Prect_base := Pos.peano_rect_base (only parsing).
Notation Prec := Pos.peano_rec (only parsing).
Notation Pind := Pos.peano_ind (only parsing).
Notation Pcase := Pos.peano_case (only parsing).
Notation Pmult_1_r := Pos.mul_1_r (only parsing).
Notation Pmult_Sn_m := Pos.mul_succ_l (only parsing).
Notation Pmult_xO_permute_r := Pos.mul_xO_r (only parsing).
Notation Pmult_xI_permute_r := Pos.mul_xI_r (only parsing).
Notation Pmult_comm := Pos.mul_comm (only parsing).
Notation Pmult_plus_distr_l := Pos.mul_add_distr_l (only parsing).
Notation Pmult_plus_distr_r := Pos.mul_add_distr_r (only parsing).
Notation Pmult_assoc := Pos.mul_assoc (only parsing).
Notation Pmult_xI_mult_xO_discr := Pos.mul_xI_mul_xO_discr (only parsing).
Notation Pmult_xO_discr := Pos.mul_xO_discr (only parsing).
Notation Pmult_reg_r := Pos.mul_reg_r (only parsing).
Notation Pmult_reg_l := Pos.mul_reg_l (only parsing).
Notation Pmult_1_inversion_l := Pos.mul_1_inversion_l (only parsing).
Notation Psquare_xO := Pos.square_xO (only parsing).
Notation Psquare_xI := Pos.square_xI (only parsing).
Notation iter_pos_swap_gen := Pos.iter_swap_gen (only parsing).
Notation iter_pos_swap := Pos.iter_swap (only parsing).
Notation iter_pos_succ := Pos.iter_succ (only parsing).
Notation iter_pos_plus := Pos.iter_add (only parsing).
Notation iter_pos_invariant := Pos.iter_invariant (only parsing).
Notation Ppow_1_r := Pos.pow_1_r (only parsing).
Notation Ppow_succ_r := Pos.pow_succ_r (only parsing).
Notation Peqb_refl := Pos.eqb_refl (only parsing).
Notation Peqb_true_eq := Pos.eqb_true_eq (only parsing).
Notation Peqb_eq := Pos.eqb_eq (only parsing).
Notation Pcompare_refl_id := Pos.compare_cont_refl (only parsing).
Notation Pcompare_eq_iff := Pos.compare_eq_iff (only parsing).
Notation Pcompare_Gt_Lt := Pos.compare_cont_Gt_Lt (only parsing).
Notation Pcompare_eq_Lt := Pos.compare_lt_iff (only parsing).
Notation Pcompare_Lt_Gt := Pos.compare_cont_Lt_Gt (only parsing).
Notation Pcompare_eq_Gt := Pos.compare_gt_iff (only parsing).
Notation Pcompare_antisym := Pos.compare_cont_antisym (only parsing).
Notation ZC1 := Pos.gt_lt (only parsing).
Notation ZC2 := Pos.lt_gt (only parsing).
Notation Pcompare_spec := Pos.compare_spec (only parsing).
Notation Pcompare_p_Sp := Pos.lt_succ_diag_r (only parsing).
Notation Pcompare_succ_succ := Pos.compare_succ_succ (only parsing).
Notation Pcompare_1 := Pos.nlt_1_r (only parsing).
Notation Plt_1 := Pos.nlt_1_r (only parsing).
Notation Plt_1_succ := Pos.lt_1_succ (only parsing).
Notation Plt_lt_succ := Pos.lt_lt_succ (only parsing).
Notation Plt_irrefl := Pos.lt_irrefl (only parsing).
Notation Plt_trans := Pos.lt_trans (only parsing).
Notation Plt_ind := Pos.lt_ind (only parsing).
Notation Ple_lteq := Pos.le_lteq (only parsing).
Notation Ple_refl := Pos.le_refl (only parsing).
Notation Ple_lt_trans := Pos.le_lt_trans (only parsing).
Notation Plt_le_trans := Pos.lt_le_trans (only parsing).
Notation Ple_trans := Pos.le_trans (only parsing).
Notation Plt_succ_r := Pos.lt_succ_r (only parsing).
Notation Ple_succ_l := Pos.le_succ_l (only parsing).
Notation Pplus_compare_mono_l := Pos.add_compare_mono_l (only parsing).
Notation Pplus_compare_mono_r := Pos.add_compare_mono_r (only parsing).
Notation Pplus_lt_mono_l := Pos.add_lt_mono_l (only parsing).
Notation Pplus_lt_mono_r := Pos.add_lt_mono_r (only parsing).
Notation Pplus_lt_mono := Pos.add_lt_mono (only parsing).
Notation Pplus_le_mono_l := Pos.add_le_mono_l (only parsing).
Notation Pplus_le_mono_r := Pos.add_le_mono_r (only parsing).
Notation Pplus_le_mono := Pos.add_le_mono (only parsing).
Notation Pmult_compare_mono_l := Pos.mul_compare_mono_l (only parsing).
Notation Pmult_compare_mono_r := Pos.mul_compare_mono_r (only parsing).
Notation Pmult_lt_mono_l := Pos.mul_lt_mono_l (only parsing).
Notation Pmult_lt_mono_r := Pos.mul_lt_mono_r (only parsing).
Notation Pmult_lt_mono := Pos.mul_lt_mono (only parsing).
Notation Pmult_le_mono_l := Pos.mul_le_mono_l (only parsing).
Notation Pmult_le_mono_r := Pos.mul_le_mono_r (only parsing).
Notation Pmult_le_mono := Pos.mul_le_mono (only parsing).
Notation Plt_plus_r := Pos.lt_add_r (only parsing).
Notation Plt_not_plus_l := Pos.lt_not_add_l (only parsing).
Notation Ppow_gt_1 := Pos.pow_gt_1 (only parsing).
Notation Ppred_mask := Pos.pred_mask (only parsing).
Notation Pminus_mask_succ_r := Pos.sub_mask_succ_r (only parsing).
Notation Pminus_mask_carry_spec := Pos.sub_mask_carry_spec (only parsing).
Notation Pminus_succ_r := Pos.sub_succ_r (only parsing).
Notation double_eq_zero_inversion := Pos.succ_double_0_discr (only parsing).
Notation double_plus_one_zero_discr := Pos.succ_double_0_discr (only parsing).
Notation double_plus_one_eq_one_inversion :=
 Pos.succ_double_eq_1_inversion (only parsing).
Notation double_eq_one_discr := Pos.double_eq_1_discr (only parsing).
Notation Pminus_mask_diag := Pos.sub_mask_diag (only parsing).

Notation Pplus_minus_eq := Pos.add_sub (only parsing).
Notation Pmult_minus_distr_l := Pos.mul_sub_distr_l (only parsing).
Notation Pminus_lt_mono_l := Pos.sub_lt_mono_l (only parsing).
Notation Pminus_compare_mono_l := Pos.sub_compare_mono_l (only parsing).
Notation Pminus_compare_mono_r := Pos.sub_compare_mono_r (only parsing).
Notation Pminus_lt_mono_r := Pos.sub_lt_mono_r (only parsing).
Notation Pminus_decr := Pos.sub_decr (only parsing).
Notation Pminus_xI_xI := Pos.sub_xI_xI (only parsing).
Notation Pplus_minus_assoc := Pos.add_sub_assoc (only parsing).
Notation Pminus_plus_distr := Pos.sub_add_distr (only parsing).
Notation Pminus_minus_distr := Pos.sub_sub_distr (only parsing).
Notation Pminus_mask_Lt := Pos.sub_mask_neg (only parsing).
Notation Pminus_Lt := Pos.sub_lt (only parsing).
Notation Pminus_Eq := Pos.sub_diag (only parsing).
Notation Psize_monotone := Pos.size_nat_monotone (only parsing).
Notation Psize_pos_gt := Pos.size_gt (only parsing).
Notation Psize_pos_le := Pos.size_le (only parsing).

(** More complex compatibility facts, expressed as lemmas
    (to preserve scopes for instance) *)

Lemma Pplus_one_succ_r p : Psucc p = p + 1.
Proof (eq_sym (Pos.add_1_r p)).
Lemma Pplus_one_succ_l p : Psucc p = 1 + p.
Proof (eq_sym (Pos.add_1_l p)).
Lemma Pcompare_refl p : Pcompare p p Eq = Eq.
Proof (Pos.compare_cont_refl p Eq).
Lemma Pcompare_Eq_eq : forall p q, Pcompare p q Eq = Eq -> p = q.
Proof Pos.compare_eq.
Lemma ZC4 p q : Pcompare p q Eq = CompOpp (Pcompare q p Eq).
Proof (Pos.compare_antisym q p).
Lemma Ppred_minus p : Ppred p = p - 1.
Proof (eq_sym (Pos.sub_1_r p)).

Lemma Pminus_mask_Gt p q :
  p > q ->
  exists h : positive,
   Pminus_mask p q = IsPos h /\
   q + h = p /\ (h = 1 \/ Pminus_mask_carry p q = IsPos (Ppred h)).
Proof.
 intros H. apply Pos.gt_lt in H.
 destruct (Pos.sub_mask_pos' p q H) as (r & U & V).
 exists r. repeat split; trivial. now apply Pos.sub_mask_carry_pos.
Qed.

Lemma Pplus_minus : forall p q, p > q -> q+(p-q) = p.
Proof.
 intros. rewrite Pos.add_comm. now apply Pos.sub_add, Pos.gt_lt.
Qed.

(** Discontinued results of little interest and little/zero use
    in user contributions:

    Pplus_carry_no_neutral
    Pplus_carry_pred_eq_plus
    Pcompare_not_Eq
    Pcompare_Lt_Lt
    Pcompare_Lt_eq_Lt
    Pcompare_Gt_Gt
    Pcompare_Gt_eq_Gt
    Psucc_lt_compat
    Psucc_le_compat
    ZC3
    Pcompare_p_Sq
    Pminus_mask_carry_diag
    Pminus_mask_IsNeg
    ZL10
    ZL11

    Infix "/" := Pdiv2 : positive_scope.
*)

(** Old stuff, to remove someday *)

Lemma Dcompare : forall r:comparison, r = Eq \/ r = Lt \/ r = Gt.
Proof.
  destruct r; auto.
Qed.

(** Incompatibilities :

 - [(_ ?= _)%positive] expects no arg now, and designates [Pos.compare]
   which is convertible but syntactically distinct to
   [Pos.compare_cont .. .. Eq].

 - [Pmult_nat] cannot be unfolded (unfold [Pos.iter_op] instead).

*)
