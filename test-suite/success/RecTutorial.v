Module Type LocalNat.

Inductive nat : Set :=
 | O : nat
 | S : nat->nat.
Check nat.
Check O.
Check S.

End LocalNat.

Print nat.


Print le.

Theorem zero_leq_three: 0 <= 3.

Proof.
 constructor 2.
 constructor 2.
 constructor 2.
 constructor 1.

Qed.

Print zero_leq_three.


Lemma zero_leq_three': 0 <= 3.
 repeat constructor.
Qed.


Lemma zero_lt_three : 0 < 3.
Proof.
 unfold lt.
 repeat constructor.
Qed.


Require Import List.

Print list.

Check list.

Check (nil (A:=nat)).

Check (nil (A:= nat -> nat)).

Check (fun A: Set => (cons (A:=A))).

Check (cons 3 (cons 2 nil)).




Require Import Bvector.

Print Vector.t.

Check (Vector.nil nat).

Check (fun (A:Set)(a:A)=> Vector.cons _ a _ (Vector.nil _)).

Check (Vector.cons _ 5 _ (Vector.cons _ 3 _ (Vector.nil _))).













Lemma eq_3_3 : 2 + 1 = 3.
Proof.
 reflexivity.
Qed.
Print eq_3_3.

Lemma eq_proof_proof : refl_equal (2*6) = refl_equal (3*4).
Proof.
 reflexivity.
Qed.
Print eq_proof_proof.

Lemma eq_lt_le : ( 2 < 4) = (3 <= 4).
Proof.
 reflexivity.
Qed.

Lemma eq_nat_nat : nat = nat.
Proof.
 reflexivity.
Qed.

Lemma eq_Set_Set : Set = Set.
Proof.
 reflexivity.
Qed.

Lemma eq_Type_Type : Type = Type.
Proof.
 reflexivity.
Qed.


Check (2 + 1 = 3).


Check (Type = Type).

Goal Type = Type.
reflexivity.
Qed.


Print or.

Print and.


Print sumbool.

Print ex.

Require Import ZArith.
Require Import Compare_dec.

Check le_lt_dec.

Definition max (n p :nat) := match le_lt_dec n p with
                             | left _ => p
                             | right _ => n
                             end.

Theorem le_max : forall n p, n <= p -> max n p = p.
Proof.
 intros n p ; unfold max ; case (le_lt_dec n p); simpl.
 trivial.
 intros; absurd (p < p); eauto with arith.
Qed.

Require Coq.extraction.Extraction.
Extraction max.






Inductive tree(A:Set)   : Set :=
    node : A -> forest A -> tree A
with
  forest (A: Set)    : Set :=
    nochild  : forest A |
    addchild : tree A -> forest A -> forest A.





Inductive
  even    : nat->Prop :=
    evenO : even  O |
    evenS : forall n, odd n -> even (S n)
with
  odd    : nat->Prop :=
    oddS : forall n, even n -> odd (S n).

Lemma odd_49 : odd (7 * 7).
 simpl; repeat constructor.
Qed.



Definition nat_case :=
 fun (Q : Type)(g0 : Q)(g1 : nat -> Q)(n:nat) =>
    match n return Q with
    | 0 => g0
    | S p => g1 p
    end.

Eval simpl in (nat_case nat 0 (fun p => p) 34).

Eval simpl in (fun g0 g1 => nat_case nat g0 g1 34).

Eval simpl in (fun g0 g1 => nat_case nat g0 g1 0).


Definition pred (n:nat) := match n with O => O | S m => m end.

Eval simpl in pred 56.

Eval simpl in pred 0.

Eval simpl in fun p => pred (S p).


Definition xorb (b1 b2:bool) :=
match b1, b2 with
 | false, true => true
 | true, false => true
 | _ , _       => false
end.


 Definition pred_spec (n:nat) := {m:nat | n=0 /\ m=0  \/ n = S m}.


 Definition predecessor : forall n:nat, pred_spec n.
  intro n;case n.
  unfold pred_spec;exists 0;auto.
  unfold pred_spec; intro n0;exists n0; auto.
 Defined.

Print predecessor.

Extraction predecessor.

Theorem nat_expand :
  forall n:nat, n = match n with 0 => 0 | S p => S p end.
 intro n;case n;simpl;auto.
Qed.

Check (fun p:False => match p return 2=3 with end).

Theorem fromFalse : False -> 0=1.
 intro absurd.
 contradiction.
Qed.

Section equality_elimination.
 Variables (A: Type)
           (a b : A)
           (p : a = b)
           (Q : A -> Type).
 Check (fun H : Q a =>
  match p in (eq _  y) return Q y with
     refl_equal => H
  end).

End equality_elimination.


Theorem trans : forall n m p:nat, n=m -> m=p -> n=p.
Proof.
 intros n m p eqnm.
 case eqnm.
 trivial.
Qed.

Lemma Rw :  forall x y: nat, y = y * x -> y * x * x = y.
 intros x y e; do 2 rewrite <- e.
 reflexivity.
Qed.


Require Import Arith.

Check mult_1_l.
(*
mult_1_l
     : forall n : nat, 1 * n = n
*)

Check mult_plus_distr_r.
(*
mult_plus_distr_r
     : forall n m p : nat, (n + m) * p = n * p + m * p

*)

Lemma mult_distr_S : forall n p : nat, n * p + p = (S n)* p.
 simpl;auto with arith.
Qed.

Lemma four_n : forall n:nat, n+n+n+n = 4*n.
 intro n;rewrite <- (mult_1_l n).

 Undo.
 intro n; pattern n at 1.


 rewrite <- mult_1_l.
 repeat rewrite   mult_distr_S.
 trivial.
Qed.


Section Le_case_analysis.
 Variables (n p : nat)
           (H : n <= p)
           (Q : nat -> Prop)
           (H0 : Q n)
           (HS : forall m, n <= m -> Q (S m)).
 Check (
    match H in (_ <= q) return (Q q)  with
    | le_n _ => H0
    | le_S _ m Hm => HS m Hm
    end
  ).


End Le_case_analysis.


Lemma predecessor_of_positive : forall n, 1 <= n ->  exists p:nat, n = S p.
Proof.
 intros n  H; case H.
 exists 0; trivial.
 intros m Hm; exists m;trivial.
Qed.

Definition Vtail_total
   (A : Set) (n : nat) (v : Vector.t A n) : Vector.t A (pred n):=
match v in (Vector.t _ n0) return (Vector.t A (pred n0)) with
| Vector.nil _ => Vector.nil A
| Vector.cons _ _ n0 v0 => v0
end.

Definition Vtail' (A:Set)(n:nat)(v:Vector.t A n) : Vector.t A (pred n).
 case v.
 simpl.
 exact (Vector.nil A).
 simpl.
 auto.
Defined.

(*
Inductive Lambda : Set :=
  lambda : (Lambda -> False) -> Lambda.


Error: Non strictly positive occurrence of "Lambda" in
 "(Lambda -> False) -> Lambda"

*)

Section Paradox.
 Variable Lambda : Set.
 Variable lambda : (Lambda -> False) ->Lambda.

 Variable matchL  : Lambda -> forall Q:Prop, ((Lambda ->False) -> Q) -> Q.
 (*
  understand matchL Q l (fun h : Lambda -> False => t)

  as match l return Q with lambda h => t end
 *)

 Definition application (f x: Lambda) :False :=
   matchL f False (fun h => h x).

 Definition Delta : Lambda := lambda (fun x : Lambda => application x x).

 Definition loop : False := application Delta Delta.

 Theorem two_is_three : 2 = 3.
 Proof.
  elim loop.
 Qed.

End Paradox.


Require Import ZArith.



Inductive itree : Set :=
| ileaf : itree
| inode : Z-> (nat -> itree) -> itree.

Definition isingle l := inode l (fun i => ileaf).

Definition t1 := inode 0 (fun n => isingle (Z.of_nat (2*n))).

Definition t2 := inode 0
                      (fun n : nat =>
                               inode (Z.of_nat n)
                                     (fun p => isingle (Z.of_nat (n*p)))).


Inductive itree_le : itree-> itree -> Prop :=
  | le_leaf : forall t, itree_le  ileaf t
  | le_node  : forall l l' s s',
                       Z.le l l' ->
                      (forall i, exists j:nat, itree_le (s i) (s' j)) ->
                      itree_le  (inode  l s) (inode  l' s').


Theorem itree_le_trans :
  forall t t', itree_le t t' ->
               forall t'', itree_le t' t'' -> itree_le t t''.
 induction t.
 constructor 1.

 intros t'; case t'.
 inversion 1.
 intros z0 i0 H0.
 intro t'';case t''.
 inversion 1.
 intros.
 inversion_clear H1.
 constructor 2.
 inversion_clear H0;eauto with zarith.
 inversion_clear H0.
 intro i2; case (H4 i2).
 intros.
 generalize (H i2 _ H0).
 intros.
 case (H3 x);intros.
 generalize (H5 _ H6).
 exists x0;auto.
Qed.



Inductive itree_le' : itree-> itree -> Prop :=
  | le_leaf' : forall t, itree_le'  ileaf t
  | le_node' : forall l l' s s' g,
                       Z.le l l' ->
                      (forall i, itree_le' (s i) (s' (g i))) ->
                       itree_le'  (inode  l s) (inode  l' s').





Lemma t1_le_t2 : itree_le t1 t2.
 unfold t1, t2.
 constructor.
 auto with zarith.
 intro i; exists (2 * i).
 unfold isingle.
 constructor.
 auto with zarith.
 exists i;constructor.
Qed.



Lemma t1_le'_t2 :  itree_le' t1 t2.
 unfold t1, t2.
 constructor 2  with (fun i : nat => 2 * i).
 auto with zarith.
 unfold isingle;
 intro i ; constructor 2 with (fun i :nat => i).
 auto with zarith.
 constructor .
Qed.


Require Import List.

Inductive ltree  (A:Set) : Set :=
          lnode   : A -> list (ltree A) -> ltree A.

Inductive prop : Prop :=
 prop_intro : Prop -> prop.

Lemma prop_inject: prop.
Proof prop_intro prop.


Inductive ex_Prop  (P : Prop -> Prop) : Prop :=
  exP_intro : forall X : Prop, P X -> ex_Prop P.

Lemma ex_Prop_inhabitant : ex_Prop (fun P => P -> P).
Proof.
  exists (ex_Prop (fun P => P -> P)).
 trivial.
Qed.





Fail Check (fun (P:Prop->Prop)(p: ex_Prop P) =>
      match p with exP_intro X HX => X end).
(*
Error:
Incorrect elimination of "p" in the inductive type
"ex_Prop", the return type has sort "Type" while it should be
"Prop"

Elimination of an inductive object of sort "Prop"
is not allowed on a predicate in sort "Type"
because proofs can be eliminated only to build proofs
*)


Fail Check (match prop_inject with (prop_intro p) => p end).
(*
Error:
Incorrect elimination of "prop_inject" in the inductive type
"prop", the return type has sort "Type" while it should be
"Prop"

Elimination of an inductive object of sort "Prop"
is not allowed on a predicate in sort "Type"
because proofs can be eliminated only to build proofs
*)
Print prop_inject.

(*
prop_inject =
prop_inject = prop_intro prop
     : prop
*)


Inductive  typ : Type :=
  typ_intro : Type -> typ.

Definition typ_inject: typ.
split.
Fail exact typ.
(*
Error: Universe Inconsistency.
*)
Abort.

Fail Inductive aSet : Set :=
  aSet_intro: Set -> aSet.
(*
User error: Large non-propositional inductive types must be in Type
*)

Inductive ex_Set  (P : Set -> Prop) : Type :=
  exS_intro : forall X : Set, P X -> ex_Set P.


Module Type Version1.

Inductive comes_from_the_left (P Q:Prop): P \/ Q -> Prop :=
  c1 : forall p, comes_from_the_left P Q (or_introl (A:=P) Q p).

Goal (comes_from_the_left _ _ (or_introl True I)).
split.
Qed.

Goal ~(comes_from_the_left _ _ (or_intror True I)).
 red;inversion 1.
 (* discriminate H0.
 *)
Abort.

End Version1.

Fail Definition comes_from_the_left (P Q:Prop)(H:P \/ Q): Prop :=
  match H with
         |  or_introl p => True
         |  or_intror q => False
  end.

(*
Error:
Incorrect elimination of "H" in the inductive type
"or", the return type has sort "Type" while it should be
"Prop"

Elimination of an inductive object of sort "Prop"
is not allowed on a predicate in sort "Type"
because proofs can be eliminated only to build proofs
*)

Definition comes_from_the_left_sumbool
            (P Q:Prop)(x:{P}+{Q}): Prop :=
  match x with
         |  left  p => True
         |  right q => False
  end.




Close Scope Z_scope.





Theorem S_is_not_O : forall n, S n <> 0.

Set Nested Proofs Allowed.

Definition Is_zero (x:nat):= match x with
                                     | 0 => True
                                     | _ => False
                             end.
 Lemma O_is_zero : forall m, m = 0 -> Is_zero m.
 Proof.
  intros m H; subst m.
  (*
  ============================
   Is_zero 0
  *)
  simpl;trivial.
 Qed.

 red; intros n Hn.
 apply O_is_zero with (m := S n).
 assumption.
Qed.

Theorem disc2 : forall n, S (S n) <> 1.
Proof.
 intros n Hn; discriminate.
Qed.


Theorem disc3 : forall n, S (S n) = 0 -> forall Q:Prop, Q.
Proof.
  intros n Hn Q.
  discriminate.
Qed.



Theorem inj_succ  : forall n m, S n = S m -> n = m.
Proof.


Lemma inj_pred : forall n m, n = m -> pred n = pred m.
Proof.
 intros n m eq_n_m.
 rewrite eq_n_m.
 trivial.
Qed.

 intros n m eq_Sn_Sm.
 apply inj_pred with (n:= S n) (m := S m); assumption.
Qed.

Lemma list_inject : forall (A:Set)(a b :A)(l l':list A),
                     a :: b :: l = b :: a :: l' -> a = b /\ l = l'.
Proof.
 intros A a b l l' e.
 injection e.
 auto.
Qed.


Theorem not_le_Sn_0 : forall n:nat, ~ (S n <= 0).
Proof.
 red; intros n H.
 case H.
Undo.

Lemma not_le_Sn_0_with_constraints :
  forall n p , S n <= p ->  p = 0 -> False.
Proof.
 intros n p H; case H ;
   intros; discriminate.
Qed.

eapply not_le_Sn_0_with_constraints; eauto.
Qed.


Theorem not_le_Sn_0' : forall n:nat, ~ (S n <= 0).
Proof.
 red; intros n H ; inversion H.
Qed.

Derive Inversion le_Sn_0_inv with (forall n :nat, S n <=  0).
Check le_Sn_0_inv.

Theorem le_Sn_0'' : forall n p : nat, ~ S n <= 0 .
Proof.
 intros n p H;
 inversion H using le_Sn_0_inv.
Qed.

Derive Inversion_clear le_Sn_0_inv' with (forall n :nat, S n <=  0).
Check le_Sn_0_inv'.


Theorem le_reverse_rules :
 forall n m:nat, n <= m ->
                   n = m \/
                   exists p, n <=  p /\ m = S p.
Proof.
  intros n m H; inversion H.
  left;trivial.
  right; exists m0; split; trivial.
Restart.
  intros n m H; inversion_clear H.
  left;trivial.
  right; exists m0; split; trivial.
Qed.

Inductive ArithExp : Set :=
     Zero : ArithExp
   | Succ : ArithExp -> ArithExp
   | Plus : ArithExp -> ArithExp -> ArithExp.

Inductive RewriteRel : ArithExp -> ArithExp -> Prop :=
     RewSucc  : forall e1 e2 :ArithExp,
                  RewriteRel e1 e2 -> RewriteRel (Succ e1) (Succ e2)
  |  RewPlus0 : forall e:ArithExp,
                  RewriteRel (Plus Zero e) e
  |  RewPlusS : forall e1 e2:ArithExp,
                  RewriteRel e1 e2 ->
                  RewriteRel (Plus (Succ e1) e2) (Succ (Plus e1 e2)).



Fixpoint plus (n p:nat) {struct n} : nat :=
  match n with
          | 0 => p
          | S m => S (plus m p)
 end.

Fixpoint plus' (n p:nat) {struct p} : nat :=
    match p with
          | 0 => n
          | S q => S (plus' n q)
    end.

Fixpoint plus'' (n p:nat) {struct n} : nat :=
  match n with
          | 0 => p
          | S m => plus'' m (S p)
 end.

Module Type even_test_v1.

Fixpoint even_test (n:nat) : bool :=
  match n
  with 0 =>  true
     | 1 =>  false
     | S (S p) => even_test p
  end.

End even_test_v1.

Module even_test_v2.

Fixpoint even_test (n:nat) : bool :=
  match n
  with
      | 0 =>  true
      | S p => odd_test p
  end
with odd_test (n:nat) : bool :=
  match n
  with
     | 0 => false
     | S p => even_test p
 end.

Eval simpl in even_test.

Eval simpl in (fun x : nat => even_test x).

Eval simpl in (fun x : nat => plus 5 x).
Eval simpl in (fun x : nat => even_test (plus 5 x)).

Eval simpl in (fun x : nat => even_test (plus x 5)).

End even_test_v2.


Section Principle_of_Induction.
Variable    P               : nat -> Prop.
Hypothesis  base_case       : P 0.
Hypothesis  inductive_step   : forall n:nat, P n -> P (S n).
Fixpoint nat_ind  (n:nat)    : (P n) :=
   match n return P n with
          | 0 => base_case
          | S m => inductive_step m (nat_ind m)
   end.

End Principle_of_Induction.

Scheme Even_induction := Minimality for even Sort Prop
with   Odd_induction  := Minimality for odd  Sort Prop.

Theorem even_plus_four : forall n:nat, even n -> even (4+n).
Proof.
 intros n H.
 elim H using Even_induction with (P0 := fun n => odd (4+n));
 simpl;repeat constructor;assumption.
Qed.


Section Principle_of_Double_Induction.
Variable    P               : nat -> nat ->Prop.
Hypothesis  base_case1      : forall x:nat, P 0 x.
Hypothesis  base_case2      : forall x:nat, P (S x) 0.
Hypothesis  inductive_step   : forall n m:nat, P n m -> P (S n) (S m).
Fixpoint nat_double_ind (n m:nat){struct n} : P n m :=
  match n, m return P n m with
         |  0 ,     x    =>  base_case1 x
         |  (S x),    0  =>  base_case2 x
         |  (S x), (S y) =>  inductive_step x y (nat_double_ind x y)
     end.
End Principle_of_Double_Induction.

Section Principle_of_Double_Recursion.
Variable    P               : nat -> nat -> Set.
Hypothesis  base_case1      : forall x:nat, P 0 x.
Hypothesis  base_case2      : forall x:nat, P (S x) 0.
Hypothesis  inductive_step   : forall n m:nat, P n m -> P (S n) (S m).
Fixpoint nat_double_rec (n m:nat){struct n} : P n m :=
  match n, m return P n m with
         |   0 ,     x    =>  base_case1 x
         |  (S x),    0   => base_case2 x
         |  (S x), (S y)  => inductive_step x y (nat_double_rec x y)
     end.
End Principle_of_Double_Recursion.

Definition min : nat -> nat -> nat  :=
  nat_double_rec (fun (x y:nat) => nat)
                 (fun (x:nat) => 0)
                 (fun (y:nat) => 0)
                 (fun (x y r:nat) => S r).

Eval compute in (min 5 8).
Eval compute in (min 8 5).



Lemma not_circular : forall n:nat, n <> S n.
Proof.
 intro n.
 apply nat_ind with (P:= fun n => n <> S n).
 discriminate.
 red; intros n0 Hn0 eqn0Sn0;injection eqn0Sn0;auto.
Qed.

Definition eq_nat_dec : forall n p:nat , {n=p}+{n <> p}.
Proof.
 intros n p.
 apply nat_double_rec with (P:= fun (n q:nat) => {q=p}+{q <> p}).
Undo.
 pattern p,n.
 elim n using nat_double_rec.
 destruct x; auto.
 destruct x; auto.
 intros n0 m H; case H.
 intro eq; rewrite eq ; auto.
 intro neg; right; red ; injection 1; auto.
Defined.

Definition eq_nat_dec' : forall n p:nat, {n=p}+{n <> p}.
 decide equality.
Defined.

Print Acc.


Require Import Minus.

Fail Fixpoint div (x y:nat){struct x}: nat :=
 if eq_nat_dec x 0
  then 0
  else if eq_nat_dec y 0
       then x
       else S (div (x-y) y).
(*
Error:
Recursive definition of div is ill-formed.
In environment
div : nat -> nat -> nat
x : nat
y : nat
_ : x <> 0
_ : y <> 0

Recursive call to div has principal argument equal to
"x - y"
instead of a subterm of x

*)

Lemma minus_smaller_S: forall x y:nat, x - y < S x.
Proof.
 intros x y; pattern y, x;
 elim x using nat_double_ind.
 destruct x0; auto with arith.
 simpl; auto with arith.
 simpl; auto with arith.
Qed.

Lemma minus_smaller_positive : forall x y:nat, x <>0 -> y <> 0 ->
                                     x - y < x.
Proof.
 destruct x; destruct y;
 ( simpl;intros; apply minus_smaller_S ||
   intros; absurd (0=0); auto).
Qed.

Definition minus_decrease : forall x y:nat, Acc lt x ->
                                         x <> 0 ->
                                         y <> 0 ->
                                         Acc lt (x-y).
Proof.
 intros x y H; case H.
 intros Hz posz posy.
 apply Hz; apply minus_smaller_positive; assumption.
Defined.

Print minus_decrease.



Fixpoint div_aux (x y:nat)(H: Acc lt x):nat.
  refine (if eq_nat_dec x 0
         then 0
         else if eq_nat_dec y 0
              then y
              else div_aux (x-y) y _).
 apply (minus_decrease x y H);assumption.
Defined.


Print div_aux.
(*
div_aux =
(fix div_aux (x y : nat) (H : Acc lt x) {struct H} : nat :=
   match eq_nat_dec x 0 with
   | left _ => 0
   | right _ =>
       match eq_nat_dec y 0 with
       | left _ => y
       | right _0 => div_aux (x - y) y (minus_decrease x y H _ _0)
       end
   end)
     : forall x : nat, nat -> Acc lt x -> nat
*)

Require Import Wf_nat.
Definition div x y := div_aux x y (lt_wf x).

Extraction div.
(*
let div x y =
  div_aux x y
*)

Extraction div_aux.

(*
let rec div_aux x y =
  match eq_nat_dec x O with
    | Left -> O
    | Right ->
        (match eq_nat_dec y O with
           | Left -> y
           | Right -> div_aux (minus x y) y)
*)

Lemma vector0_is_vnil : forall (A:Set)(v:Vector.t A 0), v = Vector.nil A.
Proof.
 intros A v;inversion v.
Abort.


Fail Lemma vector0_is_vnil_aux : forall (A:Set)(n:nat)(v:Vector.t A n),
                                  n= 0 -> v = Vector.nil A.
(*
Error: In environment
A : Set
n : nat
v : Vector.t A n
The term "[]" has type "Vector.t A 0" while it is expected to have type
 "Vector.t A n"
*)
 Require Import JMeq.

Lemma vector0_is_vnil_aux : forall (A:Set)(n:nat)(v:Vector.t A n),
                                  n= 0 -> JMeq v (Vector.nil A).
Proof.
 destruct v.
 auto.
 intro; discriminate.
Qed.

Lemma vector0_is_vnil : forall (A:Set)(v:Vector.t A 0), v = Vector.nil A.
Proof.
 intros a v;apply JMeq_eq.
 apply vector0_is_vnil_aux.
 trivial.
Qed.


Arguments Vector.cons [A] _ [n].
Arguments Vector.nil [A].
Arguments Vector.hd [A n].
Arguments Vector.tl [A n].

Definition Vid : forall (A : Type)(n:nat), Vector.t A n -> Vector.t A n.
Proof.
 destruct n; intro v.
 exact Vector.nil.
 exact (Vector.cons  (Vector.hd v) (Vector.tl v)).
Defined.

Eval simpl in (fun (A:Set)(v:Vector.t A 0) => (Vid _ _ v)).

Eval simpl in (fun (A:Set)(v:Vector.t A 0) => v).



Lemma Vid_eq : forall (n:nat) (A:Type)(v:Vector.t A n), v=(Vid _ n v).
Proof.
 destruct v.
 reflexivity.
 reflexivity.
Defined.

Theorem zero_nil : forall A (v:Vector.t A 0), v = Vector.nil.
Proof.
 intros.
 change (Vector.nil (A:=A)) with (Vid _ 0 v).
 apply Vid_eq.
Defined.


Theorem decomp :
  forall (A : Set) (n : nat) (v : Vector.t A (S n)),
  v = Vector.cons (Vector.hd v) (Vector.tl v).
Proof.
 intros.
 change (Vector.cons (Vector.hd v) (Vector.tl v)) with (Vid _  (S n) v).
 apply Vid_eq.
Defined.



Definition vector_double_rect :
    forall (A:Set) (P: forall (n:nat),(Vector.t A n)->(Vector.t A n) -> Type),
        P 0 Vector.nil Vector.nil ->
        (forall n (v1 v2 : Vector.t A n) a b, P n v1 v2 ->
             P (S n) (Vector.cons a v1) (Vector.cons  b v2)) ->
        forall n (v1 v2 : Vector.t A n), P n v1 v2.
 induction n.
 intros; rewrite (zero_nil _ v1); rewrite (zero_nil _ v2).
 auto.
 intros v1 v2; rewrite (decomp _ _ v1);rewrite (decomp _ _ v2).
 apply X0; auto.
Defined.

Require Import Bool.

Definition bitwise_or n v1 v2 : Vector.t bool n :=
   vector_double_rect bool  (fun n v1 v2 => Vector.t bool n)
                        Vector.nil
                        (fun n v1 v2 a b r => Vector.cons (orb a b) r) n v1 v2.


Fixpoint vector_nth (A:Set)(n:nat)(p:nat)(v:Vector.t A p){struct v}
                  : option A :=
  match n,v  with
    _   , Vector.nil => None
  | 0   , Vector.cons b _ => Some b
  | S n', Vector.cons _ v' => vector_nth A n' _ v'
  end.

Arguments vector_nth [A] _ [p].


Lemma nth_bitwise : forall (n:nat) (v1 v2: Vector.t bool n) i  a b,
      vector_nth i v1 = Some a ->
      vector_nth i v2 = Some b ->
      vector_nth i (bitwise_or _ v1 v2) = Some (orb a b).
Proof.
 intros  n v1 v2; pattern n,v1,v2.
 apply vector_double_rect.
 simpl.
 destruct i; discriminate 1.
 destruct i; simpl;auto. 
 injection 1 as ->; injection 1 as ->; auto.
Qed.

 Set Implicit Arguments.

 CoInductive Stream (A:Set) : Set   :=
 |  Cons : A -> Stream A -> Stream A.

 CoInductive LList (A: Set) : Set :=
 |  LNil : LList A
 |  LCons : A -> LList A -> LList A.





 Definition head (A:Set)(s : Stream A) := match s with Cons a s' => a end.

 Definition tail (A : Set)(s : Stream A) :=
      match s with Cons a s' => s' end.

 CoFixpoint repeat (A:Set)(a:A) : Stream A := Cons a (repeat a).

 CoFixpoint iterate (A: Set)(f: A -> A)(a : A) : Stream A:=
    Cons a (iterate f (f a)).

 CoFixpoint map (A B:Set)(f: A -> B)(s : Stream A) : Stream B:=
  match s with Cons a tl => Cons (f a) (map f tl) end.

Eval simpl in (fun (A:Set)(a:A) => repeat a).

Eval simpl in (fun (A:Set)(a:A) => head (repeat a)).


CoInductive EqSt (A: Set) : Stream A -> Stream A -> Prop :=
  eqst : forall s1 s2: Stream A,
      head s1 = head s2 ->
      EqSt (tail s1) (tail s2) ->
      EqSt s1 s2.


Section Parks_Principle.
Variable A : Set.
Variable    R      : Stream A -> Stream A -> Prop.
Hypothesis  bisim1 : forall s1 s2:Stream A, R s1 s2 ->
                                          head s1 = head s2.
Hypothesis  bisim2 : forall s1 s2:Stream A, R s1 s2 ->
                                          R (tail s1) (tail s2).

CoFixpoint park_ppl     : forall s1 s2:Stream A, R s1 s2 ->
                                               EqSt s1 s2 :=
 fun s1 s2 (p : R s1 s2) =>
      eqst s1 s2 (bisim1  p)
                 (park_ppl  (bisim2  p)).
End Parks_Principle.


Theorem map_iterate : forall (A:Set)(f:A->A)(x:A),
                       EqSt (iterate f (f x)) (map f (iterate f x)).
Proof.
 intros A f x.
 apply park_ppl with
   (R:=  fun s1 s2 => exists x: A,
                      s1 = iterate f (f x) /\ s2 = map f (iterate f x)).

 intros s1 s2 (x0,(eqs1,eqs2));rewrite eqs1;rewrite eqs2;reflexivity.
 intros s1 s2 (x0,(eqs1,eqs2)).
 exists (f x0);split;[rewrite eqs1|rewrite eqs2]; reflexivity.
 exists x;split; reflexivity.
Qed.

Ltac infiniteproof f :=
  cofix f; constructor; [clear f| simpl; try (apply f; clear f)].


Theorem map_iterate' : forall (A:Set)(f:A->A)(x:A),
                       EqSt (iterate f (f x)) (map f (iterate f x)).
infiniteproof map_iterate'.
 reflexivity.
Qed.


Arguments LNil [A].

Lemma Lnil_not_Lcons : forall (A:Set)(a:A)(l:LList A),
                               LNil <> (LCons a l).
 intros;discriminate.
Qed.

Lemma injection_demo : forall (A:Set)(a b : A)(l l': LList A),
                       LCons a (LCons b l) = LCons b (LCons a l') ->
                       a = b /\ l = l'.
Proof.
 intros A a b l l' e; injection e; auto.
Qed.


Inductive Finite (A:Set) : LList A -> Prop :=
|  Lnil_fin : Finite (LNil (A:=A))
|  Lcons_fin : forall a l, Finite l -> Finite (LCons a l).

CoInductive Infinite  (A:Set) : LList A -> Prop :=
| LCons_inf : forall a l, Infinite l -> Infinite (LCons a l).

Lemma LNil_not_Infinite : forall (A:Set), ~ Infinite (LNil (A:=A)).
Proof.
  intros A H;inversion H.
Qed.

Lemma Finite_not_Infinite : forall (A:Set)(l:LList A),
                                Finite l -> ~ Infinite l.
Proof.
 intros A l H; elim H.
 apply LNil_not_Infinite.
 intros a l0 F0 I0' I1.
 case I0'; inversion_clear I1.
 trivial.
Qed.

Lemma Not_Finite_Infinite : forall (A:Set)(l:LList A),
                            ~ Finite l -> Infinite l.
Proof.
 cofix H.
 destruct l.
 intro; absurd (Finite (LNil (A:=A)));[auto|constructor].
 constructor.
 apply H.
 red; intro H1;case H0.
 constructor.
 trivial.
Qed.




