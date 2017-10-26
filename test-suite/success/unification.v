Let test_stack_unification_interaction_with_delta A
  : (if negb _ then true else false) = if orb false (negb A) then true else false
  := eq_refl.

(* Test patterns unification *)

Lemma l1 : (forall P, (exists x:nat, P x) -> False)
         -> forall P, (exists x:nat, P x /\ P x) -> False.
Proof.
intros; apply (H _ H0).
Qed.

Lemma l2 :  forall A:Set, forall Q:A->Set,
           (forall (P: forall x:A, Q x -> Prop),
                   (exists x:A, exists y:Q x, P x y) -> False)
         -> forall (P: forall x:A, Q x -> Prop),
                   (exists x:A, exists y:Q x, P x y /\ P x y) -> False.
Proof.
intros; apply (H _ H0).
Qed.

Lemma l3 : (forall P, ~(exists x:nat, P x))
         -> forall P:nat->Prop, ~(exists x:nat, P x -> P x).
Proof.
intros; apply H.
Qed.

  (* Feature introduced June 2011 *)

Lemma l7 : forall x (P:nat->Prop), (forall f, P (f x)) -> P (x+x).
Proof.
intros x P H; apply H.
Qed.

(* Example submitted for Zenon *)

Axiom zenon_noteq : forall T : Type, forall t : T, ((t <> t) -> False).
Axiom zenon_notall : forall T : Type, forall P : T -> Prop,
  (forall z : T, (~(P z) -> False)) -> (~(forall x : T, (P x)) -> False).

  (* Must infer "P := fun x => x=x" in zenon_notall *)
Check (fun _h1 => (zenon_notall nat _ (fun _T_0 =>
          (fun _h2 => (zenon_noteq _ _T_0 _h2))) _h1)).


(* Core of an example submitted by Ralph Matthes (BZ#849)

   It used to fail because of the K-variable x in the type of "sum_rec ..."
   which was not in the scope of the evar ?B. Solved by a head
   beta-reduction of the type "(fun _ : unit + unit => L unit) x" of
   "sum_rec ...". Shall we used more reduction when solving evars (in
   real_clean)?? Is there a risk of starting too long reductions?

   Note that the example originally came from a non re-typable
   pretty-printed term (the checked term is actually re-printed the
   same form it is checked).
*)

Set Implicit Arguments.
Inductive L (A:Set) : Set := c : A -> L A.
Parameter f: forall (A:Set)(B:Set), (A->B) -> L A -> L B.
Parameter t: L (unit + unit).

Check (f (fun x : unit + unit =>
  sum_rec (fun _ : unit + unit => L unit)
    (fun y => c y) (fun y => c y) x) t).


(* Test patterns unification in apply *)

Require Import Arith.
Parameter x y : nat.
Parameter G:x=y->x=y->Prop.
Parameter K:x<>y->x<>y->Prop.
Lemma l4 : (forall f:x=y->Prop, forall g:x<>y->Prop,
            match eq_nat_dec x y with left a => f a | right a => g a end)
   -> match eq_nat_dec x y with left a => G a a | right a => K a a end.
Proof.
intros.
apply H.
Qed.


(* Test unification modulo eta-expansion (if possible) *)

(* In this example, two instances for ?P (argument of hypothesis H) can be
   inferred (one is by unifying the type [Q true] and [?P true] of the
   goal and type of [H]; the other is by unifying the argument of [f]);
   we need to unify both instances up to allowed eta-expansions of the
   instances (eta is allowed if the meta was applied to arguments)

   This used to fail before revision 9389 in trunk
*)

Lemma l5 :
   forall f : (forall P, P true), (forall P, f P = f P) ->
   forall Q, f (fun x => Q x) = f (fun x => Q x).
Proof.
intros.
apply H.
Qed.

(* Feature deactivated in commit 14189 (see commit log)
(* Test instantiation of evars by unification *)

Goal (forall x, 0 + x = 0 -> True) -> True.
intros; eapply H.
rewrite <- plus_n_Sm. (* should refine ?x with S ?x' *)
Abort.
*)

(* Check handling of identity equation between evars *)
(* The example failed to pass until revision 10623 *)

Lemma l6 :
  (forall y, (forall x, (forall z, y = 0 -> y + z = 0) -> y + x = 0) -> True)
  -> True.
intros.
eapply H.
intros.
apply H0. (* Check that equation ?n[H] = ?n[H] is correctly considered true *)
reflexivity.
Qed.

(* Check treatment of metas erased by K-redexes at the time of turning
   them to evas *)

Inductive nonemptyT (t : Type) : Prop := nonemptyT_intro : t -> nonemptyT t.
Goal True.
try case nonemptyT_intro. (* check that it fails w/o anomaly *)
Abort.

(* Test handling of return type and when it is decided to make the
   predicate dependent or not - see "bug" BZ#1851 *)

Goal forall X (a:X) (f':nat -> X), (exists f : nat -> X, True).
intros.
exists (fun n => match n with O => a | S n' => f' n' end).
constructor.
Qed.

(* Check use of types in unification (see Andrej Bauer's mail on
   coq-club, June 1 2009; it did not work in 8.2, probably started to
   work after Sozeau improved support for the use of types in unification) *)

Goal (forall (A B : Set) (f : A -> B), (fun x => f x) = f) ->
 forall (A B C : Set) (g : (A -> B) -> C) (f : A -> B), g (fun x => f x) = g f.
Proof.
  intros.
  rewrite H with (f:=f0).
Abort.

(* Three tests provided by Dan Grayson as part of a custom patch he
   made for a more powerful "destruct" for handling Voevodsky's
   Univalent Foundations. The test checks if second-order matching in
   tactic unification is able to guess by itself on which dependent
   terms to abstract so that the elimination predicate is well-typed *)

Definition test1 (X : Type) (x : X) (fxe : forall x1 : X, identity x1 x1) :
  identity (fxe x) (fxe x).
Proof. destruct (fxe x). apply identity_refl. Defined.

(* a harder example *)

Definition UU := Type .
Inductive paths {T:Type}(t:T): T -> UU := idpath: paths t t.
Inductive foo (X0:UU) (x0:X0) : forall (X:UU)(x:X), UU := newfoo : foo x0 x0.
Definition idonfoo {X0:UU} {x0:X0} {X1:UU} {x1:X1} : foo x0 x1 -> foo x0 x1.
Proof. intros t. exact t. Defined.

Lemma test2 (T:UU) (t:T) (k : foo t t) : paths k (idonfoo k).
Proof.
  destruct k.
  apply idpath.
Defined.

(* an example with two constructors *)

Inductive foo' (X0:UU) (x0:X0) : forall (X:UU)(x:X), UU :=
| newfoo1 : foo' x0 x0
| newfoo2 : foo' x0 x0 .
Definition idonfoo' {X0:UU} {x0:X0} {X1:UU} {x1:X1} :
  foo' x0 x1 -> foo' x0 x1.
Proof. intros t. exact t. Defined.
Lemma test3 (T:UU) (t:T) (k : foo' t t) : paths k (idonfoo' k).
Proof.
  destruct k.
  apply idpath.
  apply idpath.
Defined.

(* An example where it is necessary to evar-normalize the instance of
   an evar to evaluate if it is a pattern *)

Check
  let a := ?[P] in
  fun (H : forall y (P : nat -> Prop), y = 0 -> P y)
      x (p:x=0) =>
    H ?[y] a p : x = 0.
(* We have to solve "?P ?y[x] == x = 0" knowing from
   "p : (x=0) == (?y[x] = 0)" that "?y := x" *)
