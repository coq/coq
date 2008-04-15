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


(* Example submitted for Zenon *)

Axiom zenon_noteq : forall T : Type, forall t : T, ((t <> t) -> False).
Axiom zenon_notall : forall T : Type, forall P : T -> Prop,
  (forall z : T, (~(P z) -> False)) -> (~(forall x : T, (P x)) -> False).

  (* Must infer "P := fun x => x=x" in zenon_notall *)
Check (fun _h1 => (zenon_notall nat _ (fun _T_0 =>
          (fun _h2 => (zenon_noteq _ _T_0 _h2))) _h1)).


(* Core of an example submitted by Ralph Matthes (#849)

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

(* Test instanciation of evars by unification *)

Goal (forall x, 0 * x = 0 -> True) -> True.    
intros; eapply H.
rewrite <- plus_n_Sm. (* should refine ?x with S ?x' *)
Abort.

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
