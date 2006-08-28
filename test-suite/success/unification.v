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
