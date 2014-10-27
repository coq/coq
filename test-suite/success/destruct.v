(* Submitted by Robert Schneck *)

Parameters A B C D : Prop.
Axiom X : A -> B -> C /\ D.

Lemma foo : A -> B -> C.
Proof.
intros.
destruct X. (* Should find axiom X and should handle arguments of X *)
assumption.
assumption.
assumption.
Qed.

(* Simplification of bug 711 *)

Parameter f : true = false.
Goal let p := f in True.
intro p.
set (b := true) in *.
(* Check that it doesn't fail with an anomaly *)
(* Ultimately, adapt destruct to make it succeeding *)
try destruct b.
Abort.

(* Used to fail with error "n is used in conclusion" before revision 9447 *)

Goal forall n, n = S n.
induction S.
Abort.

(* Check that elimination with remaining evars do not raise an bad
   error message *)

Theorem Refl : forall P, P <-> P. tauto. Qed.
Goal True.
case Refl || ecase Refl.
Abort.


(* Submitted by B. Baydemir (bug #1882) *)

Require Import List.

Definition alist R := list (nat * R)%type.

Section Properties.
  Variable A : Type.
  Variable a : A.
  Variable E : alist A.

  Lemma silly : E = E.
  Proof.
    clear. induction E.  (* this fails. *)
  Abort.

End Properties.

(* This used not to work before revision 11944 *)

Goal forall P:(forall n, 0=n -> Prop), forall H: 0=0, P 0 H.
destruct H.
Abort.

(* The calls to "destruct" below did not work before revision 12356 *)

Variable A0:Type.
Variable P:A0->Type.
Require Import JMeq.
Goal forall a b (p:P a) (q:P b),
  forall H:a = b, eq_rect a P p b H = q -> JMeq (existT _ a p) (existT _ b q).
intros.
destruct H.
destruct H0.
reflexivity.
Qed.

(* These did not work before 8.4 *)

Goal (exists x, x=0) -> True.
destruct 1 as (_,_); exact I.
Abort.

Goal (exists x, x=0 /\ True) -> True.
destruct 1 as (_,(_,H)); exact H.
Abort.

Goal (exists x, x=0 /\ True) -> True.
destruct 1 as (_,(_,x)); exact x.
Abort.

Goal let T:=nat in forall (x:nat) (g:T -> nat), g x = 0.
intros.
destruct (g _). (* This was failing in at least r14571 *)
Abort.

(* Check that subterm selection does not solve existing evars *)

Goal exists x, S x = S 0.
eexists.
destruct (S _). (* Incompatible occurrences but takes the first one since Oct 2014 *)
change (0 = S 0).
Abort.

Goal exists x, S 0 = S x.
eexists.
destruct (S _). (* Incompatible occurrences but takes the first one since Oct 2014 *)
change (0 = S ?x).
Abort.

Goal exists n p:nat, (S n,S n) = (S p,S p) /\ p = n.
do 2 eexists.
destruct (_, S _). (* Was unifying at some time in trunk, now takes the first occurrence *)
change ((n, n0) = (S ?p, S ?p) /\ ?p = ?n0).
Abort.

(* Avoid unnatural selection of a subterm larger than expected *)

Goal let g := fun x:nat => x in g (S 0) = 0.
intro.
destruct S.
(* Check that it is not the larger subterm "g (S 0)" which is
   selected, as it was the case in 8.4 *)
unfold g at 1.
Abort.

(* Some tricky examples convenient to support *)

Goal forall x, nat_rect (fun _ => nat) O (fun x y => S x) x = nat_rect (fun _ => nat) O (fun x y => S x) x.
intros.
destruct (nat_rect _ _ _ _).
Abort.
(* Check compatibility in selecting what is open or "shelved" *)

Goal (forall x, x=0 -> nat) -> True.
intros.
Fail destruct H.
edestruct H.
- reflexivity.
- exact Logic.I.
- exact Logic.I.
Qed.

(* Check an example which was working with case/elim in 8.4 but not with
   destruct/induction *)

Goal forall x, (True -> x = 0) -> 0=0. 
intros.
destruct H.
- trivial.
- apply (eq_refl x).
Qed.

(* Check an example which was working with case/elim in 8.4 but not with
   destruct/induction (not the different order between induction/destruct) *)

Goal forall x, (True -> x = 0) -> 0=0. 
intros.
induction H.
- apply (eq_refl x).
- trivial.
Qed.

(* This test assumes that destruct/induction on non-dependent hypotheses behave the same
   when using holes or not

Goal forall x, (True -> x = 0) -> 0=0. 
intros.
destruct (H _).
- apply I.
- apply (eq_refl x).
Qed.
*)

(* Check destruct vs edestruct *)

Goal forall x, (forall y, y = 0 -> x = 0) -> 0=0.
intros.
Fail destruct H.
edestruct H.
- trivial.
- apply (eq_refl x).
Qed.

Goal forall x, (forall y, y = 0 -> x = 0) -> 0=0.
intros.
Fail destruct (H _).
edestruct (H _).
- trivial.
- apply (eq_refl x).
Qed.

Goal forall x, (forall y, y = 0 -> x = 0) -> 0=0.
intros.
Fail destruct (H _ _).
(* Now a test which assumes that destruct/induction on non-dependent hypotheses behave the same
   when using holes or not
edestruct (H _ _).
- trivial.
- apply (eq_refl x).
Qed.
*)
Abort.

(* Test selection when not in an inductive type *)
Parameter T:Type.
Axiom elim: forall P, T -> P.
Goal forall a:T, a = a.
induction a using elim.
Qed.

Goal forall a:nat -> T, a 0 = a 1.
intro a.
induction (a 0) using elim.
Qed.

(* From Oct 2014, a subterm is found, as if without "using"; in 8.4,
   it did not find a subterm *)

Goal forall a:nat -> T, a 0 = a 1.
intro a.
induction a using elim.
Qed.

Goal forall a:nat -> T, forall b, a 0 = b.
intros a b.
induction a using elim.
Qed.

(* From Oct 2014, first subterm is found; in 8.4, it failed because it
   found "a 0" and wanted to clear a *)

Goal forall a:nat -> nat, a 0 = a 1.
intro a.
destruct a.
change (0 = a 1).
Abort.

(* This example of a variable not fully applied in the goal was working in 8.4*)

Goal forall H : 0<>0, H = H.
destruct H.
reflexivity.
Qed.

(* Check that variables not fully applied in the goal are not erased
   (this example was failing in 8.4 because of a forbidden "clear H" in
   the code of "destruct H" *)

Goal forall H : True -> True, H = H.
destruct H.
- exact I.
- reflexivity.
Qed.

(* Check destruct on idents with maximal implicit arguments - which did
   not work in 8.4 *)

Parameter f : forall {n:nat}, n=n -> nat.
Goal f (eq_refl 0) = 0.
destruct f.
Abort.

(* This one was working in 8.4 (because of full conv on closed arguments) *)

Class A.
Instance a:A.
Goal forall f : A -> nat -> nat, f (id a) 0 = f a 0.
intros.
destruct (f _).
change (0=0).
Abort.

(* This one was not working in 8.4 because an occurrence of f was
   remaining, blocking the "clear f" *)

Goal forall f : A -> nat -> nat, f a 0 = f a 1.
intros.
destruct f.
