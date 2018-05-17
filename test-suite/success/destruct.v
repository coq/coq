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

(* Simplification of BZ#711 *)

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

(* Submitted by B. Baydemir (BZ#1882) *)

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
eexists ?[x].
Show x.  (* Incidentally test Show on a named goal *)
destruct (S _). (* Incompatible occurrences but takes the first one since Oct 2014 *)
change (0 = S 0).
Abort.

Goal exists x, S 0 = S x.
eexists ?[x].
destruct (S _). (* Incompatible occurrences but takes the first one since Oct 2014 *)
change (0 = S ?x).
[x]: exact 0. (* Incidentally test applying a tactic to a goal on the shelve *)
Abort.

Goal exists n p:nat, (S n,S n) = (S p,S p) /\ p = n.
eexists ?[n]; eexists ?[p].
destruct (_, S _). (* Was unifying at some time in trunk, now takes the first occurrence *)
change ((n, n0) = (S ?p, S ?p) /\ ?p = ?n).
Abort.

(* An example with incompatible but convertible occurrences *)

Goal id (id 0) = 0.
Fail destruct (id _) at 1 2.
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
Fail destruct (H _ _).
(* Now a test which assumes that edestruct on non-dependent
   hypotheses accept unresolved subterms in the induction argument.
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

Parameter g : forall {n:nat}, n=n -> nat.
Goal g (eq_refl 0) = 0.
destruct g.
Abort.

(* This one was working in 8.4 (because of full conv on closed arguments) *)

Class E.
Instance a:E.
Goal forall h : E -> nat -> nat, h (id a) 0 = h a 0.
intros.
destruct (h _).
change (0=0).
Abort.

(* This one was not working in 8.4 because an occurrence of f was
   remaining, blocking the "clear f" *)

Goal forall h : E -> nat -> nat, h a 0 = h a 1.
intros.
destruct h.
Abort.

(* This was not working in 8.4 *)

Section S1.
Variables x y : Type.
Variable H : x = y.
Goal True.
destruct H. (* Was not working in 8.4 *)
(* Now check that H statement has itself be subject of the rewriting *)
change (x=x) in H.
Abort.
End S1.

(* This was not working in 8.4 because of untracked dependencies *)
Goal forall y, forall h:forall x, x = y, h 0 = h 0.
intros.
destruct (h 0).
Abort.

(* Check absence of useless local definitions *)

Section S2.
Variable H : 1=1.
Goal 0=1.
destruct H.
Fail clear n. (* Check that there is no n as it was in Coq <= 8.4 *)
Abort.
End S2.

Goal forall x:nat, x=x->x=1.
intros x H.
destruct H.
Fail clear n. (* Check that there is no n as it was in Coq <= 8.4 *)
Fail clear H. (* Check that H has been removed *)
Abort.

(* Check support for induction arguments which do not expose an inductive
   type rightaway *)

Definition U := nat -> nat.
Definition S' := S : U.
Goal forall n, S' n = 0.
intro.
destruct S'.
Abort.

(* This was working by chance in 8.4 thanks to "accidental" use of select
   subterms _syntactically_ equal to the first matching one.

Parameter f2:bool -> unit.
Parameter r2:f2 true=f2 true.
Goal forall (P: forall b, b=b -> Prop), f2 (id true) = tt -> P (f2 true) r2.
intros.
destruct f2.
Abort.
*)

(* This did not work in 8.4, because of a clear failing *)

Inductive IND : forall x y:nat, x=y -> Type := CONSTR : IND 0 0 eq_refl.
Goal forall x y e (h:x=y -> y=x) (z:IND y x (h e)), e = e /\ z = z.
intros.
destruct z.
Abort.

(* The two following examples show how the variables occurring in the
   term being destruct affects the generalization; don't know if these
   behaviors are "good". None of them was working in 8.4. *)

Goal forall x y e (t:x=y) (z:x=y -> IND y x e), e = e.
intros.
destruct (z t).
change (0=0) in t. (* Generalization made *)
Abort.

Goal forall x y e (t:x=y) (z:x=y -> IND y x e), e = e /\ z t = z t.
intros.
destruct (z t).
change (0=0) in t. (* Generalization made *)
Abort.

(* Check that destruct on a scheme with a functional argument works *)

Goal (forall P:Prop, (nat->nat) -> P) -> forall h:nat->nat, h 0 = h 0.
intros.
destruct h using H.
Qed.

Goal (forall P:Prop, (nat->nat) -> P) -> forall h:nat->nat->nat, h 0 0 = h 1 0.
intros.
induction (h 1) using H.
Qed.

(* Check blocking generalization is not too strong (failed at some time) *)

Goal (E -> 0=1) -> 1=0 -> True.
intros.
destruct (H _).
change (0=0) in H0. (* Check generalization on H0 was made *)
Abort.

(* Check absence of anomaly (failed at some time) *)

Goal forall A (a:A) (P Q:A->Prop), (forall a, P a -> Q a) -> True.
intros.
Fail destruct H.
Abort.

(* Check keep option (BZ#3791) *)

Goal forall b:bool, True.
intro b.
destruct (b).
clear b. (* b has to be here *)
Abort.

(* Check clearing of names *)

Inductive IND2 : nat -> Prop := CONSTR2 : forall y, y = y -> IND2 y.
Goal forall x y z:nat, y = z -> x = y -> y = x -> x = y.
intros * Heq H Heq'.
destruct H.
Abort.

Goal 2=1 -> 1=0.
intro H. destruct H.
Fail (match goal with n:nat |- _ => unfold n end). (* Check that no let-in remains *)
Abort.

(* Check clearing of names *)

Inductive eqnat (x : nat) : nat -> Prop :=
  reflnat : forall y, x = y -> eqnat x y.

Goal forall x z:nat, x = z -> eqnat x z -> True.
intros * H1 H.
destruct H.
Fail clear z. (* Should not be here *)
Abort.

(* Check ok in the presence of an equation *)

Goal forall b:bool, b = b.
intros.
destruct b eqn:H.
Abort.

(* Check natural instantiation behavior when the goal has already an evar *)

Goal exists x, S x = x.
eexists ?[x].
destruct (S _).
change (0 = ?x).
Abort.

Goal (forall P, P 0 -> True/\True) -> True.
intro H.
destruct (H (fun x => True)).
match goal with |- True => idtac end.
Abort.
