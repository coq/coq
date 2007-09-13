Require Export NAxioms.

Module StrongRecProperties (Import NBaseMod : NBaseSig).
Module Export NBasePropMod := NBasePropFunct NBaseMod.
Open Local Scope NatScope.

Section StrongRecursion.

Variable A : Set.
Variable EA : relation A.

Hypothesis EA_equiv : equiv A EA.

Definition strong_rec (a : A) (f : N -> (N -> A) -> A) (x : N) : A :=
(recursion (fun _ : N => a)
           (fun (x : N) (p : N -> A) (y : N) => if (e y x) then (f x p) else (p y))
           (S x)) x.

Lemma strong_rec_step_wd : forall f : N -> (N -> A) -> A,
fun2_wd E (eq_fun E EA) EA f ->
  fun2_wd E (eq_fun E EA) (eq_fun E EA)
    (fun (x : N) (p : N -> A) (y : N) => if (e y x) then (f x p) else (p y)).
Proof.
unfold fun2_wd; intros f f_wd.
intros x x' Exx'. unfold eq_fun. intros g g' Egg' y y' Eyy'.
assert (H : e y x = e y' x'). now apply e_wd. rewrite H.
destruct (e y' x'); simpl.
now apply f_wd. now apply Egg'.
Qed.

Theorem strong_rec_wd :
forall a a', EA a a' ->
  forall f f', eq_fun2 E (eq_fun E EA) EA f f' ->
    forall x x', x == x' ->
      EA (strong_rec a f x) (strong_rec a' f' x').
Proof.
intros a a' Eaa' f f' Eff' x x' Exx'.
assert (H : eq_fun E EA
  (recursion (fun _ : N => a)
           (fun (x : N) (p : N -> A) (y : N) => if (e y x) then (f x p) else (p y))
           (S x))
  (recursion (fun _ : N => a')
           (fun (x : N) (p : N -> A) (y : N) => if (e y x) then (f' x p) else (p y))
           (S x'))).
apply recursion_wd with (EA := eq_fun E EA).
unfold eq_fun; now intros.
unfold eq_fun2. intros y y' Eyy' p p' Epp'. unfold eq_fun. intros z z' Ezz'.
assert (H: e z y = e z' y'); [now apply e_wd|].
rewrite <- H. destruct (e z y); [now apply Eff' | now apply Epp'].
now rewrite Exx'.
unfold strong_rec.
now apply H.
Qed.

(* To do:
Definition step_good (g : N -> (N -> A) -> A) :=
  forall (x : N) (h1 h2 : N -> A),
    (forall y : N, y < x -> EA (h1 y) (h2 y)) -> EA (g x h1) (g x h2).

Theorem strong_recursion_fixpoint : forall a g, step_good g ->
  let f x := (strong_rec a g x) in forall x, EA (f x) (g x f).
*)

End StrongRecursion.

Implicit Arguments strong_rec [A].

End StrongRecProperties.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
