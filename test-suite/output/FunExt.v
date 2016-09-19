Require Import FunctionalExtensionality.

(* Basic example *)
Goal (forall x y z, x+y+z = z+y+x) -> (fun x y z => z+y+x) = (fun x y z => x+y+z).
intro H.
extensionality in H.
symmetry in H.
assumption.
Qed.

(* Test rejection of non-equality *)
Goal forall H:(forall A:Prop, A), H=H -> forall H'':True, H''=H''.
intros H H' H''.
Fail extensionality in H.
clear H'.
Fail extensionality in H.
Fail extensionality in H''.
Abort.

(* Test success on dependent equality *)
Goal forall (p : forall x, S x = x + 1), p = p -> S = fun x => x + 1.
intros p H.
extensionality in p.
assumption.
Qed.

(* Test dependent functional extensionality *)
Goal forall (P:nat->Type) (Q:forall a, P a -> Type) (f g:forall a (b:P a), Q a b),
   (forall x y, f x y = g x y) -> f = g.
intros * H.
extensionality in H.
assumption.
Qed.

(* Other tests, courtesy of Jason Gross *)

Goal forall A B C (D : forall a : A, C a -> Type) (f g : forall a : A, B -> forall c : C a, D a c), (forall a b c, f a b c = g a b c) -> f = g.
Proof.
  intros A B C D f g H.
  extensionality in H.
  match type of H with f = g => idtac end.
  exact H.
Qed.

Section test_section.
  Context A B C (D : forall a : A, C a -> Type) (f g : forall a : A, B -> forall c : C a, D a c)
          (H : forall a b c, f a b c = g a b c).
  Goal f = g.
  Proof.
    extensionality in H.
    match type of H with f = g => idtac end.
    exact H.
  Qed.
End test_section.

Section test2.
  Context A B C (D : forall a : A, C a -> Type) (f g : forall a : A, B -> forall c : C a, D a c)
          (H : forall b a c, f a b c = g a b c).
  Goal (fun b a c => f a b c) = (fun b a c => g a b c).
  Proof.
    extensionality in H.
    match type of H with (fun b a => f a b) = (fun b' a' => g a' b') => idtac end.
    exact H.
  Qed.
End test2.

Section test3.
  Context A B C (D : forall a : A, C a -> Type) (f g : forall a : A, B -> forall c : C a, D a c)
          (H : forall a c, (fun b => f a b c) = (fun b => g a b c)).
  Goal (fun a c b => f a b c) = (fun a c b => g a b c).
  Proof.
    extensionality in H.
    match type of H with (fun a c b => f a b c) = (fun a' c' b' => g a' b' c') => idtac end.
    exact H.
  Qed.
End test3.

Section test4.
  Context A B C (D : forall a : A, C a -> Type) (f g : forall a : A, B -> forall c : C a, D a c -> Type)
          (H : forall b, (forall a c d, f a b c d) = (forall a c d, g a b c d)).
  Goal (fun b => forall a c d, f a b c d) = (fun b => forall a c d, g a b c d).
  Proof.
    extensionality in H.
    exact H.
  Qed.
End test4.

Section test5.
  Goal nat -> True.
  Proof.
    intro n.
    Fail extensionality in n.
    constructor.
  Qed.
End test5.

Section test6.
  Goal let f := fun A (x : A) => x in let pf := fun A x => @eq_refl _ (f A x) in f = f.
  Proof.
    intros f pf.
    extensionality in pf.
    match type of pf with f = f => idtac end.
    exact pf.
  Qed.
End test6.

Section test7.
  Context A B C (D : forall a : A, C a -> Type) (f g : forall a : A, B -> forall c : C a, D a c)
          (H : forall a b c, True -> f a b c = g a b c).
  Goal True.
  Proof.
    extensionality in H.
    match type of H with (fun a b c (_ : True) => f a b c) = (fun a' b' c' (_ : True) => g a' b' c') => idtac end.
    constructor.
  Qed.
End test7.

Section test8.
  Context A B C (D : forall a : A, C a -> Type) (f g : forall a : A, B -> forall c : C a, D a c)
          (H : True -> forall a b c, f a b c = g a b c).
  Goal True.
  Proof.
    extensionality in H.
    match type of H with (fun (_ : True) => f) = (fun (_ : True) => g) => idtac end.
    constructor.
  Qed.
End test8.

Section test9.
  Context A B C (D : forall a : A, C a -> Type) (f g : forall a : A, B -> forall c : C a, D a c)
          (H : forall b a c, f a b c = g a b c).
  Goal (fun b a c => f a b c) = (fun b a c => g a b c).
  Proof.
    pose H as H'.
    extensionality in H.
    extensionality in H'.
    let T := type of H in let T' := type of H' in constr_eq T T'.
    match type of H with (fun b a => f a b) = (fun b' a' => g a' b') => idtac end.
    exact H'.
  Qed.
End test9.

Section test10.
  Context A B C (D : forall a : A, C a -> Type) (f g : forall a : A, B -> forall c : C a, D a c)
          (H : f = g).
  Goal True.
  Proof.
    Fail extensionality in H.
    constructor.
  Qed.
End test10.

Section test11.
  Context A B C (D : forall a : A, C a -> Type) (f g : forall a : A, B -> forall c : C a, D a c)
          (H : forall a b c, f a b c = f a b c).
  Goal True.
  Proof.
    pose H as H'.
    pose (eq_refl : H = H') as e.
    extensionality in H.
    Fail extensionality in H'.
    clear e.
    extensionality in H'.
    let T := type of H in let T' := type of H' in constr_eq T T'.
    lazymatch type of H with f = f => idtac end.
    constructor.
  Qed.
End test11.
