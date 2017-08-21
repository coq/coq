Unset Strict Universe Declaration.
(* File reduced by coq-bug-finder from original input, then from 11542 lines to 325 lines, then from 347 lines to 56 lines, then from 58 lines to 15 lines *)
(* coqc version trunk (September 2014) compiled on Sep 25 2014 2:53:46 with OCaml 4.01.0
   coqtop version cagnode16:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (bec7e0914f4a7144cd4efa8ffaccc9f72dbdb790) *)

Axiom transport : forall {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x), P y.
Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).
Inductive V : Type@{U'} := | set {A : Type@{U}} (f : A -> V) : V.
Module NonPrim.
  Record hProp := hp { hproptype :> Type ; isp : Set}.
  Goal forall (A B : Type) (H_f : A -> V -> hProp) (H_g : B -> V -> hProp)
              (C : Type) (h : C -> V) (b : B) (a : A) (c : C),
         H_f a (h c) -> H_f a (h c) = H_g b (h c) -> H_g b (h c).
    intros A B H_f H_g C h b a c H3 H'.
    exact (@transport hProp (fun x => x) _ _ H' H3).
    Undo.
    Set Debug Unification.
    exact (H' # H3).
  Defined.
End NonPrim.

Module Prim.
  Set Primitive Projections.
  Set Universe Polymorphism.
  Record hProp := hp { hproptype :> Type ; isp : Set}.
  Goal forall (A B : Type) (H_f : A -> V -> hProp) (H_g : B -> V -> hProp)
              (C : Type) (h : C -> V) (b : B) (a : A) (c : C),
         H_f a (h c) -> H_f a (h c) = H_g b (h c) -> H_g b (h c).
    intros A B H_f H_g C h b a c H3 H'.
    exact (@transport hProp (fun x => x) _ _ H' H3).
    Undo.
    Set Debug Unification.
    exact (H' # H3).
    (* Toplevel input, characters 7-14:
Error:
In environment
A : Type
B : Type
H_f : A -> V -> hProp
H_g : B -> V -> hProp
C : Type
h : C -> V
b : B
a : A
c : C
H3 : H_f a (h c)
H' : H_f a (h c) = H_g b (h c)
Unable to unify "hproptype (H_f a (h c))" with "?T (H_f a (h c))".
 *)
  Defined.
End Prim.
