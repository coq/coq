Require Import TestSuite.admit.
(* -*- mode: coq; coq-prog-args: ("-indices-matter") -*- *)
Set Universe Polymorphism.

Inductive Empty : Prop := .

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Arguments idpath {A a} , [A] a.

Definition idmap {A : Type} : A -> A := fun x => x.

Definition path_sum {A B : Type} (z z' : A + B)
           (pq : match z, z' with
                   | inl z0, inl z'0 => z0 = z'0
                   | inr z0, inr z'0 => z0 = z'0
                   | _, _ => Empty
                 end)
: z = z'.

  admit.
Defined.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

Theorem ex2_8 {A B A' B' : Type} (g : A -> A') (h : B -> B') (x y : A + B)

        (pq : match (x, y) with (inl x', inl y') => x' = y' | (inr x', inr y') => x' = y' | _ => Empty end) :
  let f z := match z with inl z' => inl (g z') | inr z' => inr (h z') end in
  ap f (path_sum x y pq) = path_sum (f x) (f y)
                                    ((match x as x return match (x, y) with
                                                              (inl x', inl y') => x' = y'
                                                            | (inr x', inr y') => x' = y'
                                                            | _ => Empty
                                                          end -> match (f x, f y) with
                                                                   | (inl x', inl y') => x' = y'
                                                                   | (inr x', inr y') => x' = y'
                                                                   | _ => Empty end with
                                        | inl x' => match y with
                                                      | inl y' => ap g
                                                      | inr y' => idmap
                                                    end
                                        | inr x' => match y with
                                                      | inl y' => idmap
                                                      | inr y' => ap h
                                                    end
                                      end) pq).

Admitted.
(* Toplevel input, characters 20-29:
Error: Matching on term "f y" of type "A' + B'" expects 2 branches. *)
