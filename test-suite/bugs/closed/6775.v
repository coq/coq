(* Issue caused and fixed during the lifetime of #6775: unification
   failing on partially applied cumulative inductives. *)

Set Universe Polymorphism.

Set Polymorphic Inductive Cumulativity.

Unset Elimination Schemes.

Inductive paths@{i} {A : Type@{i}} (a : A) : A -> Type@{i} :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.

Arguments inverse {A x y} p : simpl nomatch.

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.

Arguments concat {A x y z} p q : simpl nomatch.

Notation "1" := idpath.

Reserved Notation "p @ q" (at level 20).
Notation "p @ q" := (concat p q).

Reserved Notation "p ^" (at level 3, format "p '^'").
Notation "p ^" := (inverse p).

Definition concat_pV_p {A} {x y z : A} (p : x = z) (q : y = z) :
  (p @ q^) @ q = p
  :=
  (match q as i return forall p, (p @ i^) @ i = p with
    idpath =>
    fun p =>
      match p with idpath => 1 end
  end) p.
