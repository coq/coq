Require Export Morphisms Setoid.

Class lops := lmk_ops {
  car: Type;
  weq: relation car
}.

Arguments car : clear implicits.

Coercion car: lops >-> Sortclass.

Instance weq_Equivalence `{lops}: Equivalence weq.
Proof.
Admitted.

Module lset.
Canonical Structure lset_ops A := lmk_ops (list A) (fun h k => True).
End lset.

Class ops := mk_ops {
  ob: Type;
  mor: ob -> ob -> lops;
  dot: forall n m p, mor n m -> mor m p -> mor n p
}.
Coercion mor: ops >-> Funclass.
Arguments ob : clear implicits.

Instance dot_weq `{ops} n m p: Proper (weq ==> weq ==> weq) (dot n m p).
Proof.
Admitted.

Section s.

Import lset.

Context `{X:lops} {I: Type}.

Axiom sup : forall (f: I -> X) (J : list I), X.

Global Instance sup_weq: Proper (pointwise_relation _ weq ==> weq ==> weq) sup.
Proof.
Admitted.

End s.

Axiom ord : forall (n : nat), Type.
Axiom seq : forall n, list (ord n).

Infix "=="   := weq (at level 79).
Infix "*" := (dot _ _ _)      (left associativity, at level 40).

Notation "∑_ ( i ∈ l ) f" := (@sup (mor _ _) _ (fun i => f) l)
  (at level 41, f at level 41, i, l at level 50).

Axiom dotxsum : forall `{X : ops} I J n m p (f: I -> X m n) (x: X p m) y,
  x * (∑_(i∈ J) f i) == y.

Definition mx X n m := ord n -> ord m -> X.

Section bsl.
Context `{X : ops} {u: ob X}.
Notation U := (car (@mor X u u)).

Lemma toto n m p q (M : mx U n m) N (P : mx U p q) Q i j : ∑_(j0 ∈ seq m) M i j0 * (∑_(j1 ∈ seq p) N j0 j1 * P j1 j) == Q.
Proof.
  Fail setoid_rewrite dotxsum.
  (* Toplevel input, characters 0-22:
Error:
Tactic failure:setoid rewrite failed: Unable to satisfy the rewriting constraints.
Unable to satisfy the following constraints:
UNDEFINED EVARS:
 ?101==[X u n m p q M N P Q i j j0 |- U] (goal evar)
 ?106==[X u n m p q M N P Q i j |- relation (X u u)] (internal placeholder)
 ?107==[X u n m p q M N P Q i j |- relation (list (ord m))]
         (internal placeholder)
 ?108==[X u n m p q M N P Q i j (do_subrelation:=do_subrelation)
         |- Proper (pointwise_relation (ord m) weq ==> ?107 ==> ?106) sup]
         (internal placeholder)
 ?109==[X u n m p q M N P Q i j |- ProperProxy ?107 (seq m)]
         (internal placeholder)
 ?110==[X u n m p q M N P Q i j |- relation (X u u)] (internal placeholder)
 ?111==[X u n m p q M N P Q i j (do_subrelation:=do_subrelation)
         |- Proper (?106 ==> ?110 ==> Basics.flip Basics.impl) weq]
         (internal placeholder)
 ?112==[X u n m p q M N P Q i j |- ProperProxy ?110 Q] (internal placeholder)UNIVERSES:
 {} |= Top.14 <= Top.37
        Top.25 <= Top.24
        Top.25 <= Top.32

ALGEBRAIC UNIVERSES:{}
UNDEFINED UNIVERSES:METAS:
 470[y] := ?101 : car (?99 ?467 ?465)
 469[x] := M i _UNBOUND_REL_1 : car (?99 ?467 ?466)  [type is checked]
 468[f] := fun i : ?463 => N _UNBOUND_REL_2 i * P i j :
 ?463 -> ?99 ?466 ?465  [type is checked]
 467[p] := u : ob ?99  [type is checked]
 466[m] := u : ob ?99  [type is checked]
 465[n] := u : ob ?99  [type is checked]
 464[J] := seq p : list ?463  [type is checked]
 463[I] := ord p : Type  [type is checked]
 *)
Abort.

End bsl.
