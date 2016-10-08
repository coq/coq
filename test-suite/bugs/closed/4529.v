(* File reduced by coq-bug-finder from original input, then from 1334 lines to 1518 lines, then from 849 lines to 59 lines *)
(* coqc version 8.5 (January 2016) compiled on Jan 22 2016 18:20:47 with OCaml 4.02.3
   coqtop version r-schnelltop:/home/r/src/coq/coq,(HEAD detached at V8.5) (5e23fb90b39dfa014ae5c4fb46eb713cca09dbff) *)
Require Coq.Setoids.Setoid.
Import Coq.Setoids.Setoid.

Class Equiv A := equiv: relation A.
Infix "≡" := equiv (at level 70, no associativity).
Notation "(≡)" := equiv (only parsing).

(* If I remove this line, everything compiles. *)
Set Primitive Projections.

Class Dist A := dist : nat -> relation A.
Notation "x ={ n }= y" := (dist n x y)
  (at level 70, n at next level, format "x  ={ n }=  y").

Record CofeMixin A `{Equiv A, Dist A} := {
  mixin_equiv_dist x y : x ≡ y <-> forall n, x ={n}= y;
  mixin_dist_equivalence n : Equivalence (dist n);
}.

Structure cofeT := CofeT {
  cofe_car :> Type;
  cofe_equiv : Equiv cofe_car;
  cofe_dist : Dist cofe_car;
  cofe_mixin : CofeMixin cofe_car
}.
Existing Instances cofe_equiv cofe_dist.
Arguments cofe_car : simpl never.

Section cofe_mixin.
  Context {A : cofeT}.
  Implicit Types x y : A.
  Lemma equiv_dist x y : x ≡ y <-> forall n, x ={n}= y.
Admitted.
End cofe_mixin.
  Context {A : cofeT}.
  Global Instance cofe_equivalence : Equivalence ((≡) : relation A).
  Proof.
    split.
    *
 intros x.
apply equiv_dist.

