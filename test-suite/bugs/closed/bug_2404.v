(* Check that dependencies in the indices of the type of the terms to
   match are taken into account and correctly generalized *)

Require Import Relations.Relation_Definitions.
Require Import Basics.

Record Base := mkBase
 {(* Primitives *)
    World : Set
  (* Names are real, links are theoretical *)
  ; Name : World -> Set

  ; wweak : World -> World -> Prop

  ; exportw : forall a b : World, (wweak a b) -> (Name b) -> option (Name a)
}.

Section Derived.
  Variable base : Base.
  Definition bWorld := World base.
  Definition bName  := Name base.
  Definition bexportw := exportw base.
  Definition bwweak := wweak base.

  Arguments bexportw [a b].

Inductive RstarSetProof {I : Type} (T : I -> I -> Type) : I -> I -> Type :=
  starReflS : forall a, RstarSetProof T a a
| starTransS : forall i j k, T i j -> (RstarSetProof T j k) -> RstarSetProof T i k.

Arguments starTransS [I T i j k].

Definition RstarInv {A : Set} (rel : relation A) : A -> A -> Type :=  (flip (RstarSetProof (flip rel))).

Definition bwweakFlip (b a : bWorld) : Prop := (bwweak a b).
Definition Rweak : forall a b : bWorld, Type := RstarInv bwweak.

Fixpoint exportRweak {a b} (aRWb : Rweak a b) (y : bName b) : option (bName a) :=
  match aRWb,y with
  | starReflS _ a, y' => Some y'
  | starTransS jWk jRWi, y' =>
    match (bexportw jWk y) with
    | Some x => exportRweak jRWi x
    | None   => None
    end
  end.
