Set Universe Polymorphism.
Set Primitive Projections.
Unset Printing Primitive Projection Compatibility.
Axiom Ω : Type.

Record Pack (A : Ω -> Type) (Aᴿ : Ω -> (forall ω : Ω, A ω) -> Type) := mkPack {
  elt : forall ω, A ω;
  prp : forall ω, Aᴿ ω elt;
}.

Record TYPE := mkTYPE {
  wit : Ω -> Type;
  rel : Ω -> (forall ω : Ω, wit ω) -> Type;
}.

Definition El (A : TYPE) : Type := Pack A.(wit) A.(rel).

Definition Typeᶠ : TYPE := {|
  wit := fun _ => Type;
  rel := fun _ A => (forall ω : Ω, A ω) -> Type;
                          |}.
Set Printing Universes.
Fail Definition Typeᵇ : El Typeᶠ :=
  mkPack _ _ (fun w => Type) (fun w A => (forall ω, A ω) -> Type).

Definition Typeᵇ : El Typeᶠ :=
  mkPack _ (fun _ (A : Ω -> Type) => (forall ω : Ω, A ω) -> _) (fun w => Type) (fun w A => (forall ω, A ω) -> Type).

(** Bidirectional typechecking helps here *)
Require Import Program.Tactics.
Program Definition progTypeᵇ : El Typeᶠ :=
  mkPack _ _ (fun w => Type) (fun w A => (forall ω, A ω) -> Type).

(**
The command has indeed failed with message:
Error: Conversion test raised an anomaly
**)

Definition Typeᵇ' : El Typeᶠ.
Proof.
unshelve refine (mkPack _ _ _ _).
+ refine (fun _ => Type).
+ simpl. refine (fun _ A => (forall ω, A ω) -> Type).
Defined.
