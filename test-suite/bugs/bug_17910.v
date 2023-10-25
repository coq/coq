Require Import Morphisms Setoid.

Class Subst {Obj : Type} (Arr : Obj -> Obj -> Type) (Sub : Obj -> Type)
      {subst_of_arr : forall {A B}, Arr A B -> Sub A}  : Prop :=
  { arrow_subst_proper A B :: Proper (eq ==> eq) (@subst_of_arr A B) }.

Record PShf (Obj : Type) := { FO :> Obj -> Type; Peq : forall A, FO A -> FO A -> Prop }.

Inductive kind : Set := KIND : kind.

Axiom Ctx : Type.
Axiom T : PShf Ctx.

Axiom nf : Ctx -> kind -> Type.
Axiom FunX : forall {Δ : Ctx}, T Δ.
Axiom FunY : forall (Δ : Ctx), T Δ.
Axiom reify : forall {κ : kind} {Δ : Ctx} (_ : T Δ), Basics.flip nf κ Δ.
Axiom rew : forall (Δ : Ctx), @Peq Ctx T Δ (@FunY Δ) (@FunX Δ).

Goal forall (Δ : Ctx) (r : nf Δ KIND),
  @eq (nf Δ KIND) (reify (@FunY Δ)) r.
Proof.
intros.
Fail rewrite (rew Δ).
Abort.
(* Anomaly "ill-typed term: found a match on a partially applied constructor." *)
