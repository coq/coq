Require Import Corelib.ssr.ssreflect.

Axiom R : Type.

Variant extended := EFin of R | EPInf | ENInf.

Definition le_ereal (x1 x2 : extended) :=
  match x1, x2 with
  | ENInf, EFin r | EFin r, EPInf => true
  | EFin r1, EFin r2 => true
  | ENInf, _    | _, EPInf => true
  | EPInf, _    | _, ENInf => false
  end.

Axiom lee_pinfty : forall (x : extended), is_true (le_ereal x (EPInf)).

Definition adde_subdef (x y : extended) :=
  match x, y with
  | EFin _, EFin _  => x
  | ENInf, _     => ENInf
  | _    , ENInf => ENInf
  | EPInf, _     => EPInf
  | _    , EPInf => EPInf
  end.

Definition adde := nosimpl adde_subdef.

Goal forall (x : R),
  (forall e : R, is_true (le_ereal (EFin x) (adde (EPInf) (EFin e)))) -> True.
Proof.
intros x.
Fail rewrite (lee_pinfty (EFin x)).
constructor.
Qed.
