Set Implicit Arguments. 
Set Universe Polymorphism.
Set Printing Universes.

Inductive type_paths (A : Type) : Type -> Prop
  := idtypepath : type_paths A A.
Monomorphic Definition comp_type_paths := Eval compute in type_paths@{Type Type}.
Check comp_type_paths.
(* comp_type_paths
     : Type (* Top.12 *) -> Type (* Top.12 *) -> Prop *)
(* This is terrible. *)

Inductive type_paths' (A : Type) : Type -> Prop
  := idtypepath' : type_paths' A A
   | other_type_path : False -> forall B : Type, type_paths' A B.
Monomorphic Definition comp_type_paths' := Eval compute in type_paths'.
Check comp_type_paths'.
(* comp_type_paths'
     : Type (* Top.24 *) -> Type (* Top.23 *) -> Prop *)
(* Ok, then ... *)

(** Fail if it's [U0 -> U0 -> _], but not on [U0 -> U1 -> _]. *)
Goal Type.
Proof.
  match type of comp_type_paths' with
    | ?U0 -> ?U1 -> ?R
      => exact (@comp_type_paths' nat U0)
  end.
Defined.

Goal Type.
Proof.
   match type of comp_type_paths with
    | ?U0 -> ?U1 -> ?R
      => exact (@comp_type_paths nat U0)
  end.
  (* Toplevel input, characters 110-112:
Error:
The term "Type (* Top.51 *)" has type "Type (* Top.51+1 *)"
while it is expected to have type "Type (* Top.51 *)"
(Universe inconsistency: Cannot enforce Top.51 < Top.51 because Top.51
= Top.51)). *)
  
Defined.
