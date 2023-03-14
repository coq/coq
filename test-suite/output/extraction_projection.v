(** Miscellaneous tests on the ocaml extraction *)

Require Import Extraction.
Extraction Language OCaml.

(** Extraction at toplevel *)

Record non_prim_record_two_fields := {non_prim_proj1_of_2:bool;non_prim_proj2_of_2:bool}.
Record non_prim_record_one_field := {non_prim_proj1_of_1:bool}.
Record non_prim_record_one_field_unused := {non_prim_proj1_of_1_unused:bool}.
Definition d11 x := x.(non_prim_proj1_of_2).
Definition d12 x := (x tt).(non_prim_proj1_of_2).
Definition e11 x := x.(non_prim_proj1_of_1).
Definition e12 x := (x tt).(non_prim_proj1_of_1).

Set Primitive Projections.
Record prim_record_two_fields := {prim_proj1_of_2:bool;prim_proj2_of_2:bool}.
Record prim_record_one_field := {prim_proj1_of_1:bool}.
Record prim_record_one_field_unused := {prim_proj1_of_1_unused:bool}.
Unset Primitive Projections.
Definition d21 x := x.(prim_proj1_of_2).
Definition d22 x := (x tt).(prim_proj1_of_2).
Definition e21 x := x.(prim_proj1_of_1).
Definition e22 x := (x tt).(prim_proj1_of_1).

Recursive Extraction d11 d12 d21 d22 e11 e12 e21 e22.

(** Extraction in module *)

Module A.
  Record non_prim_record_two_fields := {non_prim_proj1_of_2:bool;non_prim_proj2_of_2:bool}.
  Record non_prim_record_one_field := {non_prim_proj1_of_1:bool}.
  Record non_prim_record_one_field_unused := {non_prim_proj1_of_1_unused:bool}.
  Definition d11 x := x.(non_prim_proj1_of_2).
  Definition d12 x := (x tt).(non_prim_proj1_of_2).
  Definition e11 x := x.(non_prim_proj1_of_1).
  Definition e12 x := (x tt).(non_prim_proj1_of_1).

  Set Primitive Projections.
  Record prim_record_two_fields := {prim_proj1_of_2:bool;prim_proj2_of_2:bool}.
  Record prim_record_one_field := {prim_proj1_of_1:bool}.
  Record prim_record_one_field_unused := {prim_proj1_of_1_unused:bool}.
  Unset Primitive Projections.
  Definition d21 x := x.(prim_proj1_of_2).
  Definition d22 x := (x tt).(prim_proj1_of_2).
  Definition e21 x := x.(prim_proj1_of_1).
  Definition e22 x := (x tt).(prim_proj1_of_1).
End A.

Recursive Extraction A.d11 A.d12 A.d21 A.d22 A.e11 A.e12 A.e21 A.e22.

(* Inside a functor *)

Module Type Nop. End Nop.
Module Empty. End Empty.

Module M (X : Nop).
  Record non_prim_record_two_fields := {non_prim_proj1_of_2:bool;non_prim_proj2_of_2:bool}.
  Record non_prim_record_one_field := {non_prim_proj1_of_1:bool}.
  Record non_prim_record_one_field_unused := {non_prim_proj1_of_1_unused:bool}.
  Definition d11 x := x.(non_prim_proj1_of_2).
  Definition d12 x := (x tt).(non_prim_proj1_of_2).
  Definition e11 x := x.(non_prim_proj1_of_1).
  Definition e12 x := (x tt).(non_prim_proj1_of_1).

  Set Primitive Projections.
  Record prim_record_two_fields := {prim_proj1_of_2:bool;prim_proj2_of_2:bool}.
  Record prim_record_one_field := {prim_proj1_of_1:bool}.
  Record prim_record_one_field_unused := {prim_proj1_of_1_unused:bool}.
  Unset Primitive Projections.
  Definition d21 x := x.(prim_proj1_of_2).
  Definition d22 x := (x tt).(prim_proj1_of_2).
  Definition e21 x := x.(prim_proj1_of_1).
  Definition e22 x := (x tt).(prim_proj1_of_1).
  End M.
Module N := M Empty.
Recursive Extraction N.d11 N.d12 N.d21 N.d22 N.e11 N.e12 N.e21 N.e22.
