(** Check that various errors in record fields are reported with the correct
underlying issue. *)

Record t :=
  { foo: unit }.

Record t' :=
  { bar: unit }.

Fail Check {| unit := tt |}.
(* unit: Not a projection. *)

Fail Check {| unit := tt;
              foo := tt |}.
(* unit: Not a projection. *)

Fail Check {| foo := tt;
              bar := tt |}.
(* This record contains fields of different records. *)

Fail Check {| unit := tt;
              unit := tt |}.
(* unit: Not a projection. *)

Fail Check {| foo := tt;
              foo := tt |}.
(* This record defines several times the field foo. *)

Fail Check {| foo := tt;
              unit := tt;
              unit := tt |}.
(* This is slightly wrong (would prefer "unit: Not a projection."), but it's
acceptable and seems an unlikely mistake. *)
(* This record defines several times the field unit. *)

Fail Check {| foo := tt;
              unit := tt |}.
(* unit: Not a projection of inductive t. *)
