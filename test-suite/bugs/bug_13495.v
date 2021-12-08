Universe u.
(* Constraint Set < u. *)
Polymorphic Cumulative Record pack@{u} := Pack { pack_type : Type@{u} }.
(* u is covariant *)

Polymorphic Definition pack_id@{u} (p : pack@{u}) : pack@{u} :=
  match p with
  | Pack T => Pack T
  end.
Definition packid_nat (p : pack@{Set}) := pack_id@{u} p.
(* No constraints: Set <= u *)

Definition sr_dont_break := Eval compute in packid_nat.
(* Incorrect elimination of "p" in the inductive type "pack":
  ill-formed elimination predicate.

  This is because it tries to enforce Set = u
  *)
