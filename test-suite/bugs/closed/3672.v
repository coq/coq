Set Primitive Projections.  (* No failures without this option. *)

Record AT :=
{ atype :> Type
; coerce : atype -> Type
}.
Coercion coerce : atype >-> Sortclass.

Record Ar C (A:AT) := { ar : forall (X Y : C), A }.

Definition t := forall C A a X, coerce _ (ar C A a X X).
Definition t' := forall C A a X, ar C A a X X.

(* The command has indeed failed with message:
=> Error: The term "ar C A a X X" has type "atype A" which is not a (co-)inductive type.
*)

Record Ar2 C (A:AT) := 
{ ar2 : forall (X Y : C), A
; id2 : forall X, coerce _ (ar2 X X) }.

Record Ar3 C (A:AT) := 
{ ar3 : forall (X Y : C), A
; id3 : forall X, ar3 X X }.
(* The command has indeed failed with message:
=> Anomaly: Bad recursive type. Please report.
*)
