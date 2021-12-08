Set Implicit Arguments.
Unset Strict Implicit.

Module OK.
Record A := mkA {
  T : Type;
  P : T -> bool;
}.

About P. (* Argument a is implicit *)
Check P (true: T (mkA negb)).
End OK.

Module KO.
Set Primitive Projections.
Record A := mkA {
  T : Type;
  P : T -> bool;
}.

About P. (* No implicit arguments *)
Check P (true: T (mkA negb)).
(*
The command has indeed failed with message:
The term "true : T {| T := bool; P := negb |}" has type "T {| T := bool; P := negb |}"
while it is expected to have type "A".
*)

End KO.
