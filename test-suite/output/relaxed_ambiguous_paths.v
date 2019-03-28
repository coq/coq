Module test1.
Section test1.

Variable (A B C D : Type).
Variable (ab : A -> B) (bd : B -> D) (ac : A -> C) (cd : C -> D).

Local Coercion ab : A >-> B.
Local Coercion bd : B >-> D.
Local Coercion ac : A >-> C.
Local Coercion cd : C >-> D.

Print Graph.

End test1.
End test1.

Module test2.
Section test2.
Variable (A : Type) (P Q : A -> Prop).

Record B := {
  B_A : A;
  B_P : P B_A }.

Record C := {
  C_A : A;
  C_Q : Q C_A }.

Record D := {
  D_A : A;
  D_P : P D_A;
  D_Q : Q D_A }.

Local Coercion B_A : B >-> A.
Local Coercion C_A : C >-> A.
Local Coercion D_A : D >-> A.
Local Coercion D_B (d : D) : B := Build_B (D_A d) (D_P d).
Local Coercion D_C (d : D) : C := Build_C (D_A d) (D_Q d).

Print Graph.

End test2.
End test2.

Module test3.
Section test3.

Variable (A : Type) (P Q : A -> Prop).

Definition A' (x : bool) := A.

Record B (x : bool) := {
  B_A' : A' x;
  B_P : P B_A' }.

Record C (x : bool) := {
  C_A' : A' x;
  C_Q : Q C_A' }.

Record D := {
  D_A : A;
  D_P : P D_A;
  D_Q : Q D_A }.

Local Coercion A'_A (x : bool) (a : A' x) : A := a.
Local Coercion B_A' : B >-> A'.
Local Coercion C_A' : C >-> A'.
Local Coercion D_A : D >-> A.
Local Coercion D_B (d : D) : B false := Build_B false (D_A d) (D_P d).
Local Coercion D_C (d : D) : C true := Build_C true (D_A d) (D_Q d).

Print Graph.

End test3.
End test3.

Module test4.
Section test4.

Variable (A : Type) (P Q : A -> Prop).

Record A' (x : bool) := { A'_A : A }.

Record B (x : bool) := {
  B_A' : A' x;
  B_P : P (A'_A x B_A') }.

Record C (x : bool) := {
  C_A' : A' x;
  C_Q : Q (A'_A x C_A') }.

Record D := {
  D_A : A;
  D_P : P D_A;
  D_Q : Q D_A }.

Local Coercion A'_A : A' >-> A.
Local Coercion B_A' : B >-> A'.
Local Coercion C_A' : C >-> A'.
Local Coercion D_A : D >-> A.
Local Coercion D_B (d : D) : B false :=
  Build_B false (Build_A' false (D_A d)) (D_P d).
Local Coercion D_C (d : D) : C true :=
  Build_C true (Build_A' true (D_A d)) (D_Q d).

Print Graph.

End test4.
End test4.
