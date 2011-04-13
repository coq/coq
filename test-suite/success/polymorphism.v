(* Some tests of sort-polymorphisme *)
Section S.
Variable A:Type.
(*
Definition f (B:Type) := (A * B)%type.
*)
Inductive I (B:Type) : Type := prod : A->B->I B.
End S.
(*
Check f nat nat : Set.
*)
Check I nat nat : Set.