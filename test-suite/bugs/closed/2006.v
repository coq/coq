(* Take the type constraint on Record into account *)

Definition Type1 := Type.
Fail Record R : Type1 := { p:Type1 }. (* was accepted before trunk revision 11619 *)

(*
Remarks:

- The behaviour was inconsistent with the one of Inductive, e.g.

  Inductive R : Type1 := Build_R : Type1 -> R.

  was correctly refused.

- CoRN makes some use of the following configuration:

  Definition CProp := Type.
  Record R : CProp := { ... }.

  CoRN may have to change the CProp definition into a notation if the
  preservation of the former semantics of Record type constraints
  turns to be required.
*)
