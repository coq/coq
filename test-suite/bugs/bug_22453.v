(* The delta-resolver of a plain submodule must agree with the one of its
   parent.

   A functor's resolver records an equivalence for the path its application will
   land on: [Module Id (X : T) := X] says that applying [Id] yields the
   argument. Including an application used to α-rename the functor onto the
   includer's path before applying it, so that equivalence was stamped onto the
   includer -- claiming that [R] below is [M] -- and then had to be expanded away
   and replaced by a marker saying that [R] is only equivalent to itself.

   That marker travels with its key, and unlike the equivalence it replaced it
   stays true nowhere: copying [Outer] to the toplevel carried it onto the copy
   of [A.B], whose resolver ended up claiming that [A.B] was canonical while
   [Outer]'s said that [A.B] was [Outer.R]. Nothing identified [A.B.S.x] with
   [R.S.x] any more, that equality being exactly what the shadowed binding stood
   for, and the definition below was rejected with "Ill-formed constant A.B.S.x:
   expected canonical name ... but found ...". *)

Module Type T. Parameter n : bool. End T.
Module M. Definition n := true. End M.
Module Id (X : T) := X.

Module Outer.
  Module R. Include Id M. Module S. Definition x := false. End S. End R.
  Module A. Module B := Outer.R. End A.
End Outer.

Include Outer.

Definition check_const : A.B.S.x = R.S.x := eq_refl.

(* The same defect was reachable a second way. [Include F] with [F] unapplied
   instantiates the parameters of [F] with the module being built -- the
   [Include Self] idiom behind [<+] -- and that instantiation is the caller's
   business, not [translate_mse_include]'s. The functor used to be renamed onto
   the includer all the same, with the same consequence. *)
Module P. Definition p := false. End P.
Module Fp (X : T) := P.

Module Outer1.
  Module R1. Include M. Include Fp. Module S. Definition x := false. End S. End R1.
  Module A1. Module B := Outer1.R1. End A1.
End Outer1.

Include Outer1.

Definition check_self : A1.B.S.x = R1.S.x := eq_refl.

(* The idiom itself must keep working. *)
Module Type HasM. Parameter m : bool. End HasM.
Module Type SelfT (X : T). Parameter q : bool. End SelfT.
Module Type UsesSelf := T <+ SelfT.
Module Rp := M <+ Fp.
Definition check_idiom : Rp.p = P.p := eq_refl.

(* Same thing when the canonical name of an inductive and of its constructors
   is what is at stake. *)
Module Outer2.
  Module R2. Include Id M. Module S. Inductive I := c. End S. End R2.
  Module A2. Module B := Outer2.R2. End A2.
End Outer2.

Include Outer2.

Definition check_ind : A2.B.S.I := R2.S.c.
Definition check_constr : Outer2.R2.S.I := A2.B.S.c.
