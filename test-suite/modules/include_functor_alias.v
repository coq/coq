(* An inclusion must not add a delta-equivalence for the includer itself.

   The body of a functor can be algebraically one of its arguments, in which
   case its codomain delta-resolver holds an equivalence for the functor path
   itself. Applying the functor turns it into an equivalence for the path of
   the module being built, and [find_prefix] then applies it to *every* label
   under that path -- including fields that are not part of the included
   signature. Those fields used to be identified with unrelated fields of the
   included module, which made False provable:

     Module P. Include Id A. Definition extra := false. End P.
     Definition h1 : A.extra = true  := eq_refl.
     Definition h2 : P.extra = false := eq_refl.
     Definition h3 : A.extra = P.extra := eq_refl.   (* accepted! *)

   Each [Fail] below is one way to build such a functor, and each of them used
   to be accepted. The positive checks guard the converse: the per-field
   equivalences an inclusion legitimately provides must be preserved. *)

Module Type T. Parameter n : bool. End T.
Module Type TS. Parameter n : bool. Declare Module Sub : T. End TS.
Module Type EXTRA. Parameter extra : bool. End EXTRA.

Module A.
  Definition n := true.
  Definition extra := true.
  Inductive I : Prop := c : I.
  Module Sub. Definition n := true. Definition extra := true. End Sub.
End A.

(* Functors whose body is algebraically built from their arguments. *)
Module Id (X : T) := X.
Module IdS (X : TS) := X.
Module Proj (X : TS) := X.Sub.
Module Id2 (X : T) := Id X.
Module Bin (X : T) (Y : T) := X.

(* The identity functor. *)
Module C1.
  Include Id A.
  Definition extra := false.
End C1.
Definition c1_ok : C1.n = A.n := eq_refl.
Fail Definition c1_ko : A.extra = C1.extra := eq_refl.

(* Same, on an inductive type: no conversion check can ever repair that one. *)
Module C2.
  Include Id A.
  Inductive I : Prop := .
End C2.
Fail Definition c2_ko : C2.I := A.c.

(* Through an indirection. *)
Module C3.
  Include Id2 A.
  Definition extra := false.
End C3.
Definition c3_ok : C3.n = A.n := eq_refl.
Fail Definition c3_ko : A.extra = C3.extra := eq_refl.

(* A binary functor projecting its first argument. *)
Module C4.
  Include Bin A A.
  Definition extra := false.
End C4.
Definition c4_ok : C4.n = A.n := eq_refl.
Fail Definition c4_ko : A.extra = C4.extra := eq_refl.

(* A functor projecting a submodule of its argument. *)
Module C5.
  Include Proj A.
  Definition extra := false.
End C5.
Definition c5_ok : C5.n = A.Sub.n := eq_refl.
Fail Definition c5_ko : A.Sub.extra = C5.extra := eq_refl.

(* The [<+] form, the extra fields coming from a module type. *)
Module C6 := Id A <+ EXTRA.
Definition c6_ok : C6.n = A.n := eq_refl.
Fail Definition c6_ko : A.extra = C6.extra := eq_refl.

(* The inclusion happening inside a functor: the bogus equivalence is then
   created afresh at every instantiation. *)
Module F7 (X : T).
  Include Id X.
  Definition extra := false.
End F7.
Module C7 := F7 A.
Definition c7_ok : C7.n = A.n := eq_refl.
Fail Definition c7_ko : A.extra = C7.extra := eq_refl.

(* The clashing field declared *before* the inclusion. *)
Module C8.
  Definition extra := false.
  Include Id A.
End C8.
Definition c8_ok : C8.n = A.n := eq_refl.
Fail Definition c8_ko : A.extra = C8.extra := eq_refl.

Module C9.
  Inductive I : Prop := .
  Include Id A.
End C9.
Fail Definition c9_ko : C9.I := A.c.

(* Including the result of an inclusion. This one was never a wrongdoer --
   [C10a] is not a functor, so the non-functor case already drops the
   equivalence -- but the assertion is the same and worth pinning down. *)
Module C10a. Include Id A. End C10a.
Module C10.
  Include C10a.
  Definition extra := false.
End C10.
Definition c10_ok : C10.n = A.n := eq_refl.
Fail Definition c10_ko : A.extra = C10.extra := eq_refl.

(* The equivalence has to be *removed*, not neutralised by mapping the includer
   to itself: [mp_in_delta] is also how [strengthen] recognises an already
   strengthened module, so an equivalence [C12 -> C12] would keep [C12.m] from
   being strengthened and the ascription below would be rejected. Before the
   fix this raised Anomaly "Constant A.m does not appear in the environment",
   [m] not being a field of [A]. *)
Module C12.
  Include Id A.
  Parameter m : bool.
End C12.
Module Type S12. Parameter n : bool. Definition m := C12.m. End S12.
Module Q12 : S12 := C12.

(* Submodule fields of the included signature are legitimately shared, and
   must stay so: a fix that simply dropped the equivalence would break this. *)
Module C11.
  Include IdS A.
End C11.
Definition c11_ok1 : C11.n = A.n := eq_refl.
Definition c11_ok2 : C11.Sub.n = A.Sub.n := eq_refl.
