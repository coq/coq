(* Inlining declarations ([Parameter Inline]) belong to module types: they are
   read back when a module type is used as a functor parameter, and turned into
   an actual substitution of bodies when the functor is applied. They are
   meaningless anywhere else. *)

Set Warnings "+inline-parameter-in-module".

(* A plain module cannot declare an inlinable parameter. *)
Module M.
  Fail Parameter Inline(1) x : Type.
End M.

Module Type T.
  Parameter Inline t : Type.
  Parameter u : t -> t.
End T.

(* The declaration survives the various ways of building a module type out of
   another one. *)
Module Type T2 := T.
Module Type T3. Include T. End T3.
Module Type T4. Declare Module Sub : T. End T4.

Module A.
  Definition t := nat.
  Definition u (x : nat) := x.
End A.

Module F (X : T) := X.
Module F2 (X : T2) := X.
Module F3 (X : T3) := X.
Module F4 (X : T4) := X.
Module B. Module Sub := A. End B.

Module A1 := F A.
Module A2 := F2 A.
Module A3 := F3 A.
Module B4 := F4 B.

(* A functor whose parameter type is itself a functor type mentioning [T]: the
   subtyping check of the argument against [FS] must not confuse the inlining
   declaration of [T] with an actual body. *)
Module Type FS (X : T). Parameter v : X.t -> X.t. End FS.
Module G (X : T). Definition v := X.u. End G.
Module H (K : FS) (X : T) := K X.
Module C := H G A.

(* The application may also be reached through an [Include], possibly nested. *)
Module I1. Include F A. End I1.
Module I2. Module Inner. Include F A. End Inner. End I2.
Module I3. Module N := F A. End I3.

(* Applying a functor type. *)
Module Type FT (X : T). Definition u := X.u. End FT.
Module Type S1 := FT A.
Module Type S2. Include FT A. End S2.
Module J1 : S1. Definition u := A.u. End J1.
Module J2 : S2. Definition u := A.u. End J2.

(* [A1.u] is [A.u], whose argument is in [nat_scope]; the notation below would
   otherwise make [1] a [bool]. Getting this right requires the body [nat] of
   the inlinable field [t] to reach the objects of the functor. See also
   test-suite/bugs/bug_15403.v. *)
Notation "1" := true.

Check A1.u 1.
Check A2.u 1.
Check A3.u 1.
Check B4.Sub.u 1.
Check C.v 1.
Check I1.u 1.
Check I2.Inner.u 1.
Check I3.N.u 1.
Check J1.u 1.
Check J2.u 1.

(* An inlinable field of a functor argument stays identified with the
   argument's field: the inlining does not replace the name equivalence. *)
Module K (X : T). Include F X. End K.
Module K1 := K A.
Definition check_alias : K1.t = A.t := eq_refl.
Definition check_alias' : K1.u = A.u := eq_refl.
