(* Including a functor application relates each copied field to the canonical
   name the application's resolver gives it. That answer is a name of the
   application, which lives at the functor's own path and names nothing: when
   it points at another field of the application -- here [F.m] is δ-equal to
   [F.A.m], [F] including its own submodule [A] -- it must be read in the
   includer's naming scheme, as [N.A.m], and not recorded as [F.A.m].

   Recorded as [F.A.m] it is not merely dangling: it is the same name for every
   inclusion of [F], so the fields two different includers get are identified,
   and since they are computed from each includer's own [n] that is a proof of
   [true = false]. *)

Module Type T. Parameter n : bool. End T.

Module F (X : T).
  Module A. Definition m := X.n. End A.
  Include A.
End F.

Module N1. Definition n := true.  Include F. End N1.
Module N2. Definition n := false. Include F. End N2.

(* Each copy is its own field, ... *)
Definition c1 : N1.m = N1.A.m := eq_refl.
Definition c2 : N2.m = N2.A.m := eq_refl.
Definition v1 : N1.m = true := eq_refl.
Definition v2 : N2.m = false := eq_refl.

(* ... and the two inclusions must not be confused. *)
Fail Definition same : N1.m = N2.m := eq_refl.
