Module M.

  Definition a := 0.
  Definition b := 1.

  Module N.

    Notation c := (a + b).

  End N.

  Inductive even : nat -> Prop :=
  | even_0 : even 0
  | even_S n : odd n -> even (S n)
  with odd : nat -> Set :=
    odd_S n : even n -> odd (S n).

End M.

Module Simple.

  Import M(a).

  Check a.
  Fail Check b.
  Fail Check N.c.

  (* todo output test: this prints a+M.b since the notation isn't imported *)
  Check M.N.c.

  Fail Import M(c).
  Fail Import M(M.b).

  Import M(N.c).
  Check N.c.
  (* interestingly prints N.c (also does with unfiltered Import M) *)

  Import M(even(..)).
  Check even. Check even_0. Check even_S.
  Check even_sind. Check even_ind.
  Fail Check even_rect. (* doesn't exist *)
  Fail Check odd. Check M.odd.
  Fail Check odd_S. Fail Check odd_sind.

End Simple.

Module WithExport.

  Module X.
    Export M(a, N.c).
  End X.

  Import X.
  Check a.
  Check N.c. (* also prints N.c *)
  Fail Check b.

End WithExport.

Module IgnoreLocals.
  Module X.
    Local Definition x := 0.
    Definition y := 1.
  End X.

  Set Warnings "+not-importable".
  Fail Import X(x,y).
  Set Warnings "-not-importable".
  Import X(x,y).
  Check y.
  Fail Check x.
  Check X.x.
End IgnoreLocals.

Module FancyFunctor.
  (* A fancy behaviour with functors, not sure if we want to keep it
     but at least the test will ensure changes are deliberate. *)

  Module Type T.
    Parameter x : nat.
  End T.
  Module X.
    Definition x := 0.
    Definition y := 1.
  End X.

  Module Y.
    Local Definition x := 2.
  End Y.

  Module F(A:T).
    Export A(x).
  End F.
  Module Import M := F X.
  Check x.
  Fail Check y.

  Module N := F Y.
  Set Warnings "+not-importable".
  Fail Import N.
  Set Warnings "-not-importable".
  Import N.
  Check eq_refl : x = 0.

End FancyFunctor.

Require Import Sumbool(sumbool_of_bool).
Check sumbool_of_bool.
Check Sumbool.bool_eq_rec.

Fail Require Sumbool(sumbool_of_bool).
Fail Require Import Sumbool(not_a_real_definition).
Fail Require Import(notations) Sumbool(sumbool_of_bool).
