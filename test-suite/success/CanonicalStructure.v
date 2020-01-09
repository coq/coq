(* Bug #1172 *)

Structure foo : Type := Foo {
   A : Set; Aopt := option A; unopt : Aopt -> A
}.

Canonical Structure unopt_nat := @Foo nat (fun _ => O).

(* Granted wish #1187 *)

Record Silly (X : Set) : Set := mkSilly { x : X }.
Definition anotherMk := mkSilly.
Definition struct := anotherMk nat 3.
Canonical Structure struct.

(* Intertwinning canonical structures and delta-expansion *)
(* Assia's short example *)

Open Scope bool_scope.

Set Implicit Arguments.

Structure test_struct : Type := mk_test {dom :> Type; f : dom -> dom -> bool}.

Notation " x != y":= (f _ x y)(at level 10).

Canonical Structure bool_test := mk_test (fun x y => x || y).

Definition b := bool.

Check (fun x : b => x != x).

Inductive four := x0 | x1 | x2 | x3.
Structure local := MKL { l : four }.

Section X.
  Definition s0 := MKL x0.
  #[local] Canonical Structure s0.
  Check (refl_equal _ : l _ = x0).

  #[local] Canonical Structure s1 := MKL x1.
  Check (refl_equal _ : l _ = x1).

  Local Canonical Structure s2 := MKL x2.
  Check (refl_equal _ : l _ = x2).

End X.
Fail Check (refl_equal _ : l _ = x0).
Fail Check (refl_equal _ : l _ = x1).
Fail Check (refl_equal _ : l _ = x2).
Check s0.
Check s1.
Check s2.

Section Y.
  Let s3 := MKL x3.
  Canonical Structure s3.
  Check (refl_equal _ : l _ = x3).
End Y.
Fail Check (refl_equal _ : l _ = x3).
Fail Check s3.

Section V.
  #[canonical] Let s3 := MKL x3.
  Check (refl_equal _ : l _ = x3).
End V.

Section W.
  #[canonical, local] Definition s2' := MKL x2.
  Check (refl_equal _ : l _ = x2).
End W.
Fail Check (refl_equal _ : l _ = x2).
