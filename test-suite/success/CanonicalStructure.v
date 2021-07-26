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

(* Lambda keys *)
Section L1.
  Structure cs_lambda := { cs_lambda_key : nat -> nat }.
  #[local] Canonical Structure cs_lambda_func :=
    {| cs_lambda_key := fun x => x + 1 |}.
  Check (refl_equal _ : cs_lambda_key _ = fun _ => _ + _).
End L1.

Section L2.
  #[local] Canonical Structure cs_lambda_func2 :=
    {| cs_lambda_key := fun x => 1 + x |}.
  Check (refl_equal _ : cs_lambda_key _ = fun x => 1 + x).
End L2.

Section L3.
  #[local] Canonical Structure cs_lambda_func3 :=
    {| cs_lambda_key := fun x => 1 + x |}.
  Check (refl_equal _ : cs_lambda_key _ = Nat.add 1).
End L3.

Section L4.
  #[local] Canonical Structure cs_lambda_func4 :=
    {| cs_lambda_key := Nat.add 1 |}.
  Check (refl_equal _ : cs_lambda_key _ = Nat.add 1).
End L4.

Section L5.
  #[local] Canonical Structure cs_lambda_func5 :=
    {| cs_lambda_key := Nat.add 1 |}.
  Check (refl_equal _ : cs_lambda_key _ = fun x => 1 + x).
End L5.

Section DepProd.
  Structure hello := { hello_key : Type }.
  Section FixedTypes.
    Local Canonical Structure hello_dep1 := {| hello_key := forall x : nat, x = x |}.
    Example ex_hello2 := let h := _ in fun f : hello_key h => (f : forall x : nat, x = x) 1.
  End FixedTypes.

  Section VariableTypes.
    Local Canonical Structure hello_dep2 v1 v2 := {| hello_key := forall x : list v1, x = v2 |}.
    Example ex_hello1 : _ -> _ = nil :=
      let h := _ in fun f : hello_key h => (f : forall x : list _, _ = _) (@nil nat).
  End VariableTypes.
End DepProd.

Section NoCasts.
  Section A.
    Structure bla (useless_param: bool) := { #[canonical=no]bla_pre : unit; bla_key : Type; #[canonical=no]bla_post: nat; }.
    Canonical Structure bla_func b : bla b := {| bla_pre:= tt; bla_key := nat -> nat; bla_post:= 0|}.
    Example ex_bla1 p := let b := _ in fun f : @bla_key p b => f 1.
    Example ex_bla2 p := let b := _ in (fun x => x) : @bla_key p b.
  End A.
  Section B.
    Local Set Primitive Projections.
    Structure pbla (useless_param: bool) := { #[canonical=no]pbla_pre : unit; pbla_key : Type; #[canonical=no]pbla_post: nat; }.
    Canonical Structure pbla_func b : pbla b := {| pbla_pre:= tt; pbla_key := nat -> nat; pbla_post:= 0|}.
    Example ex_pbla1 p := let b := _ in fun f : @pbla_key p b => f 1.
    Example ex_pbla2 p := let b := _ in (fun x => x) : @pbla_key p b.
  End B.
End NoCasts.
