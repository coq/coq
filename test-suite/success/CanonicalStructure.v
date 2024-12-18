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

Module X.
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
Check X.s0.
Check X.s1.
Check X.s2.

Module Y.
  Definition s3 := MKL x3.
  Canonical Structure s3.
  Check (refl_equal _ : l _ = x3).
End Y.
Fail Check (refl_equal _ : l _ = x3).
Fail Check s3.

Module V.
  #[canonical] Definition s3 := MKL x3.
  Check (refl_equal _ : l _ = x3).
End V.

Module W.
  #[canonical, local] Definition s2' := MKL x2.
  Check (refl_equal _ : l _ = x2).
End W.
Fail Check (refl_equal _ : l _ = x2).

(* Lambda keys *)
Module LambdaKeys.
  Structure cs_lambda := { cs_lambda_key : nat -> nat }.
  Module L1.
    #[local] Canonical Structure cs_lambda_func :=
      {| cs_lambda_key := fun x => x + 1 |}.
    Check (refl_equal _ : cs_lambda_key _ = fun _ => _ + _).
  End L1.

  Module L2.
    #[local] Canonical Structure cs_lambda_func2 :=
      {| cs_lambda_key := fun x => 1 + x |}.
    Check (refl_equal _ : cs_lambda_key _ = fun x => 1 + x).
  End L2.

  Module L3.
    #[local] Canonical Structure cs_lambda_func3 :=
      {| cs_lambda_key := fun x => 1 + x |}.
    Check (refl_equal _ : cs_lambda_key _ = Nat.add 1).
  End L3.

  Module L4.
    #[local] Canonical Structure cs_lambda_func4 :=
      {| cs_lambda_key := Nat.add 1 |}.
    Check (refl_equal _ : cs_lambda_key _ = Nat.add 1).
  End L4.

  Module L5.
    #[local] Canonical Structure cs_lambda_func5 :=
      {| cs_lambda_key := Nat.add 1 |}.
    Check (refl_equal _ : cs_lambda_key _ = fun x => 1 + x).
  End L5.
End LambdaKeys.

Module DepProd.
  Structure hello := { hello_key : Type }.
  Module FixedTypes.
    Local Canonical Structure hello_dep1 := {| hello_key := forall x : nat, x = x |}.
    Example ex_hello2 := let h := _ in fun f : hello_key h => (f : forall x : nat, x = x) 1.
  End FixedTypes.

  Module VariableTypes.
    Local Canonical Structure hello_dep2 v1 v2 := {| hello_key := forall x : list v1, x = v2 |}.
    Example ex_hello1 : _ -> _ = nil :=
      let h := _ in fun f : hello_key h => (f : forall x : list _, _ = _) (@nil nat).
  End VariableTypes.
End DepProd.


(* Testing that canonical projections equipped with function type instances
   ([forall _, _]) or default instances ([_]) can be used in places where
   functions/function types are expected.
   This feature triggers CS search in two typing cases:
   1. [f x : _] when [f : proj _]
   2. [(fun x => _) : proj _].
 *)
Module NoCasts.
  Module Basic.
    Structure r1 (useless_param: bool) :=
      { #[canonical=no]  r1_pre : unit
      ; #[canonical=yes] r1_key : Type
      ; #[canonical=no]  r1_post: nat
      }.
    Canonical Structure r1_func b : r1 b := {| r1_pre:= tt; r1_key := nat -> nat; r1_post:= 0|}.
    Example ex_r1_1 p := let b := _ in fun f : @r1_key p b => f 1.
    Example ex_r1_2 p := let b := _ in (fun x => x) : @r1_key p b.
  End Basic.

  Module Primitive.
    Local Set Primitive Projections.
    Structure r2 (useless_param: bool) :=
      { #[canonical=no]  r2_pre : unit
      ; #[canonical=yes] r2_key : Type
      ; #[canonical=no]  r2_post: nat; }.
    Canonical Structure r2_func b : r2 b := {| r2_pre:= tt; r2_key := nat -> nat; r2_post:= 0|}.
    Example ex_r2_1 p := let b := _ in fun f : @r2_key p b => f 1.
    Example ex_r2_2 p := let b := _ in (fun x => x) : @r2_key p b.
  End Primitive.

  Module UsedParameters.
    Structure r3 (useless_param: bool) (T : Type) :=
      { #[canonical=no]  r3_pre : unit
      ; #[canonical=yes] r3_key : Type
      ; #[canonical=no]  r3_post: T
      }.
    Canonical Structure r3_func b : r3 b nat := {| r3_pre:= tt; r3_key := nat -> nat; r3_post:= 0|}.
    Example ex_r3_1 p := let b := _ in fun f : @r3_key p _ b => f 1.
    Example ex_r3_2 p := let b := _ in (fun x => x) : @r3_key p _ b.
  End UsedParameters.

  Module LetBoundFieldBefore.
    Structure r4 (useless_param: bool) :=
      { #[canonical=no]  r4_pre : unit
      ; #[canonical=no]  r4_let := true
      ; #[canonical=yes] r4_key : Type
      ; #[canonical=no]  r4_post: nat;
      }.
    Canonical Structure r4_func b : r4 b := {| r4_pre:= tt; r4_key := nat -> nat; r4_post:= 0|}.
    Example ex_r4_1 p := let b := _ in fun f : @r4_key p b => f 1.
    Example ex_r4_2 p := let b := _ in (fun x => x) : @r4_key p b.
  End LetBoundFieldBefore.

  Module LetBoundFieldAfter.
    Structure r4 (useless_param: bool) :=
      { #[canonical=no]  r4_pre : unit
      ; #[canonical=yes] r4_key : Type
      ; #[canonical=no]  r4_let := true
      ; #[canonical=no]  r4_post: nat;
      }.
    Canonical Structure r4_func b : r4 b := {| r4_pre:= tt; r4_key := nat -> nat; r4_post:= 0|}.
    Example ex_r4_1 p := let b := _ in fun f : @r4_key p b => f 1.
    Example ex_r4_2 p := let b := _ in (fun x => x) : @r4_key p b.
  End LetBoundFieldAfter.

  Module Tele.
    Inductive tele : Type :=
    | TeleO : tele
    | TeleS {X} : (X -> tele) -> tele.

    #[local] Set Primitive Projections.
    Structure tele_of := { tele_term : Type; #[canonical=no] tele_tele : tele; }.
    Canonical Structure tele_of_prod {X} {t :  X -> tele_of} := {| tele_term := forall x, (tele_term (t x)); tele_tele := TeleS (fun x => tele_tele (t x))|}.
    Canonical Structure tele_of_base {T} := {| tele_term := T; tele_tele := TeleO |}.

    Check let t : tele_of := _ in fun f : tele_term t => (f 0).
    (* Was Error: Ill-typed evar instance in #12383/#14715 original version *)
  End Tele.

End NoCasts.

(* Testing that we find coherent surrounding stacks for CS problems. *)
Module ExtraArgs.
  Structure Fun := {apply : nat -> nat}.

  Canonical S_Fun := {| apply := S |}.
  Check eq_refl : apply _ = S.
  Check eq_refl : apply _ 0 = S 0.

  Canonical generic_Fun (f : nat -> nat) := {| apply := f |}.
  Set Debug "unification".
  Set Printing All.
  Check fun (f : nat -> nat) => eq_refl : apply _ = f.
  Check fun (f : nat -> nat) => eq_refl : apply _ 0 = f 0.

End ExtraArgs.

(* Testing that we unfold keys that match but do not unify *)
Module TestKeys.
Structure Dummy (b : bool) := {T : Type}.
Definition boolF := bool.
Canonical Dummy_boolF : Dummy false := {| T := boolF |}.
Definition boolT := boolF.
Canonical Dummy_boolT : Dummy true := {| T := boolT |}.

Set Debug "unification".
Check eq_refl : id (@T false _) = boolT.
End TestKeys.
