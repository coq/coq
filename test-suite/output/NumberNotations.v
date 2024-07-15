(* Test that we fail, rather than raising anomalies, on opaque terms during interpretation *)

Declare Scope opaque_scope.

(* https://github.com/coq/coq/pull/8064#discussion_r202497516 *)
Module Test1.
  Axiom hold : forall {A B C}, A -> B -> C.
  Definition opaque3 (x : Number.int) : Number.int := hold x (fix f (x : nat) : nat := match x with O => O | S n => S (f n) end).
  Number Notation Number.int opaque3 opaque3 : opaque_scope.
  Delimit Scope opaque_scope with opaque.
  Fail Check 1%opaque.
End Test1.

(* https://github.com/coq/coq/pull/8064#discussion_r202497990 *)
Module Test2.
  Axiom opaque4 : option Number.int.
  Definition opaque6 (x : Number.int) : option Number.int := opaque4.
  Number Notation Number.int opaque6 opaque6 : opaque_scope.
  Delimit Scope opaque_scope with opaque.
  Open Scope opaque_scope.
  Fail Check 1%opaque.
End Test2.

Declare Scope silly_scope.

Module Test3.
  Inductive silly := SILLY (v : Number.uint) (f : forall A, A -> A).
  Definition to_silly (v : Number.uint) := SILLY v (fun _ x => x).
  Definition of_silly (v : silly) := match v with SILLY v _ => v end.
  Number Notation silly to_silly of_silly : silly_scope.
  Delimit Scope silly_scope with silly.
  Fail Check 1%silly.
End Test3.

Module Test4.
  Declare Scope opaque_scope.
  Declare Scope silly_scope.
  Declare Scope pto.
  Declare Scope ppo.
  Declare Scope ptp.
  Declare Scope ppp.
  Declare Scope uto.
  Declare Scope upo.
  Declare Scope utp.
  Declare Scope upp.
  Declare Scope ppps.
  Polymorphic NonCumulative Inductive punit := ptt.
  Polymorphic Definition pto_punit (v : Number.uint) : option punit := match Nat.of_num_uint v with O => Some ptt | _ => None end.
  Polymorphic Definition pto_punit_all (v : Number.uint) : punit := ptt.
  Polymorphic Definition pof_punit (v : punit) : Number.uint := Nat.to_num_uint 0.
  Definition to_punit (v : Number.uint) : option punit := match Nat.of_num_uint v with O => Some ptt | _ => None end.
  Definition of_punit (v : punit) : Number.uint := Nat.to_num_uint 0.
  Polymorphic Definition pto_unit (v : Number.uint) : option unit := match Nat.of_num_uint v with O => Some tt | _ => None end.
  Polymorphic Definition pof_unit (v : unit) : Number.uint := Nat.to_num_uint 0.
  Definition to_unit (v : Number.uint) : option unit := match Nat.of_num_uint v with O => Some tt | _ => None end.
  Definition of_unit (v : unit) : Number.uint := Nat.to_num_uint 0.
  Number Notation punit to_punit of_punit : pto.
  Number Notation punit pto_punit of_punit : ppo.
  Number Notation punit to_punit pof_punit : ptp.
  Number Notation punit pto_punit pof_punit : ppp.
  Number Notation unit to_unit of_unit : uto.
  Delimit Scope pto with pto.
  Delimit Scope ppo with ppo.
  Delimit Scope ptp with ptp.
  Delimit Scope ppp with ppp.
  Delimit Scope uto with uto.
  Check let v := 0%pto in v : punit.
  Check let v := 0%ppo in v : punit.
  Check let v := 0%ptp in v : punit.
  Check let v := 0%ppp in v : punit.
  Check let v := 0%uto in v : unit.
  Fail Check 1%uto.
  Fail Check (-1)%uto.
  Number Notation unit pto_unit of_unit : upo.
  Number Notation unit to_unit pof_unit : utp.
  Number Notation unit pto_unit pof_unit : upp.
  Delimit Scope upo with upo.
  Delimit Scope utp with utp.
  Delimit Scope upp with upp.
  Check let v := 0%upo in v : unit.
  Check let v := 0%utp in v : unit.
  Check let v := 0%upp in v : unit.

  Polymorphic Definition pto_punits := pto_punit_all@{Set}.
  Polymorphic Definition pof_punits := pof_punit@{Set}.
  Number Notation punit pto_punits pof_punits (abstract after 0) : ppps.
  Delimit Scope ppps with ppps.
  Universe u.
  Constraint Set < u.
  Check let v := 0%ppps in v : punit@{u}. (* Check that universes are refreshed *)
  Fail Check let v := 1%ppps in v : punit@{u}. (* Note that universes are not refreshed here *)
End Test4.

Module Test5.
  Check S. (* At one point gave Error: Anomaly "Uncaught exception Pretype_errors.PretypeError(_, _, _)." Please report at http://coq.inria.fr/bugs/. *)
End Test5.

Module Test6.
  (* Check that number notations on enormous terms don't take forever to print/parse *)
  (* Ackerman definition from https://stackoverflow.com/a/10303475/377022 *)
  Fixpoint ack (n m : nat) : nat :=
    match n with
    | O => S m
    | S p => let fix ackn (m : nat) :=
                 match m with
                 | O => ack p 1
                 | S q => ack p (ackn q)
                 end
             in ackn m
    end.

  Timeout 1 Check (S (ack 4 4)). (* should be instantaneous *)

  Local Set Primitive Projections.
  Record > wnat := wrap { unwrap :> nat }.
  Definition to_uint (x : wnat) : Number.uint := Nat.to_num_uint x.
  Definition of_uint (x : Number.uint) : wnat := Nat.of_num_uint x.
  Module Export Scopes.
    Declare Scope wnat_scope.
    Delimit Scope wnat_scope with wnat.
  End Scopes.
  Module Export Notations.
    Export Scopes.
    Number Notation wnat of_uint to_uint (abstract after 4999) : wnat_scope.
  End Notations.
  Set Printing Coercions.
  Check let v := 0%wnat in v : wnat.
  Check wrap O.
  Timeout 1 Check wrap (ack 4 4). (* should be instantaneous *)
End Test6.

Module Test6_2.
  Import Test6.Scopes.
  Check Test6.wrap 0.
  Import Test6.Notations.
  Check let v := 0%wnat in v : Test6.wnat.
End Test6_2.

Module Test7.
  Local Set Primitive Projections.
  Record wuint := wrap { unwrap : Number.uint }.
  Declare Scope wuint_scope.
  Delimit Scope wuint_scope with wuint.
  Number Notation wuint wrap unwrap : wuint_scope.
  Check let v := 0%wuint in v : wuint.
  Check let v := 1%wuint in v : wuint.
End Test7.

Module Test8.
  Local Set Primitive Projections.
  Record wuint := wrap { unwrap : Number.uint }.
  Declare Scope wuint8_scope.
  Declare Scope wuint8'_scope.
  Delimit Scope wuint8_scope with wuint8.
  Delimit Scope wuint8'_scope with wuint8'.
  Section with_var.
    Context (dummy : unit).
    Definition wrap' := let __ := dummy in wrap.
    Definition unwrap' := let __ := dummy in unwrap.
    Number Notation wuint wrap' unwrap' : wuint8_scope.
    Check let v := 0%wuint8 in v : wuint.
  End with_var.
  Check let v := 0%wuint8 in v : nat.
  Fail Check let v := 0%wuint8 in v : wuint.
  Compute wrap (Nat.to_num_uint 0).

  Notation wrap'' := wrap.
  Notation unwrap'' := unwrap.
  Number Notation wuint wrap'' unwrap'' : wuint8'_scope.
  Check let v := 0%wuint8' in v : wuint.
End Test8.

Module Test9.
  Declare Scope wuint9_scope.
  Declare Scope wuint9'_scope.
  Delimit Scope wuint9_scope with wuint9.
  Delimit Scope wuint9'_scope with wuint9'.
  Section with_let.
    Local Set Primitive Projections.
    Record wuint := wrap { unwrap : Number.uint }.
    Let wrap' := wrap.
    Let unwrap' := unwrap.
    Local Notation wrap'' := wrap.
    Local Notation unwrap'' := unwrap.
    Number Notation wuint wrap' unwrap' : wuint9_scope.
    Check let v := 0%wuint9 in v : wuint.
    Number Notation wuint wrap'' unwrap'' : wuint9'_scope.
    Check let v := 0%wuint9' in v : wuint.
  End with_let.
  Check let v := 0%wuint9 in v : nat.
  Fail Check let v := 0%wuint9 in v : wuint.
End Test9.

Module Test10.
  (* Test that it is only a warning to add abstract after to an optional parsing function *)
  Definition to_uint (v : unit) := Nat.to_num_uint 0.
  Definition of_uint (v : Number.uint) := match Nat.of_num_uint v with O => Some tt | _ => None end.
  Definition of_any_uint (v : Number.uint) := tt.
  Declare Scope unit_scope.
  Declare Scope unit2_scope.
  Delimit Scope unit_scope with unit.
  Delimit Scope unit2_scope with unit2.
  Number Notation unit of_uint to_uint (abstract after 0) : unit_scope.
  Local Set Warnings Append "+abstract-large-number-no-op".
  (* Check that there is actually a warning here *)
  Fail Number Notation unit of_uint to_uint (abstract after 0) : unit2_scope.
  (* Check that there is no warning here *)
  Number Notation unit of_any_uint to_uint (abstract after 0) : unit2_scope.
End Test10.

Module Test12.
  (* Test for number notations on context variables *)
  Declare Scope test12_scope.
  Delimit Scope test12_scope with test12.
  Section test12.
    Context (to_uint : unit -> Number.uint) (of_uint : Number.uint -> unit).

    Number Notation unit of_uint to_uint : test12_scope.
    Check let v := 1%test12 in v : unit.
  End test12.
End Test12.

Module Test13.
  (* Test for number notations on notations which do not denote references *)
  Declare Scope test13_scope.
  Declare Scope test13'_scope.
  Declare Scope test13''_scope.
  Delimit Scope test13_scope with test13.
  Delimit Scope test13'_scope with test13'.
  Delimit Scope test13''_scope with test13''.
  Definition to_uint (x y : unit) : Number.uint := Nat.to_num_uint O.
  Definition of_uint (x : Number.uint) : unit := tt.
  Definition to_uint_good := to_uint tt.
  Notation to_uint' := (to_uint tt).
  Notation to_uint'' := (to_uint _).
  Number Notation unit of_uint to_uint_good : test13_scope.
  Check let v := 0%test13 in v : unit.
  Fail Number Notation unit of_uint to_uint' : test13'_scope.
  Fail Check let v := 0%test13' in v : unit.
  Fail Number Notation unit of_uint to_uint'' : test13''_scope.
  Fail Check let v := 0%test13'' in v : unit.
End Test13.

Module Test14.
  (* Test that number notations follow [Import], not [Require], and
     also test that [Local Number Notation]s do not escape modules
     nor sections. *)
  Declare Scope test14_scope.
  Declare Scope test14'_scope.
  Declare Scope test14''_scope.
  Declare Scope test14'''_scope.
  Delimit Scope test14_scope with test14.
  Delimit Scope test14'_scope with test14'.
  Delimit Scope test14''_scope with test14''.
  Delimit Scope test14'''_scope with test14'''.
  Module Inner.
    Definition to_uint (x : unit) : Number.uint := Nat.to_num_uint O.
    Definition of_uint (x : Number.uint) : unit := tt.
    Local Number Notation unit of_uint to_uint : test14_scope.
    Global Number Notation unit of_uint to_uint : test14'_scope.
    Check let v := 0%test14 in v : unit.
    Check let v := 0%test14' in v : unit.
  End Inner.
  Fail Check let v := 0%test14 in v : unit.
  Fail Check let v := 0%test14' in v : unit.
  Import Inner.
  Fail Check let v := 0%test14 in v : unit.
  Check let v := 0%test14' in v : unit.
  Section InnerSection.
    Definition to_uint (x : unit) : Number.uint := Nat.to_num_uint O.
    Definition of_uint (x : Number.uint) : unit := tt.
    Local Number Notation unit of_uint to_uint : test14''_scope.
    Fail Global Number Notation unit of_uint to_uint : test14'''_scope.
    Check let v := 0%test14'' in v : unit.
    Fail Check let v := 0%test14''' in v : unit.
  End InnerSection.
  Fail Check let v := 0%test14'' in v : unit.
  Fail Check let v := 0%test14''' in v : unit.
End Test14.

Module Test15.
  (** Test module include *)
  Declare Scope test15_scope.
  Delimit Scope test15_scope with test15.
  Module Inner.
    Definition to_uint (x : unit) : Number.uint := Nat.to_num_uint O.
    Definition of_uint (x : Number.uint) : unit := tt.
    Number Notation unit of_uint to_uint : test15_scope.
    Check let v := 0%test15 in v : unit.
  End Inner.
  Module Inner2.
    Include Inner.
    Check let v := 0%test15 in v : unit.
  End Inner2.
  Import Inner Inner2.
  Check let v := 0%test15 in v : unit.
End Test15.

Module Test16.
  (** Test functors *)
  Declare Scope test16_scope.
  Delimit Scope test16_scope with test16.
  Module Type A.
    Axiom T : Set.
    Axiom t : T.
  End A.
  Module F (a : A).
    Inductive Foo := foo (_ : a.T).
    Definition to_uint (x : Foo) : Number.uint := Nat.to_num_uint O.
    Definition of_uint (x : Number.uint) : Foo := foo a.t.
    Global Number Notation Foo of_uint to_uint : test16_scope.
    Check let v := 0%test16 in v : Foo.
  End F.
  Module a <: A.
    Definition T : Set := unit.
    Definition t : T := tt.
  End a.
  Module Import f := F a.
  (** Ideally this should work, but it should definitely not anomaly *)
  Fail Check let v := 0%test16 in v : Foo.
End Test16.

Require Import PrimInt63.
Module Test17.
  (** Test uint63 *)
  Declare Scope test17_scope.
  Declare Scope test17_scope.
  Delimit Scope test17_scope with test17.
  Local Set Primitive Projections.
  Record myint63 := of_int { to_int : int }.
  Definition parse x :=
    match x with Pos x => Some (of_int x) | Neg _ => None end.
  Definition print x := Pos (to_int x).
  Number Notation myint63 parse print : test17_scope.
  Check let v := 0%test17 in v : myint63.
End Test17.

Module Test18.
  (** Test https://github.com/coq/coq/issues/9840 *)
  Record Q := { num : nat ; den : nat ; reduced : Nat.gcd num den = 1 }.
  Declare Scope Q_scope.
  Delimit Scope Q_scope with Q.

  Definition nat_eq_dec (x y : nat) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition transparentify {A} (D : {A} + {not A}) (H : A) : A :=
    match D with
    | left pf => pf
    | right npf => match npf H with end
    end.

  Axiom gcd_good : forall x, Nat.gcd x 1 = 1.

  Definition Q_of_nat (x : nat) : Q := {| num := x ; den := 1 ; reduced := transparentify (nat_eq_dec _ _) (gcd_good _) |}.
  Definition nat_of_Q (x : Q) : option nat
    := if Nat.eqb x.(den) 1 then Some (x.(num)) else None.
  Definition Q_of_uint (x : Number.uint) : Q := Q_of_nat (Nat.of_num_uint x).
  Definition uint_of_Q (x : Q) : option Number.uint
    := option_map Nat.to_num_uint (nat_of_Q x).

  Number Notation Q Q_of_uint uint_of_Q : Q_scope.

  Check let v := 0%Q in v : Q.
  Check let v := 1%Q in v : Q.
  Check let v := 2%Q in v : Q.
  Check let v := 3%Q in v : Q.
  Check let v := 4%Q in v : Q.
  Compute let v := 0%Q in (num v, den v).
  Compute let v := 1%Q in (num v, den v).
  Compute let v := 2%Q in (num v, den v).
  Compute let v := 3%Q in (num v, den v).
  Compute let v := 4%Q in (num v, den v).
End Test18.

Require Import Stdlib.Lists.ListDef.
Require Import BinNums IntDef.
Module Test19.
  (** Test another thing related to https://github.com/coq/coq/issues/9840 *)
  Record Zlike := { summands : list Z }.
  Declare Scope Zlike_scope.
  Delimit Scope Zlike_scope with Zlike.

  Section Fold_Right_Recursor.
    Variables (A : Type) (B : Type).
    Variable f : B -> A -> A.
    Variable a0 : A.

    Fixpoint fold_right (l:list B) : A :=
      match l with
      | nil => a0
      | cons b t => f b (fold_right t)
      end.
    End Fold_Right_Recursor.

  Definition Z_of_Zlike (x : Zlike) := fold_right _ _ Z.add Z0 (summands x).
  Definition Zlike_of_Z (x : Z) := {| summands := cons x nil |}.

  Number Notation Zlike Zlike_of_Z Z_of_Zlike : Zlike_scope.

  Check let v := (-1)%Zlike in v : Zlike.
  Check let v := 0%Zlike in v : Zlike.
  Check let v := 1%Zlike in v : Zlike.
  Check let v := 2%Zlike in v : Zlike.
  Check let v := 3%Zlike in v : Zlike.
  Check let v := 4%Zlike in v : Zlike.
  Check {| summands := cons (Zpos xH) (cons (Zpos (xO xH)) (cons (Zneg xH) nil)) |}.
  Check {| summands := nil |}.
End Test19.

Module Test20.
  (** Test Sorts *)
  Local Set Universe Polymorphism.
  Inductive known_type : Type -> Type :=
  | prop : known_type Prop
  | set : known_type Set
  | type : known_type Type
  | zero : known_type Empty_set
  | one : known_type unit
  | two : known_type bool.

  Existing Class known_type.
  #[global]
  Existing Instances zero one two prop.
  #[global]
  Existing Instance set | 2.
  #[global]
  Existing Instance type | 4.

  Record > ty := { t : Type ; kt : known_type t }.

  Definition ty_of_uint (x : Number.uint) : option ty
    := match Nat.of_num_uint x with
       | 0 => @Some ty zero
       | 1 => @Some ty one
       | 2 => @Some ty two
       | 3 => @Some ty prop
       | 4 => @Some ty set
       | 5 => @Some ty type
       | _ => None
       end.
  Definition uint_of_ty (x : ty) : Number.uint
    := Nat.to_num_uint match kt x with
                   | prop => 3
                   | set => 4
                   | type => 5
                   | zero => 0
                   | one => 1
                   | two => 2
                   end.

  Declare Scope kt_scope.
  Delimit Scope kt_scope with kt.

  Number Notation ty ty_of_uint uint_of_ty : kt_scope.

  Check let v := 0%kt in v : ty.
  Check let v := 1%kt in v : ty.
  Check let v := 2%kt in v : ty.
  Check let v := 3%kt in v : ty.
  Check let v := 4%kt in v : ty.
  Check let v := 5%kt in v : ty.
  Fail Check let v := 6%kt in v : ty.
  Eval cbv in (_ : known_type Empty_set) : ty.
  Eval cbv in (_ : known_type unit) : ty.
  Eval cbv in (_ : known_type bool) : ty.
  Eval cbv in (_ : known_type Prop) : ty.
  Eval cbv in (_ : known_type Set) : ty.
  Eval cbv in (_ : known_type Type) : ty.
  Local Set Printing All.
  Check let v := 0%kt in v : ty.
  Check let v := 1%kt in v : ty.
  Check let v := 2%kt in v : ty.
  Check let v := 3%kt in v : ty.
  Check let v := 4%kt in v : ty.
  Check let v := 5%kt in v : ty.
End Test20.

Module Test21.

  Check 00001.
  Check 1_000.

End Test21.

Module Test22.

Notation "0" := False.
Notation "+0" := true.
Notation "-0" := false.
Notation "00" := (0%nat, 0%nat).
Check 0.
Check +0.
Check -0.
Check 00.

Notation "1000" := True.
Notation "1_000" := (cons 1 nil).
Check 1000.
Check 1_000.

(* To do: preserve parsing of -0:
Require Import ZArith.
Check (-0)%Z.
*)

End Test22.

(* Test the via ... mapping ... option *)
Module Test23.

Inductive sum (A : Set) (B : Set) : Set := pair : A -> B -> sum A B.

Inductive I :=
| Iempty : I
| Iunit : I
| Isum : I -> I -> I.

Definition of_uint (x : Number.uint) : I :=
  let fix f n :=
      match n with
      | O => Iempty
      | S O => Iunit
      | S n => Isum Iunit (f n)
      end in
  f (Nat.of_num_uint x).

Definition to_uint (x : I) : Number.uint :=
  let fix f i :=
      match i with
      | Iempty => O
      | Iunit => 1
      | Isum i1 i2 => f i1 + f i2
      end in
  Nat.to_num_uint (f x).

Notation nSet := (Set) (only parsing).  (* needed as a reference is expected in Number Notation and Set is syntactically not a reference *)
Number Notation nSet of_uint to_uint (via I
  mapping [Empty_set => Iempty, unit => Iunit, sum => Isum])
  : type_scope.

Local Open Scope type_scope.

Check Empty_set.
Check unit.
Check sum unit unit.
Check sum unit (sum unit unit).
Set Printing All.
Check 0.
Check 1.
Check 2.
Check 3.
Unset Printing All.

(* Test error messages *)

(* missing constructor *)
Fail Number Notation nSet of_uint to_uint (via I
  mapping [Empty_set => Iempty, unit => Iunit])
  : type_scope.

(* duplicate constructor *)
Fail Number Notation nSet of_uint to_uint (via I
  mapping [Empty_set => Iempty, unit => Iunit, sum => Isum, unit => Iunit])
  : type_scope.

(* not an inductive *)
Fail Number Notation nSet of_uint to_uint (via add
  mapping [Empty_set => Iempty, unit => Iunit, sum => Isum])
  : type_scope.

(* not a constructor *)
Fail Number Notation nSet of_uint to_uint (via I
  mapping [Empty_set => Iempty, unit => add, sum => Isum])
  : type_scope.

(* put constructors of the wrong inductive ~~> missing constructors *)
Fail Number Notation nSet of_uint to_uint (via I
  mapping [Empty_set => O, unit => S])
  : type_scope.

(* Test warnings *)

(* wrong type *)
Inductive I' :=
| I'empty : I'
| I'unit : I'
| I'sum : I -> I' -> I'.
Definition of_uint' (x : Number.uint) : I' := I'empty.
Definition to_uint' (x : I') : Number.uint := Number.UIntDecimal Decimal.Nil.
Number Notation nSet of_uint' to_uint' (via I'
  mapping [Empty_set => I'empty, unit => I'unit, sum => I'sum])
  : type_scope.

(* wrong type mapping *)
Number Notation nSet of_uint to_uint (via I
  mapping [Empty_set => Iempty, O => Iunit, sum => Isum])
  : type_scope.

(* incompatibility with abstract (but warning is fine) *)
Fail Number Notation nSet of_uint to_uint (via I
  mapping [Empty_set => Iempty, unit => Iunit, sum => Isum],
  abstract after 11)
  : type_scope.
Number Notation nSet of_uint to_uint (via I
  mapping [Empty_set => Iempty, unit => Iunit, sum => Isum],
  warning after 12)
  : type_scope.

(* Test reduction of types when building the notation *)

Inductive foo := bar : match (true <: bool) with true => nat -> foo | false => True end.

Definition foo_of_uint (x : Number.uint) : foo := bar (Nat.of_num_uint x).
Definition foo_to_uint (x : foo) : Number.uint :=
  match x with
  | bar x => Nat.to_num_uint x
  end.

Number Notation foo foo_of_uint foo_to_uint (via foo mapping [bar => bar])
  : type_scope.

Inductive foo' := bar' : let n := nat in n -> foo'.

Definition foo'_of_uint (x : Number.uint) : foo' := bar' (Nat.of_num_uint x).
Definition foo'_to_uint (x : foo') : Number.uint :=
  match x with
  | bar' x => Nat.to_num_uint x
  end.

Number Notation foo' foo'_of_uint foo'_to_uint (via foo' mapping [bar' => bar'])
  : type_scope.

Inductive foo'' := bar'' : (nat <: Type) -> (foo'' <: Type).

Definition foo''_of_uint (x : Number.uint) : foo'' := bar'' (Nat.of_num_uint x).
Definition foo''_to_uint (x : foo'') : Number.uint :=
  match x with
  | bar'' x => Nat.to_num_uint x
  end.

Number Notation foo'' foo''_of_uint foo''_to_uint (via foo'' mapping [bar'' => bar''])
  : type_scope.

End Test23.

(* Test the via ... mapping ... option with implicit arguments *)
Module Test24.

Inductive I :=
| I1 : I
| IS : I -> I.

Definition of_uint (x : Number.uint) : I :=
  let fix f n :=
      match n with
      | O => I1
      | S n => IS (f n)
      end in
  f (Nat.of_num_uint x).

Definition to_uint (x : I) : Number.uint :=
  let fix f i :=
      match i with
      | I1 => O
      | IS n => S (f n)
      end in
  Nat.to_num_uint (f x).

Local Open Scope type_scope.

Module Fin.
Inductive t : nat -> Set :=
|F1 : forall {n}, t (S n)
|FS : forall {n}, t n -> t (S n).
End Fin.

(* ignoring implicit arguments doesn't work *)
Number Notation Fin.t of_uint to_uint (via I
  mapping [Fin.F1 => I1, Fin.FS => IS])
  : type_scope.

Fail Check 1.

Number Notation Fin.t of_uint to_uint (via I
  mapping [[Fin.F1] => I1, [Fin.FS] => IS])
  : type_scope.

Check Fin.F1.
Check Fin.FS Fin.F1.
Check Fin.FS (Fin.FS Fin.F1).
Check Fin.FS (Fin.FS (Fin.FS Fin.F1)).
Check Fin.F1 : Fin.t 3.
Check Fin.FS Fin.F1 : Fin.t 3.
Check Fin.FS (Fin.FS Fin.F1) : Fin.t 3.
Fail Check Fin.FS (Fin.FS (Fin.FS Fin.F1)) : Fin.t 3.
Set Printing All.
Check 0.
Check 1.
Check 2.
Check 3.
Check 0 : Fin.t 3.
Check 1 : Fin.t 3.
Check 2 : Fin.t 3.
Fail Check 3 : Fin.t 3.
Unset Printing All.

End Test24.

(* Test number notations for parameterized inductives *)
Module Test25.

Definition of_uint (u : Number.uint) : list unit :=
  let fix f n :=
    match n with
    | O => nil
    | S n => cons tt (f n)
    end in
  f (Nat.of_num_uint u).

Definition to_uint (l : list unit) : Number.uint :=
  let fix f n :=
    match n with
    | nil => O
    | cons tt l => S (f l)
    end in
  Nat.to_num_uint (f l).

Notation listunit := (list unit) (only parsing).
Number Notation listunit of_uint to_uint : nat_scope.

Check 0.
Check 1.
Check 2.

Check cons tt (cons tt nil).
Check cons O (cons O nil).  (* printer not called on list nat *)

(* inductive with multiple parameters that are not the first
   parameters and not in the same order for each constructor *)
Inductive Ip : Type -> Type -> Type :=
| Ip0 : forall T T', nat -> Ip T T'
| Ip1 : forall T' T, nat -> Ip T T'
| Ip2 : forall T, nat -> forall T', Ip T T'
| Ip3 : nat -> forall T T', Ip T T'.

Definition Ip_of_uint (u : Number.uint) : option (Ip nat bool) :=
  let f n :=
    match n with
    | O => Some (Ip0 nat bool O)
    | S O => Some (Ip1 bool nat (S O))
    | S (S O) => Some (Ip2 nat (S (S O)) bool)
    | S (S (S O)) => Some (Ip3 (S (S (S O))) nat bool)
    | _ => None
    end in
  f (Nat.of_num_uint u).

Definition Ip_to_uint (l : Ip nat bool) : Number.uint :=
  let f n :=
    match n with
    | Ip0 _ _ n => n
    | Ip1 _ _ n => n
    | Ip2 _ n _ => n
    | Ip3 n _ _ => n
    end in
  Nat.to_num_uint (f l).

Notation Ip_nat_bool := (Ip nat bool) (only parsing).
Number Notation Ip_nat_bool Ip_of_uint Ip_to_uint : nat_scope.

Check 0.
Check 1.
Check 2.
Check 3.
Check Ip0 nat bool (S O).
Check Ip1 bool nat (S O).
Check Ip2 nat (S O) bool.
Check Ip3 (S O) nat bool.
Check Ip0 nat nat (S O).  (* not printed *)
Check Ip0 bool bool (S O).  (* not printed *)
Check Ip1 nat nat (S O).  (* not printed *)
Check Ip3 (S O) nat nat.  (* not printed *)
Set Printing All.
Check 0.
Check 1.
Check 2.
Check 3.
Unset Printing All.

Notation eqO := (eq _ O) (only parsing).
Definition eqO_of_uint (x : Number.uint) : eqO := eq_refl O.
Definition eqO_to_uint (x : O = O) : Number.uint :=
  match x with
  | eq_refl _ => Nat.to_num_uint O
  end.
Number Notation eqO eqO_of_uint eqO_to_uint : nat_scope.

Check 42.
Check eq_refl (S O).  (* doesn't match eq _ O, printer not called *)
Check eq_refl O. (* matches eq _ O, printer called *)
Check eq_refl (id O). (* doesn't match eq _ O, printer not called *)

Notation eq_ := (eq _ _) (only parsing).
Number Notation eq_ eqO_of_uint eqO_to_uint : nat_scope.

Check eq_refl (S O).  (* matches eq _ _, printer called, but type incorrect *)
Check eq_refl O. (* matches eq _ _, printer called *)
Check eq_refl (id O). (* matches eq _ _, but contains a global constant, printer not called *)

Inductive extra_list : Type -> Type :=
| nil (n : nat) (v : Type) : extra_list v
| cons (n : nat) (t : Type) (x : t) : extra_list t -> extra_list t.

Definition extra_list_unit_of_uint (x : Number.uint) : extra_list unit :=
  let fix f n :=
      match n with
      | O => nil O unit
      | S n => cons O unit tt (f n)
      end in
  f (Nat.of_num_uint x).

Definition extra_list_unit_to_uint (x : extra_list unit) : Number.uint :=
  let fix f T (x : extra_list T) :=
      match x with
      | nil _ _ => O
      | cons _ T _ x => S (f T x)
      end in
  Nat.to_num_uint (f unit x).

Notation extra_list_unit := (extra_list unit).
Number Notation extra_list_unit
        extra_list_unit_of_uint extra_list_unit_to_uint : nat_scope.

Check 2.
Set Printing All.
Check 2.
Unset Printing All.

End Test25.

(* Test the via ... mapping ... option with let-binders, beta-redexes, delta-redexes, etc *)
Module Test26.

Inductive sum (A : Set) (B : Set) : Set := pair : A -> B -> sum A B.

Inductive I (dummy:=O) :=
| Iempty : let v := I in id v
| Iunit : (fun x => x) I
| Isum : let v := I in (fun A B => A -> B) (let v' := v in v') (forall x : match O with O => I | _ => Empty_set end, let dummy2 := x in I).

Definition of_uint (x : (fun x => let v := I in x) Number.uint) : (fun x => let v := I in x) I :=
  let fix f n :=
      match n with
      | O => Iempty
      | S O => Iunit
      | S n => Isum Iunit (f n)
      end in
  f (Nat.of_num_uint x).

Definition to_uint (x : (fun x => let v := x in v) I) : match O with O => Number.uint | _ => Empty_set end :=
  let fix f i :=
      match i with
      | Iempty => O
      | Iunit => 1
      | Isum i1 i2 => f i1 + f i2
      end in
  Nat.to_num_uint (f x).

Notation nSet := (Set) (only parsing).  (* needed as a reference is expected in Number Notation and Set is syntactically not a reference *)
Number Notation nSet of_uint to_uint (via I
  mapping [Empty_set => Iempty, unit => Iunit, sum => Isum])
  : type_scope.

Local Open Scope type_scope.

Check Empty_set.
Check unit.
Check sum unit unit.
Check sum unit (sum unit unit).
Set Printing All.
Check 0.
Check 1.
Check 2.
Check 3.
Unset Printing All.
End Test26.

(* Test the via ... mapping ... option with implicit arguments with let binders, etc *)
Module Test27.

Module Fin.
Inductive t0 (x:=O) :=
with
  t (x:=O) : forall y : nat, let z := y in Set :=
| F1 (y:=O) {n} : match y with O => t (S n) | _ => Empty_set end
| FS (y:=x) {n} (v:=n+y) (m:=n) : id (match y with O => id (t n) | _ => Empty_set end -> (fun x => x) t (S m))
with t' (x:=O) := .
End Fin.

Inductive I (dummy:=O) :=
| I1 : I
| IS : let x := I in id x -> I.

Definition of_uint (x : Number.uint) : I :=
  let fix f n :=
      match n with
      | O => I1
      | S n => IS (f n)
      end in
  f (Nat.of_num_uint x).

Definition to_uint (x : I) : Number.uint :=
  let fix f i :=
      match i with
      | I1 => O
      | IS n => S (f n)
      end in
  Nat.to_num_uint (f x).

Local Open Scope type_scope.

Number Notation Fin.t of_uint to_uint (via I
  mapping [[Fin.F1] => I1, [Fin.FS] => IS])
  : type_scope.

Check Fin.F1.
Check Fin.FS Fin.F1.
Check Fin.FS (Fin.FS Fin.F1).
Check Fin.FS (Fin.FS (Fin.FS Fin.F1)).
Check Fin.F1 : Fin.t 3.
Check Fin.FS Fin.F1 : Fin.t 3.
Check Fin.FS (Fin.FS Fin.F1) : Fin.t 3.
Fail Check Fin.FS (Fin.FS (Fin.FS Fin.F1)) : Fin.t 3.
Set Printing All.
Check 0.
Check 1.
Check 2.
Check 3.
Check 0 : Fin.t 3.
Check 1 : Fin.t 3.
Check 2 : Fin.t 3.
Fail Check 3 : Fin.t 3.
Unset Printing All.

End Test27.

Module Test28.
Module Fin.
Inductive t : nat -> Set :=
| F1 {n : (nat : Set)} : (t (S n) : Set)
| FS {n : (nat : Set)} : (t n : Set) -> (t (S n) : Set).
End Fin.

Inductive I :=
| I1 : I
| IS : I -> I.

Definition of_uint (x : Number.uint) : I :=
  let fix f n :=
      match n with
      | O => I1
      | S n => IS (f n)
      end in
  f (Nat.of_num_uint x).

Definition to_uint (x : I) : Number.uint :=
  let fix f i :=
      match i with
      | I1 => O
      | IS n => S (f n)
      end in
  Nat.to_num_uint (f x).

Local Open Scope type_scope.

Number Notation Fin.t of_uint to_uint (via I
  mapping [[Fin.F1] => I1, [Fin.FS] => IS])
  : type_scope.

Check Fin.F1.
Check Fin.FS Fin.F1.
Check Fin.FS (Fin.FS Fin.F1).
Check Fin.FS (Fin.FS (Fin.FS Fin.F1)).
Check Fin.F1 : Fin.t 3.
Check Fin.FS Fin.F1 : Fin.t 3.
Check Fin.FS (Fin.FS Fin.F1) : Fin.t 3.
Fail Check Fin.FS (Fin.FS (Fin.FS Fin.F1)) : Fin.t 3.
Set Printing All.
Check 0.
Check 1.
Check 2.
Check 3.
Check 0 : Fin.t 3.
Check 1 : Fin.t 3.
Check 2 : Fin.t 3.
Fail Check 3 : Fin.t 3.
Unset Printing All.

End Test28.

Require Import PrimFloat.

Module Test29.

Definition printer (x : float_wrapper) : Number.uint :=
  if get_sign (float_wrap x) then Number.UIntDecimal (Decimal.D1 Decimal.Nil)
  else Number.UIntDecimal (Decimal.D0 Decimal.Nil).

Definition parser (x : float) : float := x.

Number Notation float parser printer : float_scope.

Check 12%float.
Check (-12)%float.
Check infinity.
Check neg_infinity.
Check nan.

End Test29.

Module Test30.

Inductive nunit : nat -> Type := NUnit n : nunit n.

Definition printer2 (x : nunit 2) : Number.uint :=
  Number.UIntDecimal (Decimal.D2 Decimal.Nil).

Definition parser2 (_ : Number.uint) : nunit 2 := NUnit 2.

Notation nunit2 := (nunit 2).
Number Notation nunit2 parser2 printer2 : nat_scope.

Check 2.
Check NUnit (S (S O)).
Check NUnit (S (S (S O))).
Check NUnit O.

Check NUnit (S O + S O).
(* doesn't print as 2, because (S O + S O) is not syntactically equal
   to (S (S O)), we could want to use a convertibility test rather
   than a syntactic equality, but this could be more costly *)

End Test30.

Module Bug10878.

Definition Zto_pos_opt (v : Z) : option positive
  := match v with
     | Zpos v => Some v
     | _ => None
     end.
Declare Scope mypos_scope.
Declare Scope mypos_scope2.
Number Notation positive Zto_pos_opt Zpos : mypos_scope. (* success *)
Arguments option {_}.
Number Notation positive Zto_pos_opt Zpos : mypos_scope2. (* was failing *)

End Bug10878.
