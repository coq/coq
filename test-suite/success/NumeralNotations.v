(* Test that we fail, rather than raising anomalies, on opaque terms during interpretation *)

(* https://github.com/coq/coq/pull/8064#discussion_r202497516 *)
Module Test1.
  Axiom hold : forall {A B C}, A -> B -> C.
  Definition opaque3 (x : Decimal.int) : Decimal.int := hold x (fix f (x : nat) : nat := match x with O => O | S n => S (f n) end).
  Numeral Notation Decimal.int opaque3 opaque3 : opaque_scope.
  Delimit Scope opaque_scope with opaque.
  Fail Check 1%opaque.
End Test1.

(* https://github.com/coq/coq/pull/8064#discussion_r202497990 *)
Module Test2.
  Axiom opaque4 : option Decimal.int.
  Definition opaque6 (x : Decimal.int) : option Decimal.int := opaque4.
  Numeral Notation Decimal.int opaque6 opaque6 : opaque_scope.
  Delimit Scope opaque_scope with opaque.
  Open Scope opaque_scope.
  Fail Check 1%opaque.
End Test2.

Module Test3.
  Inductive silly := SILLY (v : Decimal.uint) (f : forall A, A -> A).
  Definition to_silly (v : Decimal.uint) := SILLY v (fun _ x => x).
  Definition of_silly (v : silly) := match v with SILLY v _ => v end.
  Numeral Notation silly to_silly of_silly : silly_scope.
  Delimit Scope silly_scope with silly.
  Fail Check 1%silly.
End Test3.


Module Test4.
  Polymorphic NonCumulative Inductive punit := ptt.
  Polymorphic Definition pto_punit (v : Decimal.uint) : option punit := match Nat.of_uint v with O => Some ptt | _ => None end.
  Polymorphic Definition pto_punit_all (v : Decimal.uint) : punit := ptt.
  Polymorphic Definition pof_punit (v : punit) : Decimal.uint := Nat.to_uint 0.
  Definition to_punit (v : Decimal.uint) : option punit := match Nat.of_uint v with O => Some ptt | _ => None end.
  Definition of_punit (v : punit) : Decimal.uint := Nat.to_uint 0.
  Polymorphic Definition pto_unit (v : Decimal.uint) : option unit := match Nat.of_uint v with O => Some tt | _ => None end.
  Polymorphic Definition pof_unit (v : unit) : Decimal.uint := Nat.to_uint 0.
  Definition to_unit (v : Decimal.uint) : option unit := match Nat.of_uint v with O => Some tt | _ => None end.
  Definition of_unit (v : unit) : Decimal.uint := Nat.to_uint 0.
  Numeral Notation punit to_punit of_punit : pto.
  Numeral Notation punit pto_punit of_punit : ppo.
  Numeral Notation punit to_punit pof_punit : ptp.
  Numeral Notation punit pto_punit pof_punit : ppp.
  Numeral Notation unit to_unit of_unit : uto.
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
  Numeral Notation unit pto_unit of_unit : upo.
  Numeral Notation unit to_unit pof_unit : utp.
  Numeral Notation unit pto_unit pof_unit : upp.
  Delimit Scope upo with upo.
  Delimit Scope utp with utp.
  Delimit Scope upp with upp.
  Check let v := 0%upo in v : unit.
  Check let v := 0%utp in v : unit.
  Check let v := 0%upp in v : unit.

  Polymorphic Definition pto_punits := pto_punit_all@{Set}.
  Polymorphic Definition pof_punits := pof_punit@{Set}.
  Numeral Notation punit pto_punits pof_punits : ppps (abstract after 1).
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
  (* Check that numeral notations on enormous terms don't take forever to print/parse *)
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
  Definition to_uint (x : wnat) : Decimal.uint := Nat.to_uint x.
  Definition of_uint (x : Decimal.uint) : wnat := Nat.of_uint x.
  Module Export Scopes.
    Delimit Scope wnat_scope with wnat.
  End Scopes.
  Module Export Notations.
    Export Scopes.
    Numeral Notation wnat of_uint to_uint : wnat_scope (abstract after 5000).
  End Notations.
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
  Record wuint := wrap { unwrap : Decimal.uint }.
  Delimit Scope wuint_scope with wuint.
  Numeral Notation wuint wrap unwrap : wuint_scope.
  Check let v := 0%wuint in v : wuint.
  Check let v := 1%wuint in v : wuint.
End Test7.

Module Test8.
  Local Set Primitive Projections.
  Record wuint := wrap { unwrap : Decimal.uint }.
  Delimit Scope wuint8_scope with wuint8.
  Delimit Scope wuint8'_scope with wuint8'.
  Section with_var.
    Context (dummy : unit).
    Definition wrap' := let __ := dummy in wrap.
    Definition unwrap' := let __ := dummy in unwrap.
    Numeral Notation wuint wrap' unwrap' : wuint8_scope.
    Check let v := 0%wuint8 in v : wuint.
  End with_var.
  Check let v := 0%wuint8 in v : nat.
  Fail Check let v := 0%wuint8 in v : wuint.
  Compute wrap (Nat.to_uint 0).

  Notation wrap'' := wrap.
  Notation unwrap'' := unwrap.
  Numeral Notation wuint wrap'' unwrap'' : wuint8'_scope.
  Check let v := 0%wuint8' in v : wuint.
End Test8.

Module Test9.
  Delimit Scope wuint9_scope with wuint9.
  Delimit Scope wuint9'_scope with wuint9'.
  Section with_let.
    Local Set Primitive Projections.
    Record wuint := wrap { unwrap : Decimal.uint }.
    Let wrap' := wrap.
    Let unwrap' := unwrap.
    Local Notation wrap'' := wrap.
    Local Notation unwrap'' := unwrap.
    Numeral Notation wuint wrap' unwrap' : wuint9_scope.
    Check let v := 0%wuint9 in v : wuint.
    Numeral Notation wuint wrap'' unwrap'' : wuint9'_scope.
    Check let v := 0%wuint9' in v : wuint.
  End with_let.
  Check let v := 0%wuint9 in v : nat.
  Fail Check let v := 0%wuint9 in v : wuint.
End Test9.

Module Test10.
  (* Test that it is only a warning to add abstract after to an optional parsing function *)
  Definition to_uint (v : unit) := Nat.to_uint 0.
  Definition of_uint (v : Decimal.uint) := match Nat.of_uint v with O => Some tt | _ => None end.
  Definition of_any_uint (v : Decimal.uint) := tt.
  Delimit Scope unit_scope with unit.
  Delimit Scope unit2_scope with unit2.
  Numeral Notation unit of_uint to_uint : unit_scope (abstract after 1).
  Local Set Warnings Append "+abstract-large-number-no-op".
  (* Check that there is actually a warning here *)
  Fail Numeral Notation unit of_uint to_uint : unit2_scope (abstract after 1).
  (* Check that there is no warning here *)
  Numeral Notation unit of_any_uint to_uint : unit2_scope (abstract after 1).
End Test10.

Module Test11.
  (* Test that numeral notations don't work on proof-local variables, especially not ones containing evars *)
  Inductive unit11 := tt11.
  Delimit Scope unit11_scope with unit11.
  Goal True.
    evar (to_uint : unit11 -> Decimal.uint).
    evar (of_uint : Decimal.uint -> unit11).
    Fail Numeral Notation unit11 of_uint to_uint : uint11_scope.
    exact I.
    Unshelve.
    all: solve [ constructor ].
  Qed.
End Test11.

Module Test12.
  (* Test for numeral notations on context variables *)
  Delimit Scope test12_scope with test12.
  Section test12.
    Context (to_uint : unit -> Decimal.uint) (of_uint : Decimal.uint -> unit).

    Numeral Notation unit of_uint to_uint : test12_scope.
    Check let v := 1%test12 in v : unit.
  End test12.
End Test12.

Module Test13.
  (* Test for numeral notations on notations which do not denote references *)
  Delimit Scope test13_scope with test13.
  Delimit Scope test13'_scope with test13'.
  Delimit Scope test13''_scope with test13''.
  Definition to_uint (x y : unit) : Decimal.uint := Nat.to_uint O.
  Definition of_uint (x : Decimal.uint) : unit := tt.
  Definition to_uint_good := to_uint tt.
  Notation to_uint' := (to_uint tt).
  Notation to_uint'' := (to_uint _).
  Numeral Notation unit of_uint to_uint_good : test13_scope.
  Check let v := 0%test13 in v : unit.
  Fail Numeral Notation unit of_uint to_uint' : test13'_scope.
  Fail Check let v := 0%test13' in v : unit.
  Fail Numeral Notation unit of_uint to_uint'' : test13''_scope.
  Fail Check let v := 0%test13'' in v : unit.
End Test13.

Module Test14.
  (* Test that numeral notations follow [Import], not [Require], and
     also test that [Local Numeral Notation]s do not escape modules
     nor sections. *)
  Delimit Scope test14_scope with test14.
  Delimit Scope test14'_scope with test14'.
  Delimit Scope test14''_scope with test14''.
  Delimit Scope test14'''_scope with test14'''.
  Module Inner.
    Definition to_uint (x : unit) : Decimal.uint := Nat.to_uint O.
    Definition of_uint (x : Decimal.uint) : unit := tt.
    Local Numeral Notation unit of_uint to_uint : test14_scope.
    Global Numeral Notation unit of_uint to_uint : test14'_scope.
    Check let v := 0%test14 in v : unit.
    Check let v := 0%test14' in v : unit.
  End Inner.
  Fail Check let v := 0%test14 in v : unit.
  Fail Check let v := 0%test14' in v : unit.
  Import Inner.
  Fail Check let v := 0%test14 in v : unit.
  Check let v := 0%test14' in v : unit.
  Section InnerSection.
    Definition to_uint (x : unit) : Decimal.uint := Nat.to_uint O.
    Definition of_uint (x : Decimal.uint) : unit := tt.
    Local Numeral Notation unit of_uint to_uint : test14''_scope.
    Fail Global Numeral Notation unit of_uint to_uint : test14'''_scope.
    Check let v := 0%test14'' in v : unit.
    Fail Check let v := 0%test14''' in v : unit.
  End InnerSection.
  Fail Check let v := 0%test14'' in v : unit.
  Fail Check let v := 0%test14''' in v : unit.
End Test14.

Module Test15.
  (** Test module include *)
  Delimit Scope test15_scope with test15.
  Module Inner.
    Definition to_uint (x : unit) : Decimal.uint := Nat.to_uint O.
    Definition of_uint (x : Decimal.uint) : unit := tt.
    Numeral Notation unit of_uint to_uint : test15_scope.
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
  Delimit Scope test16_scope with test16.
  Module Type A.
    Axiom T : Set.
    Axiom t : T.
  End A.
  Module F (a : A).
    Inductive Foo := foo (_ : a.T).
    Definition to_uint (x : Foo) : Decimal.uint := Nat.to_uint O.
    Definition of_uint (x : Decimal.uint) : Foo := foo a.t.
    Global Numeral Notation Foo of_uint to_uint : test16_scope.
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
