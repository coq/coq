Require Import Ltac2.Ltac2.

Set Warnings "+deprecated".

Ltac2 Type foo := [
  | #[deprecated(since="bar")] Bar
  | #[deprecated(since="baz")] Baz
  ].

(* can still use foo even if its constructors are deprecated *)
Ltac2 diagonal (x:foo) := (x, x).

(* deprecated constructors warn when using them to construct values *)
Fail Ltac2 nobuild := Bar.

(* deprecated constructors also warn when matching on them *)
Fail Ltac2 nomatch x :=
  match x with
  | Bar => 0
  | _ => 1
  end.

(* warnings are per constructor so we can disable one and not the other
   (because this test uses difference "since" annotations) *)
Set Warnings "-deprecated-since-bar".

Fail Ltac2 nobuild := Baz.

Ltac2 build_warn_bar_disabled := Bar.

(* warnings are per constructor, so we still can't match on Baz *)
Fail Ltac2 nomatch x :=
  match x with
  | Baz => 0
  | _ => 1
  end.

(* but we can match on Bar with its warning disabled *)
Ltac2 match_warn_bar_disabled x :=
  match x with
  | Bar => 0
  | _ => 1
  end.

(* the warning is at intern time *)
Ltac2 Notation bar_nota := Bar.

Ltac2 Notation "isBar_nota" x(tactic) := match x with Bar => true | _ => false end.

Set Warnings "+deprecated-since-bar".

(* sanity check *)
Fail Ltac2 nobuild := Bar.

Ltac2 bar_def := bar_nota.

Ltac2 isBar_def x := isBar_nota x.

Ltac2 Eval Control.assert_true (isBar_def bar_def).

#[warnings="-deprecated-since-baz"]
  Ltac2 Eval Control.assert_false (isBar_def Baz).
