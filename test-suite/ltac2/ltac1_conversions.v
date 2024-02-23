Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Got (Std.intro_pattern option) ].

(* we can't return a value from a ltac1 notation so we get it out using Control.zero *)
Tactic Notation "foo" simple_intropattern(x) :=
  let f := ltac2:(y |- Control.zero (Got (Ltac1.to_intro_pattern y))) in
  f x.

Ltac2 Notation "ipat" x(intropattern) := x.

Goal nat. (* we need an open goal because ltac1 auto focuses *)
  Ltac2 Eval match Control.case (fun () => ltac1:(foo y%nat)) with
    | Err (Got (Some (Std.IntroAction
                         (Std.IntroApplyOn
                            c
                            (Std.IntroNaming (Std.IntroIdentifier id)))))) =>
        Control.assert_true (Ident.equal id @y);
        match! c () with
        | nat => ()
        | _ => Control.throw Assertion_failure
        end
    | Val _ | Err _ => Control.throw Assertion_failure
    end.

  Ltac2 Eval match Ltac1.to_intro_pattern (Ltac1.of_intro_pattern (ipat ?w)) with
    | Some (Std.IntroNaming (Std.IntroFresh id)) => Control.assert_true (Ident.equal id @w)
    | _ => Control.throw Assertion_failure
    end.

  Ltac2 Eval
    ltac1:(
      let n := numgoals in
      let t := ltac2:(n |-
        match Ltac1.to_int n with
        | Some 1 => ()
        | _ => Control.throw Assertion_failure
        end)
      in
      t n).

  Fail Ltac2 Eval
    ltac1:(
      let n := numgoals in
      let t := ltac2:(n |-
        match Ltac1.to_int n with
        | None => ()
        | _ => Control.throw Assertion_failure
        end)
      in
      t n).

  Ltac2 Eval
   ltac1:(n |- do n assert False; [| | |]) (Ltac1.of_int 2).

Abort.
