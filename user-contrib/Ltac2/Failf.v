(* printf-style formatted failures gfail/fail/anomaly *)

Require Import Ltac2.Ltac2.

(* "global fail", i.e. without first focusing on a goal.
   Advantage over normal `fail` is that it can return any 'a instead of unit *)
Ltac2 gfail0 () := Control.zero (Tactic_failure None).
Ltac2 gfail_with_fmt fmt :=
  Message.Format.kfprintf (fun msg => Control.zero (Tactic_failure (Some msg))) fmt.

Ltac2 Notation "gfail" fmt(format) := gfail_with_fmt fmt.
Ltac2 Notation "gfail" := gfail0 ().

(* Unfortunately, since `fail` auto-focuses, we can't pass it constr arguments,
   because that would require focusing first, so it would have to be thunked constrs,
   which doesn't work nicely either, see https://github.com/coq/coq/issues/17463.
   So for now, we only support simple string messages. *)
Ltac2 fail_with_string (s : string) : unit :=
  Control.enter (fun _ => Control.zero (Tactic_failure (Some (Message.of_string s)))).

Ltac2 Notation "fail" s(tactic) := fail_with_string s.
Ltac2 Notation "fail" := fail0 ().

Ltac2 Type exn ::= [ Anomaly (message option) ].

Ltac2 anomaly0 () := Control.throw (Anomaly None).
Ltac2 anomaly_with_fmt fmt :=
  Message.Format.kfprintf (fun msg => Control.throw (Anomaly (Some msg))) fmt.

Ltac2 Notation "anomaly" fmt(format) := anomaly_with_fmt fmt.
Ltac2 Notation "anomaly" := anomaly0 ().
