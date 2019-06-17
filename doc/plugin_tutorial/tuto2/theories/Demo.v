From Tuto2 Require Import Loader.

(*** A no-op command ***)

Nothing.

(*** No-op commands with arguments ***)

(*
 * Terminal parameters:
 *)
Command With Some Terminal Parameters.
(* Command. *) (* does not parse *)

(*
 * A single non-terminal argument:
 *)
Pass 42.
(* Pass. *) (* does not parse *)
(* Pass True. *) (* does not parse *)
(* Pass 15 20. *) (* does not parse *)

(*
 * A list of non-terminal arguments:
 *)
Accept 100 200 300 400.
Accept.
Accept 2.

(*
 * A custom argument:
 *)
Foobar Foo.
Foobar Bar.

(*** Commands that give feedback ***)

(*
 * Simple feedback:
 *)
Is Everything Awesome.

(*** Storage and side effects ***)

(*
 * Local side effects:
 *)
Count.
Count.
Count.
(*
 * See Count.v for behavior in modules that import this one.
 *)

(*
 * Persistent side effects:
 *)
Count Persistent.
Count Persistent.
Count Persistent.
(*
 * See Count.v for behavior in modules that import this one.
 *)
