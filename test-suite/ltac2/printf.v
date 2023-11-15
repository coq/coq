Require Import Ltac2.Ltac2.
Require Import Ltac2.Printf.

(* Check that the arguments have type unit *)
Ltac2 ignore (x : unit) := ().

Ltac2 dummy (_ : unit) (_ : int) := Message.of_string "dummy".

(** Simple test for all specifications *)

Ltac2 Eval ignore (printf "%i" 42).
Ltac2 Eval ignore (printf "%s" "abc").
Ltac2 Eval ignore (printf "%I" @Foo).
Ltac2 Eval ignore (printf "%t" '(1 + 1 = 0)).
Ltac2 Eval ignore (printf "%%").
Ltac2 Eval ignore (printf "%a" dummy 18).

(** More complex tests *)

Ltac2 Eval ignore (printf "%I foo%a bar %s" @ok dummy 18 "yes").

Ltac2 Eval Message.print (fprintf "%I foo%a bar %s" @ok dummy 18 "yes").

(** Failure tests *)

Fail Ltac2 Eval printf "%i" "foo".
Fail Ltac2 Eval printf "%s" 0.
Fail Ltac2 Eval printf "%I" "foo".
Fail Ltac2 Eval printf "%t" "foo".
Fail Ltac2 Eval printf "%a" (fun _ _ => ()).
Fail Ltac2 Eval printf "%a" (fun _ i => Message.of_int i) "foo".

Import Message.

Ltac2 print_if b fmt :=
  if b then Format.kfprintf Message.to_string fmt
  else Format.ikfprintf Message.to_string (Message.of_string "") fmt.

Ltac2 Notation "print_if" b(tactic(0)) fmt(format) := print_if b fmt.

Ltac2 Eval Control.assert_true (String.equal "hello friend" (print_if true "hello %s" "friend")).

Ltac2 Eval Control.assert_true (String.equal "" (print_if false "hello %s" "friend")).

Fail Ltac2 Eval print_if true "%a" (fun _ => Control.throw Assertion_failure) ().

(* ikfprintf doesn't run the closure *)
Ltac2 Eval print_if false "%a" (fun _ => Control.throw Assertion_failure) ().
