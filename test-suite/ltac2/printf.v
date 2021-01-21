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
