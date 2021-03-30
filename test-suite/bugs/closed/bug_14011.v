(** Test that Ltac2 Array.init doesn't compute the first argument twice, and has the correct asymptotics when nested *)
Require Import Ltac2.Ltac2.

(** Non-performance-based test *)
Ltac2 foo () :=
  let x := { contents := 0 } in
  let _ := Array.init 1 (fun _ => x.(contents) := Int.add 1 (x.(contents))) in
  Control.assert_true (Int.equal 1 (x.(contents))).

Ltac2 Eval foo ().

Ltac2 Type rec singleton := [ Single (int) | Arr (singleton array) ].
Ltac2 rec init_rec (n : int) :=
  match Int.equal n 0 with
  | true => Single 0
  | false => Arr (Array.init 1 (fun _ => init_rec (Int.sub n 1)))
  end.
Ltac2 rec timing (n : int) :=
  (match Int.equal n 0 with
   | true => ()
   | false => timing (Int.sub n 1)
   end;
  Message.print (Message.concat (Message.of_int n) (Message.of_string ": "));
  let _ := Control.time None (fun _ => init_rec n) in
  ()).
(** Should take less than 0.1 seconds if the asymptotics are correct.
Previous behavior was to take an expected 1 million times the age of
the universe.  Capping the time at 100 seconds seems like a reasonable
middle ground between these times, as I expect that compilation of Coq
itself will not finish in reasonable time if the computer is running
1000x slower than modern machines. *)
Timeout 100 Ltac2 Eval timing 100.
