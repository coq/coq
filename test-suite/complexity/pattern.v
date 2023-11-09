(** Testing the performance of [pattern].  For not regressing on COQBUG(https://github.com/coq/coq/issues/11150) and COQBUG(https://github.com/coq/coq/issues/6502) *)
(* Expected time < 2.00s *)
(* reference: 0.673s after adjustment *)
Definition Let_In {A P} (v : A) (f : forall x : A, P x) : P v
:= let x := v in f x.

Fixpoint big (a : nat) (sz : nat) : nat
  := match sz with
     | O => a
     | S sz' => Let_In (a * a) (fun a' => big a' sz')
     end.

Ltac do_time n :=
  try (
      once (assert (exists e, e = big 1 n);
            [ lazy -[big]; (*match goal with |- ?G => idtac G end;*) lazy [big];
              time pattern Nat.mul, S, O, (@Let_In nat (fun _ => nat))
            | ]);
      fail).

Ltac do_time_to n :=
  lazymatch (eval vm_compute in n) with
  | O => idtac
  | ?n' => do_time_to (Nat.div2 n'); idtac n'; do_time n'
  end.

Local Set Warnings "-abstract-large-number".

(* Don't spend lots of time printing *)
Notation hide := (_ = _).

Goal True.
Proof.
  (* do_time_to 16384. *) (* should be linear, not quadratic *)
  assert (exists e, e = big 1 16384).
  lazy -[big]; (*match goal with |- ?G => idtac G end;*) lazy [big].
  Timeout 15 Time pattern Nat.mul, S, O, (@Let_In nat (fun _ => nat)).
Abort.
