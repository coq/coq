Axiom f : nat -> nat -> nat.
Fixpoint do_n (n : nat) (k : nat) :=
  match n with
    | 0 => k
    | S n' => do_n n' (f k k)
  end.

Notation big := (_ = _).
Axiom k : nat.
Goal True.
Timeout 1 let H := fresh "H" in
     let x := constr:(let n := 17 in do_n n = do_n n) in
     let y := (eval lazy in x) in 
     pose proof y as H. (* Finished transaction in 1.102 secs (1.084u,0.016s) (successful) *)
Timeout 1 let H := fresh "H" in
     let x := constr:(let n := 17 in do_n n = do_n n) in
     let y := (eval lazy in x) in
     pose y as H; clearbody H. (* Finished transaction in 0.412 secs (0.412u,0.s) (successful) *)

Timeout 1 Time let H := fresh "H" in
     let x := constr:(let n := 17 in do_n n = do_n n) in
     let y := (eval lazy in x) in
     assert (H := y). (* Finished transaction in 1.19 secs (1.164u,0.024s) (successful) *)
