

Module M.
  Private Inductive foo := .
  Definition bar (A:Prop) (_:A=True) (x:foo) : A := match x with end.
End M.

Goal M.foo -> False.
Proof.
  Fail let c := eval cbv in c in
  match c with
    context c [True] =>
      (* ltac context instantiation calls Typing *)
      let c := context c [False] in
      exact c
  end.
  let c := open_constr:(M.bar False (ltac:(exact_no_check (eq_refl True)))) in
  let c := eval cbv in c in
    exact c.
(* check no goals remain *)
Unshelve.
all:fail.
Fail Qed.
Abort.

Fail Definition bar := Eval cbv in M.bar.

Module N.
  Private Inductive foo := C : nat -> nat -> foo.
  Definition use x := match x with C a b => a + b end.
End N.

Definition five := N.C 2 3.
Definition five' := Eval cbv in N.use five.
Check eq_refl : five' = 5.
