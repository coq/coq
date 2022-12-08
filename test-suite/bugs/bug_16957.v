Module Test1.

  Goal True.
  Proof.
    evar (x:nat).
    generalize (eq_refl:x = x).
    vm_compute.
    intros _.
    generalize (eq_refl:x + 1 = x + 1).
    let x := constr:(eq_refl : x = 0) in idtac.
    vm_compute.
    (* vm_compute still thinks variable x is defined to an undefined evar, so computes to a blocked fix *)

    match goal with |- 1 = 1 -> True => idtac end.
  Abort.

  Goal False.
  Proof.
    evar (x:nat).
    assert_succeeds (
        let y := constr:(eq_refl : x = 1) in
        generalize (eq_refl:x = x);
        vm_compute).
    (* vm_compute now believes x = 1 *)
    generalize (eq_refl:x = 0).
    vm_compute.
    match goal with |- 0 = 0 -> False => idtac end.
  Abort.

End Test1.

Module Test2.
  Section S.

    Let x := 0.

    (* Notes:
     - using a Proof. instead of ltac:() would make the context go through
       Declare.initialize_named_context_for_proof which renews the lazy_vals
       and so prevents proof time mutation from affecting the kernel.
     - we could use the previous examples of the bug to get a variable y := false
       but believed by vm_compute to be true, then use that to get change to turn
       x := 0 into x := 1 up to vm_compute.
       However change goes through Logic.reorder_val_context which renewes the lazy_vals
       before we can get vm_compute to believe in x := 1.
       Since this means we have to use change_no_check, we don't bother with the trickery
       and just change 0 with 1.
     *)
    Fail Definition foo : x = 1
      := ltac:(
                 change_no_check 0 with 1 in x;
                 vm_compute;
                 reflexivity).

  End S.
End Test2.

Module Test3.
  Section S.
    Let x := 0.
    Fail Definition foo : x = 1 := ltac:(change_no_check 0 with 1 in x; vm_compute).
    Fail Definition foo : x = 1 := ltac:(vm_cast_no_check (eq_refl 1)).
  End S.
End Test3.
