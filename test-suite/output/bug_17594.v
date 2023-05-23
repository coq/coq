From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.

Ltac2 msg s := print (of_string s).

Goal True.
  (* should be the exact error *)
  Fail multi_match! 'True with
    | True => msg "1"
    | _ => msg "2"
    end;
    msg "3"; exact 0.

  Fail ltac1:(multimatch True with
    | True => idtac "1"
    | _ => idtac "2"
    end; idtac "3"; exact 0).

  Fail multi_match! goal with
    | [ |- True ] => msg "1"
    | [ |- _ ] => msg "2"
    end;
    msg "3"; exact 0.

  Fail ltac1:(multimatch goal with
    | |- True => idtac "1"
    | |- _ => idtac "2"
    end; idtac "3"; exact 0).

  (* should be match error *)
  Fail multi_match! 'True with
    | True => msg "1"
    | False => msg "2"
    end;
    msg "3"; exact 0.

  Fail ltac1:(multimatch True with
    | True => idtac "1"
    | False => idtac "2"
    end; idtac "3"; exact 0).

  Fail multi_match! goal with
    | [ |- True ] => msg "1"
    | [ |- False ] => msg "2"
    end;
    msg "3"; exact 0.

  Fail ltac1:(multimatch goal with
    | |- True => idtac "1"
    | |- False => idtac "2"
    end; idtac "3"; exact 0).

Abort.
