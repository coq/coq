Require Import Ltac2.Ltac2.

Ltac2 Type ABC := [A | B(bool) | C(constr)].

Print Ltac2 B.
Check Ltac2 B.

Ltac2 msg_of_bool b := Message.of_string
                         (match b with
                          | true => "true"
                          | false => "false"
                          end).

Ltac2 Notation x(self) "++" y(self) := Message.concat x y.

Ltac2 explain_abc abc :=
  match abc with
  | A => Message.print (Message.of_string "A")
  | B b => Message.print (Message.of_string "B " ++ msg_of_bool b)
  | C c => Message.print (Message.of_string "C " ++ Message.of_constr c)
  end.

Ltac2 Eval explain_abc A.
Ltac2 Eval explain_abc (B true).
Ltac2 Eval explain_abc (C constr:(2 + 3)).
