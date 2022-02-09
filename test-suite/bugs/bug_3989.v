(* 9e6b28c04ad98369a012faf3bd4d630cf123a473 *)
Record foo := { bar : Type }.
Arguments bar _ / .
Definition baz (x : Type) := x.
Arguments baz / : simpl nomatch.
Goal forall x, baz (bar x) = baz (bar x).
Proof.
  assert_succeeds
    (repeat simpl; match goal with
                   | [ |- forall x : foo, (let (bar) := x in bar) = (let (bar) := x in bar) ] => idtac
                   | [ |- ?G ] => fail 1 G
                   end). (* success *)
  repeat cbn; match goal with
                | [ |- forall x : foo, (let (bar) := x in bar) = (let (bar) := x in bar) ] => idtac
                | [ |- ?G ] => fail 1 G
              end. (* Tactic failure: (forall x : foo, baz (let (bar) := x in bar) = baz (let (bar) := x in bar)). *)
Abort.
