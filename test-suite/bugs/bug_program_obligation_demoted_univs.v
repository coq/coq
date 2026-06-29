From Corelib Require Import Program.Tactics.

#[local] Obligation Tactic := idtac.

Class C (A : Type) := { c1 : True; c2 : True }.

Section S.
  Context (A : Type).

  Local Program Instance c_inst : C A := {}.
  Next Obligation.
    (* This nested [abstract] creates demoted universe constraints in the
       obligation proof state. The second opaque obligation below used to
       fail with:
         Anomaly "in Univ.repr: Universe ... undefined".
       The regression was that restricting an obligation universe context
       removed local universes from the graph, but kept demoted constraints
       mentioning those removed universes. *)
    assert (H : Type) by abstract (assert Type by abstract exact Type; exact nat).
    exact I.
  Qed.
  Next Obligation.
    exact I.
  Qed.
End S.
