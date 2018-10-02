Set Primitive Projections.

CoInductive stream A := { hd : A; tl : stream A }.

CoFixpoint ticks (n : nat) : stream unit := {| hd := tt; tl := ticks n |}.

Lemma expand : exists n : nat, (ticks n) = (ticks n).(tl _).
Proof.
  eexists.
  (* Set Debug Tactic Unification. *)
  (* Set Debug RAKAM. *)
  reflexivity.
