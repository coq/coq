(** This is a change of behaviour introduced by PR #12532. It is not clear
    whether it is a legit behaviour but it is worth having it in the test
    suite. *)

Module Foo.

Axiom whatever : Type.
Axiom name : Type.
Axiom nw : forall (P : Type), name -> P.
Axiom raft_data : Type.
Axiom In : raft_data -> Prop.

Axiom foo : forall st st', In st -> In st'.

Definition params := prod whatever raft_data.

Goal forall
  (d : raft_data),
  (forall (h : name), In (@snd whatever raft_data (@nw params h))) ->
  In d.
Proof.
intros.
eapply foo.
solve [debug eauto].
Abort.

End Foo.

Module Bar.

Axiom whatever : Type.
Axiom AppendEntries : whatever -> Prop.
Axiom name : Type.
Axiom nw : forall (P : Type), name -> P.
Axiom raft_data : Type.
Axiom In : raft_data -> Prop.

Axiom foo :
  forall st st' lid,
    (AppendEntries lid -> In st) -> AppendEntries lid -> In st'.

Definition params := prod whatever raft_data.

Goal forall
  (d : raft_data),
  (forall (h : name) (w : whatever),
    AppendEntries w -> In (@snd whatever raft_data (@nw params h))) ->
  In d.
Proof.
intros.
eapply foo.
intros.
solve [debug eauto].
Abort.

End Bar.
