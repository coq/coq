Module Err1.
  Axiom u:unit.
  Axiom p:unit -> unit * unit.

  Lemma foo : let (r, n) := p u in n = n.
  Proof.
    set (t := _ u).
    clearbody t.
    destruct t as [_ []].
    exact (eq_refl tt).
  Qed.
End Err1.

Module Err2.

  Inductive lookahead_action (term:unit) := Shift_act.

  Class IsValidator (P : Prop) (b : bool) := {}.

  Global Hint Extern 2 (IsValidator (match ?u with _ => _ end) ?b0) =>
    let b := fresh "b" in
    unshelve notypeclasses refine (let b : bool := _ in _);
    [destruct u; intros; shelve|];
    unify b b0;
    unfold b; destruct u; clear b
    : typeclass_instances.

  Axiom Awt : forall t:unit, lookahead_action t.

  Lemma foo x0
    : exists g:bool, forall x1,
        IsValidator
          match x0 with
          | tt =>
            match Awt x1 with
            | Shift_act _ => False
            end
          end g.
  Proof.
    eexists.
    Fail apply _.
  Abort.

End Err2.
