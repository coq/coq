Parameter g : nat -> Prop.
Axiom a : forall n, g (S n).
Lemma foo (H : True) : exists n, g n /\ g n.
eexists.
clear H.
split.
simple apply a.
(* goal is "g (S ?Goal0@ {H:=H})" while H has long ceased to exist *)
simpl.
Abort.
