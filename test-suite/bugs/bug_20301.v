Set Universe Polymorphism.

Axiom Ty : Set.
Axiom Exp : Ty -> Set.

Axiom halts@{u} : forall {τ : Ty} (_ : Exp τ), Type@{u}.

Axiom step_preserves_halting@{u|} :
  forall {τ : Ty} (e e' : Exp τ), (halts@{u} e) -> (halts@{u} e').

Axiom SN@{u} : forall {τ : Ty} (_ : Exp τ), Type@{u}.

Lemma foo@{u} : forall
  (τ1 τ2 : Ty)
  (e e' e'' : Exp τ2)
  (X : @halts@{u} τ2 e)
  (Y : forall (x : Exp τ1) (_ : @SN@{u} τ1 x), @SN@{u} τ2 e'')
  (IHτ : forall (_ : @SN@{u} τ2 e''), False),
  prod (forall (x : Exp τ1) (_ : @SN@{u} τ1 x), False) (@halts@{u} τ2 e').
Proof.
intros.
pose proof (step_preserves_halting e e') as H2.
split.
+ refine (fun x H => IHτ (Y x H)).
+ solve[firstorder].
Qed.
