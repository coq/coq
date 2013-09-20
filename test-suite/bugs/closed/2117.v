(* Check pattern-unification on evars in apply unification *)

Axiom app : forall tau tau':Type, (tau -> tau') -> tau -> tau'.

Axiom copy : forall tau:Type, tau -> tau -> Prop.
Axiom copyr : forall tau:Type, tau -> tau -> Prop.
Axiom copyf : forall tau:Type, tau -> tau -> Prop.
Axiom eq : forall tau:Type, tau -> tau -> Prop.
Axiom subst : forall tau tau':Type, (tau -> tau') -> tau -> tau' -> Prop.

Axiom copy_atom : forall tau:Type, forall t t':tau, eq tau t t' -> copy tau t t'.
Axiom copy_fun: forall tau tau':Type, forall t t':(tau->tau'),
(forall x:tau, copyr tau x x->copy tau' (t x) (t' x))
->copy (tau->tau') t t'.

Axiom copyr_atom : forall tau:Type, forall t t':tau, copyr tau t t' -> eq tau t t'.
Axiom copyr_fun: forall tau tau':Type, forall t t':(tau->tau'),
copyr (tau->tau') t t'
->(forall x y:tau, copy tau x y->copyr tau' (t x) (t' y)).

Axiom copyf_atom : forall tau:Type, forall t t':tau, copyf tau t t' -> eq tau t t'.
Axiom copyf_fun: forall tau tau':Type, forall t t':(tau->tau'),
copyr (tau->tau') t t'
->(forall x y:tau, forall z1 z2:tau',
(copy tau x y)->
(subst tau tau' t x z1)->
(subst tau tau' t' y z2)->
copyf tau' z1 z2).

Axiom eqappg: forall tau tau':Type, forall t:tau->tau', forall q:tau, forall r:tau',forall t':tau',
( ((subst tau tau' t q t') /\ (eq tau' t' r))
->eq tau' (app tau tau' t q) r).

Axiom eqappd: forall tau tau':Type, forall t:tau->tau', forall q:tau, forall r:tau',
forall t':tau', ((subst tau tau' t q t') /\ (eq tau' r t'))
->eq tau' r (app tau tau' t q).

Axiom substcopy: forall tau tau':Type, forall t:tau->tau', forall q:tau, forall r:tau',
(forall x:tau, (copyf tau x q) -> (copy tau' (t x) r))
->subst tau tau' t q r.

Ltac EtaLong := (apply copy_fun;intros;EtaLong)|| apply copy_atom.
Ltac Subst := apply substcopy;intros;EtaLong.
Ltac Rigid_aux := fun A => apply A|| Rigid_aux (copyr_fun _ _ _ _ A).
Ltac Rigid := fun A => apply copyr_atom; Rigid_aux A.

Theorem church0: forall i:Type, exists X:(i->i)->i->i,
copy ((i->i)->i->i) (fun f:i->i => fun x:i=>f (X f x)) (fun f:i->i=>fun x:i=>app i i (X f) (f x)).
intros.
esplit.
EtaLong.
eapply eqappd;split.
Subst.
apply copyf_atom.
Show Existentials.
apply H1.
