Generalizable All Variables.

Open Scope type_scope.

Section type_reification.

Inductive term :Type :=
   Fun : term -> term -> term
 | Prod : term -> term -> term
 | Bool : term
 | SET :term
 | PROP :term
 | TYPE :term
 | Var : Type -> term.

Fixpoint interp (t:term) :=
  match t with
    Bool => bool
  | SET => Set
  | PROP => Prop
  | TYPE => Type
  | Fun a b => interp a -> interp b
  | Prod a b => interp a * interp b
  | Var x => x
end.

Class interp_pair (abs : Type) :=
 { repr : term;
  link: abs = interp repr }.

Arguments repr _ {interp_pair}.
Arguments link _ {interp_pair}.

Lemma prod_interp `{interp_pair a, interp_pair b} : a * b = interp (Prod (repr a) (repr b)).
  simpl. intros. rewrite <- link. rewrite <- (link b). reflexivity.
Qed.

Lemma fun_interp :forall `{interp_pair a, interp_pair b}, (a -> b) = interp (Fun (repr a) (repr b)).
  simpl. intros. rewrite <- link. rewrite <- (link b). reflexivity.
Qed.

Coercion repr : interp_pair >-> term.

Definition abs `{interp_pair a} : Type := a.
Coercion abs : interp_pair >-> Sortclass.

Lemma fun_interp' :forall `{ia : interp_pair, ib : interp_pair}, (ia -> ib) = interp (Fun ia ib).
  simpl. intros a ia b ib. rewrite <- link. rewrite <- (link b). reflexivity.
Qed.

Instance ProdCan `(interp_pair a, interp_pair b) : interp_pair (a * b) :=
  { repr := Prod (repr a) (repr b) ; link := prod_interp }.

Instance FunCan `(interp_pair a, interp_pair b) : interp_pair (a -> b) :=
  { link := fun_interp }.

Instance BoolCan : interp_pair bool :=
  { repr := Bool ; link := refl_equal _ }.

Instance VarCan x : interp_pair x | 10 := { repr := Var x ; link := refl_equal _ }.
Instance SetCan : interp_pair Set := { repr := SET ; link := refl_equal _ }.
Instance PropCan : interp_pair Prop := { repr := PROP ; link := refl_equal _ }.
Instance TypeCan : interp_pair Type := { repr := TYPE ; link := refl_equal _ }.

(* Print Canonical Projections. *)

Variable A:Type.

Variable Inhabited: term -> Prop.

Variable Inhabited_correct: forall `{interp_pair p}, Inhabited (repr p) -> p.

Lemma L : Prop * A -> bool * (Type -> Set) .
apply (Inhabited_correct _ _).
change (Inhabited (Fun (Prod PROP (Var A)) (Prod Bool (Fun TYPE SET)))).
Admitted.

End type_reification.
