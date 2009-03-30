Require Import Quote.

Parameter A B : Prop.

Inductive formula : Type :=
  | f_and : formula -> formula -> formula
  | f_or : formula -> formula -> formula
  | f_not : formula -> formula
  | f_true : formula
  | f_atom : index -> formula
  | f_const : Prop -> formula.

Fixpoint interp_f (vm:
                    varmap Prop) (f:formula) {struct f} : Prop :=
  match f with
  | f_and f1 f2 => interp_f vm f1 /\ interp_f vm f2
  | f_or f1 f2 => interp_f vm f1 \/ interp_f vm f2
  | f_not f1 => ~ interp_f vm f1
  | f_true => True
  | f_atom i => varmap_find True i vm
  | f_const c => c
  end.

Goal A \/ B -> A /\ (B \/ A) /\ (A \/ ~ B).
intro H.
match goal with
  | H : ?a \/ ?b |- _ => quote interp_f in a using (fun x => idtac x; change (x \/ b) in H)
end.
match goal with
  |- ?g => quote interp_f [ A ] in g using (fun x => idtac x)
end.
quote interp_f.
Show.
simpl; quote interp_f [ A ].
Show.
Admitted.
