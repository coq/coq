(* coq-prog-args: ("-color" "on" "-diffs" "on" "-async-proofs" "off") *)
(* Re: -async-proofs off, see https://github.com/coq/coq/issues/9671 *)
(* Shows diffs in an error message for an "Unable to unify" error *)
Require Import ListDef.

Inductive btree (T : Type) : Type :=
  Leaf | Node (val : T) (t1 t2 : btree T).

Arguments Leaf {T}.
Arguments Node {T}.

Fixpoint rev_tree {T : Type} (t : btree T) : btree T :=
match t with
| Leaf => Leaf
| Node x t1 t2 => Node x (rev_tree t2) (rev_tree t1)
end.

Fixpoint count {T : Type} (p : T -> bool) (t : btree T) : nat :=
match t with
| Leaf => 0
| Node x t1 t2 =>
  (if p x then 1 else 0) + (count p t1 + count p t2)
end.

Axiom add_comm : forall x y, x + y = y + x.

Lemma count_rev_tree {T} (p : T -> bool) t : count p (rev_tree t) = count p t.
Proof.
induction t as [ | a t1 IH1 t2 IH2].
  easy.
simpl.
rewrite IH1.
rewrite IH2.
Fail reflexivity.
rewrite (add_comm (count p t2)).
easy.
Qed.
