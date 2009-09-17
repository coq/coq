

Set Implicit Arguments.

Inductive T (A:Set) : Set :=
 app : T A -> T A -> T A.

Fixpoint map (A B:Set)(f:A->B)(t:T A) : T B :=
 match t with
   app t1 t2 => app (map f t1)(map f t2)
 end.

Fixpoint subst (A B:Set)(f:A -> T B)(t:T A) :T B :=
 match t with
    app t1 t2 => app (subst f t1)(subst f t2)
 end.

(* This is the culprit: *)
Definition k0:=Set.

(** interaction of subst with map *)
Lemma substLaw1 (A:k0)(B C:Set)(f: A -> B)(g:B -> T C)(t: T A):
 subst g (map f t) = subst (fun x => g (f x)) t.
Proof.
 intros.
 generalize B C f g; clear B C f g.
 induction t; intros; simpl.
 f_equal.
Admitted.
