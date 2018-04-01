Require Import TestSuite.admit.
Section Counted_list.

  Variable A : Type.

  Inductive counted_list : nat -> Type :=
    | counted_nil : counted_list 0
    | counted_cons : forall(n : nat), 
        A -> counted_list n -> counted_list (S n).


  Fixpoint counted_def_nth{n : nat}(l : counted_list n)
                          (i : nat)(def : A) : A :=
    match i with
      | 0 => match l with
               | counted_nil => def
               | counted_cons _ a _ => a
             end
      | S i => match l with
                 | counted_nil => def
                 | counted_cons _ _ tl => counted_def_nth tl i def
               end
    end.


  Lemma counted_list_equal_nth_char : 
    forall(n : nat)(l1 l2 : counted_list n)(def : A),
      (forall(i : nat), counted_def_nth l1 i def = counted_def_nth l2 i def) ->
        l1 = l2.
  Proof.
    admit.
  Qed.

End Counted_list.

Arguments counted_def_nth [A n].

Section Finite_nat_set.

  Variable set_size : nat.

  Definition fnat_subset : Type := counted_list bool set_size.

  Definition fnat_member(fs : fnat_subset)(n : nat) : Prop := 
    is_true (counted_def_nth fs n false).


  Lemma fnat_subset_member_eq : forall(fs1 fs2 : fnat_subset),
    fs1 = fs2 <->
      forall(n : nat), fnat_member fs1 n <-> fnat_member fs2 n.

  Proof.
    intros fs1 fs2.
    split.
      intros H n.
      subst fs1.
      apply iff_refl.
    intros H.
    eapply (counted_list_equal_nth_char _ _ _ _ ?[def]).
    intros i.
    destruct (counted_def_nth fs1 i _ ) eqn:H0.
    (* This was not part of the initial bug report; this is to check that
       the existential variable kept its name *)
    change (true = counted_def_nth fs2 i ?def).
