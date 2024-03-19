Definition A' := (nat * nat)%type.
Lemma iscategory_sig
  : forall s d : A', { x : Set | x = x }.
Proof.
  intros s d.
  unshelve econstructor.
  1: destruct s.
  2: lazymatch goal with
     | [ |- (let (n, n0) := s in (fun n1 n2 : nat => _) n n0) =
              (let (n, n0) := s in (fun n1 n2 : nat => _) n n0) ]
       => idtac "good"
     end.
Abort.
