(* Check that dependent rewrite applies on arbitrary terms *)

Inductive listn : nat-> Set := 
  niln : (listn O) 
| consn : (n:nat)nat->(listn n) -> (listn (S n)).

Axiom ax : (n,n':nat)(l:(listn (plus n n')))(l':(listn (plus n' n)))
  (existS ? ? (plus n n') l) =(existS ? ? (plus n' n) l').

Lemma lem : (n,n':nat)(l:(listn (plus n n')))(l':(listn (plus n' n)))
   (plus n n')=(plus n' n)
    /\ (existT ? ? (plus n n') l) =(existT ? ? (plus n' n) l').
Proof.
Intros n n' l l'.
Dependent Rewrite (ax n n' l l').
Split; Reflexivity.
Qed.
