Definition decidable := [P:Prop] P \/ ~P.

Theorem dec_not_not : (P:Prop)(decidable P) -> (~P -> False) -> P.
Unfold decidable; Tauto. 
Save.

Theorem dec_True: (decidable True).
Unfold decidable; Auto.
Save.

Theorem dec_False: (decidable False).
Unfold decidable not; Auto.
Save.

Theorem dec_or: (A,B:Prop)(decidable A) -> (decidable B) -> (decidable (A\/B)).
Unfold decidable; Tauto. 
Save.

Theorem dec_and: (A,B:Prop)(decidable A) -> (decidable B) ->(decidable (A/\B)).
Unfold decidable; Tauto. 
Save.

Theorem dec_not: (A:Prop)(decidable A) -> (decidable ~A).
Unfold decidable; Tauto. 
Save.

Theorem dec_imp: (A,B:Prop)(decidable A) -> (decidable B) ->(decidable (A->B)).
Unfold decidable; Tauto. 
Save.

Theorem not_not : (P:Prop)(decidable P) -> (~(~P)) -> P.
Unfold decidable; Tauto. Save.

Theorem not_or : (A,B:Prop) ~(A\/B) -> ~A /\ ~B.
Tauto. Save.

Theorem not_and : (A,B:Prop) (decidable A) -> ~(A/\B) -> ~A \/ ~B.
Unfold decidable; Tauto. Save.

Theorem not_imp : (A,B:Prop) (decidable A) -> ~(A -> B) -> A /\ ~B.
Unfold decidable;Tauto.
Save.

Theorem imp_simp : (A,B:Prop) (decidable A) -> (A -> B) -> ~A \/ B.
Unfold decidable; Tauto.
Save.

