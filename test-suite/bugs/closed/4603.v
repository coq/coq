Axiom A : Type.

Goal True. exact I.
Check (fun P => P A).
Abort.

Goal True.
Definition foo (A : Type) : Prop:= True. 
  set (x:=foo). split.
Qed.
