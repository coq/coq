Axiom cons_data_one :
  forall (Aone : unit -> Set) (i : unit) (a : Aone i), nat.
Axiom P : nat -> Prop.
Axiom children_data_rect3 : forall {Aone : unit -> Set}
  (cons_one_case : forall (i : unit) (b : Aone i),
     nat -> nat -> P (cons_data_one Aone i b)),
  P 0.
Fail Definition decide_children_equality IH := children_data_rect3
  (fun _ '(existT _ _ _) => match IH with tt => _ end).
