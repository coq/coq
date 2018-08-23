Set Printing Universes.

Module Auto.
  Inductive Box (A:Type) : Type := box : A -> Box A.

  About Box.

  (* This checks that Box is template poly, see module No for how it fails *)
  Universe i j. Constraint i < j.
  Definition j_lebox (A:Type@{j}) := Box A.
  Definition box_lti A := Box A : Type@{i}.

End Auto.

Module Yes.
  #[template]
  Inductive Box@{i} (A:Type@{i}) : Type@{i} := box : A -> Box A.

  About Box.

  Universe i j. Constraint i < j.
  Definition j_lebox (A:Type@{j}) := Box A.
  Definition box_lti A := Box A : Type@{i}.

End Yes.

Module No.
  #[notemplate]
  Inductive Box (A:Type) : Type := box : A -> Box A.

  About Box.

  Universe i j. Constraint i < j.
  Definition j_lebox (A:Type@{j}) := Box A.
  Fail Definition box_lti A := Box A : Type@{i}.
End No.
