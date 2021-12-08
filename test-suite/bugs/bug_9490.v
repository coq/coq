Declare Custom Entry with_pattern.
Declare Custom Entry M_branch.
Notation "'with' | p1 | .. | pn 'end'" :=
  (cons p1 (.. (cons pn nil) ..))
  (in custom with_pattern at level 91, p1 custom M_branch at level 202, pn custom M_branch at level 202).
Notation "'bla'" := I (in custom M_branch at level 202).
Notation "'[use_with'  l  ]" := (l) (at level 0, l custom with_pattern at level 91).
Check [use_with with | bla end].
Check [use_with with | bla | bla end].
