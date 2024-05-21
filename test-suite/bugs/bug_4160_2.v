Inductive paths {A : Set} (a : A) : forall _ : A, Set := idpath : paths a a.
Inductive bool := B.
Inductive String : Set := string (c : bool) : String.
Definition head_type (s : String) : Set :=
match s with string _ => bool end.
Axiom head : forall s : String, head_type s.
Definition ne_head (x y : bool) (H : paths (string x) (string y)) :
paths (head (string x)) (head (string y)).
Proof.
Fail case H.
Abort.
