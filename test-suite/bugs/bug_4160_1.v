(* -*- mode: coq; coq-prog-args: ("-indices-matter") -*- *)
Axiom proof_admitted : False.
Tactic Notation "admit" := case proof_admitted.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@ paths _ x y) : type_scope.
Inductive String : Set :=
| empty : String
| string (c : bool) (cs : String) : String.
Definition head_type (s : String) : Set :=
  match s with
  | empty => unit
  | string _ _ => bool
  end.
Definition head (s : String) : head_type s :=
  match s return head_type s with
  | empty => tt
  | string c _ => c
  end.
Definition ne_head (x y : bool) (xs ys: String)
: string x xs = string y ys -> head (string x xs) = head (string y ys).
Proof.
  intro H.
  Fail destruct H.
Abort.
