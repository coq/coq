Require Import ZArith Coq.Program.Wf Coq.Program.Utils.

Parameter data:Set.

Inductive t : Set :=
  | Leaf : t
  | Node : t -> data -> t -> Z -> t.

Parameter avl : t -> Prop.
Parameter bst : t -> Prop.
Parameter In : data -> t -> Prop.
Parameter cardinal : t -> nat.
Definition card2 (s:t*t) := let (s1,s2) := s in cardinal s1 + cardinal s2.

Parameter split : data -> t -> t*(bool*t).
Parameter join : t -> data -> t -> t.
Parameter add : data -> t -> t.

Program Fixpoint union
  (s u:t)
  (hb1: bst s)(ha1: avl s)(hb2: bst u)(hb2: avl u)
  { measure (cardinal s + cardinal u) } :
  {s' : t | bst s' /\ avl s' /\ forall x, In x s' <-> In x s \/ In x u} :=
  match s, u with
    | Leaf,t2 => t2
    | t1,Leaf => t1
    | Node l1 v1 r1 h1, Node l2 v2 r2 h2 =>
        if (Z_ge_lt_dec h1 h2) then
          if (Z.eq_dec h2 1)
          then add v2 s
          else
            let (l2', r2') := split v1 u in
            join (union l1 l2' _ _ _ _) v1 (union r1 (snd r2') _ _ _ _)
        else
          if (Z.eq_dec h1 1)
          then add v1 s
          else
            let (l1', r1') := split v2 u in
            join (union l1' l2 _ _ _ _) v2 (union (snd r1') r2 _ _ _ _)
  end.
