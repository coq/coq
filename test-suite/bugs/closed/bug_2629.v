Class Join (t: Type) : Type := mkJoin {join: t -> t -> t -> Prop}.

Class sepalg (t: Type) {JOIN: Join t} : Type :=
  SepAlg   {
   join_eq: forall {x y z z'}, join x y z -> join x y z' -> z = z';
   join_assoc: forall {a b c d e}, join a b d -> join d c e ->
                    {f : t & join b c f /\ join a f e};
   join_com: forall {a b c}, join a b c -> join b a c;
   join_canc: forall {a1 a2 b c}, join a1 b c -> join a2 b c -> a1=a2;

   unit_for : t -> t -> Prop := fun e a => join e a a;
   join_ex_units: forall a, {e : t & unit_for e a}
}.

Definition joins {A} `{Join A} (a b : A) : Prop :=
 exists c, join a b c.

Lemma join_joins {A} `{sepalg A}: forall {a b c},
 join a b c -> joins a b.
Proof.
 firstorder.
Qed.
