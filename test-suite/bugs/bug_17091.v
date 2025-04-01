Require Program.Tactics.

Axiom admit : False.

Axiom V : Type.
Axiom VSet : Type.
Axiom VSet_mem : V -> VSet -> bool.

Axiom DisjointAdd : V -> VSet -> VSet -> Prop.
Axiom EdgeOf : V -> V -> Set.

Inductive PathOf : V -> V -> Type :=
| pathOf_refl x : PathOf x x
| pathOf_step x y z : EdgeOf x y -> PathOf y z -> PathOf x z.

Arguments pathOf_step {x y z} e p.

Axiom nodes : forall {x y} (p : PathOf x y), VSet.

Inductive SPath : VSet -> V -> V -> Type :=
| spath_refl s x : SPath s x x
| spath_step s s' x y z : DisjointAdd x s s' -> EdgeOf x y
                           -> SPath s y z -> SPath s' x z.

Fixpoint is_simple {x y} (p : PathOf x y) :=
  match p with
  | pathOf_refl x => true
  | @pathOf_step x y z e p => andb (negb (VSet_mem x (nodes p))) (is_simple p)
  end.

Program Definition to_simple : forall {x y} (p : PathOf x y),
    is_simple p = true -> SPath (nodes p) x y
  := fix to_simple {x y} p (Hp : is_simple p = true) {struct p} :=
       match
         p in PathOf t t0
         return is_simple p = true -> SPath (nodes p) t t0
       with
       | pathOf_refl x =>
         fun _ => spath_refl (nodes (pathOf_refl x)) x
       | @pathOf_step x y z e p0 =>
         fun Hp0 => @spath_step _ _ _ _ _ _ e (to_simple p0 _)
       end Hp.
Next Obligation.
elim admit.
Defined.

Final Obligation.
clear to_simple. elim admit.
Qed.
