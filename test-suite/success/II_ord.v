
Reserved Infix ">>" (at level 20).
Reserved Notation "'ω^' a '+' b '[' r ']'" (format "'ω^' a + b [ r ]", at level 0).

(** Cantor-normal form ordinal notation. *)

Inductive Ord :=
| zero : Ord
| omega (exp : Ord) (sum : Ord) : exp >> sum -> Ord

with lt : Ord -> Ord -> Prop :=
| lt1 {a b r} : zero < (omega a b r)
| lt2 {a b c d r s} : a < c -> (omega a b r) < (omega c d s)
| lt3 {a b c d r s} : a = c -> b < d -> (omega a b r) < (omega c d s)

with gt_head : Ord -> Ord -> Prop :=
| gt1 {a} : a >> zero
| gt2 {a b c d} : (omega b c d) < a -> a >> b

where "x < y" := (lt x y)
  and "x >> y" := (gt_head x y)
.

Notation "'ω^' a '+' b '[' r ']'" := (omega a b r).
