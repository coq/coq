Axiom proof_admitted : False.
Goal forall (P0 : Prop) (T : Type) (ls : T) (P : T -> Prop) (x y : P ls) (f : P ls -> P0), f x = f y.
  intros.
  abstract (set (ls' := ls); change ls with ls' in x; case proof_admitted).
  (* Error:
In environment
P0 : Prop
T : Type
ls : T
P : T -> Prop
x : P ls
y : P ls
f : P ls -> P0
ls' := ls : T
The term "x" has type "P ls" while it is expected to have type "T".
   *)
Qed.
