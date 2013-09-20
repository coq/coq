Inductive R {A} : A -> A -> Type := c : forall x y, R x y.

Goal forall A (x y : A) P (e : R x y) (f : forall x y, P x y (c x y)),
  let g := match e in R x y return P x y e with c x y => f x y end in
  True.
Proof.
intros A x y P e f g.
let t := eval red in g in
match t with
  (match ?E as e in R x y return @?P x y e with c X Y => @?f X Y end) => idtac P f
end.
Abort.
