Inductive box P := box_intro : P -> box P.
Inductive P := P_intro : box P -> P.

Fixpoint size (d : P) {struct d} : nat :=
  let 'P_intro p := d in
  match tt as t
  return box (match t with tt => P end) -> nat
  with
  | tt => fun tu =>
      size (let 'box_intro _ tu' := tu in tu')
  end p.
