(** Check that bound variables in case patterns are handled correctly. *)

Goal forall (ch : unit) (t : list unit) (s : list unit),
  match s with
  | nil => False
  | cons a l => ch = a /\ l = t
  end.
Proof.
intros.
match goal with
| |- match ?e with
    | nil => ?N
    | cons a b => ?P
    end =>
     let f :=
      constr:((fun (e' : list unit) => match e' with
                          | nil => N
                          | cons a b => P
                          end))
     in
     change (f e)
end.
Abort.

Goal forall (ch : unit) (n : nat) (s : prod unit nat),
  let (a, l) := s in ch = a /\ l = n.
Proof.
intros.
match goal with
| [ |- let (a, b) := ?e in ?P ] =>
  let f := constr:((fun (e' : prod unit nat) => match e' with pair a b => P end)) in
  change (f e)
end.
Abort.
