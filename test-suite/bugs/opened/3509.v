Lemma match_bool_fn b A B xT xF
: match b as b return forall x : A, B b x with
    | true => xT
    | false => xF
  end
  = fun x : A => match b as b return B b x with
                   | true => xT x
                   | false => xF x
                 end.
admit.
Defined.
Lemma match_bool_comm_1 (b : bool) A B (F : forall x : A, B x) t f
: (if b as b return B (if b then t else f) then F t else F f)
  = F (if b then t else f).
admit.
Defined.
Hint Rewrite match_bool_fn : matchdb.
Fail Hint Rewrite match_bool_comm_1 : matchdb.
