Lemma match_option_fn T (b : option T) A B s n
: match b as b return forall x : A, B b x with
    | Some k => s k
    | None => n
  end
  = fun x : A => match b as b return B b x with
                   | Some k => s k x
                   | None => n x
                 end.
admit.
Defined.
Lemma match_option_comm_2 T (p : option T) A B R (f : forall (x : A) (y : B x), R x y) (s1 : T -> A) (s2 : forall x : T, B (s1 x)) n1 n2
: match p as p return R match p with
                          | Some k => s1 k
                          | None => n1
                        end
                        match p as p return B match p with Some k => s1 k | None => n1 end with
                          | Some k => s2 k
                          | None => n2
                        end with
    | Some k => f (s1 k) (s2 k)
    | None => f n1 n2
  end
  = f match p return A with
        | Some k => s1 k
        | None => n1
      end
      match p as p return B match p with Some k => s1 k | None => n1 end with
        | Some k => s2 k
        | None => n2
      end.
admit.
Defined.
Fail Hint Rewrite match_option_fn match_option_comm_2 : matchdb.
