Goal forall b : bool, match b as b' return if b' then True else True with true => I | false => I end = match b as b' return if b' then True else True with true => I | false => I end.
intro.
Fail lazymatch goal with
| [ |- appcontext[match ?b as b' return @?P b' with true => ?t | false => ?f end] ]
  => change (match b as b' return P b with true => t | false => f end) with (@bool_rect P t f)
end. (* Toplevel input, characters 153-154:
Error: The reference P was not found in the current environment. *)
