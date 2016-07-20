Goal forall b : bool, match b as b' return if b' then True else True with true => I | false => I end = match b as b' return if b' then True else True with true => I | false => I end.
intro.
lazymatch goal with
| [ |- context[match ?b as b' in bool return @?P b' with true => ?t | false => ?f end] ]
  => change (match b as b' in bool return P b' with true => t | false => f end) with (@bool_rect P t f b)
end.
