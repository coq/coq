Require Peano.
Hint eq_S : v62 := Resolve (f_equal nat nat S).
Hint eq_nat_unary : core := Resolve (f_equal nat).
Hint eq_pred : v62 := Resolve (f_equal nat nat pred).
Hints Immediate eq_add_S : core v62.
Hints Resolve not_eq_S : core v62.
Hints Resolve O_S : core v62.
Hints Resolve n_Sn : core v62.
Hint eq_plus : v62 := Resolve (f_equal2 nat nat nat plus).
Hint eq_nat_binary : core := Resolve (f_equal2 nat nat).
Hints Resolve plus_n_O : core v62.
Hints Resolve plus_n_Sm : core v62.
Hint eq_mult : core v62 := Resolve (f_equal2 nat nat nat mult).
Hints Resolve mult_n_O : core v62.
Hints Resolve mult_n_Sm : core v62.
Hint constr_le : core v62 := Constructors le.
(*i equivalent to : "Hints Resolve le_n le_S : core v62." i*)
Hints Unfold lt : core v62.
Hints Unfold ge : core v62.
Hints Unfold gt : core v62.
