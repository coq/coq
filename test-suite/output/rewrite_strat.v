Ltac k1 := rewrite_strat (subterms id; (choice (subterm fail) fail)); fail. Print Ltac k1.
Ltac k2 := rewrite_strat subterms id; (choice (subterm fail) fail); fail. Print Ltac k2.
Ltac k3 := rewrite_strat subterms id; ((choice (subterm fail) fail); fail). Print Ltac k3.
Ltac k4 := rewrite_strat subterms (id; choice (subterm fail) fail; fail). Print Ltac k4.
Ltac k5 := rewrite_strat (subterms subterms fail; subterms subterms fail); choice (subterms try fail; subterms repeat fail). Print Ltac k5.
