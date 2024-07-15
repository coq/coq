Ltac k1 := rewrite_strat (subterms id; (choice (subterm fail) fail)); fail. Print Ltac k1.
Ltac k2 := rewrite_strat subterms id; (choice (subterm fail) fail); fail. Print Ltac k2.
Ltac k3 := rewrite_strat subterms id; ((choice (subterm fail) fail); fail). Print Ltac k3.
Ltac k4 := rewrite_strat subterms (id; choice (subterm fail) fail; fail). Print Ltac k4.
Ltac k5 := rewrite_strat (subterms subterms fail; subterms subterms fail); choice (subterms try fail; subterms repeat fail). Print Ltac k5.
Ltac mytry rewstrategy1 := rewrite_strat choice (rewstrategy1) id. Print Ltac mytry.
Ltac myany rewstrategy1 := rewrite_strat fix fixident := try (rewstrategy1 ; fixident). Print Ltac myany.
Ltac myrepeat rewstrategy1 := rewrite_strat (rewstrategy1; any rewstrategy1). Print Ltac myrepeat.
Ltac mybottomup rewstrategy1 := rewrite_strat fix fixident := (choice (progress subterms fixident) (rewstrategy1) ; try fixident). Print Ltac mybottomup.
Ltac mytopdown rewstrategy1 := rewrite_strat fix fixident := (choice (rewstrategy1) (progress subterms fixident) ; try fixident). Print Ltac mytopdown.
Ltac myinnermost rewstrategy1 := rewrite_strat fix fixident := choice (subterm fixident) (rewstrategy1). Print Ltac myinnermost.
Ltac myoutermost rewstrategy1 := rewrite_strat fix fixident := choice (rewstrategy1) (subterm fixident). Print Ltac myoutermost.
