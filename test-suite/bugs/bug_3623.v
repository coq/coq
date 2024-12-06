Goal app (cons 1 (cons 2 nil)) (cons 3 nil) = (cons 1 (cons 2 (cons 3 nil))).
change (@app nat (?a :: ?b) ?c) with (cons a (@app nat b c)).
Abort.
