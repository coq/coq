Require Import List.
Goal  (1 :: 2 :: nil) ++ (3::nil) = (1::2::3::nil).
change (@app nat (?a :: ?b) ?c) with (a :: @app nat b c).
Abort.
