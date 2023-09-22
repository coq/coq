Set Typeclasses Unique Instances.

Class Foo (x y : bool) := {}.
Class Bar (x y : bool) := {}.
Class Bax (x : bool) := {}.

Instance bar_1 : Bar true false := {}.
Instance bar_2 : Bar true true := {}.

Instance bax_1 : Bax false := {}.

Instance foo x y : Bar x y -> Bax y -> Foo x y := {}.

Typeclasses eauto := debug.

Fail Definition bla : Foo true _ := _.

 (*
Debug: Calling typeclass resolution with flags: depth = ∞,unique = false,do_split = true,fail = false
Debug: 1: looking for (Foo true ?y) with backtracking
Debug: 1.1: simple apply foo on (Foo true ?y), 2 subgoal(s)
Debug: 1.1-1 : (Bar true ?y)
Debug: 1.1-1: looking for (Bar true ?y) with backtracking
Debug: 1.1-1.1: exact bar_2 on (Bar true ?y), 0 subgoal(s)
Debug: 1.1-2 : (Bax true)
Debug: 1.1-2: looking for (Bax true) without backtracking
Debug: 1.1-2: no match for (Bax true), 0 possibilities
Debug: 1.1-1.2: exact bar_1 on (Bar true ?y), 0 subgoal(s)
Debug: 1.1-2 : (Bax false)
Debug: 1.1-2: looking for (Bax false) without backtracking
Debug: 1.1-2.1: exact bax_1 on (Bax false), 0 subgoal(s)

produces bla =
foo true false bar_1 bax_1 : Foo true false
     : Foo true false
*)
