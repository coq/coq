Unset Strict Universe Declaration.
Set Printing Universes.
Set Universe Polymorphism.
Definition foo (a := Type) (b := Type) (c := Type) := Type.
Print foo.
(* foo@{Top.2 Top.3 Top.5 Top.6 Top.8 Top.9 Top.10} =
let a := Type@{Top.2} in let b := Type@{Top.5} in let c := Type@{Top.8} in Type@{Top.10}
     : Type@{Top.10+1}
(* Top.2 Top.3 Top.5 Top.6 Top.8 Top.9 Top.10 |= Top.2 < Top.3
                                                 Top.5 < Top.6
                                                 Top.8 < Top.9
                                                  *)
 *)
Check @foo. (* foo@{Top.11 Top.12 Top.13 Top.14 Top.15 Top.16
Top.17}
     : Type@{Top.17+1}
(* Top.11 Top.12 Top.13 Top.14 Top.15 Top.16 Top.17 |= Top.11 < Top.12
                                                       Top.13 < Top.14
                                                       Top.15 < Top.16
                                                        *)
 *)
Definition bar := ltac:(let t := eval compute in foo in exact t).
Check @bar. (* bar@{Top.27}
     : Type@{Top.27+1}
(* Top.27 |=  *) *)

Check @bar@{i}.
Definition baz (a := Type) (b := Type : a) (c := Type : b) := a -> c.
Definition qux := Eval compute in baz.
Check @qux. (* qux@{Top.38 Top.39 Top.40
Top.41}
     : Type@{max(Top.38+1, Top.41+1)}
(* Top.38 Top.39 Top.40 Top.41 |= Top.38 < Top.39
                                  Top.40 < Top.38
                                  Top.41 < Top.40
                                   *) *)
Print qux. (* qux@{Top.34 Top.35 Top.36 Top.37} =
Type@{Top.34} -> Type@{Top.37}
     : Type@{max(Top.34+1, Top.37+1)}
(* Top.34 Top.35 Top.36 Top.37 |= Top.34 < Top.35
                                  Top.36 < Top.34
                                  Top.37 < Top.36
                                   *) *)
Check @qux@{Type Type}.
(* used to have 4 universes *)
