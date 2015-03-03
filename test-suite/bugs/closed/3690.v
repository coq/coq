Set Printing Universes.
Set Universe Polymorphism.
Definition foo (a := Type) (b := Type) (c := Type) := Type.
Print foo.
(* foo =
let a := Type@{Top.1} in
let b := Type@{Top.2} in let c := Type@{Top.3} in Type@{Top.4}
     : Type@{Top.4+1}
(* Top.1
   Top.2
   Top.3
   Top.4 |=  *) *)
Check @foo. (* foo@{Top.5 Top.6 Top.7
Top.8}
     : Type@{Top.8+1}
(* Top.5
   Top.6
   Top.7
   Top.8 |=  *) *)
Definition bar := $(let t := eval compute in foo in exact t)$.
Check @bar. (* bar@{Top.13 Top.14 Top.15
Top.16}
     : Type@{Top.16+1}
(* Top.13
   Top.14
   Top.15
   Top.16 |=  *) *)
(* The following should fail, since [bar] should only need one universe. *)
Check @bar@{i j}.
Definition baz (a := Type) (b := Type : a) (c := Type : b) := a -> c.
Definition qux := Eval compute in baz.
Check @qux. (* qux@{Top.24 Top.25
Top.26}
     : Type@{max(Top.24+1, Top.26+1)}
(* Top.24
   Top.25
   Top.26 |= Top.25 < Top.24
              Top.26 < Top.25
               *) *)
Print qux. (* qux =
Type@{Top.21} -> Type@{Top.23}
     : Type@{max(Top.21+1, Top.23+1)}
(* Top.21
   Top.22
   Top.23 |= Top.22 < Top.21
              Top.23 < Top.22
               *) *)
Fail Check @qux@{Set Set}.
Fail Check @qux@{Set Set Set}.
(* [qux] should only need two universes *)
Check @qux@{i j k}.  (* Error: The command has not failed!, but I think this is suboptimal *)
Fail Check @qux@{i j}.
