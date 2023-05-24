Declare ML Module "observer.plugin".

Class Def (A : Type) := { default : A }.

Instance def_nat : Def nat := {| default := 0 |}.

Instance def_bool : Def bool | 33 := {| default := false |}.

Section X.
  Instance def_bool2 : Def bool | 21 := {| default := false |}.
End X.
