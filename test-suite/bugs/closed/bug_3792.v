Fail Definition pull_if_dep
: forall {A} (P : bool -> Type) (a : A true) (a' : A false)
         (b : bool),
    P (if b as b return A b then a else a').
