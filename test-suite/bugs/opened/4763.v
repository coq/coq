Require Import Coq.Arith.Arith Coq.Classes.Morphisms Coq.Classes.RelationClasses.
Coercion is_true : bool >-> Sortclass.
Global Instance: Transitive leb.
Admitted.

Goal forall x y z, leb x y -> leb y z -> True.
  intros ??? H H'.
  Typeclasses eauto := debug.
  Fail lazymatch goal with
  | [ H : is_true (?R ?x ?y), H' : is_true (?R ?y ?z) |- _ ]
    => pose proof (transitivity H H' : is_true (R x z))
  end. (* should succeed without [Fail], as in 8.4 *)
(* 8.4:
1.1: exact Transitive_instance_0 on
(Transitive ?16)
*)

(* Debug: 1.1: apply @Equivalence_Transitive on (Transitive ?R)
Debug: 1.1.1: no match for (Equivalence ?R) , 8 possibilities
Debug: Backtracking after apply @Equivalence_Transitive
Debug: 1.2: apply @StrictOrder_Transitive on (Transitive ?R)
Debug: 1.2.1: no match for (StrictOrder ?R) , 6 possibilities
Debug: Backtracking after apply @StrictOrder_Transitive
Debug: 1.3: apply @PreOrder_Transitive on (Transitive ?R)
Debug: 1.3.1.1: apply @Equivalence_PreOrder on (PreOrder ?R)
Debug: 1.3.1.1.1: no match for (Equivalence ?R) , 8 possibilities
Debug: Backtracking after apply @Equivalence_PreOrder
Debug: Backtracking after apply @PreOrder_Transitive
Debug: 1.4: apply @PER_Transitive on (Transitive ?R)
Debug: 1.4.1.1: apply @Equivalence_PER on (PER ?R)
Debug: 1.4.1.1.1: no match for (Equivalence ?R) , 8 possibilities
Debug: Backtracking after apply @Equivalence_PER
Debug: Backtracking after apply @PER_Transitive
Debug: 1.1: apply @Equivalence_Transitive on (Transitive ?R)
Debug: 1.1.1: no match for (Equivalence ?R) , 8 possibilities
Debug: Backtracking after apply @Equivalence_Transitive
Debug: 1.2: apply @StrictOrder_Transitive on (Transitive ?R)
Debug: 1.2.1: no match for (StrictOrder ?R) , 6 possibilities
Debug: Backtracking after apply @StrictOrder_Transitive
Debug: 1.3: apply @PreOrder_Transitive on (Transitive ?R)
Debug: 1.3.1.1: apply @Equivalence_PreOrder on (PreOrder ?R)
Debug: 1.3.1.1.1: no match for (Equivalence ?R) , 8 possibilities
Debug: Backtracking after apply @Equivalence_PreOrder
Debug: Backtracking after apply @PreOrder_Transitive
Debug: 1.4: apply @PER_Transitive on (Transitive ?R)
Debug: 1.4.1.1: apply @Equivalence_PER on (PER ?R)
Debug: 1.4.1.1.1: no match for (Equivalence ?R) , 8 possibilities
Debug: Backtracking after apply @Equivalence_PER
Debug: Backtracking after apply @PER_Transitive
Error:
Unable to satisfy the following constraints:
In environment:
x, y, z : nat
H : x <=? y
H' : y <=? z

?A : "Type"
?R : "Relation_Definitions.relation ?A"
?Transitive : "Transitive ?R"
?x : "?A"
?y : "?A"
?z : "?A"[x y z H H'] [] |- (x <=? y) = true <= ?X13@{__:=x; __:=y; __:=z; __:=H; __:=H'} ?X15@{__:=x; __:=y; __:=z; __:=H; __:=H'}
                                                  ?X16@{__:=x; __:=y; __:=z; __:=H; __:=H'}
[x y z H H'] [] |- (y <=? z) = true <= ?X13@{__:=x; __:=y; __:=z; __:=H; __:=H'} ?X16@{__:=x; __:=y; __:=z; __:=H; __:=H'}
                                         ?X17@{__:=x; __:=y; __:=z; __:=H; __:=H'}
[x y z H H'] [] |- ?X13@{__:=x; __:=y; __:=z; __:=H; __:=H'} ?X15@{__:=x; __:=y; __:=z; __:=H; __:=H'}
                     ?X17@{__:=x; __:=y; __:=z; __:=H; __:=H'} <= (x <=? z) = true  *)
