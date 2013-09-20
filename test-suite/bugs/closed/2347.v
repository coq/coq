Require Import EquivDec List.
Generalizable All Variables.

Program Definition list_eqdec `(eqa : EqDec A eq) : EqDec (list A) eq := 
 (fun (x y : list A) => _).
Admit Obligations of list_eqdec.

Program Definition list_eqdec' `(eqa : EqDec A eq) : EqDec (list A) eq :=
  (fun _ : nat => (fun (x y : list A) => _)) 0.
Admit Obligations of list_eqdec'.
