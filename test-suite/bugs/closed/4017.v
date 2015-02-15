Set Implicit Arguments.

(* Use of implicit arguments was lost in multiple variable declarations *)
Variables 
  (A1 : Type)
  (A2 : forall (x1 : A1), Type) 
  (A3 : forall (x1 : A1) (x2 : A2 x1), Type)
  (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type).
