(* A type, not a class *)
Variant T := mkT.

(* :> declares a coercion *)
Record R := { t_of_r :> T }.
Check forall r : R, r = r :> T.

(* A class *)
Class A := { p : Prop }.
(* A sub-class *)
Class B := { a_of_b :: A ; t_of_b :: T }.
(* The sub-instance is automatically inferred due to :: for a_of_b *)
Check forall b : B, p.
(* No coercion is introduced by :> in t_of_b *)
Fail Check forall b : B, b = b :> T.

(* Using :: when the RHS is not a class produces a “not-a-class” warning. *)
Set Warnings "+not-a-class".
Fail Class B' := { a_of_b' :: A ; t_of_b' :: T }.
