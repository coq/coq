From Stdlib Require FunInd.
Set Universe Polymorphism.
Inductive ARG := phy | inf.
Function Phy (x:ARG): ARG := match x with inf => inf | _ => phy end
with Inf (x:ARG): ARG := match x with phy => phy | _ => inf end.
(* Used to be: Anomaly: Universe Top.998 undefined. Please report at
http://coq.inria.fr/bugs/.*)
