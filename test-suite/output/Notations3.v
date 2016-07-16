(**********************************************************************)
(* Check printing of notations with several instances of a recursive pattern *)
(* Was wrong but I could not trigger a problem due to the collision between *)
(* different instances of ".." *)

Notation "[< x , y , .. , z >]" := (pair (.. (pair x y) ..) z,pair y ( .. (pair z x) ..)).
Check [<0,2>].
Check ((0,2),(2,0)).
Check ((0,2),(2,2)).
Unset Printing Notations.
Check [<0,2>].
Set Printing Notations.
