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

Notation "<< x , y , .. , z >>" := ((.. (x,y) .., z),(z, .. (y,x) ..)).
Check <<0,2,4>>.
Check (((0,2),4),(4,(2,0))).
Check (((0,2),4),(2,(2,0))).
Check (((0,2),4),(0,(2,4))).
Unset Printing Notations.
Check <<0,2,4>>.
Set Printing Notations.

(**********************************************************************)
(* Check notations with recursive notations both in binders and terms *)

Notation "'ETA' x .. y , f" :=
  (fun x => .. (fun y => (.. (f x) ..) y ) ..)
  (at level 200, x binder, y binder).
Check ETA (x:nat) (y:nat), Nat.add.
Check ETA (x y:nat), Nat.add.
Check ETA x y, Nat.add.
Unset Printing Notations.
Check ETA (x:nat) (y:nat), Nat.add.
Set Printing Notations.
Check ETA x y, le_S.

Notation "'CURRY' x .. y , f" := (fun x => .. (fun y => f (x, .. (y,tt) ..)) ..) (at level 200, x binder, y binder).
Check fun f => CURRY (x:nat) (y:bool), f.
