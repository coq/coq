(* Simplification of bug 711 *)

Parameter f:true=false.
Goal let p=f in True.
Intro p.
LetTac b:=true.
(* Check that it doesn't fail with an anomaly *)
(* Ultimately, adapt destruct to make it succeeding *)
Try NewDestruct b.
