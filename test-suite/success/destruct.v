(* Simplification of bug 711 *)

Parameter f:true=false.
Goal let p=f in True.
Intro p.
LetTac b:=true.
NewDestruct b.
