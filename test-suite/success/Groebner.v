Require Import GroebnerR ZArith Reals List Ring_polynom.

(** These exemples were initially in GroebnerR.v *)

Section Examples.

Delimit Scope PE_scope with PE.
Infix "+" := PEadd : PE_scope.
Infix "*" := PEmul : PE_scope.
Infix "-" := PEsub : PE_scope.
Infix "^" := PEpow : PE_scope.
Notation "[ n ]" := (@PEc Z n) (at level 0).

Open Scope R_scope.

Lemma example1 : forall x y,
  x+y=0 ->
  x*y=0 ->
  x^2=0.
Proof.
 groebnerR.
Qed.

Lemma example2 : forall x, x^2=0 -> x=0.
Proof.
 groebnerR.
Qed.

(*
Notation X  := (PEX Z 3).
Notation Y  := (PEX Z 2).
Notation Z_ := (PEX Z 1).
*)
Lemma example3 : forall x y z,
  x+y+z=0 ->
  x*y+x*z+y*z=0->
  x*y*z=0 -> x^3=0.
Proof.
Time groebnerR.
Qed.

(*
Notation X  := (PEX Z 4).
Notation Y  := (PEX Z 3).
Notation Z_ := (PEX Z 2).
Notation U  := (PEX Z 1).
*)
Lemma example4 : forall x y z u,
  x+y+z+u=0 ->
  x*y+x*z+x*u+y*z+y*u+z*u=0->
  x*y*z+x*y*u+x*z*u+y*z*u=0->
  x*y*z*u=0 -> x^4=0.
Proof.
Time groebnerR.
Qed.

(*
Notation x_ := (PEX Z 5).
Notation y_ := (PEX Z 4).
Notation z_ := (PEX Z 3).
Notation u_ := (PEX Z 2).
Notation v_ := (PEX Z 1).
Notation "x :: y" := (List.cons x y)
(at level 60, right associativity, format "'[hv' x  ::  '/' y ']'").
Notation "x :: y" := (List.app x y)
(at level 60, right associativity, format "x :: y").
*)

Lemma example5 : forall x y z u v,
  x+y+z+u+v=0 ->
  x*y+x*z+x*u+x*v+y*z+y*u+y*v+z*u+z*v+u*v=0->
  x*y*z+x*y*u+x*y*v+x*z*u+x*z*v+x*u*v+y*z*u+y*z*v+y*u*v+z*u*v=0->
  x*y*z*u+y*z*u*v+z*u*v*x+u*v*x*y+v*x*y*z=0 ->
  x*y*z*u*v=0 -> x^5=0.
Proof.
Time groebnerR.
Qed.

End Examples.