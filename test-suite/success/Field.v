(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(**** Tests of Field with real numbers ****)

Require Reals.

(* Example 1 *)
Goal (eps:R)``eps*1/(2+2)+eps*1/(2+2) == eps*1/2``.
Proof.
  Intros.
  Field.
Abort.

(* Example 2 *)
Goal  (f,g:(R->R); x0,x1:R)
    ``((f x1)-(f x0))*1/(x1-x0)+((g x1)-(g x0))*1/(x1-x0) == ((f x1)+
    (g x1)-((f x0)+(g x0)))*1/(x1-x0)``.
Proof.
  Intros.
  Field.
Abort.
 
(* Example 3 *)
Goal (a,b:R)``1/(a*b)*1/1/b == 1/a``.
Proof.
  Intros.
  Field.
Abort.
 
(* Example 4 *)
Goal (a,b:R)``a <> 0``->``b <> 0``->``1/(a*b)/1/b == 1/a``.
Proof.
  Intros.
  Field.
Abort.
 
(* Example 5 *)
Goal (a:R)``1 == 1*1/a*a``.
Proof.
  Intros.
  Field.
Abort.
 
(* Example 6 *)
Goal (a,b:R)``b == b*/a*a``.
Proof.
  Intros.
  Field.
Abort.
 
(* Example 7 *)
Goal (a,b:R)``b == b*1/a*a``.
Proof.
  Intros.
  Field.
Abort.

(* Example 8 *)
Goal (x,y:R)``x*((1/x)+x/(x+y)) == -(1/y)*y*(-(x*x/(x+y))-1)``.
Proof.
  Intros.
  Field.
Abort.
