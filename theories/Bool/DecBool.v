(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Implicit Arguments On.

Definition ifdec : (A,B:Prop)(C:Set)({A}+{B})->C->C->C
   := [A,B,C,H,x,y]if H then [_]x else [_]y.


Theorem ifdec_left : (A,B:Prop)(C:Set)(H:{A}+{B})~B->(x,y:C)(ifdec H x y)=x.
Intros; Case H; Auto.
Intro; Absurd B; Trivial.
Save.

Theorem ifdec_right : (A,B:Prop)(C:Set)(H:{A}+{B})~A->(x,y:C)(ifdec H x y)=y.
Intros; Case H; Auto.
Intro; Absurd A; Trivial.
Save.

Implicit Arguments Off.
