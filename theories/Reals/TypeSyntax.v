(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(*********************************************************)
(*        Or and Exist in Type                           *)
(*                                                       *)
(*********************************************************)

(**********)
Inductive sumboolT [A,B:Prop]:Type:=
   leftT : A->(sumboolT A B)
  |rightT: B->(sumboolT A B).

(**********)
Inductive sumorT [A:Type;B:Prop]:Type:=
   inleftT : A->(sumorT A B)
  |inrightT: B->(sumorT A B).

(**********)
Inductive sigT [A:Set;P:A->Prop]:Type:=
   existT: (x:A)(P x)->(sigT A P).

(**********)
Inductive sigTT [A:Type;P:A->Prop]:Type:=
   existTT: (x:A)(P x)->(sigTT A P).
