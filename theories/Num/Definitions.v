(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(*i $Id $ i*)

(*s 
  Axiomatisation of a numerical set 
  It will be instantiated by Z and R later on
  We choose to introduce many operation to allow flexibility in definition 
  ([S] is primitive in the definition of [nat] while [add] and [one] 
   are primitive in the definition 
*)

Parameter N:Type.
Parameter zero:N.
Parameter one:N.
Parameter add:N->N->N.
Parameter S:N->N.

(*s Relations *)
Parameter eq,lt,le,gt,ge:N->N->Prop.    
Definition neq [x,y:N] := (eq x y)->False.

