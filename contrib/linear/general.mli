(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

val substract : 'a list -> 'a list -> 'a list 
val union : 'a list -> 'a list -> 'a list
val glue : 'a list list -> 'a list
val disjoint : 'a list -> 'a list -> bool
val such_that : 'a list -> ('a -> bool) -> 'a list

