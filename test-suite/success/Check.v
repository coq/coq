(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(* Compiling the theories allows to test parsing and typing but not printing *)
(* This file tests that pretty-printing does not fail                        *)
(* Test of exact output is not specified                                     *)

Check O.
Check S.
Check nat.
