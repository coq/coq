(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(* Compiling the theories allows testing parsing and typing but not printing *)
(* This file tests that pretty-printing does not fail                        *)
(* Test of exact output is not specified                                     *)

Check 0.
Check S.
Check nat.
