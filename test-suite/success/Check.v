(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(* Compiling the theories allows to test parsing and typing but not printing *)
(* This file tests that pretty-printing does not fail                        *)
(* Test of exact output is not specified                                     *)

Check 0.
Check S.
Check nat.
