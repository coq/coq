(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* some data to have informations on how we can indent proofs *)
type interp_node

(* the default value of this data *)
val first_interp_node : interp_node

(* the function to compute our data *)
val compute_interp_node :
  Ide_blob.goals Ide_blob.value ->
  interp_node -> Lib.library_segment Ide_blob.value -> interp_node * string option

(* our data are abstract, so we need to get access to some of it informations to
 * use it; that is the aim of (compute_nesting)
 * *)
type nesting = {
  module_levels : int;
  section_levels : int;
  subgoal_levels : int;
  tactic_levels : int;
  tactic_alinea : bool;
}
val compute_nesting : interp_node -> nesting
