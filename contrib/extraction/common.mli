(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Names
open Miniml
open Mlutil

val print_one_decl :
  ml_structure -> module_path -> ml_decl -> unit

val print_structure_to_file : 
  (string * string) option -> extraction_params -> ml_structure -> unit


