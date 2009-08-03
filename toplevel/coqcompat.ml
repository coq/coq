(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* File initially created by Hugo Herbelin, Aug 2009 *)

(* This file centralizes the support for compatibility with previous
   versions of Coq *)

open Pp
open Util
open Goptions

let set_compat_options = function
  | "8.2" ->
      set_bool_option_value ["Tactic";"Evars";"Pattern";"Unification"] false;
      set_bool_option_value ["Discriminate";"Introduction"] false;
      set_bool_option_value ["Intuition";"Iff";"Unfolding"] true

  | "8.1" ->
      warning "Compatibility with version 8.1 not supported."

  | "8.0" ->
      warning "Compatibility with version 8.0 not supported."

  | s ->
      error ("Unknown compatibility version \""^s^"\".")
