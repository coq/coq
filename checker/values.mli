(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type value =
  | Any
  | Fail of string
  | Tuple of string * value array
  | Sum of string * int * value array array
  | Array of value
  | List of value
  | Opt of value
  | Int
  | String
  | Annot of string * value
  | Dyn

val v_univopaques : value
val v_libsum : value
val v_lib : value
val v_opaques : value
val v_stm_seg : value
