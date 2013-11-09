(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Names
open Tacexpr

type alias = string

let alias_map = Summary.ref ~name:"tactic-alias"
  (String.Map.empty : (DirPath.t * glob_tactic_expr) String.Map.t)

let register_alias key dp tac =
  alias_map := String.Map.add key (dp, tac) !alias_map

let interp_alias key =
  try String.Map.find key !alias_map
  with Not_found -> Errors.anomaly (str "Unknown tactic alias: " ++ str key)
