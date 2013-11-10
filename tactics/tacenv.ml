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

type alias = KerName.t

let alias_map = Summary.ref ~name:"tactic-alias"
  (KNmap.empty : (DirPath.t * glob_tactic_expr) KNmap.t)

let register_alias key dp tac =
  alias_map := KNmap.add key (dp, tac) !alias_map

let interp_alias key =
  try KNmap.find key !alias_map
  with Not_found -> Errors.anomaly (str "Unknown tactic alias: " ++ KerName.print key)
