(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** The ast type contains generic metadata for AST nodes. *)
type 'a ast = {
  v   : 'a;
  loc : Loc.t option;
}

let make ?loc v = { v; loc }

let map f n = { n with v = f n.v }
let map_with_loc f n = { n with v = f ?loc:n.loc n.v }
let map_from_loc f n =
  let loc, v = Loc.to_pair n in
  { v = f ?loc v ; loc }

let with_val f n = f n.v
let with_loc_val f n = f ?loc:n.loc n.v
