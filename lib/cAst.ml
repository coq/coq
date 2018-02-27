(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The ast type contains generic metadata for AST nodes. *)
type 'a t = {
  v   : 'a;
  loc : Loc.t option;
}

let make ?loc v = { v; loc }

let map f n = { n with v = f n.v }
let map_with_loc f n = { n with v = f ?loc:n.loc n.v }
let map_from_loc f l =
  let loc, v = l in
  { v = f ?loc v ; loc }

let with_val f n = f n.v
let with_loc_val f n = f ?loc:n.loc n.v
