(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp

let pr_located pr (loc, x) =
  if !Flags.beautify && loc <> Loc.ghost then
    let (b, e) = Loc.unloc loc in
    (* Side-effect: order matters *)
    let before = Pp.comment (CLexer.extract_comments b) in
    let x = pr x in
    let after = Pp.comment (CLexer.extract_comments e) in
    before ++ x ++ after
  else pr x
