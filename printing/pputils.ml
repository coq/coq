(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp

let pr_located pr (loc, x) =
  if Flags.do_beautify () && loc <> Loc.ghost then
    let (b, e) = Loc.unloc loc in
    Pp.comment b ++ pr x ++ Pp.comment e
  else pr x
