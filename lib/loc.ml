(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp

include Compat.Loc

(* Locations management *)

let dummy_loc = Compat.Loc.ghost
let join_loc = Compat.Loc.merge
let make_loc = Compat.make_loc
let unloc = Compat.unloc

type 'a located = t * 'a
let located_fold_left f x (_,a) = f x a
let located_iter2 f (_,a) (_,b) = f a b
let down_located f (_,a) = f a

let pr_located pr (loc, x) =
  if Flags.do_beautify () && loc <> dummy_loc then
    let (b, e) = unloc loc in
    Pp.comment b ++ pr x ++ Pp.comment e
  else pr x
