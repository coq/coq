(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Misctypes
open Pp

(** Printing of [intro_pattern] *)

let rec pr_intro_pattern prc (_,pat) = match pat with
  | IntroForthcoming true -> str "*"
  | IntroForthcoming false -> str "**"
  | IntroNaming p -> pr_intro_pattern_naming p
  | IntroAction p -> pr_intro_pattern_action prc p

and pr_intro_pattern_naming = function
  | IntroIdentifier id -> Nameops.pr_id id
  | IntroFresh id -> str "?" ++ Nameops.pr_id id
  | IntroAnonymous -> str "?"

and pr_intro_pattern_action prc = function
  | IntroWildcard -> str "_"
  | IntroOrAndPattern pll -> pr_or_and_intro_pattern prc pll
  | IntroInjection pl ->
      str "[=" ++ hv 0 (prlist_with_sep spc (pr_intro_pattern prc) pl) ++
      str "]"
  | IntroApplyOn (c,pat) -> pr_intro_pattern prc pat ++ str "/" ++ prc c
  | IntroRewrite true -> str "->"
  | IntroRewrite false -> str "<-"

and pr_or_and_intro_pattern prc = function
  | [pl] ->
      str "(" ++ hv 0 (prlist_with_sep pr_comma (pr_intro_pattern prc) pl) ++ str ")"
  | pll ->
      str "[" ++
      hv 0 (prlist_with_sep pr_bar (prlist_with_sep spc (pr_intro_pattern prc)) pll)
      ++ str "]"

(** Printing of [move_location] *)

let pr_move_location pr_id = function
  | MoveAfter id -> brk(1,1) ++ str "after " ++ pr_id id
  | MoveBefore id -> brk(1,1) ++ str "before " ++ pr_id id
  | MoveFirst -> str " at top"
  | MoveLast -> str " at bottom"
