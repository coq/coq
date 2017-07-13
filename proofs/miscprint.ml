(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
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
  | IntroApplyOn ((_,c),pat) -> pr_intro_pattern prc pat ++ str "%" ++ prc c
  | IntroRewrite true -> str "->"
  | IntroRewrite false -> str "<-"

and pr_or_and_intro_pattern prc = function
  | IntroAndPattern pl ->
      str "(" ++ hv 0 (prlist_with_sep pr_comma (pr_intro_pattern prc) pl) ++ str ")"
  | IntroOrPattern pll ->
      str "[" ++
      hv 0 (prlist_with_sep pr_bar (prlist_with_sep spc (pr_intro_pattern prc)) pll)
      ++ str "]"

(** Printing of [move_location] *)

let pr_move_location pr_id = function
  | MoveAfter id -> brk(1,1) ++ str "after " ++ pr_id id
  | MoveBefore id -> brk(1,1) ++ str "before " ++ pr_id id
  | MoveFirst -> str " at top"
  | MoveLast -> str " at bottom"

(** Printing of bindings *)
let pr_binding prc = function
  | loc, (NamedHyp id, c) -> hov 1 (Names.Id.print id ++ str " := " ++ cut () ++ prc c)
  | loc, (AnonHyp n, c) -> hov 1 (int n ++ str " := " ++ cut () ++ prc c)

let pr_bindings prc prlc = function
  | ImplicitBindings l ->
    brk (1,1) ++ str "with" ++ brk (1,1) ++
    pr_sequence prc l
  | ExplicitBindings l ->
    brk (1,1) ++ str "with" ++ brk (1,1) ++
    pr_sequence (fun b -> str"(" ++ pr_binding prlc b ++ str")") l
  | NoBindings -> mt ()

let pr_bindings_no_with prc prlc = function
  | ImplicitBindings l ->
    brk (0,1) ++ prlist_with_sep spc prc l
  | ExplicitBindings l ->
    brk (0,1) ++ prlist_with_sep spc (fun b -> str"(" ++ pr_binding prlc b ++ str")") l
  | NoBindings -> mt ()

let pr_with_bindings prc prlc (c,bl) =
  hov 1 (prc c ++ pr_bindings prc prlc bl)

