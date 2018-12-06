(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Printing of [intro_pattern] *)
open Pp
open Names
open Tactypes

let rec pr_intro_pattern prc {CAst.v=pat} = match pat with
  | IntroForthcoming true -> str "*"
  | IntroForthcoming false -> str "**"
  | IntroNaming p -> pr_intro_pattern_naming p
  | IntroAction p -> pr_intro_pattern_action prc p

and pr_intro_pattern_naming = let open Namegen in function
  | IntroIdentifier id -> Id.print id
  | IntroFresh id -> str "?" ++ Id.print id
  | IntroAnonymous -> str "?"

and pr_intro_pattern_action prc = function
  | IntroWildcard -> str "_"
  | IntroOrAndPattern pll -> pr_or_and_intro_pattern prc pll
  | IntroInjection pl ->
      str "[=" ++ hv 0 (prlist_with_sep spc (pr_intro_pattern prc) pl) ++
      str "]"
  | IntroApplyOn ({CAst.v=c},pat) -> pr_intro_pattern prc pat ++ str "%" ++ prc c
  | IntroRewrite true -> str "->"
  | IntroRewrite false -> str "<-"

and pr_or_and_intro_pattern prc = function
  | IntroAndPattern pl ->
      str "(" ++ hv 0 (prlist_with_sep pr_comma (pr_intro_pattern prc) pl) ++ str ")"
  | IntroOrPattern pll ->
      str "[" ++
      hv 0 (prlist_with_sep pr_bar (prlist_with_sep spc (pr_intro_pattern prc)) pll)
      ++ str "]"
