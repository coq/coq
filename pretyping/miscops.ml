(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Misctypes
open Pp
open Nameops

(** Mapping [cast_type] *)

let map_cast_type f = function
  | CastConv a -> CastConv (f a)
  | CastVM a -> CastVM (f a)
  | CastCoerce -> CastCoerce
  | CastNative a -> CastNative (f a)

let smartmap_cast_type f c =
  match c with
    | CastConv a -> let a' = f a in if a' == a then c else CastConv a'
    | CastVM a -> let a' = f a in if a' == a then c else CastVM a'
    | CastCoerce -> CastCoerce
    | CastNative a -> let a' = f a in if a' == a then c else CastNative a'

(** Printing of [intro_pattern] *)

let rec pr_intro_pattern (_,pat) = match pat with
  | IntroOrAndPattern pll -> pr_or_and_intro_pattern pll
  | IntroWildcard -> str "_"
  | IntroRewrite true -> str "->"
  | IntroRewrite false -> str "<-"
  | IntroIdentifier id -> pr_id id
  | IntroFresh id -> str "?" ++ pr_id id
  | IntroForthcoming true -> str "*"
  | IntroForthcoming false -> str "**"
  | IntroAnonymous -> str "?"

and pr_or_and_intro_pattern = function
  | [pl] ->
      str "(" ++ hv 0 (prlist_with_sep pr_comma pr_intro_pattern pl) ++ str ")"
  | pll ->
      str "[" ++
      hv 0 (prlist_with_sep pr_bar (prlist_with_sep spc pr_intro_pattern) pll)
      ++ str "]"

(** Printing of [move_location] *)

let pr_move_location pr_id = function
  | MoveAfter id -> brk(1,1) ++ str "after " ++ pr_id id
  | MoveBefore id -> brk(1,1) ++ str "before " ++ pr_id id
  | MoveFirst -> str " at top"
  | MoveLast -> str " at bottom"
