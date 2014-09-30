(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Misctypes

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

(** Equalities on [glob_sort] *)

let glob_sort_eq g1 g2 = match g1, g2 with
| GProp, GProp -> true
| GSet, GSet -> true
| GType l1, GType l2 -> List.for_all2 CString.equal l1 l2
| _ -> false

let intro_pattern_naming_eq nam1 nam2 = match nam1, nam2 with
| IntroAnonymous, IntroAnonymous -> true
| IntroIdentifier id1, IntroIdentifier id2 -> Names.Id.equal id1 id2
| IntroFresh id1, IntroFresh id2 -> Names.Id.equal id1 id2
| _ -> false
