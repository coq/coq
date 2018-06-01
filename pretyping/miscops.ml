(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
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

let glob_sort_eq g1 g2 = let open Glob_term in match g1, g2 with
| GProp, GProp -> true
| GSet, GSet -> true
| GType l1, GType l2 ->
   List.equal (Option.equal (fun (x,m) (y,n) -> Libnames.eq_reference x y && Int.equal m n)) l1 l2
| _ -> false

let intro_pattern_naming_eq nam1 nam2 = match nam1, nam2 with
| IntroAnonymous, IntroAnonymous -> true
| IntroIdentifier id1, IntroIdentifier id2 -> Names.Id.equal id1 id2
| IntroFresh id1, IntroFresh id2 -> Names.Id.equal id1 id2
| _ -> false

(** Mapping bindings *)

let map_explicit_bindings f l =
  let map = CAst.map (fun (hyp, x) -> (hyp, f x)) in
  List.map map l

let map_bindings f = function
| ImplicitBindings l -> ImplicitBindings (List.map f l)
| ExplicitBindings expl -> ExplicitBindings (map_explicit_bindings f expl)
| NoBindings -> NoBindings

let map_with_bindings f (x, bl) = (f x, map_bindings f bl)
