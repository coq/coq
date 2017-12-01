(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Misctypes
open Genredexpr

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
| GType l1, GType l2 ->
   List.equal (Option.equal (fun (x,m) (y,n) -> Libnames.eq_reference x y && Int.equal m n)) l1 l2
| _ -> false

let intro_pattern_naming_eq nam1 nam2 = match nam1, nam2 with
| IntroAnonymous, IntroAnonymous -> true
| IntroIdentifier id1, IntroIdentifier id2 -> Names.Id.equal id1 id2
| IntroFresh id1, IntroFresh id2 -> Names.Id.equal id1 id2
| _ -> false

(** Mapping [red_expr_gen] *)

let map_flags f flags =
  { flags with rConst = List.map f flags.rConst }

let map_occs f (occ,e) = (occ,f e)

let map_red_expr_gen f g h = function
  | Fold l -> Fold (List.map f l)
  | Pattern occs_l -> Pattern (List.map (map_occs f) occs_l)
  | Simpl (flags,occs_o) ->
     Simpl (map_flags g flags, Option.map (map_occs (map_union g h)) occs_o)
  | Unfold occs_l -> Unfold (List.map (map_occs g) occs_l)
  | Cbv flags -> Cbv (map_flags g flags)
  | Lazy flags -> Lazy (map_flags g flags)
  | CbvVm occs_o -> CbvVm (Option.map (map_occs (map_union g h)) occs_o)
  | CbvNative occs_o -> CbvNative (Option.map (map_occs (map_union g h)) occs_o)
  | Cbn flags -> Cbn (map_flags g flags)
  | ExtraRedExpr _ | Red _ | Hnf as x -> x

(** Mapping bindings *)

let map_explicit_bindings f l =
  let map (loc, (hyp, x)) = (loc, (hyp, f x)) in
  List.map map l

let map_bindings f = function
| ImplicitBindings l -> ImplicitBindings (List.map f l)
| ExplicitBindings expl -> ExplicitBindings (map_explicit_bindings f expl)
| NoBindings -> NoBindings

let map_with_bindings f (x, bl) = (f x, map_bindings f bl)
