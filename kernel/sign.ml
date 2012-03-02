(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Jean-Christophe Filliâtre out of names.ml as part of the
   rebuilding of Coq around a purely functional abstract type-checker,
   Aug 1999 *)
(* Miscellaneous extensions, restructurations and bug-fixes by Hugo
   Herbelin and Bruno Barras *)

(* This file defines types and combinators regarding indexes-based and
   names-based contexts *)

open Names
open Errors
open Util
open Term

(*s Signatures of named hypotheses. Used for section variables and
    goal assumptions. *)

type named_context = named_declaration list

let empty_named_context = []

let add_named_decl d sign = d::sign

let rec lookup_named id = function
  | (id',_,_ as decl) :: _ when id=id' -> decl
  | _ :: sign -> lookup_named id sign
  | [] -> raise Not_found

let named_context_length = List.length
let named_context_equal = list_equal eq_named_declaration

let vars_of_named_context = List.map (fun (id,_,_) -> id)

let instance_from_named_context sign =
  let rec inst_rec = function
    | (id,None,_) :: sign -> mkVar id :: inst_rec sign
    | _ :: sign -> inst_rec sign
    | [] -> [] in
  Array.of_list (inst_rec sign)

let fold_named_context f l ~init = List.fold_right f l init
let fold_named_context_reverse f ~init l = List.fold_left f init l

(*s Signatures of ordered section variables *)
type section_context = named_context

let fold_rel_context f l ~init:x = List.fold_right f l x
let fold_rel_context_reverse f ~init:x l = List.fold_left f x l

let map_context f l =
  let map_decl (n, body_o, typ as decl) =
    let body_o' = Option.smartmap f body_o in
    let typ' = f typ in
      if body_o' == body_o && typ' == typ then decl else
	(n, body_o', typ')
  in
    list_smartmap map_decl l

let map_rel_context = map_context
let map_named_context = map_context

let iter_rel_context f = List.iter (fun (_,b,t) -> f t; Option.iter f b)
let iter_named_context f = List.iter (fun (_,b,t) -> f t; Option.iter f b)

(* Push named declarations on top of a rel context *)
(* Bizarre. Should be avoided. *)
let push_named_to_rel_context hyps ctxt =
  let rec push = function
    | (id,b,t) :: l ->
	let s, hyps = push l in
	let d = (Name id, Option.map (subst_vars s) b, subst_vars s t) in
	id::s, d::hyps
    | [] -> [],[] in
  let s, hyps = push hyps in
  let rec subst = function
    | d :: l ->
	let n, ctxt = subst l in
	(n+1), (map_rel_declaration (substn_vars n s) d)::ctxt
    | [] -> 1, hyps in
  snd (subst ctxt)
