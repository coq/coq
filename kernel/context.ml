(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

open Util
open Names

(***************************************************************************)
(*     Type of assumptions                                                 *)
(***************************************************************************)

type named_declaration = Id.t * Constr.t option * Constr.t
type named_list_declaration = Id.t list * Constr.t option * Constr.t
type rel_declaration = Name.t * Constr.t option * Constr.t

let map_named_declaration_skel f (id, (v : Constr.t option), ty) =
  (id, Option.map f v, f ty)
let map_named_list_declaration = map_named_declaration_skel
let map_named_declaration = map_named_declaration_skel

let map_rel_declaration = map_named_declaration

let fold_named_declaration f (_, v, ty) a = f ty (Option.fold_right f v a)
let fold_rel_declaration = fold_named_declaration

let exists_named_declaration f (_, v, ty) = Option.cata f false v || f ty
let exists_rel_declaration f (_, v, ty) = Option.cata f false v || f ty

let for_all_named_declaration f (_, v, ty) = Option.cata f true v && f ty
let for_all_rel_declaration f (_, v, ty) = Option.cata f true v && f ty

let eq_named_declaration (i1, c1, t1) (i2, c2, t2) =
  Id.equal i1 i2 && Option.equal Constr.equal c1 c2 && Constr.equal t1 t2

let eq_rel_declaration (n1, c1, t1) (n2, c2, t2) =
  Name.equal n1 n2 && Option.equal Constr.equal c1 c2 && Constr.equal t1 t2

(***************************************************************************)
(*     Type of local contexts (telescopes)                                 *)
(***************************************************************************)

(*s Signatures of ordered optionally named variables, intended to be
   accessed by de Bruijn indices (to represent bound variables) *)

type rel_context = rel_declaration list

let empty_rel_context = []

let add_rel_decl d ctxt = d::ctxt

let rec lookup_rel n sign =
  match n, sign with
  | 1, decl :: _ -> decl
  | n, _ :: sign -> lookup_rel (n-1) sign
  | _, []        -> raise Not_found

let rel_context_length = List.length

let rel_context_nhyps hyps =
  let rec nhyps acc = function
    | [] -> acc
    | (_,None,_)::hyps -> nhyps (1+acc) hyps
    | (_,Some _,_)::hyps -> nhyps acc hyps in
  nhyps 0 hyps

let rel_context_tags ctx =
  let rec aux l = function
  | [] -> l
  | (_,Some _,_)::ctx -> aux (true::l) ctx
  | (_,None,_)::ctx -> aux (false::l) ctx
  in aux [] ctx

(*s Signatures of named hypotheses. Used for section variables and
    goal assumptions. *)

type named_context = named_declaration list
type named_list_context = named_list_declaration list

let empty_named_context = []

let add_named_decl d sign = d::sign

let rec lookup_named id = function
  | (id',_,_ as decl) :: _ when Id.equal id id' -> decl
  | _ :: sign -> lookup_named id sign
  | [] -> raise Not_found

let named_context_length = List.length
let named_context_equal = List.equal eq_named_declaration

let vars_of_named_context ctx =
  List.fold_left (fun accu (id, _, _) -> Id.Set.add id accu) Id.Set.empty ctx

let instance_from_named_context sign =
  let filter = function
  | (id, None, _) -> Some (Constr.mkVar id)
  | (_, Some _, _) -> None
  in
  List.map_filter filter sign

let fold_named_context f l ~init = List.fold_right f l init
let fold_named_list_context f l ~init = List.fold_right f l init
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
    List.smartmap map_decl l

let map_rel_context = map_context
let map_named_context = map_context

let iter_rel_context f = List.iter (fun (_,b,t) -> f t; Option.iter f b)
let iter_named_context f = List.iter (fun (_,b,t) -> f t; Option.iter f b)
