(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names

(***************************************************************************)
(*     Type of assumptions                                                 *)
(***************************************************************************)

type named_declaration = Id.t * Constr.t option * Constr.t
type rel_declaration = Name.t * Constr.t option * Constr.t

let map_named_declaration f (id, (v : Constr.t option), ty) =
  (id, Option.map f v, f ty)

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
