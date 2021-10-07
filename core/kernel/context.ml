(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Jean-Christophe Filliâtre out of names.ml as part of the
   rebuilding of Coq around a purely functional abstract type-checker,
   Aug 1999 *)
(* Miscellaneous extensions, restructurations and bug-fixes by Hugo
   Herbelin and Bruno Barras *)

(* This file defines types and combinators regarding indexes-based and
   names-based contexts *)

(** The modules defined below represent a {e local context}
    as defined by Chapter 4 in the Reference Manual:

    A {e local context} is an ordered list of of {e local declarations}
    of names that we call {e variables}.

    A {e local declaration} of some variable can be either:
    - a {e local assumption}, or
    - a {e local definition}.
*)

open Util
open Names

type 'a binder_annot = { binder_name : 'a; binder_relevance : Sorts.relevance }

let eq_annot eq {binder_name=na1;binder_relevance=r1} {binder_name=na2;binder_relevance=r2} =
  eq na1 na2 && Sorts.relevance_equal r1 r2

let hash_annot h {binder_name=n;binder_relevance=r} =
  Hashset.Combine.combinesmall (Sorts.relevance_hash r) (h n)

let map_annot f {binder_name=na;binder_relevance} =
  {binder_name=f na;binder_relevance}

let make_annot x r = {binder_name=x;binder_relevance=r}

let binder_name x = x.binder_name
let binder_relevance x = x.binder_relevance

let annotR x = make_annot x Sorts.Relevant

let nameR x = annotR (Name x)
let anonR = annotR Anonymous

(** Representation of contexts that can capture anonymous as well as non-anonymous variables.
    Individual declarations are then designated by de Bruijn indexes. *)
module Rel =
struct
  (** Representation of {e local declarations}. *)
  module Declaration =
  struct
    (* local declaration *)
    type ('constr, 'types) pt =
      | LocalAssum of Name.t binder_annot * 'types            (** name, type *)
      | LocalDef of Name.t binder_annot * 'constr * 'types   (** name, value, type *)

    let get_annot = function
      | LocalAssum (na,_) | LocalDef (na,_,_) -> na

    (** Return the name bound by a given declaration. *)
    let get_name x = (get_annot x).binder_name

    (** Return [Some value] for local-declarations and [None] for local-assumptions. *)
    let get_value = function
      | LocalAssum _ -> None
      | LocalDef (_,v,_) -> Some v

    (** Return the type of the name bound by a given declaration. *)
    let get_type = function
      | LocalAssum (_,ty)
      | LocalDef (_,_,ty) -> ty

    let get_relevance x = (get_annot x).binder_relevance

    (** Set the name that is bound by a given declaration. *)
    let set_name na = function
      | LocalAssum (x,ty) -> LocalAssum ({x with binder_name=na}, ty)
      | LocalDef (x,v,ty) -> LocalDef ({x with binder_name=na}, v, ty)

    (** Set the type of the bound variable in a given declaration. *)
    let set_type ty = function
      | LocalAssum (na,_) -> LocalAssum (na, ty)
      | LocalDef (na,v,_) -> LocalDef (na, v, ty)

    (** Return [true] iff a given declaration is a local assumption. *)
    let is_local_assum = function
      | LocalAssum _ -> true
      | LocalDef _ -> false

    (** Return [true] iff a given declaration is a local definition. *)
    let is_local_def = function
      | LocalAssum _ -> false
      | LocalDef _ -> true

    (** Check whether any term in a given declaration satisfies a given predicate. *)
    let exists f = function
      | LocalAssum (_, ty) -> f ty
      | LocalDef (_, v, ty) -> f v || f ty

      (** Check whether all terms in a given declaration satisfy a given predicate. *)
    let for_all f = function
      | LocalAssum (_, ty) -> f ty
      | LocalDef (_, v, ty) -> f v && f ty

    (** Check whether the two given declarations are equal. *)
    let equal eq decl1 decl2 =
      match decl1, decl2 with
      | LocalAssum (n1,ty1), LocalAssum (n2, ty2) ->
          eq_annot Name.equal n1 n2 && eq ty1 ty2
      | LocalDef (n1,v1,ty1), LocalDef (n2,v2,ty2) ->
          eq_annot Name.equal n1 n2 && eq v1 v2 && eq ty1 ty2
      | _ ->
          false

    (** Map the name bound by a given declaration. *)
    let map_name f x =
      let na = get_name x in
      let na' = f na in
      if na == na' then x else set_name na' x

    (** For local assumptions, this function returns the original local assumptions.
        For local definitions, this function maps the value in the local definition. *)
    let map_value f = function
      | LocalAssum _ as decl -> decl
      | LocalDef (na, v, t) as decl ->
          let v' = f v in
          if v == v' then decl else LocalDef (na, v', t)

    (** Map the type of the name bound by a given declaration. *)
    let map_type f = function
      | LocalAssum (na, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (na, ty')
      | LocalDef (na, v, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalDef (na, v, ty')

    (** Map all terms in a given declaration. *)
    let map_constr f = function
      | LocalAssum (na, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (na, ty')
      | LocalDef (na, v, ty) as decl ->
          let v' = f v in
          let ty' = f ty in
          if v == v' && ty == ty' then decl else LocalDef (na, v', ty')

    let map_constr_het f = function
      | LocalAssum (na, ty) ->
          let ty' = f ty in
          LocalAssum (na, ty')
      | LocalDef (na, v, ty) ->
          let v' = f v in
          let ty' = f ty in
          LocalDef (na, v', ty')

    (** Perform a given action on all terms in a given declaration. *)
    let iter_constr f = function
      | LocalAssum (_,ty) -> f ty
      | LocalDef (_,v,ty) -> f v; f ty

    (** Reduce all terms in a given declaration to a single value. *)
    let fold_constr f decl acc =
      match decl with
      | LocalAssum (_n,ty) -> f ty acc
      | LocalDef (_n,v,ty) -> f ty (f v acc)

    let to_tuple = function
      | LocalAssum (na, ty) -> na, None, ty
      | LocalDef (na, v, ty) -> na, Some v, ty

    let drop_body = function
      | LocalAssum _ as d -> d
      | LocalDef (na, _v, ty) -> LocalAssum (na, ty)

  end

  (** Rel-context is represented as a list of declarations.
      Inner-most declarations are at the beginning of the list.
      Outer-most declarations are at the end of the list. *)
  type ('constr, 'types) pt = ('constr, 'types) Declaration.pt list

  (** empty rel-context *)
  let empty = []

  (** Return a new rel-context enriched by with a given inner-most declaration. *)
  let add d ctx = d :: ctx

  (** Return the number of {e local declarations} in a given rel-context. *)
  let length = List.length

  (** Return the number of {e local assumptions} in a given rel-context. *)
  let nhyps ctx =
    let open Declaration in
    let rec nhyps acc = function
      | [] -> acc
      | LocalAssum _ :: hyps -> nhyps (succ acc) hyps
      | LocalDef _ :: hyps -> nhyps acc hyps
    in
    nhyps 0 ctx

  (** Return a declaration designated by a given de Bruijn index.
      @raise Not_found if the designated de Bruijn index is not present in the designated rel-context. *)
  let rec lookup n ctx =
    match n, ctx with
    | 1, decl :: _ -> decl
    | n, _ :: sign -> lookup (n-1) sign
    | _, []        -> raise Not_found

  (** Check whether given two rel-contexts are equal. *)
  let equal eq l = List.equal (fun c -> Declaration.equal eq c) l

  (** Map all terms in a given rel-context. *)
  let map f = List.Smart.map (Declaration.map_constr f)

  (** Map all terms in a given rel-context. *)
  let map_with_binders f ctx =
    let rec aux k = function
      | decl :: ctx as l ->
        let decl' = Declaration.map_constr (f k) decl in
        let ctx' = aux (k-1) ctx in
        if decl == decl' && ctx == ctx' then l else decl' :: ctx'
      | [] -> []
    in
    aux (length ctx) ctx

  (** Perform a given action on every declaration in a given rel-context. *)
  let iter f = List.iter (Declaration.iter_constr f)

  (** Reduce all terms in a given rel-context to a single value.
      Innermost declarations are processed first. *)
  let fold_inside f ~init = List.fold_left f init

  (** Reduce all terms in a given rel-context to a single value.
      Outermost declarations are processed first. *)
  let fold_outside f l ~init = List.fold_right f l init

  (** Map a given rel-context to a list where each {e local assumption} is mapped to [true]
      and each {e local definition} is mapped to [false]. *)
  let to_tags l =
    let rec aux l = function
      | [] -> l
      | Declaration.LocalDef _ :: ctx -> aux (true::l) ctx
      | Declaration.LocalAssum _ :: ctx -> aux (false::l) ctx
    in aux [] l

  let drop_bodies l = List.Smart.map Declaration.drop_body l

  (** [extended_list n Γ] builds an instance [args] such that [Γ,Δ ⊢ args:Γ]
      with n = |Δ| and with the {e local definitions} of [Γ] skipped in
      [args]. Example: for [x:T, y:=c, z:U] and [n]=2, it gives [Rel 5, Rel 3]. *)
  let to_extended_list mk n l =
    let rec reln l p = function
      | Declaration.LocalAssum _ :: hyps -> reln (mk (n+p) :: l) (p+1) hyps
      | Declaration.LocalDef _ :: hyps -> reln l (p+1) hyps
      | [] -> l
    in
    reln [] 1 l

  (** [extended_vect n Γ] does the same, returning instead an array. *)
  let to_extended_vect mk n hyps = Array.of_list (to_extended_list mk n hyps)

  (** Consistency with terminology in Named *)
  let instance = to_extended_vect
  let instance_list = to_extended_list
end

(** This module represents contexts that can capture non-anonymous variables.
    Individual declarations are then designated by the identifiers they bind. *)
module Named =
struct
  (** Representation of {e local declarations}. *)
  module Declaration =
  struct
    (** local declaration *)
    type ('constr, 'types) pt =
      | LocalAssum of Id.t binder_annot * 'types             (** identifier, type *)
      | LocalDef of Id.t binder_annot * 'constr * 'types    (** identifier, value, type *)

    let get_annot = function
      | LocalAssum (na,_) | LocalDef (na,_,_) -> na

    (** Return the identifier bound by a given declaration. *)
    let get_id x = (get_annot x).binder_name

    (** Return [Some value] for local-declarations and [None] for local-assumptions. *)
    let get_value = function
      | LocalAssum _ -> None
      | LocalDef (_,v,_) -> Some v

    (** Return the type of the name bound by a given declaration. *)
    let get_type = function
      | LocalAssum (_,ty)
      | LocalDef (_,_,ty) -> ty

    let get_relevance x = (get_annot x).binder_relevance

    (** Set the identifier that is bound by a given declaration. *)
    let set_id id =
      let set x = {x with binder_name = id} in
      function
      | LocalAssum (x,ty) -> LocalAssum (set x, ty)
      | LocalDef (x, v, ty) -> LocalDef (set x, v, ty)

    (** Set the type of the bound variable in a given declaration. *)
    let set_type ty = function
      | LocalAssum (id,_) -> LocalAssum (id, ty)
      | LocalDef (id,v,_) -> LocalDef (id, v, ty)

    (** Return [true] iff a given declaration is a local assumption. *)
    let is_local_assum = function
      | LocalAssum _ -> true
      | LocalDef _ -> false

    (** Return [true] iff a given declaration is a local definition. *)
    let is_local_def = function
      | LocalDef _ -> true
      | LocalAssum _ -> false

    (** Check whether any term in a given declaration satisfies a given predicate. *)
    let exists f = function
      | LocalAssum (_, ty) -> f ty
      | LocalDef (_, v, ty) -> f v || f ty

    (** Check whether all terms in a given declaration satisfy a given predicate. *)
    let for_all f = function
      | LocalAssum (_, ty) -> f ty
      | LocalDef (_, v, ty) -> f v && f ty

    (** Check whether the two given declarations are equal. *)
    let equal eq decl1 decl2 =
      match decl1, decl2 with
      | LocalAssum (id1, ty1), LocalAssum (id2, ty2) ->
          eq_annot Id.equal id1 id2 && eq ty1 ty2
      | LocalDef (id1, v1, ty1), LocalDef (id2, v2, ty2) ->
          eq_annot Id.equal id1 id2 && eq v1 v2 && eq ty1 ty2
      | _ ->
          false

    (** Map the identifier bound by a given declaration. *)
    let map_id f x =
      let id = get_id x in
      let id' = f id in
      if id == id' then x else set_id id' x

    (** For local assumptions, this function returns the original local assumptions.
        For local definitions, this function maps the value in the local definition. *)
    let map_value f = function
      | LocalAssum _ as decl -> decl
      | LocalDef (na, v, t) as decl ->
          let v' = f v in
          if v == v' then decl else LocalDef (na, v', t)

    (** Map the type of the name bound by a given declaration. *)
    let map_type f = function
      | LocalAssum (id, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (id, ty')
      | LocalDef (id, v, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalDef (id, v, ty')

    (** Map all terms in a given declaration. *)
    let map_constr f = function
      | LocalAssum (id, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (id, ty')
      | LocalDef (id, v, ty) as decl ->
          let v' = f v in
          let ty' = f ty in
          if v == v' && ty == ty' then decl else LocalDef (id, v', ty')

    let map_constr_het f = function
      | LocalAssum (id, ty) ->
          let ty' = f ty in
          LocalAssum (id, ty')
      | LocalDef (id, v, ty) ->
          let v' = f v in
          let ty' = f ty in
          LocalDef (id, v', ty')

    (** Perform a given action on all terms in a given declaration. *)
    let iter_constr f = function
      | LocalAssum (_, ty) -> f ty
      | LocalDef (_, v, ty) -> f v; f ty

    (** Reduce all terms in a given declaration to a single value. *)
    let fold_constr f decl a =
      match decl with
      | LocalAssum (_, ty) -> f ty a
      | LocalDef (_, v, ty) -> a |> f v |> f ty

    let to_tuple = function
      | LocalAssum (id, ty) -> id, None, ty
      | LocalDef (id, v, ty) -> id, Some v, ty

    let of_tuple = function
      | id, None, ty -> LocalAssum (id, ty)
      | id, Some v, ty -> LocalDef (id, v, ty)

    let drop_body = function
      | LocalAssum _ as d -> d
      | LocalDef (id, _v, ty) -> LocalAssum (id, ty)

    let of_rel_decl f = function
      | Rel.Declaration.LocalAssum (na,t) ->
          LocalAssum (map_annot f na, t)
      | Rel.Declaration.LocalDef (na,v,t) ->
          LocalDef (map_annot f na, v, t)

    let to_rel_decl =
      let name x = {binder_name=Name x.binder_name;binder_relevance=x.binder_relevance} in
      function
      | LocalAssum (id,t) ->
          Rel.Declaration.LocalAssum (name id, t)
      | LocalDef (id,v,t) ->
          Rel.Declaration.LocalDef (name id,v,t)
  end

  (** Named-context is represented as a list of declarations.
      Inner-most declarations are at the beginning of the list.
      Outer-most declarations are at the end of the list. *)
  type ('constr, 'types) pt = ('constr, 'types) Declaration.pt list

  (** empty named-context *)
  let empty = []

  (** Return a new named-context enriched by with a given inner-most declaration. *)
  let add d ctx = d :: ctx

  (** Return the number of {e local declarations} in a given named-context. *)
  let length = List.length

(** Return a declaration designated by a given identifier
    @raise Not_found if the designated identifier is not present in the designated named-context. *)
  let rec lookup id = function
    | decl :: _ when Id.equal id (Declaration.get_id decl) -> decl
    | _ :: sign -> lookup id sign
    | [] -> raise Not_found

  (** Check whether given two named-contexts are equal. *)
  let equal eq l = List.equal (fun c -> Declaration.equal eq c) l

  (** Map all terms in a given named-context. *)
  let map f = List.Smart.map (Declaration.map_constr f)

  (** Perform a given action on every declaration in a given named-context. *)
  let iter f = List.iter (Declaration.iter_constr f)

  (** Reduce all terms in a given named-context to a single value.
      Innermost declarations are processed first. *)
  let fold_inside f ~init = List.fold_left f init

  (** Reduce all terms in a given named-context to a single value.
      Outermost declarations are processed first. *)
  let fold_outside f l ~init = List.fold_right f l init

  (** Return the set of all identifiers bound in a given named-context. *)
  let to_vars l =
    List.fold_left (fun accu decl -> Id.Set.add (Declaration.get_id decl) accu) Id.Set.empty l

  let drop_bodies l = List.Smart.map Declaration.drop_body l

  (** [to_instance Ω] builds an instance [args] in reverse order such
      that [Ω ⊢ args:Ω] where [Ω] is a named context and with the local
      definitions of [Ω] skipped. Example: for [id1:T,id2:=c,id3:U], it
      gives [Var id1, Var id3]. All [idj] are supposed distinct. *)
  let to_instance mk l =
    let filter = function
      | Declaration.LocalAssum (id, _) -> Some (mk id.binder_name)
      | _ -> None
    in
    List.map_filter filter l

  (** [instance Ω] builds an instance [args] such
      that [Ω ⊢ args:Ω] where [Ω] is a named context and with the local
      definitions of [Ω] skipped. Example: for [id1:T,id2:=c,id3:U], it
      gives [Var id1, Var id3]. All [idj] are supposed distinct. *)
  let instance_list mk l =
    let filter = function
      | Declaration.LocalAssum (id, _) -> Some (mk id.binder_name)
      | _ -> None
    in
    List.rev (List.map_filter filter l)

  let instance mk l =
    Array.of_list (instance_list mk l)
end

module Compacted =
  struct
    module Declaration =
      struct
        type ('constr, 'types) pt =
          | LocalAssum of Id.t binder_annot list * 'types
          | LocalDef of Id.t binder_annot list * 'constr * 'types

        let map_constr f = function
          | LocalAssum (ids, ty) as decl ->
             let ty' = f ty in
             if ty == ty' then decl else LocalAssum (ids, ty')
          | LocalDef (ids, c, ty) as decl ->
             let ty' = f ty in
             let c' = f c in
             if c == c' && ty == ty' then decl else LocalDef (ids,c',ty')

        let of_named_decl = function
          | Named.Declaration.LocalAssum (id,t) ->
              LocalAssum ([id],t)
          | Named.Declaration.LocalDef (id,v,t) ->
              LocalDef ([id],v,t)

        let to_named_context = function
          | LocalAssum (ids, t) ->
             List.map (fun id -> Named.Declaration.LocalAssum (id,t)) ids
          | LocalDef (ids, v, t) ->
             List.map (fun id -> Named.Declaration.LocalDef (id,v,t)) ids
      end

    type ('constr, 'types) pt = ('constr, 'types) Declaration.pt list

    let fold f l ~init = List.fold_right f l init
  end
