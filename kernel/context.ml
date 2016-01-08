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

(** Representation of contexts that can capture anonymous as well as non-anonymous variables.
    Individual declarations are then designated by de Bruijn indexes. *)
module Rel =
  struct
    (** Representation of {e local declarations}.

        [(name, None, typ)] represents a {e local assumption}.
        In the Reference Manual we denote them as [(name:typ)].

        [(name, Some value, typ)] represents a {e local definition}.
        In the Reference Manual we denote them as [(name := value : typ)].
    *)
    module Declaration =
      struct
	type t = Name.t * Constr.t option * Constr.t

	(** Map all terms in a given declaration. *)
	let map f (n, v, ty) = (n, Option.map f v, f ty)

	(** Reduce all terms in a given declaration to a single value. *)
	let fold f (_, v, ty) a = f ty (Option.fold_right f v a)

	(** Check whether any term in a given declaration satisfies a given predicate. *)
	let exists f (_, v, ty) = Option.cata f false v || f ty

	(** Check whether all terms in a given declaration satisfy a given predicate. *)
	let for_all f (_, v, ty) = Option.cata f true v && f ty

	(** Check whether the two given declarations are equal. *)
	let equal (n1, v1, ty1) (n2, v2, ty2) =
	  Name.equal n1 n2 && Option.equal Constr.equal v1 v2 && Constr.equal ty1 ty2
      end

    (** Rel-context is represented as a list of declarations.
        Inner-most declarations are at the beginning of the list.
        Outer-most declarations are at the end of the list. *)
    type t = Declaration.t list

    (** empty rel-context *)
    let empty = []

    (** Return a new rel-context enriched by with a given inner-most declaration. *)
    let add d ctx = d :: ctx

    (** Return a declaration designated by a given de Bruijn index.
        @raise Not_found if the designated de Bruijn index is not present in the designated rel-context. *)
    let rec lookup n ctx =
      match n, ctx with
      | 1, decl :: _ -> decl
      | n, _ :: sign -> lookup (n-1) sign
      | _, []        -> raise Not_found

    (** Map all terms in a given rel-context. *)
    let map f =
      let map_decl (n, body_o, typ as decl) =
	let body_o' = Option.smartmap f body_o in
	let typ' = f typ in
	if body_o' == body_o && typ' == typ then decl else
          (n, body_o', typ')
      in
      List.smartmap map_decl

    (** Reduce all terms in a given rel-context to a single value.
        Innermost declarations are processed first. *)
    let fold_inside f ~init = List.fold_left f init

    (** Reduce all terms in a given rel-context to a single value.
        Outermost declarations are processed first. *)
    let fold_outside f l ~init = List.fold_right f l init

    (** Perform a given action on every declaration in a given rel-context. *)
    let iter f = List.iter (fun (_,b,t) -> f t; Option.iter f b)

    (** Return the number of {e local declarations} in a given context. *)
    let length = List.length

    (** [extended_rel_list n Γ] builds an instance [args] such that [Γ,Δ ⊢ args:Γ]
        with n = |Δ| and with the local definitions of [Γ] skipped in
        [args]. Example: for [x:T,y:=c,z:U] and [n]=2, it gives [Rel 5, Rel 3]. *)
    let nhyps =
      let rec nhyps acc = function
	| [] -> acc
	| (_,None,_)::hyps -> nhyps (1+acc) hyps
	| (_,Some _,_)::hyps -> nhyps acc hyps in
      nhyps 0

    (** Map a given rel-context to a list where each {e local assumption} is mapped to [true]
        and each {e local definition} is mapped to [false]. *)
    let to_tags =
      let rec aux l = function
	| [] -> l
	| (_,Some _,_)::ctx -> aux (true::l) ctx
	| (_,None,_)::ctx -> aux (false::l) ctx
      in aux []

    (** [extended_list n Γ] builds an instance [args] such that [Γ,Δ ⊢ args:Γ]
        with n = |Δ| and with the {e local definitions} of [Γ] skipped in
        [args]. Example: for [x:T, y:=c, z:U] and [n]=2, it gives [Rel 5, Rel 3]. *)
    let to_extended_list n =
      let rec reln l p = function
	| (_, None, _) :: hyps -> reln (Constr.mkRel (n+p) :: l) (p+1) hyps
	| (_, Some _, _) :: hyps -> reln l (p+1) hyps
	| [] -> l
      in
      reln [] 1

    (** [extended_vect n Γ] does the same, returning instead an array. *)
    let to_extended_vect n hyps = Array.of_list (to_extended_list n hyps)
  end

(** This module represents contexts that can capture non-anonymous variables.
    Individual declarations are then designated by the identifiers they bind. *)
module Named =
  struct
    (** Representation of {e local declarations}.

        [(id, None, typ)] represents a {e local assumption}.
        In the Reference Manual we denote them as [(name:typ)].

        [(id, Some value, typ)] represents a {e local definition}.
        In the Reference Manual we denote them as [(name := value : typ)].
   *)
    module Declaration =
      struct
	(** Named-context is represented as a list of declarations.
            Inner-most declarations are at the beginning of the list.
            Outer-most declarations are at the end of the list. *)
	type t = Id.t * Constr.t option * Constr.t

	(** Map all terms in a given declaration. *)
	let map = Rel.Declaration.map

	(** Reduce all terms in a given declaration to a single value. *)
	let fold f (_, v, ty) a = f ty (Option.fold_right f v a)

	(** Check whether any term in a given declaration satisfies a given predicate. *)
	let exists f (_, v, ty) = Option.cata f false v || f ty

	(** Check whether all terms in a given declaration satisfy a given predicate. *)
	let for_all f (_, v, ty) = Option.cata f true v && f ty

	(** Check whether the two given declarations are equal. *)
	let equal (i1, v1, ty1) (i2, v2, ty2) =
	  Id.equal i1 i2 && Option.equal Constr.equal v1 v2 && Constr.equal ty1 ty2
      end

    type t = Declaration.t list

    (** empty named-context *)
    let empty = []

    (** empty named-context *)
    let add d ctx = d :: ctx

    (** Return a declaration designated by a given de Bruijn index.
        @raise Not_found if the designated identifier is not present in the designated named-context. *)
    let rec lookup id = function
      | (id',_,_ as decl) :: _ when Id.equal id id' -> decl
      | _ :: sign -> lookup id sign
      | [] -> raise Not_found

    (** Map all terms in a given named-context. *)
    let map f =
      let map_decl (n, body_o, typ as decl) =
	let body_o' = Option.smartmap f body_o in
	let typ' = f typ in
	if body_o' == body_o && typ' == typ then decl else
          (n, body_o', typ')
      in
      List.smartmap map_decl

    (** Reduce all terms in a given named-context to a single value.
        Innermost declarations are processed first. *)
    let fold_inside f ~init = List.fold_left f init

    (** Reduce all terms in a given named-context to a single value.
        Outermost declarations are processed first. *)
    let fold_outside f l ~init = List.fold_right f l init

    (** Perform a given action on every declaration in a given named-context. *)
    let iter f = List.iter (fun (_,b,t) -> f t; Option.iter f b)

    (** Return the number of {e local declarations} in a given named-context. *)
    let length = List.length

    (** Check whether given two named-contexts are equal. *)
    let equal = List.equal Declaration.equal

    (** Return the set of all identifiers bound in a given named-context. *)
    let to_vars =
      List.fold_left (fun accu (id, _, _) -> Id.Set.add id accu) Id.Set.empty

    (** [instance_from_named_context Ω] builds an instance [args] such
        that [Ω ⊢ args:Ω] where [Ω] is a named context and with the local
        definitions of [Ω] skipped. Example: for [id1:T,id2:=c,id3:U], it
        gives [Var id1, Var id3]. All [idj] are supposed distinct. *)
    let to_instance =
      let filter = function
	| (id, None, _) -> Some (Constr.mkVar id)
	| (_, Some _, _) -> None
      in
      List.map_filter filter
  end

module NamedList =
  struct
    module Declaration =
      struct
	type t = Id.t list * Constr.t option * Constr.t
	let map = Named.Declaration.map
      end
    type t = Declaration.t list
    let fold f l ~init = List.fold_right f l init
  end

type section_context = Named.t
