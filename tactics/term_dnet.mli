(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Mod_subst

(** Dnets on constr terms.

   An instantiation of Dnet on (an approximation of) constr. It
   associates a term (possibly with Evar) with an
   identifier. Identifiers must be unique (no two terms sharing the
   same ident), and there must be a way to recover the full term from
   the identifier (function constr_of).

   Optionally, a pre-treatment on terms can be performed before adding
   or searching (reduce). Practically, it is used to do some kind of
   delta-reduction on terms before indexing them.

   The results returned here are perfect, since post-filtering is done
   inside here.

   See tactics/dnet.mli for more details.
*)

(** Identifiers to store (right hand side of the association) *)
module type IDENT = sig
  type t
  val compare : t -> t -> int

  (** how to substitute them for storage *)
  val subst : substitution -> t -> t

  (** how to recover the term from the identifier *)
  val constr_of : t -> constr
end

(** Options : *)
module type OPT = sig

  (** pre-treatment to terms before adding or searching *)
  val reduce : constr -> constr

  (** direction of post-filtering w.r.t sort subtyping :
     - true means query <= terms in the structure
     - false means terms <= query
 *)
  val direction : bool
end

module type S =
sig
  type t
  type ident

  val empty : t

  (** [add c i dn] adds the binding [(c,i)] to [dn]. [c] can be a
     closed term or a pattern (with untyped Evars). No Metas accepted *)
  val add : constr -> ident -> t -> t

  (** merge of dnets. Faster than re-adding all terms *)
  val union : t -> t -> t

  val subst : substitution -> t -> t

  (*
   * High-level primitives describing specific search problems
   *)

  (** [search_pattern dn c] returns all terms/patterns in dn
     matching/matched by c *)
  val search_pattern : t -> constr -> ident list

  (** [find_all dn] returns all idents contained in dn *)
  val find_all : t -> ident list

  val map : (ident -> ident) -> t -> t

  val refresh_metas : t -> t
end

module Make :
  functor (Ident : IDENT) ->
  functor (Opt : OPT) ->
    S with type ident = Ident.t
