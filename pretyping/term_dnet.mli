(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id:$ *)

(*i*)
open Term
open Sign
open Libnames
open Mod_subst
(*i*)

(* Dnets on constr terms.

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

   See lib/dnet.mli for more details.
*)

(* Identifiers to store (right hand side of the association) *)
module type IDENT = sig
  type t
  val compare : t -> t -> int

  (* how to substitute them for storage *)
  val subst : substitution -> t -> t

  (* how to recover the term from the identifier *)
  val constr_of : t -> constr
end

(* Options : *)
module type OPT = sig

  (* pre-treatment to terms before adding or searching *)
  val reduce : constr -> constr

  (* direction of post-filtering w.r.t sort subtyping :
     - true means query <= terms in the structure
     - false means terms <= query
 *)
  val direction : bool
end

module type S =
sig
  type t
  type ident

  (* results of filtering : identifier, a context (term with Evar
     hole) and the substitution in that context*)
  type result = ident * (constr*existential_key) * Termops.subst

  val empty : t

  (* [add c i dn] adds the binding [(c,i)] to [dn]. [c] can be a
     closed term or a pattern (with untyped Evars). No Metas accepted *)
  val add : constr -> ident -> t -> t

  (* merge of dnets. Faster than re-adding all terms *)
  val union : t -> t -> t

  val subst : substitution -> t -> t

  (*
   * High-level primitives describing specific search problems
   *)

  (* [search_pattern dn c] returns all terms/patterns in dn
     matching/matched by c *)
  val search_pattern : t -> constr -> result list

  (* [search_concl dn c] returns all matches under products and
     letins, i.e. it finds subterms whose conclusion matches c. The
     complexity depends only on c ! *)
  val search_concl : t -> constr -> result list

  (* [search_head_concl dn c] matches under products and applications
     heads. Finds terms of the form [forall H_1...H_n, C t_1...t_n]
     where C matches c *)
  val search_head_concl : t -> constr -> result list

  (* [search_eq_concl dn eq c] searches terms of the form [forall
     H1...Hn, eq _ X1 X2] where either X1 or X2 matches c *)
  val search_eq_concl : t -> constr -> constr -> result list

  (* [find_all dn] returns all idents contained in dn *)
  val find_all : t -> ident list

  val map : (ident -> ident) -> t -> t
end

module Make :
  functor (Ident : IDENT) ->
  functor (Opt : OPT) ->
    S with type ident = Ident.t
