(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Vernacexpr
open Constrexpr

(** {6 Inductive and coinductive types} *)

(** Entry points for the vernacular commands Inductive and CoInductive *)

type uniform_inductive_flag =
  | UniformParameters
  | NonUniformParameters

val do_mutual_inductive
  :  template:bool option
  -> universe_decl_expr option
  -> (one_inductive_expr * decl_notation list) list
  -> cumulative:bool
  -> poly:bool
  -> private_ind:bool
  -> uniform:uniform_inductive_flag
  -> Declarations.recursivity_kind
  -> unit

(** User-interface API *)

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

val make_cases : Names.inductive -> string list list

val declare_mutual_inductive_with_eliminations
  : ?primitive_expected:bool
  -> Entries.mutual_inductive_entry
  -> UnivNames.universe_binders
  -> DeclareInd.one_inductive_impls list
  -> Names.MutInd.t
  [@@ocaml.deprecated "Please use DeclareInd.declare_mutual_inductive_with_eliminations"]

(************************************************************************)
(** Internal API, exported for Record                                   *)
(************************************************************************)

val should_auto_template : Id.t -> bool -> bool
(** [should_auto_template x b] is [true] when [b] is [true] and we
   automatically use template polymorphism. [x] is the name of the
   inductive under consideration. *)

val template_polymorphism_candidate :
  Environ.env -> Entries.universes_entry -> Constr.rel_context -> Sorts.t option -> bool
(** [template_polymorphism_candidate env uctx params conclsort] is
   [true] iff an inductive with params [params] and conclusion
   [conclsort] would be definable as template polymorphic.  It should
   have at least one universe in its monomorphic universe context that
   can be made parametric in its conclusion sort, if one is given.
   If the [Template Check] flag is false we just check that the conclusion sort
   is not small. *)

val sign_level : Environ.env -> Evd.evar_map -> Constr.rel_declaration list -> Univ.Universe.t
(** [sign_level env sigma ctx] computes the universe level of the context [ctx]
    as the [sup] of its individual assumptions, which should be well-typed in [env] and [sigma] *)
