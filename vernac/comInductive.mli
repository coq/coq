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
open Entries
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

(************************************************************************)
(** Internal API, exported for Record                                   *)
(************************************************************************)

(** Registering a mutual inductive definition together with its
   associated schemes *)

type one_inductive_impls =
  Impargs.manual_implicits (* for inds *) *
  Impargs.manual_implicits list (* for constrs *)

val declare_mutual_inductive_with_eliminations :
  ?primitive_expected:bool ->
  mutual_inductive_entry -> UnivNames.universe_binders -> one_inductive_impls list ->
  MutInd.t

val should_auto_template : Id.t -> bool -> bool
(** [should_auto_template x b] is [true] when [b] is [true] and we
   automatically use template polymorphism. [x] is the name of the
   inductive under consideration. *)
