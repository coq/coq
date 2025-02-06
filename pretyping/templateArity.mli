(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr

type template_binder = {
  bind_sort : Sorts.t;
  default : Sorts.t;
}

(** NB: the types and rel_contexts may mention previous args
   eg "sigT : forall A, (A -> Type) -> Type" is
   "TemplateArg ([], u, TemplateArg ([_:Rel 1], v, IndType (_, [], Type@{max(u,v)})))"
   note the "Rel 1" *)
type template_arity =
  | NonTemplateArg of Name.t binder_annot * types * template_arity
  | TemplateArg of Name.t binder_annot * rel_context * template_binder * template_arity
  | DefParam of Name.t binder_annot * constr * types * template_arity
  | CtorType of Declarations.template_universes * types
  | IndType of Declarations.template_universes * rel_context * Sorts.t

val get_template_arity
  : Environ.env
  -> Names.inductive
  -> ctoropt:int option
  -> template_arity
