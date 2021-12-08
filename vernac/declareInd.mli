(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Registering a mutual inductive definition together with its
   associated schemes *)

type one_inductive_impls =
  Impargs.manual_implicits (* for inds *) *
  Impargs.manual_implicits list (* for constrs *)

val declare_mutual_inductive_with_eliminations
  : ?primitive_expected:bool
  -> ?typing_flags:Declarations.typing_flags
  -> Entries.mutual_inductive_entry
  -> UState.named_universes_entry
  -> one_inductive_impls list
  -> Names.MutInd.t

(** {6 For legacy support, do not use}  *)
module Internal :
sig

type inductive_obj
val objInductive : (Names.Id.t * inductive_obj) Libobject.Dyn.tag

end

val declare_primitive_projection :
  Names.Projection.Repr.t -> Names.Constant.t -> unit
