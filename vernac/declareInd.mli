(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

type default_dep_elim = DefaultElim | PropButDepElim

type indlocs = (Loc.t option * Loc.t option list) list
(** Inductive type and constructor locs, for .glob and src loc info *)

val declare_mutual_inductive_with_eliminations
  : ?typing_flags:Declarations.typing_flags
  -> ?indlocs:indlocs
  -> ?default_dep_elim:default_dep_elim list
  -> Entries.mutual_inductive_entry (* Inductive types declaration *)
  -> UState.named_universes_entry (* Global universes, including the template default instance *)
  -> one_inductive_impls list (* Implicit arguments *)
  -> Names.MutInd.t

(** {6 For legacy support, do not use}  *)
module Internal :
sig

type inductive_obj
val objInductive : (Names.Id.t * inductive_obj) Libobject.Dyn.tag

end

val declare_primitive_projection :
  Names.Projection.Repr.t -> Names.Constant.t -> unit
