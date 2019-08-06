open Stages
open Environ
open Constr

(** The Staging module contains functions that semantically belong
  in Stages or Constr, but cannot because they depend on Environ. *)

type variance =
  | Variant
  | Bivariant

val add_constraint_from_ind : env -> variance ->
  Constraints.t -> Names.inductive -> Annot.t -> Annot.t -> Constraints.t

val add_constraint_from_ind_ref : env -> variance ->
  Constraints.t ref -> Names.inductive -> Annot.t -> Annot.t -> bool

val annotate_global : env -> constr -> constr
