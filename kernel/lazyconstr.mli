(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Mod_subst

type work_list = Id.t array Cmap.t * Id.t array Mindmap.t
type cooking_info = { modlist : work_list; abstract : Context.named_context } 

(** [constr_substituted] are [constr] with possibly pending
    substitutions of kernel names. *)

type constr_substituted

val from_val : constr -> constr_substituted
val force : constr_substituted -> constr
val subst_constr_subst :
  substitution -> constr_substituted -> constr_substituted

(** Opaque proof terms might be in some external tables. The
    [force_opaque] function below allows to access these tables,
    this might trigger the read of some extra parts of .vo files *)

type lazy_constr
type proofterm = (constr * Univ.constraints) Future.computation

(** From a [constr] to some (immediate) [lazy_constr]. *)
val opaque_from_val : proofterm -> lazy_constr

(** Turn an immediate [lazy_constr] into an indirect one, thanks
    to the indirect opaque creator configured below. *)
val turn_indirect : lazy_constr -> lazy_constr

(** From a [lazy_constr] back to a [constr]. This might use the
    indirect opaque accessor configured below. *)
val force_opaque : lazy_constr -> constr
val force_opaque_w_constraints : lazy_constr -> constr * Univ.constraints
val get_opaque_future_constraints :
  lazy_constr -> Univ.constraints Future.computation option
val get_opaque_futures :
  lazy_constr ->
    Term.constr Future.computation * Univ.constraints Future.computation

val subst_lazy_constr : substitution -> lazy_constr -> lazy_constr

(* val hcons_lazy_constr : lazy_constr -> lazy_constr *)

(* Used to discharge the proof term. *)
val iter_direct_lazy_constr : (constr -> unit) -> lazy_constr -> lazy_constr
val discharge_direct_lazy_constr : work_list -> Context.named_context -> (constr -> constr) -> lazy_constr -> lazy_constr

val join_lazy_constr : lazy_constr -> unit

(** When stored indirectly, opaque terms are indexed by their library
    dirpath and an integer index. The following two functions activate
    this indirect storage, by telling how to store and retrieve terms.
    Default creator always returns [None], preventing the creation of
    any indirect link, and default accessor always raises an error.
*)

val set_indirect_creator :
  (cooking_info list * proofterm -> (DirPath.t * int) option) -> unit
val set_indirect_opaque_accessor :
  (DirPath.t -> int -> Term.constr Future.computation) -> unit
val set_indirect_univ_accessor :
  (DirPath.t -> int -> Univ.constraints Future.computation option) -> unit
val set_join_indirect_local_opaque : (DirPath.t -> int -> unit) -> unit
val set_join_indirect_local_univ : (DirPath.t -> int -> unit) -> unit
val reset_indirect_creator : unit -> unit
