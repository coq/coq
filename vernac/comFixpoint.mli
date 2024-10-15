(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vernacexpr

(** {6 Fixpoints and cofixpoints} *)

(** Entry points for the vernacular commands Fixpoint and CoFixpoint *)

val do_mutually_recursive
  :  ?pm:Declare.OblState.t
     (* Obligation mode turns unresolved evars into obligations *)
  -> program_mode:bool
     (* [program_mode] means here:
        - a special treatment of subsets in pretyping
        - a special treatment of type class inference in pretyping
        - if a wf/measure fixpoint, encapsulation under a combinator (in which case, it requires [pm])
        Note: for turning unresolved evars into obligations, set also [pm] *)
  -> ?use_inference_hook:bool
     (* Tell to try the obligation tactic to solve evars *)
  -> ?scope:Locality.definition_scope
     (* Local or Global visibility *)
  -> ?clearbody:bool
     (* Hide body if in sections *)
  -> kind:Decls.logical_kind
     (* Logical kind: Theorem, Definition, Fixpoint, etc.*)
  -> poly:bool
     (* Use universe polymorphism *)
  -> ?typing_flags:Declarations.typing_flags
  -> ?user_warns:Globnames.extended_global_reference UserWarn.with_qf
     (* Warnings and deprecations *)
  -> ?using:Vernacexpr.section_subset_expr
     (* Tell which section variables to use *)
  -> recursives_expr
  -> Declare.OblState.t option * Declare.Proof.t option
     (* Returns open obligations and open proof, if any *)

(************************************************************************)
(** Internal API  *)
(************************************************************************)

(** Exported for Funind *)

val interp_fixpoint_short
  :  Constrexpr.fixpoint_order_expr option list
  -> recursive_expr_gen list
  -> Constr.types list * Evd.evar_map
