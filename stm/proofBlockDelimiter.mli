(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file implements proof block detection for:
   - blocks delimited by { and }
   - bullets with indentation
   - par: terminator

   It exports utility functions to ease the development of other proof block
   detection code.
*)

(** A goal is simple if it nor depends on nor impacts on any other goal.
    This function is used to detect, dynamically, if a proof block leaks,
    i.e. if skipping it could impact other goals (like not instantiating their
    type).  `Simple carries the list of focused goals.
*)
val simple_goal : Evd.evar_map -> Evar.t -> Evar.t list -> bool
val is_focused_goal_simple : doc:Stm.doc -> Stateid.t -> [ `Simple of Evar.t list | `Not ]

type 'a until = [ `Stop | `Found of Stm.static_block_declaration | `Cont of 'a ]

(* Simpler function to crawl the document backward to detect the block.
 * ?init is the entry point of the document view if not given *)
val crawl :
  Stm.document_view -> ?init:Stm.document_node option ->
  ('a -> Stm.document_node -> 'a until) -> 'a ->
    Stm.static_block_declaration option

(* Dummy value for static_block_declaration when no real value is needed *)
val unit_val : Stm.DynBlockData.t

(* Bullets *)
val of_bullet_val : Proof_bullet.t -> Stm.DynBlockData.t
val to_bullet_val : Stm.DynBlockData.t -> Proof_bullet.t

