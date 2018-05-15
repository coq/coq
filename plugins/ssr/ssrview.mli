(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ssrast

(* Adaptor DB (Hint View) *)
module AdaptorDb : sig

  type kind = Forward | Backward | Equivalence

  val get : kind -> Glob_term.glob_constr list
  val declare : kind -> Glob_term.glob_constr list -> unit

end

(* Apply views to the top of the stack (intro pattern). If clear_if_id is
 * true (default false) then views that happen to be a variable are considered
 * as to be cleared (see the to_clear argument to the continuation) *)
val tclIPAT_VIEWS :
    views:ast_closure_term list -> ?clear_if_id:bool ->
    conclusion:(to_clear:Names.Id.t list -> unit Proofview.tactic) ->
  unit Proofview.tactic

(* Apply views to a given subject (as if was the top of the stack), then
   call conclusion on the obtained term (something like [v2 (v1 subject)]).
   The term being passed to conclusion is abstracted over non-resolved evars:
   if [simple_types] then all unnecessary dependencies among the abstracted
   evars are pruned *)
val tclWITH_FWD_VIEWS :
  simple_types:bool ->
    subject:EConstr.t ->
    views:ast_closure_term list ->
    conclusion:(EConstr.t -> unit Proofview.tactic) ->
  unit Proofview.tactic
