(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val check_evars : Environ.env -> Evd.evar_map -> unit

type obligation_info =
  ( Names.Id.t
  * Constr.types
  * Evar_kinds.t Loc.located
  * (bool * Evar_kinds.obligation_definition_status)
  * Int.Set.t
  * unit Proofview.tactic option )
  array
(** ident, type, location of the original evar, (opaque or
   transparent, expand or define), dependencies as indexes into the
   array, tactic to solve it *)

type obligation_name_lifter =
  (Names.Id.t -> EConstr.t) -> EConstr.t -> Constr.t

val retrieve_obligations :
     Environ.env
  -> Names.Id.t
  -> Evd.evar_map
  -> int
  -> ?deps:Evar.Set.t
  -> ?status:Evar_kinds.obligation_definition_status
  -> EConstr.t
  -> EConstr.types
  -> obligation_info
     * ( (Evar.t * Names.Id.t) list * obligation_name_lifter )
     * Constr.t
     * Constr.t
(** [retrieve_obligations env id sigma fs ?status body type] returns
   [obls, (evnames, evmap), nbody, ntype] a list of obligations built
   from evars in [body, type].

    [fs] is the number of function prototypes to try to clear from
   evars contexts. [evnames, evmap] is the list of names /
   substitution functions used to program with holes. This is not used
   in Rocq, but in the equations plugin; [evnames] is actually
   redundant with the information contained in [obls] *)
