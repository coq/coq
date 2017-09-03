(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Ltac2.Init.

Ltac2 Type t := pattern.

Ltac2 Type context.

Ltac2 Type 'a constr_match := [
| ConstrMatchPattern (pattern, constr array -> 'a)
| ConstrMatchContext (pattern, constr -> constr array -> 'a)
].

Ltac2 @ external matches : t -> constr -> (ident * constr) list :=
  "ltac2" "pattern_matches".
(** If the term matches the pattern, returns the bound variables. If it doesn't,
    fail with [Match_failure]. Panics if not focussed. *)

Ltac2 @ external matches_subterm : t -> constr -> context * ((ident * constr) list) :=
  "ltac2" "pattern_matches_subterm".
(** Returns a stream of results corresponding to all of the subterms of the term
    that matches the pattern as in [matches]. The stream is encoded as a
    backtracking value whose last exception is [Match_failure]. The additional
    value compared to [matches] is the context of the match, to be filled with
    the instantiate function. *)

Ltac2 @ external instantiate : context -> constr -> constr :=
  "ltac2" "pattern_instantiate".
(** Fill the hole of a context with the given term. *)
