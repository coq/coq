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

Ltac2 Type match_kind := [
| MatchPattern
| MatchContext
].

Ltac2 @ external empty_context : unit -> context :=
  "ltac2" "pattern_empty_context".
(** A trivial context only made of the hole. *)

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

Ltac2 @ external matches_vect : t -> constr -> constr array :=
  "ltac2" "pattern_matches_vect".
(** Internal version of [matches] that does not return the identifiers. *)

Ltac2 @ external matches_subterm_vect : t -> constr -> context * constr array :=
  "ltac2" "pattern_matches_subterm_vect".
(** Internal version of [matches_subterms] that does not return the identifiers. *)

Ltac2 @ external matches_goal : bool -> (match_kind * t) list -> (match_kind * t) ->
  ident array * context array * constr array * context :=
  "ltac2" "pattern_matches_goal".
(** Given a list of patterns [hpats] for hypotheses and one pattern [cpat] for the
    conclusion, [matches_goal rev hpats cpat] produces (a stream of) tuples of:
    - An array of idents, whose size is the length of [hpats], corresponding to the
      name of matched hypotheses.
    - An array of contexts, whose size is the length of [hpats], corresponding to
      the contexts matched for every hypothesis pattern. In case the match kind of
      a hypothesis was [MatchPattern], the corresponding context is ensured to be empty.
    - An array of terms, whose size is the total number of pattern variables without
      duplicates. Terms are ordered by identifier order, e.g. ?a comes before ?b.
    - A context corresponding to the conclusion, which is ensured to be empty if
      the kind of [cpat] was [MatchPattern].
    This produces a backtracking stream of results containing all the possible
    result combinations. The order of considered hypotheses is reversed if [rev]
    is true.
*)

Ltac2 @ external instantiate : context -> constr -> constr :=
  "ltac2" "pattern_instantiate".
(** Fill the hole of a context with the given term. *)
