(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Coq.ltac2.Init.

(** Panic *)

Ltac2 @ external throw : exn -> 'a := "ltac2" "throw".
(** Fatal exception throwing. This does not induce backtracking. *)

(** Generic backtracking control *)

Ltac2 @ external zero : exn -> 'a := "ltac2" "zero".
Ltac2 @ external plus : (unit -> 'a) -> (exn -> 'a) -> 'a := "ltac2" "plus".
Ltac2 @ external once : (unit -> 'a) -> 'a := "ltac2" "once".
Ltac2 @ external dispatch : (unit -> unit) list -> unit := "ltac2" "dispatch".
Ltac2 @ external extend : (unit -> unit) list -> (unit -> unit) -> (unit -> unit) list -> unit := "ltac2" "extend".
Ltac2 @ external enter : (unit -> unit) -> unit := "ltac2" "enter".

(** Proof state manipulation *)

Ltac2 @ external focus : int -> int -> (unit -> 'a) -> 'a := "ltac2" "focus".
Ltac2 @ external shelve : unit -> unit := "ltac2" "shelve".
Ltac2 @ external shelve_unifiable : unit -> unit := "ltac2" "shelve_unifiable".

(** Goal inspection *)

Ltac2 @ external goal : unit -> constr := "ltac2" "goal".
(** Panics if there is not exactly one goal under focus. Otherwise returns
    the conclusion of this goal. *)

Ltac2 @ external hyp : ident -> constr := "ltac2" "hyp".
(** Panics if there is more than one goal under focus. If there is no
    goal under focus, looks for the section variable with the given name.
    If there is one, looks for the hypothesis with the given name. *)

(** Refinement *)

Ltac2 @ external refine : (unit -> constr) -> unit := "ltac2" "refine".
