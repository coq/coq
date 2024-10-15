(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Proofview
open Tac2ffi
open Tac2val

(** Interface for defining external tactics via a high-level spec. *)

(** Type [('v,'f) spec] represents a high-level Ltac2 tactic specification. It
    indicates how to turn a value of type ['f] into an Ltac2 tactic, which may
    involve converting between OCaml and Ltac2 value representations, and also
    lifting a pure function to the tactic monad. The type parameter ['v] gives
    the type of value produced by interpreting the specification. *)
type (_, _) spec

(** [tac r] is the specification of a tactic (in the tactic monad sense) whose
    return type is specified (and converted into an Ltac2 value) via [r]. *)
val tac :
  'r repr ->
  (valexpr tactic, 'r tactic) spec

(** [tac'] is similar to [tac], but only needs a conversion function. *)
val tac' :
  ('r -> valexpr) ->
  (valexpr tactic, 'r tactic) spec

(** [ret r] is the specification of a pure tactic (i.e., a tactic defined as a
    pure OCaml value, not needing the tactic monad) whose return type is given
    by [r] (see [tac]). *)
val ret :
  'r repr ->
  (valexpr tactic, 'r) spec

(** [ret'] is similar to [ret], but only needs a conversion function. *)
val ret' :
  ('r -> valexpr) ->
  (valexpr tactic, 'r) spec

(** [eret] is similar to [ret], but for tactics that can be implemented with a
    pure OCaml value, provided extra arguments [env] and [sigma], computed via
    [tclENV] and [tclEVARMAP]. *)
val eret :
  'r repr ->
  (valexpr tactic, Environ.env -> Evd.evar_map -> 'r) spec

(** [eret'] is similar to [eret], but only needs a conversion function. *)
val eret' :
  ('r -> valexpr) ->
  (valexpr tactic, Environ.env -> Evd.evar_map -> 'r) spec

(** [gret] is similar to [ret], but for tactics that can be implemented with a
    pure OCaml value, provided the current goal [g] as extra argument. A fatal
    error is produced when there is not exactly one goal in focus at the point
    of using an Ltac2 value defined with this specification. Indeed, the value
    of [g] is computed using [Goal.enter_one]. *)
val gret :
  'r repr ->
  (valexpr tactic, Goal.t -> 'r) spec

(** [gret'] is similar to [gret], but only needs a conversion function. *)
val gret' :
  ('r -> valexpr) ->
  (valexpr tactic, Goal.t -> 'r) spec

(** [r @-> s] extends the specification [s] with a closure argument whose type
    is specified by (and converted from an Ltac2 value via) [r]. *)
val (@->) :
  'a repr ->
  ('t,'f) spec ->
  (valexpr -> 't, 'a -> 'f) spec

(** [(@-->)] is similar to [(@->)], but only needs a conversion function. *)
val (@-->) :
  (valexpr -> 'a) ->
  ('t,'f) spec ->
  (valexpr -> 't, 'a -> 'f) spec

(** [define tac s f] defines an external tactic [tac] by interpreting [f] with
    the specification [s]. The [Invalid_argument] exception is raised when the
    given [s] does not produce a "pure" tactic, that is, something that can be
    turned into an Ltac2 value (i.e., a closure, or a pure value). *)
val define : Tac2expr.ml_tactic_name -> (_, 'f) spec -> 'f -> unit
