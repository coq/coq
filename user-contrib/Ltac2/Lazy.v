(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.
Require Ltac2.Ref.
Require Ltac2.Control.

Ltac2 Type 'a lazy_data := [ Value ('a) | Thunk (unit -> 'a) ].

(** Type of a lazy cell, similar to OCaml's ['a Lazy.t] type. The functions of
    this module do not have any specific backtracking support, so any function
    passed to primitives of this module is handled as if it had one success at
    most (potential other successes are ignored). *)
Ltac2 Type 'a t := 'a lazy_data Ref.ref.

(** [from_val v] creates a new lazy cell storing (already-computed) value [v].
    Forcing (i.e., using the [force] function on) the produced cell gives back
    value [v], and never gives an exception. *)
Ltac2 from_val (v : 'a) : 'a t :=
  Ref.ref (Value v).

(** [from_fun f] creates a new lazy cell from the given thunk [f]. There is no
    specific support for backtracking in the [Lazy] module, so if [f] has more
    than one success, only the first one will be considered. *)
Ltac2 from_fun (f : unit -> 'a) : 'a t :=
  Ref.ref (Thunk f).

(** [is_val r] indicates whether the given lazy cell [r] holds a forced value.
    In particular, [is_val r] always returns [true] if [r] was created via the
    [from_val] function. If [r] was created using [from_fun], then [true] will
    only be returned if the value of [r] was previously forced (e.g., with the
    [force] function), and if no exception was produced by said forcing. *)
Ltac2 is_val (r : 'a t) : bool :=
  match Ref.get r with
  | Value _ => true
  | Thunk _ => false
  end.

(** Exception raised in case of a "cyclic" lazy cell. *)
Ltac2 Type exn ::= [ Undefined ].

(** [force r] gives the value represented by the lazy cell [r], which requires
    forcing a thunk and updating [r] to the produced value if [r] does not yet
    have a value. Note that if forcing produces an exception, subsequent calls
    to [force] will immediately yield the same exception (without re-computing
    the whole thunk). Additionally, the [Undefined] exception is produced (and
    set to be produced by [r] on subsequent calls to [force]) if [r] relies on
    its own value for its definition (i.e., if [r] is "cyclic"). *)
Ltac2 force (r : 'a t) : 'a :=
  match Ref.get r with
  | Value v => v
  | Thunk f =>
      Ref.set r (Thunk (fun () => Control.throw Undefined));
      match Control.case f with
      | Val (v, _) =>
          Ref.set r (Value v);
          v
      | Err e =>
          Ref.set r (Thunk (fun () => Control.zero e));
          Control.zero e
      end
  end.

(** [map f r] is equivalent to [from_fun (fun () => f (force r))]. *)
Ltac2 map (f : 'a -> 'b) (r : 'a t) : 'b t :=
  from_fun (fun () => f (force r)).

(** [map_val f r] is similar to [map f r], but the function [f] is immediately
    applied if [r] contains a forced value. If the immediate application gives
    an exception, then any subsequent forcing of produced lazy cell will raise
    the same exception. *)
Ltac2 map_val (f : 'a -> 'b) (r : 'a t) : 'b t :=
  match Ref.get r with
  | Value v =>
      match Control.case (fun () => f v) with
      | Val (v, _) => from_val v
      | Err e => from_fun (fun () => Control.zero e)
      end
  | Thunk t => from_fun (fun () => f (t ()))
  end.

Module Export Notations.
  Ltac2 Notation "lazy!" f(thunk(self)) := from_fun f.
End Notations.
