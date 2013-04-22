(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module registers the declaration of global tables, which will be kept
   in synchronization during the various backtracks of the system. *)

type 'a summary_declaration = {
  freeze_function : unit -> 'a;
  unfreeze_function : 'a -> unit;
  init_function : unit -> unit }

(** For tables registered during the launch of coqtop, the [init_function]
    will be run only once, during an [init_summaries] done at the end of
    coqtop initialization. For tables registered later (for instance
    during a plugin dynlink), [init_function] is used when unfreezing
    an earlier frozen state that doesn't contain any value for this table.

    Beware: for tables registered dynamically after the initialization
    of Coq, their init functions may not be run immediately. It is hence
    the responsability of plugins to initialize themselves properly.
*)

val declare_summary : string -> 'a summary_declaration -> unit

(** All-in-one reference declaration + summary registration.
    It behaves just as OCaml's standard [ref] function, except
    that a [declare_summary] is done, with [name] as string.
    The [init_function] restores the reference to its initial value. *)

val ref : name:string -> 'a -> 'a ref

(** For global tables registered statically before the end of coqtop
    launch, the following empty [init_function] could be used. *)

val nop : unit -> unit

(** The type [frozen] is a snapshot of the states of all the registered
    tables of the system. *)

type frozen

val freeze_summaries : unit -> frozen
val unfreeze_summaries : frozen -> unit
val init_summaries : unit -> unit
