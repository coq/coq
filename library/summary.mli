(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module registers the declaration of global tables, which will be kept
   in synchronization during the various backtracks of the system. *)

type marshallable =
  [ `Yes       (* Full data will be marshalled to disk                        *)
  | `No        (* Full data will be store in memory, e.g. for Undo            *)
  | `Shallow ] (* Only part of the data will be marshalled to a slave process *)

(** Types of global Coq states. The ['a] type should be pure and marshallable by
    the standard OCaml marshalling function. *)
type 'a summary_declaration = {
  (** freeze_function [true] is for marshalling to disk. 
   *  e.g. lazy must be forced *)
  freeze_function : marshallable -> 'a;
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

(** We provide safe projection from the summary to the types stored in
   it.*)
module Dyn : Dyn.S

val declare_summary_tag : string -> 'a summary_declaration -> 'a Dyn.tag

(** All-in-one reference declaration + summary registration.
    It behaves just as OCaml's standard [ref] function, except
    that a [declare_summary] is done, with [name] as string.
    The [init_function] restores the reference to its initial value.
    The [freeze_function] can be overridden *)

val ref : ?freeze:(marshallable -> 'a -> 'a) -> name:string -> 'a -> 'a ref
val ref_tag : ?freeze:(marshallable -> 'a -> 'a) -> name:string -> 'a -> 'a ref * 'a Dyn.tag

(* As [ref] but the value is local to a process, i.e. not sent to, say, proof
 * workers.  It is useful to implement a local cache for example. *)
module Local : sig

  type 'a local_ref
  val ref : ?freeze:('a -> 'a) -> name:string -> 'a -> 'a local_ref
  val (:=) : 'a local_ref -> 'a -> unit
  val (!) : 'a local_ref -> 'a

end

(** Special summary for ML modules.  This summary entry is special
    because its unfreeze may load ML code and hence add summary
    entries.  Thus is has to be recognizable, and handled properly.
   *)
val declare_ml_modules_summary : 'a summary_declaration -> unit

(** For global tables registered statically before the end of coqtop
    launch, the following empty [init_function] could be used. *)

val nop : unit -> unit

(** The type [frozen] is a snapshot of the states of all the registered
    tables of the system. *)

type frozen

val empty_frozen : frozen
val freeze_summaries : marshallable:marshallable -> frozen
val unfreeze_summaries : ?partial:bool -> frozen -> unit
val init_summaries : unit -> unit

(** Typed projection of the summary. Experimental API, use with CARE *)

val modify_summary : frozen -> 'a Dyn.tag -> 'a -> frozen
val project_from_summary : frozen -> 'a Dyn.tag -> 'a
val remove_from_summary : frozen -> 'a Dyn.tag -> frozen

(** {6 Debug} *)
val dump : unit -> (int * string) list
