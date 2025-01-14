(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module registers the declaration of global tables, which will be kept
   in synchronization during the various backtracks of the system. *)
module Stage : sig

(** We distinguish two stages and separate the system state accordingly.
    [Synterp] is the syntactic interpretation phase, i.e. vernacular parsing and
    execution of commands having an effect on parsing. [Interp] is the
    interpretation phase, where standard commands are executed. *)
  type t = Synterp | Interp

  val equal : t -> t -> bool

end

(** Types of global Rocq states. The ['a] type should be pure and marshallable by
    the standard OCaml marshalling function. *)
type 'a summary_declaration = {
  stage : Stage.t;
  freeze_function : unit -> 'a;
  unfreeze_function : 'a -> unit;
  init_function : unit -> unit }

(** For tables registered during the launch of rocq repl, the [init_function]
    will be run only once, during an [init_summaries] done at the end of
    coqtop initialization. For tables registered later (for instance
    during a plugin dynlink), [init_function] is used when unfreezing
    an earlier frozen state that doesn't contain any value for this table.

    Beware: for tables registered dynamically after the initialization
    of Coq, their init functions may not be run immediately. It is hence
    the responsibility of plugins to initialize themselves properly.
*)

val declare_summary : string -> ?make_marshallable:('a -> 'a) -> 'a summary_declaration -> unit

(** We provide safe projection from the summary to the types stored in
   it.*)
module Dyn : Dyn.S

val declare_summary_tag : string -> ?make_marshallable:('a -> 'a) -> 'a summary_declaration -> 'a Dyn.tag

(** All-in-one reference declaration + summary registration.
    It behaves just as OCaml's standard [ref] function, except
    that a [declare_summary] is done, with [name] as string.
    The [init_function] restores the reference to its initial value.
    The [stage] argument defaults to [Interp] and should be changed to [Synterp]
    for references which are read from and written to during the syntactic
    interpretation.

    When [local:true] the value is local to the process, i.e. not sent to proof workers.
    Consequently it doesn't need to be of a marshallable type.
    It is useful to implement a local cache for example.

    [ref_tag] is never local.
*)

val ref : ?stage:Stage.t -> ?local:bool -> name:string -> 'a -> 'a ref
val ref_tag : ?stage:Stage.t -> name:string -> 'a -> 'a ref * 'a Dyn.tag

(** Special summary for ML modules.  This summary entry is special
    because its unfreeze may load ML code and hence add summary
    entries.  Thus is has to be recognizable, and handled properly.

    The args correspond to Mltop.PluginSpec.t , that is to say, the
    findlib name for the plugin.  *)
val declare_ml_modules_summary : string list summary_declaration -> unit

(** For global tables registered statically before the end of coqtop
    launch, the following empty [init_function] could be used. *)

val nop : unit -> unit

module type FrozenStage = sig

  (** The type [frozen] is a snapshot of the states of all the registered
      tables of the system. *)

  type frozen

  val empty_frozen : frozen
  val freeze_summaries : unit -> frozen
  val make_marshallable : frozen -> frozen
  val unfreeze_summaries : ?partial:bool -> frozen -> unit
  val init_summaries : unit -> unit
  val project_from_summary : frozen -> 'a Dyn.tag -> 'a

end

module Synterp : FrozenStage
module Interp : sig

  include FrozenStage

  (** Typed projection of the summary. Experimental API, use with CARE *)

  val modify_summary : frozen -> 'a Dyn.tag -> 'a -> frozen
  val remove_from_summary : frozen -> 'a Dyn.tag -> frozen

end

(** {6 Debug} *)
val dump : unit -> (int * string) list
