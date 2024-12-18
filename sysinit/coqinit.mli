(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Main etry point to the sysinit component, all other modules are private.

    The following API shoud be called in order, and the first 3 steps only once
    since they initialize global data. On the contrary step 4 can be called
    many times to init the compilation of a unit.
*)

(** 1 initialization of OCaml's runtime

    Profiling, GC parameters and signals. Nothing specific to Coq per se, but
    the defaults here are good for Coq.
    This API should be called up very early, or not at all. *)
val init_ocaml : unit -> unit

val dirpath_of_top : Coqargs.top -> Names.DirPath.t

(** 2 parsing of Sys.argv

    This API parses command line options which are known by Coq components.
    Ideally it is functional, but some values in the `Flags` modules are set
    on the spot instead of being represented as "injection commands" (a field
    of Coqargs.t).

    The [string list] argument is typically [List.tl (Array.to_list Sys.argv)].

    [parse_extra] and [usage] can be used to parse/document more options. *)
val parse_arguments :
  parse_extra:(Coqargs.t -> string list -> 'a * string list) ->
  ?initial_args:Coqargs.t ->
  string list ->
  Coqargs.t * 'a

(** 3 initialization of global runtime data

    All global setup is done here, like ROCQLIB and the paths for native
    compilation. If Coq is used to process multiple libraries, what is set up
    here is really global and common to all of them.

    This API must be called, typically jsut after parsing arguments. *)
val init_runtime : usage:Boot.Usage.specific_usage -> Coqargs.t -> unit

val init_document : Coqargs.t -> unit

(** 4 Start a library (sets options and loads objects like the prelude)

    Given the logical name [top] of the current library and the set of initial
    options and required libraries, it starts its processing (see also
    Declaremods.start_library) *)
val start_library :
  intern:Library.Intern.t -> top:Names.DirPath.t -> Coqargs.injection_command list -> unit
