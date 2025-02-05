(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Rocq runtime enviroment API.

This module provides functions for manipulation of Rocq's runtime
enviroment, including the standard directories and support files.

This API is similar in spirit to findlib's or dune-sites API,
see their documentation for more information:

- http://projects.camlcity.org/projects/dl/findlib-1.9.1/doc/ref-html/lib/index.html
- https://dune.readthedocs.io/en/stable/sites.html#sites

It is important that this library has a minimal dependency set.

The Rocq runtime enviroment needs to be properly initialized before use;
we detail the rules below. It is recommended that applications requiring
multiple accesses to the environment, do initialize it once and keep a ref
to it. We don't forbid yet double initialization, (second time is a noop)
but we may do so in the future. Rules for "coqlib" are:

- the [ROCQLIB] env variable will be used if set
- if not, the existence of [theories/Init/Prelude.vo] will be checked,
  in the following order:
  + [coqlibsuffix] given in configure
  + [coqlib] given in configure
- if none of the above succeeds, the initialization will fail

- The [ROCQRUNTIMELIB] env variable is also used if set, if not, the location
  of the rocq-runtime files will be assumed to be [ROCQLIB/../rocq-runtime], except
  if [ROCQLIB/plugins] exists [as in some developers layouts], in which case
  we will set [ROCQRUNTIMELIB:=ROCQLIB].

Note that [set_coqlib] is used by some commands to process the [-coqlib] option,
as of now this sets both [coqlib] and [coqcorelib]; this part of the initialization
will be eventually moved here.

The error handling policy of this module is simple for now: failing to
initialize Rocq's env will produce a fatal error, and the application will exit with
code 1. No error handling is thus required on the client yet.

*)

module Path : sig

  (** This API is loosely inspired by [Stdune.Path], for now we keep
     it minimal, but at some point we may extend it. *)

  (** Paths are private, and owned by the functions below *)
  type t

  (** [relative path string] build a path relative to an existing one *)
  val relative : t -> string -> t

  (** We should gradually add some more functions to handle common dirs
      here such the theories directories or share files. Abstracting it
      hereere does allow to use system-specific functionalities *)

  (** [exists file] checks if [file] exists *)
  val exists : t -> bool

  (** String representation *)
  val to_string : t -> string

end

(** Rocq runtime enviroment, including location of Rocq's stdlib *)
type t

(** [init ()] will initialize the Rocq environment. *)
val init : unit -> t

(** [stdlib directory] *)
val stdlib : t -> Path.t

(** [plugins directory] *)
val plugins : t -> Path.t

(** [user contrib directory] *)
val user_contrib : t -> Path.t

(** [tool-specific directory] *)
val tool : t -> string -> Path.t

(** .cmi files needed for native compilation *)
val native_cmi : t -> string -> Path.t

(** The location of the revision file *)
val revision : t -> Path.t

(** rocq-runtime/lib directory, not sure if to keep this *)
val corelib : t -> Path.t

(** coq/lib directory, not sure if to keep this *)
val coqlib : t -> Path.t

(** [camlfind ()] is the path to the ocamlfind binary. *)
val ocamlfind : unit -> string

val print_config : ?prefix_var_name:string -> t -> out_channel -> unit

(** Needs a Rocq environment for Where and Config.
    If the [usage] argument is [None], the query must not be PrintHelp. *)
val print_query : Usage.specific_usage option -> Usage.query -> unit

(** Where and Config need to be able to find coqlib (i.e. -boot won't work) *)
val query_needs_env : Usage.query -> bool

(** Internal, should be set automatically by passing cmdline args to
   init; note that this will set both [coqlib] and [corelib] for now. *)
val set_coqlib : string -> unit
