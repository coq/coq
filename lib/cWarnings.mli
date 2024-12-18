(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type status = Disabled | Enabled | AsError

type category
(** Categories and warnings form a DAG with a common root [all] and warnings as the leaves. *)

val all : category

type warning
(** Each warning belongs to some categories maybe including ["default"].
    It is possible to query the status of a [warning] (unlike categories).
    XXX we should probably have ["default-error"] too. *)

type 'a msg
(** A [msg] belongs to a [warning]. *)

val warn : 'a msg -> ?loc:Loc.t -> ?quickfix:Quickfix.t list -> 'a -> unit
(** Emit a message in some warning. *)

(** Creation functions

    Note that names are in a combined namespace including the special name ["none"].
*)

val create_category : ?from:category list -> name:string -> unit -> category
(** When [from] is not specified it defaults to [[all]]. Empty list
    [from] is not allowed. "default" is not allowed in [from]. *)

val create_warning : ?from:category list -> ?default:status -> name:string -> unit -> warning
(** [from] works the same as with [create_category]. In particular
    default status is specified through the [default] argument not by
    using the "default" category. *)

val create_hybrid : ?from:category list -> ?default:status -> name:string -> unit -> category * warning
(** As [create_warning], but the warning can also be used as a category i.e. have sub-warnings. *)

val create_msg : warning -> unit -> 'a msg
(** A message with data ['a] in the given warning. *)

val create_in : warning -> ('a -> Pp.t) -> ?loc:Loc.t -> ?quickfix:Quickfix.t list -> 'a -> unit
(** Create a msg with registered printer. *)

val register_printer : 'a msg -> ('a -> Pp.t) -> unit
(** Register the printer for a given message. If a printer is already registered it is replaced. *)

val create : name:string -> ?category:category -> ?default:status ->
  ('a -> Pp.t) -> ?loc:Loc.t -> 'a -> unit
(** Combined creation function. [name] must be a fresh name. *)

val create_with_quickfix : name:string -> ?category:category -> ?default:status ->
    ('a -> Pp.t) -> ?loc:Loc.t -> ?quickfix:Quickfix.t list -> 'a -> unit
  (** Combined creation function. [name] must be a fresh name. *)

(** Misc APIs *)

val get_flags : unit -> string
val set_flags : string -> unit

type 'a elt =
  | There of 'a
  | NotThere
  | OtherType

val get_category : string -> category elt
(** Get preexisting category by name. *)

val get_warning : string -> warning elt
(** Get preexisting warning by name. *)

val warning_status : warning -> status
(** Current status of the warning. *)

val get_status : name:string -> status
(* [@@ocaml.deprecated "(8.18) Use [CWarnings.warning_status]"] *)

val normalize_flags_string : string -> string
(** Cleans up a user provided warnings status string, e.g. removing unknown
    warnings (in which case a warning is emitted) or subsumed warnings . *)

val with_warn: string -> ('b -> 'a) -> 'b -> 'a
(** [with_warn "-xxx,+yyy..." f x] calls [f x] after setting the
   warnings as specified in the string (keeping other previously set
   warnings), and restores current warnings after [f()] returns or
   raises an exception. If both f and restoring the warnings raise
   exceptions, the latter is raised. *)

val check_unknown_warnings : string -> unit
(** Warn with "unknown-warning" if any unknown warnings are in the
    string with non-disabled status. *)

val override_unknown_warning : bool ref
[@@ocaml.deprecated "(8.18) Do not use, internal."]
(** For command line -w, this avoids using the warning system to avoid breaking
    "-w -unknown-warning". *)

module CoreCategories : sig
  (** Categories used in rocq-runtime. Might not be exhaustive. *)

  val automation : category
  val bytecode_compiler : category
  val coercions : category
  val deprecated : category
  val extraction : category
  val filesystem : category
  val fixpoints : category
  val fragile : category
  val funind : category
  val implicits : category
  val ltac : category
  val ltac2 : category
  val native_compiler : category
  val numbers : category
  val parsing : category
  val pedantic : category
  val records : category
  val rewrite_rules : category
  val ssr : category
  val syntax : category
  val tactics : category
  val user_warn : category
  val vernacular : category

end
