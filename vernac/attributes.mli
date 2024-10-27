(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The type of parsing attribute data *)
type vernac_flag_type =
  | FlagQualid of Libnames.qualid
  | FlagString of string

type vernac_flags = vernac_flag list
and vernac_flag = (string * vernac_flag_value) CAst.t
and vernac_flag_value =
  | VernacFlagEmpty
  | VernacFlagLeaf of vernac_flag_type
  | VernacFlagList of vernac_flags

val pr_vernac_flag : vernac_flag -> Pp.t

type +'a attribute
(** The type of attributes. When parsing attributes if an ['a
   attribute] is present then an ['a] value will be produced.
    In the most general case, an attribute transforms the raw flags
   along with its value. *)

val parse : 'a attribute -> vernac_flags -> 'a
(** Errors on unsupported attributes. *)

val unsupported_attributes : vernac_flags -> unit
(** Errors if the list of flags is nonempty. *)

module Notations : sig
  (** Notations to combine attributes. *)

  include Monad.Def with type 'a t = 'a attribute
  (** Attributes form a monad. [a1 >>= f] means [f] will be run on the
     flags transformed by [a1] and using the value produced by [a1].
      The trivial attribute [return x] does no action on the flags. *)

  val (++) : 'a attribute -> 'b attribute -> ('a * 'b) attribute
  (** Combine 2 attributes. If any keys are in common an error will be raised. *)

end

(** Definitions for some standard attributes. *)

val raw_attributes : vernac_flags attribute

val polymorphic : bool attribute
val program : bool attribute
val template : bool option attribute
val unfold_fix : bool attribute
val locality : bool option attribute
val option_locality : Goptions.option_locality attribute
val opacity : bool option attribute
val reversible : bool option attribute
val canonical_field : bool attribute
val canonical_instance : bool attribute
val using : string option attribute
val explicit_hint_locality : Hints.hint_locality option attribute
val bind_scope_where : Notation.add_scope_where option attribute

(** "deprecated" *)
val deprecation : Deprecation.t option attribute
val deprecation_with_use_globref_instead : Globnames.extended_global_reference Deprecation.with_qf option attribute

(** Just the "warn" attribute *)
val user_warn_warn : UserWarn.warn list attribute

(** "warn" and "deprecated" *)
val user_warns : UserWarn.t option attribute
val user_warns_with_use_globref_instead : Globnames.extended_global_reference UserWarn.with_qf option attribute

(** Default: if sections are opened then Local otherwise Export.
    Although this is named and uses the type [hint_locality]
    it may be used as the standard 3-valued locality attribute.
*)
val hint_locality : Hints.hint_locality attribute

(** Like [hint_locality] but the default in and out of sections is [SuperGlobal]. *)
val hint_locality_default_superglobal : Hints.hint_locality attribute

(** Enable/Disable universe checking *)
val typing_flags : Declarations.typing_flags option attribute

val program_mode_option_name : string list
(** For internal use when messing with the global option. *)

val only_locality : vernac_flags -> bool option
(** Parse attributes allowing only locality. *)

val only_polymorphism : vernac_flags -> bool
(** Parse attributes allowing only polymorphism.
    Uses the global flag for the default value. *)

val parse_drop_extra : 'a attribute -> vernac_flags -> 'a
(** Ignores unsupported attributes. *)

val parse_with_extra : 'a attribute -> vernac_flags -> vernac_flags * 'a
(** Returns unsupported attributes. *)

(** * Defining attributes. *)

type 'a key_parser = ?loc:Loc.t -> 'a option -> vernac_flag_value -> 'a
(** A parser for some key in an attribute. It is given a nonempty ['a
    option] when the attribute is multiply set for some command.

    eg in [#[polymorphic] Monomorphic Definition foo := ...], when
   parsing [Monomorphic] it will be given [Some true]. *)

val attribute_of_list : (string * 'a key_parser) list -> 'a option attribute
(** Make an attribute from a list of key parsers together with their
   associated key. *)

val payload_parser : ?cat:(string -> string -> string) -> name:string -> string key_parser
(** [payload_parser ?cat ~name] parses attributes like [#[name="payload"]].
    If the attribute is used multiple times and [cat] is non-None,
    the payloads are concatenated using it.
    If [cat] is None, having multiple occurences of the attribute is forbidden. *)

val payload_attribute : ?cat:(string -> string -> string) -> name:string -> string option attribute
(** This is just [attribute_of_list] for a single [payload_parser]. *)

(** Define boolean attribute [name], of the form [name={yes,no}]. The
   attribute may only be set once for a command. *)
val bool_attribute : name:string -> bool option attribute

val qualify_attribute : string -> 'a attribute -> 'a attribute
(** [qualified_attribute qual att] treats [#[qual(atts)]] like [att]
   treats [atts]. *)

(** Combinators to help define your own parsers. See the
   implementation of [bool_attribute] for practical use. *)

val assert_empty : ?loc:Loc.t -> string -> vernac_flag_value -> unit
(** [assert_empty key v] errors if [v] is not empty. [key] is used in
   the error message as the name of the attribute. *)

val assert_once : ?loc:Loc.t -> name:string -> 'a option -> unit
(** [assert_once ~name v] errors if [v] is not empty. [name] is used
   in the error message as the name of the attribute. Used to ensure
   that a given attribute is not reapeated. *)

val single_key_parser : name:string -> key:string -> 'a -> 'a key_parser
(** [single_key_parser ~name ~key v] makes a parser for attribute
    [name] giving the constant value [v] for key [key] taking no
    arguments. [name] may only be given once. *)

val make_attribute : (vernac_flags -> vernac_flags * 'a) -> 'a attribute
(** Make an attribute using the internal representation, thus with
   access to the full power of attributes. Unstable. *)

(** Compatibility values for parsing [Polymorphic]. *)
val vernac_polymorphic_flag : Loc.t option -> vernac_flag
val vernac_monomorphic_flag : Loc.t option -> vernac_flag

(** For internal use. *)
val universe_polymorphism_option_name : string list
val is_universe_polymorphism : unit -> bool
