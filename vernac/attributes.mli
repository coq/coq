(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The type of parsing attribute data *)
type vernac_flags = vernac_flag list
and vernac_flag = string * vernac_flag_value
and vernac_flag_value =
  | VernacFlagEmpty
  | VernacFlagLeaf of string
  | VernacFlagList of vernac_flags

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

val polymorphic : bool attribute
val program : bool attribute
val template : bool option attribute
val locality : bool option attribute
val deprecation : Deprecation.t option attribute
val canonical : bool attribute

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

type 'a key_parser = 'a option -> vernac_flag_value -> 'a
(** A parser for some key in an attribute. It is given a nonempty ['a
    option] when the attribute is multiply set for some command.

    eg in [#[polymorphic] Monomorphic Definition foo := ...], when
   parsing [Monomorphic] it will be given [Some true]. *)

val attribute_of_list : (string * 'a key_parser) list -> 'a option attribute
(** Make an attribute from a list of key parsers together with their
   associated key. *)

val bool_attribute : name:string -> on:string -> off:string -> bool option attribute
(** Define boolean attribute [name] with value [true] when [on] is
   provided and [false] when [off] is provided. The attribute may only
   be set once for a command. *)

val qualify_attribute : string -> 'a attribute -> 'a attribute
(** [qualified_attribute qual att] treats [#[qual(atts)]] like [att]
   treats [atts]. *)

(** Combinators to help define your own parsers. See the
   implementation of [bool_attribute] for practical use. *)

val assert_empty : string -> vernac_flag_value -> unit
(** [assert_empty key v] errors if [v] is not empty. [key] is used in
   the error message as the name of the attribute. *)

val assert_once : name:string -> 'a option -> unit
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
val vernac_polymorphic_flag : vernac_flag
val vernac_monomorphic_flag : vernac_flag

(** For the stm, do not use! *)

val polymorphic_nowarn : bool attribute

(** For internal use, avoid warning if not qualified as eg [universes(polymorphic)]. *)
val universe_polymorphism_option_name : string list
val is_universe_polymorphism : unit -> bool
