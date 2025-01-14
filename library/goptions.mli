(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module manages customization parameters at the vernacular level     *)

(** Two kinds of things are managed : tables and options value
   - Tables are created by applying the [MakeTable] functor.
   - Variables storing options value are created by applying one of the
   [declare_int_option], [declare_bool_option], ... functions.

   Each table/option is uniquely identified by a key of type [option_name]
   which consists in a list of strings. Note that for parsing constraints,
   table names must not be made of more than 2 strings while option names
   can be of arbitrary length.

   The declaration of a table, say of name [["Toto";"Titi"]]
   automatically makes available the following vernacular commands:

      Add Toto Titi foo.
      Remove Toto Titi foo.
      Print Toto Titi.
      Test Toto Titi.

   The declaration of a non boolean option value, say of name
   [["Tata";"Tutu";"Titi"]], automatically makes available the
   following vernacular commands:

       Set Tata Tutu Titi val.
       Print Table Tata Tutu Titi.

   If it is the declaration of a boolean value, the following
   vernacular commands are made available:

       Set Tata Tutu Titi.
       Unset Tata Tutu Titi.
       Print Table Tata Tutu Titi. (** synonym: Test Table Tata Tutu Titi. *)

   All options are synchronized with the document.
*)

type option_name = string list

type _ option_kind =
  | BoolKind : bool option_kind
  | IntKind : int option option_kind
  | StringKind : string option_kind
  | StringOptKind : string option option_kind

type option_locality = OptDefault | OptLocal | OptExport | OptGlobal

(** {6 Tables. } *)

(** The functor [MakeStringTable] declares a table containing objects
   of type [string]; the function [member_message] say what to print
   when invoking the "Test Toto Titi foo." command; at the end [title]
   is the table name printed when invoking the "Print Toto Titi."
   command; [active] is roughly the internal version of the vernacular
   "Test ...": it tells if a given object is in the table; [elements]
   returns the list of elements of the table *)

module MakeStringTable :
  functor
    (_ : sig
       val key : option_name
       val title : string
       val member_message : string -> bool -> Pp.t
     end) ->
sig
  val v : unit -> CString.Set.t
  val active : string -> bool
end

(** The functor [MakeRefTable] declares a new table of objects of type
   [A.t] practically denoted by [reference]; the encoding function
   [encode : env -> reference -> A.t] is typically a globalization function,
   possibly with some restriction checks; the function
   [member_message] say what to print when invoking the "Test Toto
   Titi foo." command; at the end [title] is the table name printed
   when invoking the "Print Toto Titi." command; [active] is roughly
   the internal version of the vernacular "Test ...": it tells if a
   given object is in the table.  *)

module type RefConvertArg = sig
  type t
  module Set : CSig.USetS with type elt = t
  val encode : Environ.env -> Libnames.qualid -> t
  val subst : Mod_subst.substitution -> t -> t

  val check_local : Libobject.locality -> t -> unit
  val discharge : t -> t
  (** Elements which cannot be discharged should only be added with Local *)

  val printer : t -> Pp.t
  val key : option_name
  val title : string
  val member_message : t -> bool -> Pp.t
end

module MakeRefTable :
  functor (A : RefConvertArg) ->
sig
  val v : unit -> A.Set.t
  val active : A.t -> bool
  val set : Libobject.locality -> A.t -> bool -> unit
end


(** {6 Options. } *)

(** These types and function are for declaring a new option of name
   [key] and access functions [read] and [write]; the parameter [name]
   is the option name used when printing the option value (command
   "Print Toto Titi."

   The declare_*_option functions are low-level, to be used when
   implementing complex option workflows, e.g. when the option data is in the global env.
   For most use cases, you should use
   the helper functions declare_*_option_and_ref. *)

type 'a option_sig = {
  optstage   : Summary.Stage.t;
  optdepr    : Deprecation.t option;
  (** whether the option is DEPRECATED *)
  optkey     : option_name;
  (** the low-level name of this option *)
  optread    : unit -> 'a;
  optwrite   : 'a -> unit
}

(** The [preprocess] function is triggered before setting the option. It can be
    used to emit a warning on certain values, and clean-up the final value.

    [StringOptKind] should be preferred to [StringKind] because it supports "Unset". *)
val declare_option   : ?preprocess:('a -> 'a) -> kind:'a option_kind -> 'a option_sig -> unit

val declare_append_only_option : ?preprocess:(string -> string) -> sep:string ->
  string option_sig -> unit

(** Helpers to declare a reference controlled by an option. *)

(** Wrapper type to separate the function calls to register the option
    at toplevel from the calls to read the option value. *)
type 'a getter = { get : unit -> 'a }

type 'a opt_decl = ?stage:Summary.Stage.t -> ?depr:Deprecation.t -> key:option_name -> value:'a -> unit -> 'a getter

val declare_int_option_and_ref : int opt_decl
val declare_intopt_option_and_ref : int option opt_decl
val declare_nat_option_and_ref : int opt_decl
val declare_bool_option_and_ref : bool opt_decl
val declare_string_option_and_ref : string opt_decl
val declare_stringopt_option_and_ref : string option opt_decl
val declare_interpreted_string_option_and_ref : (string -> 'a) -> ('a -> string) -> 'a opt_decl

(** {6 Special functions supposed to be used only in vernacentries.ml } *)

module OptionMap : CSig.MapS with type key = option_name

type 'a table_of_A =  {
  add : Environ.env -> Libobject.locality -> 'a -> unit;
  remove : Environ.env -> Libobject.locality -> 'a -> unit;
  mem : Environ.env -> 'a -> unit;
  print : unit -> unit;
}

val get_string_table :
  option_name -> string table_of_A
val get_ref_table :
  option_name -> Libnames.qualid table_of_A

(** The first argument is a locality flag.
    If [stage] is provided, the option is set/unset only if it is declared in the corresponding stage.
    If omitted, the option is always set/unset. *)
val set_int_option_value_gen    : ?locality:option_locality -> ?stage:Summary.Stage.t -> option_name -> int option -> unit
val set_bool_option_value_gen   : ?locality:option_locality -> ?stage:Summary.Stage.t -> option_name -> bool   -> unit
val set_string_option_value_gen : ?locality:option_locality -> ?stage:Summary.Stage.t -> option_name -> string -> unit
val unset_option_value_gen : ?locality:option_locality -> ?stage:Summary.Stage.t -> option_name -> unit

val set_int_option_value    : ?stage:Summary.Stage.t -> option_name -> int option -> unit
val set_bool_option_value   : ?stage:Summary.Stage.t -> option_name -> bool   -> unit
val set_string_option_value : ?stage:Summary.Stage.t -> option_name -> string -> unit

val print_option_value : option_name -> unit

type option_value =
  | BoolValue   of bool
  | IntValue    of int option
  | StringValue of string
  | StringOptValue of string option

type table_value =
  | StringRefValue of string
  | QualidRefValue of Libnames.qualid

(** [get_option_value key] returns [None] if option with name [key] was not found. *)
val get_option_value : option_name -> (unit -> option_value) option

type 'a check_and_cast = { check_and_cast : 'b. 'a -> 'b option_kind -> 'b }

val set_option_value : ?locality:option_locality -> ?stage:Summary.Stage.t ->
  'a check_and_cast -> option_name -> 'a -> unit
(** [set_option_value ?locality f name v] sets [name] to the result of
    applying [f] to [v] and [name]'s option kind. Use for behaviour
    depending on the type of the option, eg erroring when ['a] doesn't
    match it. *)

(** Summary of an option status *)
type option_state = {
  opt_depr  : Deprecation.t option;
  opt_value : option_value;
}

val get_tables : unit -> option_state OptionMap.t
val print_tables : unit -> Pp.t

type iter_table_aux = { aux : 'a. 'a table_of_A -> Environ.env -> 'a -> unit }
val iter_table : Environ.env -> iter_table_aux -> option_name -> table_value list -> unit

val error_undeclared_key : option_name -> 'a

(** Compat *)

val declare_int_option   : ?preprocess:(int option -> int option) ->
                           int option option_sig -> unit
val declare_bool_option  : ?preprocess:(bool -> bool) ->
                           bool option_sig   -> unit
val declare_string_option: ?preprocess:(string -> string) ->
                           string option_sig -> unit
val declare_stringopt_option: ?preprocess:(string option -> string option) ->
                              string option option_sig -> unit
