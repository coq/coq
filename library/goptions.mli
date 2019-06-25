(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

open Libnames
open Mod_subst

type option_name = string list

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
    (A : sig
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

module MakeRefTable :
  functor
    (A : sig
       type t
       module Set : CSig.SetS with type elt = t
       val encode : Environ.env -> qualid -> t
       val subst : substitution -> t -> t
       val printer : t -> Pp.t
       val key : option_name
       val title : string
       val member_message : t -> bool -> Pp.t
     end) ->
sig
  val v : unit -> A.Set.t
  val active : A.t -> bool
end


(** {6 Options. } *)

(** These types and function are for declaring a new option of name [key]
   and access functions [read] and [write]; the parameter [name] is the option name
   used when printing the option value (command "Print Toto Titi." *)

type 'a option_sig = {
  optdepr    : bool;
  (** whether the option is DEPRECATED *)
  optname    : string;
  (** a short string describing the option *)
  optkey     : option_name;
  (** the low-level name of this option *)
  optread    : unit -> 'a;
  optwrite   : 'a -> unit
}

(** The [preprocess] function is triggered before setting the option. It can be
    used to emit a warning on certain values, and clean-up the final value. *)

val declare_int_option   : ?preprocess:(int option -> int option) ->
                           int option option_sig -> unit
val declare_bool_option  : ?preprocess:(bool -> bool) ->
                           bool option_sig   -> unit
val declare_string_option: ?preprocess:(string -> string) ->
                           string option_sig -> unit
val declare_stringopt_option: ?preprocess:(string option -> string option) ->
                              string option option_sig -> unit

(** Helper to declare a reference controlled by an option. Read-only
   as to avoid races. *)
val declare_bool_option_and_ref : depr:bool -> name:string -> key:option_name -> value:bool -> (unit -> bool)

(** {6 Special functions supposed to be used only in vernacentries.ml } *)

module OptionMap : CSig.MapS with type key = option_name

type 'a table_of_A =  {
  add : Environ.env -> 'a -> unit;
  remove : Environ.env -> 'a -> unit;
  mem : Environ.env -> 'a -> unit;
  print : unit -> unit;
}

val get_string_table :
  option_name -> string table_of_A
val get_ref_table :
  option_name -> qualid table_of_A

(** The first argument is a locality flag. *)
val set_int_option_value_gen    : ?locality:option_locality -> option_name -> int option -> unit
val set_bool_option_value_gen   : ?locality:option_locality -> option_name -> bool   -> unit
val set_string_option_value_gen : ?locality:option_locality -> option_name -> string -> unit
val set_string_option_append_value_gen : ?locality:option_locality -> option_name -> string -> unit
val unset_option_value_gen : ?locality:option_locality -> option_name -> unit

val set_int_option_value    : option_name -> int option -> unit
val set_bool_option_value   : option_name -> bool   -> unit
val set_string_option_value : option_name -> string -> unit

val print_option_value : option_name -> unit

type option_value =
  | BoolValue   of bool
  | IntValue    of int option
  | StringValue of string
  | StringOptValue of string option

val set_option_value : ?locality:option_locality ->
  ('a -> option_value -> option_value) -> option_name -> 'a -> unit
(** [set_option_value ?locality f name v] sets [name] to the result of
    applying [f] to [v] and [name]'s current value. Use for behaviour
    depending on the type of the option, eg erroring when ['a] doesn't
    match it. Changing the type will result in errors later so don't do
    that. *)

(** Summary of an option status *)
type option_state = {
  opt_depr  : bool;
  opt_name  : string;
  opt_value : option_value;
}

val get_tables : unit -> option_state OptionMap.t
val print_tables : unit -> Pp.t

val error_undeclared_key : option_name -> 'a
