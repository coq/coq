(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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

   The created table/option may be declared synchronous or not
   (synchronous = consistent with the resetting commands)                   *)

open Pp
open Libnames
open Mod_subst

type option_name = string list

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
       val member_message : string -> bool -> std_ppcmds
       val synchronous : bool
     end) ->
sig
  val active : string -> bool
  val elements : unit -> string list
end

(** The functor [MakeRefTable] declares a new table of objects of type
   [A.t] practically denoted by [reference]; the encoding function
   [encode : reference -> A.t] is typically a globalization function,
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
           val compare : t -> t -> int
           val encode : reference -> t
	   val subst : substitution -> t -> t
           val printer : t -> std_ppcmds
           val key : option_name
           val title : string
           val member_message : t -> bool -> std_ppcmds
           val synchronous : bool
         end) ->
    sig
      val active : A.t -> bool
      val elements : unit -> A.t list
    end


(** {6 Options. } *)

(** These types and function are for declaring a new option of name [key]
   and access functions [read] and [write]; the parameter [name] is the option name
   used when printing the option value (command "Print Toto Titi." *)

type 'a option_sig = {
  optsync    : bool;
  (** whether the option is synchronous w.r.t to the section/module system. *)
  optdepr    : bool;
  (** whether the option is DEPRECATED *)
  optname    : string;
  (** a short string describing the option *)
  optkey     : option_name;
  (** the low-level name of this option *)
  optread    : unit -> 'a;
  optwrite   : 'a -> unit
}

(** When an option is declared synchronous ([optsync] is [true]), the output is
   a synchronous write function. Otherwise it is [optwrite] *)
(** The [preprocess] function is triggered before setting the option. It can be
    used to emit a warning on certain values, and clean-up the final value. *)

type 'a write_function = 'a -> unit

val declare_int_option   : ?preprocess:(int option -> int option) ->
                           int option option_sig -> int option write_function
val declare_bool_option  : ?preprocess:(bool -> bool) ->
                           bool option_sig   -> bool write_function
val declare_string_option: ?preprocess:(string -> string) ->
                           string option_sig -> string write_function
val declare_stringopt_option: ?preprocess:(string option -> string option) ->
                              string option option_sig -> string option write_function


(** {6 Special functions supposed to be used only in vernacentries.ml } *)

module OptionMap : CSig.MapS with type key = option_name

val get_string_table :
  option_name ->
    < add : string -> unit;
      remove : string -> unit;
      mem : string -> unit;
      print : unit >

val get_ref_table :
  option_name ->
    < add : reference -> unit;
      remove : reference -> unit;
      mem : reference -> unit;
      print : unit >

(** The first argument is a locality flag.
    [Some true] = "Local", [Some false]="Global". *)
val set_int_option_value_gen    : bool option -> option_name -> int option -> unit
val set_bool_option_value_gen   : bool option -> option_name -> bool   -> unit
val set_string_option_value_gen : bool option -> option_name -> string -> unit
val set_string_option_append_value_gen : bool option -> option_name -> string -> unit
val unset_option_value_gen : bool option -> option_name -> unit

val set_int_option_value    : option_name -> int option -> unit
val set_bool_option_value   : option_name -> bool   -> unit
val set_string_option_value : option_name -> string -> unit

val print_option_value : option_name -> unit

type option_value =
  | BoolValue   of bool
  | IntValue    of int option
  | StringValue of string
  | StringOptValue of string option


(* For use in tactics: to be used in pairs *)
type previous_option_value
val override_option_value    : option_name -> option_value -> previous_option_value
val restore_option_value : option_name -> previous_option_value -> unit

val with_option_value : option_name -> option_value -> ('a -> 'b) -> 'a -> 'b

(** Summary of an option status *)
type option_state = {
  opt_sync  : bool;
  opt_depr  : bool;
  opt_name  : string;
  opt_value : option_value;
}

val get_tables : unit -> option_state OptionMap.t
val print_tables : unit -> std_ppcmds

val error_undeclared_key : option_name -> 'a
