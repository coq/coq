(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(* This module manages customization parameters at the vernacular level     *)

(* Two kinds of things are managed : tables and options value
   - Tables are created by applying the [MakeTable] functor.
   - Variables storing options value are created by applying one of the
   [declare_int_option], [declare_bool_option], ... functions.

   Each table/option is uniquely identified by a key of type [option_name].
   There are two kinds of table/option idenfiers: the primary ones
   (supposed to be more global) and the secondary ones

   The declaration of a table, say of name [SecondaryTable("Toto","Titi")] 
   automatically makes available the following vernacular commands:

      Add Toto Titi foo.
      Remove Toto Titi foo.
      Print Toto Titi.
      Test Toto Titi.

   The declaration of a non boolean option value, say of name
   [SecondaryTable("Tata","Tutu")], automatically makes available the
   following vernacular commands:

       Set Tata Tutu val.
       Print Table Tata Tutu.

   If it is the declaration of a boolean value, the following
   vernacular commands are made available:

       Set Tata Tutu.
       Unset Tata Tutu.
       Print Table Tata Tutu. (* synonym: Test Table Tata Tutu. *)

   For a primary table, say of name [PrimaryTable("Bidule")], the
   vernacular commands look like

      Add Bidule foo.
      Print Table Bidule foo.
      Set Bidule foo.
      ...

   The created table/option may be declared synchronous or not
   (synchronous = consistent with the resetting commands)                   *)

(*i*)
open Pp
open Names
open Libnames
open Term
open Nametab
(*i*)

(*s Things common to tables and options. *)

(* The type of primary or secondary table/option keys *)
type option_name =
  | PrimaryTable of string
  | SecondaryTable of string * string

val error_undeclared_key : option_name -> 'a


(*s Tables. *)

(* The functor [MakeStringTable] declares a table containing objects
   of type [string]; the function [check] is for testing if a given
   object is allowed to be added to the table; the function
   [member_message] say what to print when invoking the "Test Toto
   Titi foo." command; at the end [title] is the table name printed
   when invoking the "Print Toto Titi." command; [active] is roughly
   the internal version of the vernacular "Test ...": it tells if a
   given object is in the table; [elements] returns the list of
   elements of the table *)

module MakeStringTable :
  functor
    (A : sig
       val check : string -> unit
       val key : option_name
       val title : string
       val member_message : string -> bool -> string
       val synchronous : bool
     end) ->
sig
  val active : string -> bool
  val elements : unit -> string list
end

(* The functor [MakeIdentTable] declares a new table of [global_reference];
   for generality, identifiers may be internally encode in other type
   which is [A.t] through an encoding function [encode : global_reference ->
   A.t] (typically, [A.t] is the persistent [global_reference] associated
   to the currentdenotation of the [global_reference] and the encoding function
   is the globalization function); the function [check] is for testing
   if a given object is allowed to be added to the table; the function
   [member_message] say what to print when invoking the "Test Toto
   Titi foo." command; at the end [title] is the table name printed
   when invoking the "Print Toto Titi." command; [active] is roughly
   the internal version of the vernacular "Test ...": it tells if a
   given object is in the table.                                            *)

module MakeIdentTable :
  functor
    (A : sig
           type t
           val encode : global_reference -> t
           val check : t -> unit
           val printer : t -> std_ppcmds
           val key : option_name
           val title : string
           val member_message : global_reference -> bool -> string
           val synchronous : bool
         end) ->
    sig
      val active : A.t -> bool
      val elements : unit -> A.t list
    end


(*s Options. *)

(* These types and function are for declaring a new option of name [key]
   and access functions [read] and [write]; the parameter [name] is the option name 
   used when printing the option value (command "Print Toto Titi." *)

type 'a option_sig = {
  optsync    : bool; 
  optname    : string;
  optkey     : option_name;
  optread    : unit -> 'a;
  optwrite   : 'a -> unit
}

(* When an option is declared synchronous ([optsync] is [true]), the output is 
   a synchronous write function. Otherwise it is [optwrite] *)

type 'a write_function = 'a -> unit

val declare_int_option   : int option_sig    -> int write_function
val declare_bool_option  : bool option_sig   -> bool write_function
val declare_string_option: string option_sig -> string write_function


(*s Special functions supposed to be used only in vernacentries.ml *)

val get_string_table :
  option_name ->
    < add : string -> unit;
      remove : string -> unit;
      mem : string -> unit;
      print : unit >

val get_ident_table :
  option_name ->
    < add : global_reference -> unit;
      remove : global_reference -> unit;
      mem : global_reference -> unit;
      print : unit >

val set_int_option_value    : option_name -> int    -> unit
val set_bool_option_value   : option_name -> bool   -> unit
val set_string_option_value : option_name -> string -> unit

val print_option_value : option_name -> unit

val print_tables : unit -> unit

