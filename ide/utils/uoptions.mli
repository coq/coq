(**************************************************************************)
(*                   Cameleon                                             *)
(*                                                                        *)
(*      Copyright (C) 2002 Institut National de Recherche en Informatique et   *)
(*      en Automatique. All rights reserved.                              *)
(*                                                                        *)
(*      This program is free software; you can redistribute it and/or modify  *)
(*      it under the terms of the GNU General Public License as published by  *)
(*      the Free Software Foundation; either version 2 of the License, or  *)
(*      any later version.                                                *)
(*                                                                        *)
(*      This program is distributed in the hope that it will be useful,   *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of    *)
(*      MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the     *)
(*      GNU General Public License for more details.                      *)
(*                                                                        *)
(*      You should have received a copy of the GNU General Public License  *)
(*      along with this program; if not, write to the Free Software       *)
(*      Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA          *)
(*      02111-1307  USA                                                   *)
(*                                                                        *)
(*      Contact: Maxence.Guesdon@inria.fr                                *)
(**************************************************************************)

(**
 This module implements a simple mechanism to handle program options files.
  An options file is defined as a set of [variable = value] lines,
  where value can be a simple string, a list of values (between brackets
or parentheses) or a set of [variable = value] lines between braces.
The option file is automatically loaded and saved, and options are
manipulated inside the program as easily as references. 

   Code from Fabrice Le Fessant.
*)

type 'a option_class
(** The abstract type for a class of options. A class is a set of options
which use the same conversion functions from loading and saving.*)
  
type 'a option_record
(** The abstract type for an option *)

type options_file

val create_options_file : string -> options_file
val set_options_file : options_file -> string -> unit
val prune_file : options_file -> unit  

(** {2 Operations on option files} *)
  
val load : options_file -> unit
(** [load file] loads the option file. All options whose value is specified
   in the option file are updated. *)
  
val append : options_file -> string -> unit
(** [append filename] loads the specified option file. All options whose 
value is specified in this file are updated. *)
  
val save : options_file -> unit
(** [save file] saves all the options values to the option file. *)

val save_with_help : options_file -> unit
(** [save_with_help ()] saves all the options values to the option file,
   with the help provided for each option. *)
  
(** {2  Creating options} *)  

val define_option : options_file ->
  string list ->  string -> 'a option_class -> 'a -> 'a option_record
val option_hook : 'a option_record -> (unit -> unit) -> unit
    
val string_option : string option_class
val color_option : string option_class
val font_option : string option_class
val int_option : int option_class
val bool_option : bool option_class
val float_option : float option_class
val string2_option : (string * string) option_class
  
  (* parameterized options *)
val list_option : 'a option_class -> 'a list option_class
val smalllist_option : 'a option_class -> 'a list option_class
val sum_option : (string * 'a) list -> 'a option_class
val tuple2_option :  
  'a option_class * 'b option_class -> ('a * 'b) option_class
val tuple3_option : 'a option_class * 'b option_class * 'c option_class ->
  ('a * 'b * 'c) option_class
val tuple4_option : 
    'a option_class * 'b option_class * 'c option_class * 'd option_class ->
  ('a * 'b * 'c * 'd) option_class

(** {2  Using options} *)
  
val ( !! ) : 'a option_record -> 'a
val ( =:= ) : 'a option_record -> 'a -> unit

val shortname : 'a option_record -> string
val get_help : 'a option_record -> string  
  
(** {2 Creating new option classes} *)

val get_class : 'a option_record -> 'a option_class

val class_hook : 'a option_class -> ('a option_record -> unit) -> unit

type option_value =
  Module of option_module
| StringValue of  string
| IntValue of int
| FloatValue of float
| List of option_value list
| SmallList of option_value list
  
and option_module =
  (string * option_value) list

val define_option_class :
  string -> (option_value -> 'a) -> ('a -> option_value) -> 'a option_class

val to_value : 'a option_class -> 'a -> option_value
val from_value : 'a option_class -> option_value -> 'a
  
val value_to_string : option_value -> string
val string_to_value : string -> option_value
val value_to_int : option_value -> int
val int_to_value : int -> option_value
val bool_of_string : string -> bool
val value_to_bool : option_value -> bool
val bool_to_value : bool -> option_value
val value_to_float : option_value -> float
val float_to_value : float -> option_value
val value_to_string2 : option_value -> string * string
val string2_to_value : string * string -> option_value
val value_to_list : (option_value -> 'a) -> option_value -> 'a list
val list_to_value : ('a -> option_value) -> 'a list -> option_value
val smalllist_to_value : ('a -> option_value) -> 'a list -> option_value

val set_simple_option : options_file -> string -> string -> unit
val simple_options : options_file -> (string * string) list
val get_simple_option : options_file -> string -> string
val set_option_hook : options_file -> string -> (unit -> unit) -> unit
  
val set_string_wrappers : 'a option_record -> 
  ('a -> string) -> (string -> 'a) -> unit

(** {2 Other functions} *)

val simple_args : options_file -> (string * Arg.spec * string) list
