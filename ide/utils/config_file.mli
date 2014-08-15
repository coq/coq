(*********************************************************************************)
(*                Cameleon                                                       *)
(*                                                                               *)
(*    Copyright (C) 2005 Institut National de Recherche en Informatique et       *)
(*    en Automatique. All rights reserved.                                       *)
(*                                                                               *)
(*    This program is free software; you can redistribute it and/or modify       *)
(*    it under the terms of the GNU Library General Public License as            *)
(*    published by the Free Software Foundation; either version 2 of the         *)
(*    License, or  any later version.                                            *)
(*                                                                               *)
(*    This program is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              *)
(*    GNU Library General Public License for more details.                       *)
(*                                                                               *)
(*    You should have received a copy of the GNU Library General Public          *)
(*    License along with this program; if not, write to the Free Software        *)
(*    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA                   *)
(*    02111-1307  USA                                                            *)
(*                                                                               *)
(*    Contact: Maxence.Guesdon@inria.fr                                          *)
(*                                                                               *)
(*********************************************************************************)

(**
  This module implements a mechanism to handle configuration files.
  A configuration file is defined as a set of [variable = value] lines,
  where value can be
    a simple string (types int, string, bool...),
    a list of values between brackets (lists) or parentheses (tuples),
    or a set of [variable = value] lines between braces.
  The configuration file is automatically loaded and saved,
  and configuration parameters are manipulated inside the program as easily as references.

  Object implementation by Jean-Baptiste Rouquier.
*)

(** {1:lowlevelinterface Low level interface} *)
(** Skip this section on a first reading... *)

(** The type of cp freshly parsed from configuration file,
not yet wrapped in their proper type. *)
module Raw : sig
  type cp =
    | String of string (** base types, reproducing the tokens of Genlex *)
    | Int of int
    | Float of float
    | List of cp list (** compound types *)
    | Tuple of cp list
    | Section of (string * cp) list

  (** A parser. *)
  val of_string : string -> cp

  (** Used to print the values into a log file for instance. *)
  val to_channel : out_channel -> cp -> unit
end

(** A type used to specialize polymorphics classes and define new classes.
  {!Config_file.predefinedwrappers} are provided.
 *)
type 'a wrappers = { to_raw : 'a -> Raw.cp; of_raw : Raw.cp -> 'a; }

(** An exception raised by {!Config_file.cp.set_raw}
  when the argument doesn't have a suitable {!Config_file.Raw.cp} type.
  The function explains the problem and flush the output.*)
exception Wrong_type of (out_channel -> unit)

(* (\** {2 Miscellaneous functions} *\) *)

(* val bool_of_string : string -> bool *)

(** {1 High level interface} *)
(** {2 The two main classes} *)

(** A Configuration Parameter, in short cp, ie
  a value we can store in and read from a configuration file. *)
class type ['a] cp = object
  (** {1 Accessing methods} *)

  method get : 'a
  method set : 'a -> unit
  method get_default : 'a
  method get_help : string
  method get_name : string list

  (** Resets to the default value. *)
  method reset : unit

  (** {1 Miscellaneous} *)

  (** All the hooks are executed each time the method set is called,
    just after setting the new value.*)
  method add_hook : ('a -> 'a -> unit) -> unit

  (** Used to generate command line arguments in {!Config_file.group.command_line_args} *)
  method set_short_name : string -> unit

  (** [None] if no optional short_name was provided during object creation
    and [set_short_name] was never called.*)
  method get_short_name : string option

  (** {1 Methods for internal use} *)

  method get_formatted : Format.formatter -> unit
  method get_default_formatted : Format.formatter -> unit
  method get_help_formatted : Format.formatter -> unit

  method get_spec : Arg.spec
  method set_raw : Raw.cp -> unit
end

(** Unification over all possible ['a cp]:
  contains the main methods of ['a cp] except the methods using the type ['a].
  A [group] manipulates only [groupable_cp] for homogeneity. *)
type groupable_cp = <
  get_name : string list;
  get_short_name : string option;
  get_help : string;

  get_formatted : Format.formatter -> unit;
  get_default_formatted : Format.formatter -> unit;
  get_help_formatted : Format.formatter -> unit;
  get_spec : Arg.spec;

  reset : unit;
  set_raw : Raw.cp -> unit; >

(** Raised in case a name is already used.
  See {!Config_file.group.add} *)
exception Double_name

(** An exception possibly raised if we want to check that
  every cp is defined in a configuration file.
  See {!Config_file.group.read}.
*)
exception Missing_cp of groupable_cp

(** A group of cps, that can be loaded and saved,
or used to generate command line arguments.

The basic usage is to have only one group and one configuration file,
but this mechanism allows having more,
for instance having another smaller group for the options to pass on the command line.
*)
class group : object
  (** Adds a cp to the group.
    Note that the type ['a] must be lost
    to allow cps of different types to belong to the same group.
    @raise Double_name if [cp#get_name] is already used. *)
(*     method add : 'a cp -> 'a cp *)
    method add : 'a cp -> unit

    (**[write filename] saves all the cps into the configuration file [filename].*)
    method write : ?with_help:bool -> string -> unit

    (** [read filename] reads [filename]
      and stores the values it specifies into the cps belonging to this group.
      The file is created (and not read) if it doesn't exists.
      In the default behaviour, no warning is issued
      if not all cps are updated or if some values of [filename] aren't used.

      If [obsoletes] is specified,
      then prints in this file all the values that are
      in [filename] but not in this group.
      Those cps are likely to be erroneous or obsolete.
      Opens this file only if there is something to write in it.

      If [no_default] is [true], then raises [Missing_cp foo] if
      the cp [foo] isn't defined in [filename] but belongs to this group.

      [on_type_error groupable_cp value output filename in_channel]
      is called if the file doesn't give suitable value
      (string instead of int for instance, or a string not belonging to the expected enumeration)
      for the cp [groupable_cp].
      [value] is the value read from the file,
      [output] is the argument of {!Config_file.Wrong_type},
      [filename] is the same argument as the one given to read,
      and [in_channel] refers to [filename] to allow a function to close it if needed.
      Default behaviour is to print an error message and call [exit 1].
*)
    method read : ?obsoletes:string -> ?no_default:bool ->
      ?on_type_error : (groupable_cp -> Raw.cp -> (out_channel -> unit) ->
                          string -> in_channel -> unit) ->
      string -> unit

    (** Interface with module Arg.
      @param section_separator the string used to concatenate the name of a cp,
      to get the command line option name.
      ["-"] is a good default.
      @return a list that can be used with [Arg.parse] and [Arg.usage].*)
    method command_line_args : section_separator:string -> (string * Arg.spec * string) list
  end

(** {2 Predefined cp classes} *)

(** The last three non-optional arguments are always
  [name] (of type string list), [default_value] and [help] (of type string).

  [name] is the path to the cp: [["section";"subsection"; ...; "foo"]].
  It can consists of a single element but must not be empty.

  [short_name] will be added a "-" and used in
  {!Config_file.group.command_line_args}.

  [group], if provided, adds the freshly defined option to it
  (something like [initializer group#add self]).

  [help] needs not contain newlines, it will be automatically truncated where needed.
  It is mandatory but can be [""].
*)

class int_cp : ?group:group -> string list -> ?short_name:string -> int -> string -> [int] cp
class float_cp : ?group:group -> string list -> ?short_name:string -> float -> string -> [float] cp
class bool_cp : ?group:group -> string list -> ?short_name:string -> bool -> string -> [bool] cp
class string_cp : ?group:group -> string list -> ?short_name:string -> string -> string -> [string] cp
class ['a] list_cp : 'a wrappers -> ?group:group -> string list -> ?short_name:string -> 'a list -> string -> ['a list] cp
class ['a] option_cp : 'a wrappers -> ?group:group -> string list -> ?short_name:string -> 'a option -> string -> ['a option] cp
class ['a] enumeration_cp : (string * 'a) list -> ?group:group -> string list -> ?short_name:string -> 'a -> string -> ['a] cp
class ['a, 'b] tuple2_cp : 'a wrappers -> 'b wrappers -> ?group:group -> string list -> ?short_name:string -> 'a * 'b -> string -> ['a * 'b] cp
class ['a, 'b, 'c] tuple3_cp : 'a wrappers -> 'b wrappers -> 'c wrappers -> ?group:group -> string list -> ?short_name:string -> 'a * 'b * 'c -> string -> ['a * 'b * 'c] cp
class ['a, 'b, 'c, 'd] tuple4_cp : 'a wrappers -> 'b wrappers -> 'c wrappers -> 'd wrappers -> ?group:group -> string list -> ?short_name:string -> 'a * 'b * 'c * 'd -> string -> ['a * 'b * 'c * 'd] cp
class string2_cp : ?group:group -> string list -> ?short_name:string -> string * string -> string -> [string, string] tuple2_cp
(* class color_cp : ?group:group -> string list -> ?short_name:string -> string -> string -> string_cp *)
class font_cp : ?group:group -> string list -> ?short_name:string -> string -> string -> string_cp
class filename_cp : ?group:group -> string list -> ?short_name:string -> string -> string -> string_cp

(** {2:predefinedwrappers Predefined wrappers} *)

val int_wrappers : int wrappers
val float_wrappers : float wrappers
val bool_wrappers : bool wrappers
val string_wrappers : string wrappers
val list_wrappers : 'a wrappers -> 'a list wrappers
val option_wrappers : 'a wrappers -> 'a option wrappers

(** If you have a [type suit = Spades | Hearts | Diamond | Clubs], then
{[enumeration_wrappers ["spades",Spades; "hearts",Hearts; "diamond",Diamond; "clubs",Clubs]]}
will allow you to use cp of this type.
For sum types with not only constant constructors,
you will need to define your own cp class. *)
val enumeration_wrappers : (string * 'a) list -> 'a wrappers
val tuple2_wrappers : 'a wrappers -> 'b wrappers -> ('a * 'b) wrappers
val tuple3_wrappers : 'a wrappers -> 'b wrappers -> 'c wrappers -> ('a * 'b * 'c) wrappers
val tuple4_wrappers : 'a wrappers -> 'b wrappers -> 'c wrappers -> 'd wrappers -> ('a * 'b * 'c * 'd) wrappers

(** {2 Defining new cp classes} *)

(** To define a new cp class, you just have to provide an implementation for the wrappers
between your type [foo] and the type [Raw.cp].
Once you have your wrappers [w], write
{[class foo_cp = [foo] cp_custom_type w]}

For further details, have a look at the commented .ml file,
section "predefined cp classes".
*)
class ['a] cp_custom_type : 'a wrappers ->
  ?group:group -> string list -> ?short_name:string -> 'a -> string -> ['a] cp


(** {1 Backward compatibility}

Deprecated.

All the functions from the module Options are available, except:

- [prune_file]: use [group#write ?obsoletes:"foo.ml"].
- [smalllist_to_value], [smalllist_option]: use lists or tuples.
- [get_class].
- [class_hook]: hooks are local to a cp.
  If you want hooks global to a class,
  define a new class that inherit from {!Config_file.cp_custom_type}.
- [set_simple_option], [get_simple_option], [simple_options], [simple_args]:
  use {!Config_file.group.write}.
- [set_option_hook]: use {!Config_file.cp.add_hook}.
- [set_string_wrappers]: define a new class with {!Config_file.cp_custom_type}.

The old configurations files are readable by this module.
*)





(**/**)
type 'a option_class
type 'a option_record
type options_file

val create_options_file : string -> options_file
val set_options_file : options_file -> string -> unit
val load : options_file -> unit
val append : options_file -> string -> unit
val save : options_file -> unit
val save_with_help : options_file -> unit
(* val define_option : options_file -> *)
(*   string list ->  string -> 'a option_class -> 'a -> 'a option_record *)
val option_hook : 'a option_record -> (unit -> unit) -> unit

val string_option : string option_class
val color_option : string option_class
val font_option : string option_class
val int_option : int option_class
val bool_option : bool option_class
val float_option : float option_class
val string2_option : (string * string) option_class

val option_option : 'a option_class -> 'a option option_class
val list_option : 'a option_class -> 'a list option_class
val sum_option : (string * 'a) list -> 'a option_class
val tuple2_option :
  'a option_class * 'b option_class -> ('a * 'b) option_class
val tuple3_option : 'a option_class * 'b option_class * 'c option_class ->
  ('a * 'b * 'c) option_class
val tuple4_option :
    'a option_class * 'b option_class * 'c option_class * 'd option_class ->
  ('a * 'b * 'c * 'd) option_class

val ( !! ) : 'a option_record -> 'a
val ( =:= ) : 'a option_record -> 'a -> unit
val shortname : 'a option_record -> string
val get_help : 'a option_record -> string

type option_value =
  Module of option_module
| StringValue of  string
| IntValue of int
| FloatValue of float
| List of option_value list
| SmallList of option_value list
and option_module = (string * option_value) list

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
