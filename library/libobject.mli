
(* $Id$ *)

(*i*)
open Names
(*i*)

(* [Libobject] declares persistent objects, given with three methods:
   a caching function specifying how to add the object in the current
   scope of theory modules;
   a loading function, specifying what to do when the object is loaded
   from the disk;
   an opening function, specifying what to do when the module containing
   the object is opened;
   a specification function, to extract its specification when writing
   the specification of a module to the disk (.vi) *)

type 'a object_declaration = {
  cache_function : section_path * 'a -> unit;
  load_function : section_path * 'a -> unit;
  open_function : section_path * 'a -> unit;
  export_function : 'a -> 'a option }

(*s Given an object name and a declaration, the function [declare_object]
   will hand back two functions, the "injection" and "projection"
   functions for dynamically typed library-objects. *)

type obj

val declare_object : 
  (string * 'a object_declaration) -> ('a -> obj) * (obj -> 'a)

val object_tag : obj -> string

val cache_object : section_path * obj -> unit
val load_object : section_path * obj -> unit
val open_object : section_path * obj -> unit
val export_object : obj -> obj option

