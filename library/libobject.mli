
(* $Id$ *)

(*i*)
open Names
(*i*)

(* [Libobject] declares persistent objects given with three methods:
   - a loading function, specifying what to do when the object is loaded
     from the disk;
   - a caching function specifying how to import the object in the current
     scope of theory modules;
   - a specification function, to extract its specification when writing
     the specification of a module to the disk (.vi) *)

type 'a object_declaration = {
  load_function : 'a -> unit;
  cache_function : section_path * 'a -> unit;
  specification_function : 'a -> 'a }

(*s given the object-name, the "loading" function, the "caching" function, 
   and the "specification" function, the function [declare_object]
   will hand back two functions, the "injection" and "projection"
   functions for dynamically typed library-objects. *)

type obj

val declare_object : 
  (string * 'a object_declaration) -> ('a -> obj) * (obj -> 'a)

val object_tag : obj -> string

val load_object : obj -> unit

val cache_object : (section_path * obj) -> unit

val extract_object_specification : obj -> obj
