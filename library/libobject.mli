(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Libnames
(*i*)

(* [Libobject] declares persistent objects, given with methods:

   * a caching function specifying how to add the object in the current
     scope;

   * a loading function, specifying what to do when the module 
     containing the object is loaded;
     Substitutive objects (see below) are required to ignore 
     the section_path argument!

   * an opening function, specifying what to do when the module 
     containing the object is opened (imported);
     Substitutive objects (see below) are required to ignore 
     the section_path argument!

   * a classification function, specyfying what to do with the object,
     when the current module (containing the object) is ended;
     The possibilities are:
     Dispose   - the object dies at the end of the module
     Substitue - meaning the object is substitutive and 
                 the module name must be updated
     Keep true - the object is not substitutive, but has to be kept 
                 for future eventual opening
     Keep false - the object is not substitutive but does not make 
                 difference if the module is closed or open (so there 
                 is no need to keep it in memory) - but must be kept 
                 on disk
     Anticipate - this is for objects which have to be explicitely 
                 managed by the end_module function (like Require 
                 and Read markers)

     The classification function is also an occasion for a cleanup
     (if this function returns Keep or Substitute of some object, the 
     cache method is never called for it)

   * a substitution function, performing the substitution; 
     this function should be declared for substitutive objects 
     only (see obove)

   * an export function, to enable optional writing of its contents 
     to disk (.vo). This function is also the oportunity to remove 
     redundant information in order to keep .vo size small 

     The export function is a little obsolete and will be removed 
     in the near future... 

*)

type 'a substitutivity = 
    Dispose | Substitute of 'a | Keep of bool * 'a | Anticipate of 'a

type 'a object_declaration = {
  object_name : string;
  cache_function : section_path * 'a -> unit;
  load_function : section_path * 'a -> unit;
  open_function : section_path * 'a -> unit;
  classify_function : section_path * 'a -> 'a substitutivity;
  subst_function : substitution -> 'a -> 'a;
  export_function : 'a -> 'a option }

(* The default object is a "Keep true" object with empty methods. 
   Object creators are advised to use the construction
   [{(default_object "MY_OBJECT") with
      cache_function = ...
   }]
   and specify only these functions which are not empty/meaningless

*)

val default_object : string -> 'a object_declaration

(*s Given an object declaration, the function [declare_object]
   will hand back two functions, the "injection" and "projection"
   functions for dynamically typed library-objects. *)

type obj

val declare_object : 
  'a object_declaration -> ('a -> obj) * (obj -> 'a)

val object_tag : obj -> string

val cache_object : section_path * obj -> unit
val load_object : section_path * obj -> unit
val open_object : section_path * obj -> unit
val subst_object : substitution -> obj -> obj
val classify_object : section_path * obj -> obj substitutivity
val export_object : obj -> obj option
val relax : bool -> unit
