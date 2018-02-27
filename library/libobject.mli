(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Libnames
open Mod_subst

(** [Libobject] declares persistent objects, given with methods:

   * a caching function specifying how to add the object in the current
     scope;
     If the object wishes to register its visibility in the Nametab,
     it should do so for all possible suffixes.

   * a loading function, specifying what to do when the module
     containing the object is loaded;
     If the object wishes to register its visibility in the Nametab,
     it should do so for all suffixes no shorter than the "int" argument

   * an opening function, specifying what to do when the module
     containing the object is opened (imported);
     If the object wishes to register its visibility in the Nametab,
     it should do so for the suffix of the length the "int" argument

   * a classification function, specifying what to do with the object,
     when the current module (containing the object) is ended;
     The possibilities are:
     Dispose    - the object dies at the end of the module
     Substitute - meaning the object is substitutive and
                  the module name must be updated
     Keep       - the object is not substitutive, but survives module
                  closing
     Anticipate - this is for objects that have to be explicitly
                  managed by the [end_module] function (like Require
                  and Read markers)

     The classification function is also an occasion for a cleanup
     (if this function returns Keep or Substitute of some object, the
     cache method is never called for it)

   * a substitution function, performing the substitution;
     this function should be declared for substitutive objects
     only (see above). NB: the substitution might now be delayed
     instead of happening at module creation, so this function
     should _not_ depend on the current environment

   * a discharge function, that is applied at section closing time to
     collect the data necessary to rebuild the discharged form of the
     non volatile objects

   * a rebuild function, that is applied after section closing to
     rebuild the non volatile content of a section from the data
     collected by the discharge function

  Any type defined as a persistent object must be pure (e.g. no references) and
  marshallable by the OCaml Marshal module (e.g. no closures).

*)

type 'a substitutivity =
    Dispose | Substitute of 'a | Keep of 'a | Anticipate of 'a

type 'a object_declaration = {
  object_name : string;
  cache_function : object_name * 'a -> unit;
  load_function : int -> object_name * 'a -> unit;
  open_function : int -> object_name * 'a -> unit;
  classify_function : 'a -> 'a substitutivity;
  subst_function :  substitution * 'a -> 'a;
  discharge_function : object_name * 'a -> 'a option;
  rebuild_function : 'a -> 'a }

(** The default object is a "Keep" object with empty methods.
   Object creators are advised to use the construction
   [{(default_object "MY_OBJECT") with
      cache_function = ...
   }]
   and specify only these functions which are not empty/meaningless

*)

val default_object : string -> 'a object_declaration

(** the identity substitution function *)
val ident_subst_function : substitution * 'a -> 'a

(** {6 ... } *)
(** Given an object declaration, the function [declare_object_full]
   will hand back two functions, the "injection" and "projection"
   functions for dynamically typed library-objects. *)

type obj

val declare_object_full :
  'a object_declaration -> ('a -> obj) * (obj -> 'a)

val declare_object :
  'a object_declaration -> ('a -> obj)

val object_tag : obj -> string

val cache_object : object_name * obj -> unit
val load_object : int -> object_name * obj -> unit
val open_object : int -> object_name * obj -> unit
val subst_object : substitution * obj -> obj
val classify_object : obj -> obj substitutivity
val discharge_object : object_name * obj -> obj option
val rebuild_object : obj -> obj

(** {6 Debug} *)

val dump : unit -> (int * string) list
