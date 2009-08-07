(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Pp
open Names
open Libnames
(*i*)

(*s This module contains the tables for globalization, which
    associates internal object references to qualified names (qualid).

    There are three classes of names:

    1a- internal kernel names: [kernel_name], [constant], [inductive],
        [module_path]

    1b- other internal names: [global_reference], [syndef_name],
        [extended_global_reference], [global_dir_reference], ...

    2- full, non ambiguous user names: [full_path] and [dir_path]

    3- non necessarily full, possibly ambiguous user names: [reference]
       and [qualid]
*)

(* Most functions in this module fall into one of the following categories:
   \begin{itemize}
   \item [push : visibility -> full_user_name -> object_reference -> unit]
   
   Registers the [object_reference] to be referred to by the
   [full_user_name] (and its suffixes according to [visibility]).
   [full_user_name] can either be a [full_path] or a [dir_path].

   \item [exists : full_user_name -> bool] 
   
   Is the [full_user_name] already atributed as an absolute user name
   of some object? 

   \item [locate : qualid -> object_reference]

   Finds the object referred to by [qualid] or raises [Not_found]

   \item [full_name : qualid -> full_user_name]

   Finds the full user name referred to by [qualid] or raises [Not_found]
   
   \item [shortest_qualid_of : object_reference -> user_name]

   The [user_name] can be for example the shortest non ambiguous [qualid] or 
   the [full_user_name] or [identifier]. Such a function can also have a 
   local context argument. 
   \end{itemize}
*)
   
  
exception GlobalizationError of qualid
exception GlobalizationConstantError of qualid

(* Raises a globalization error *)
val error_global_not_found_loc : loc -> qualid -> 'a
val error_global_not_found     : qualid -> 'a
val error_global_constant_not_found_loc : loc -> qualid -> 'a

(*s Register visibility of things *)

(* The visibility can be registered either
   \begin{itemize}

   \item for all suffixes not shorter then a given int -- when the
   object is loaded inside a module -- or

   \item for a precise suffix, when the module containing (the module
   containing ...) the object is opened (imported) 
   \end{itemize}
*)

type visibility = Until of int | Exactly of int

val push : visibility -> full_path -> global_reference -> unit
val push_modtype : visibility -> full_path -> module_path -> unit
val push_dir : visibility -> dir_path -> global_dir_reference -> unit
val push_syndef : visibility -> full_path -> syndef_name -> unit

type ltac_constant = kernel_name
val push_tactic : visibility -> full_path -> ltac_constant -> unit


(*s The following functions perform globalization of qualified names *)

(* These functions globalize a (partially) qualified name or fail with
   [Not_found] *)

val locate : qualid -> global_reference
val locate_extended : qualid -> extended_global_reference
val locate_constant : qualid -> constant
val locate_syndef : qualid -> syndef_name
val locate_modtype : qualid -> module_path
val locate_dir : qualid -> global_dir_reference
val locate_module : qualid -> module_path
val locate_section : qualid -> dir_path
val locate_tactic : qualid -> ltac_constant

(* These functions globalize user-level references into global
   references, like [locate] and co, but raise a nice error message
   in case of failure *)

val global : reference -> global_reference
val global_inductive : reference -> inductive

(* These functions locate all global references with a given suffix;
   if [qualid] is valid as such, it comes first in the list *)

val locate_all : qualid -> global_reference list
val locate_extended_all : qualid -> extended_global_reference list

(* Mapping a full path to a global reference *)

val global_of_path : full_path -> global_reference
val extended_global_of_path : full_path -> extended_global_reference

(*s These functions tell if the given absolute name is already taken *)

val exists_cci : full_path -> bool
val exists_modtype : full_path -> bool
val exists_dir : dir_path -> bool
val exists_section : dir_path -> bool (* deprecated synonym of [exists_dir] *)
val exists_module : dir_path -> bool (* deprecated synonym of [exists_dir] *)

(*s These functions locate qualids into full user names *)

val full_name_cci : qualid -> full_path
val full_name_modtype : qualid -> full_path
val full_name_module : qualid -> dir_path

(*s Reverse lookup -- finding user names corresponding to the given
  internal name *)

(* Returns the full path bound to a global reference or syntactic
   definition, and the (full) dirpath associated to a module path *)

val path_of_syndef : syndef_name -> full_path
val path_of_global : global_reference -> full_path
val dirpath_of_module : module_path -> dir_path

(* Returns in particular the dirpath or the basename of the full path
   associated to global reference *)

val dirpath_of_global : global_reference -> dir_path
val basename_of_global : global_reference -> identifier

(* Printing of global references using names as short as possible *)
val pr_global_env : Idset.t -> global_reference -> std_ppcmds


(* The [shortest_qualid] functions given an object with [user_name]
   Coq.A.B.x, try to find the shortest among x, B.x, A.B.x and
   Coq.A.B.x that denotes the same object. *)

val shortest_qualid_of_global : Idset.t -> global_reference -> qualid
val shortest_qualid_of_syndef : Idset.t -> syndef_name -> qualid
val shortest_qualid_of_modtype : module_path -> qualid
val shortest_qualid_of_module : module_path -> qualid
val shortest_qualid_of_tactic : ltac_constant -> qualid

(* Deprecated synonyms *)

val extended_locate : qualid -> extended_global_reference (*= locate_extended *)
val absolute_reference : full_path -> global_reference (* = global_of_path *)
