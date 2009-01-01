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
  associates internal object references to qualified names (qualid). *)

(* Most functions in this module fall into one of the following categories:
   \begin{itemize}
   \item [push : visibility -> full_user_name -> object_reference -> unit]
   
   Registers the [object_reference] to be referred to by the
   [full_user_name] (and its suffixes according to [visibility]).
   [full_user_name] can either be a [section_path] or a [dir_path].

   \item [exists : full_user_name -> bool] 
   
   Is the [full_user_name] already atributed as an absolute user name
   of some object? 

   \item [locate : qualid -> object_reference]

   Finds the object referred to by [qualid] or raises [Not_found]
   
   \item [name_of : object_reference -> user_name]

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

val push : visibility -> section_path -> global_reference -> unit
val push_syntactic_definition : 
  visibility -> section_path -> kernel_name -> unit
val push_modtype : visibility -> section_path -> module_path -> unit
val push_dir : visibility -> dir_path -> global_dir_reference -> unit
val push_object : visibility -> section_path -> unit
val push_tactic : visibility -> section_path -> kernel_name -> unit


(*s The following functions perform globalization of qualified names *)

(* This returns the section path of a constant or fails with [Not_found] *)
val locate : qualid -> global_reference

(* This function is used to transform a qualified identifier into a
   global reference, with a nice error message in case of failure *)
val global : reference -> global_reference

(* The same for inductive types *)
val inductive_of_reference : reference -> inductive

(* This locates also syntactic definitions; raise [Not_found] if not found *)
val extended_locate : qualid -> extended_global_reference

(* This locates all names with a given suffix, if qualid is valid as
   such, it comes first in the list *)
val extended_locate_all : qualid -> extended_global_reference list

(* This locates all global references with a given suffixe *)
val locate_all : qualid -> global_reference list

val locate_obj : qualid -> section_path

val locate_constant : qualid -> constant
val locate_mind : qualid -> mutual_inductive
val locate_section : qualid -> dir_path
val locate_modtype : qualid -> module_path
val locate_syntactic_definition : qualid -> kernel_name

type ltac_constant = kernel_name
val locate_tactic : qualid -> ltac_constant
val locate_dir : qualid -> global_dir_reference
val locate_module : qualid -> module_path

(* A variant looking up a [section_path] *)
val absolute_reference : section_path -> global_reference
val extended_absolute_reference : section_path -> extended_global_reference


(*s These functions tell if the given absolute name is already taken *)

val exists_cci : section_path -> bool
val exists_modtype : section_path -> bool

(* Those three functions are the same *)
val exists_dir : dir_path -> bool
val exists_section : dir_path -> bool (* deprecated *)
val exists_module : dir_path -> bool (* deprecated *)


(*s These functions turn qualids into full user names: [section_path]s
  or [dir_path]s *)

val full_name_modtype : qualid -> section_path
val full_name_cci : qualid -> section_path

(* As above but checks that the path found is indeed a module *)
val full_name_module : qualid -> dir_path


(*s Reverse lookup -- finding user names corresponding to the given
  internal name *)

val sp_of_syntactic_definition : kernel_name -> section_path
val shortest_qualid_of_global : Idset.t -> global_reference -> qualid
val shortest_qualid_of_syndef : Idset.t -> kernel_name -> qualid
val shortest_qualid_of_tactic : ltac_constant -> qualid

val dir_of_mp : module_path -> dir_path

val sp_of_global : global_reference -> section_path
val id_of_global : global_reference -> identifier

(* Printing of global references using names as short as possible *)
val pr_global_env : Idset.t -> global_reference -> std_ppcmds


(* The [shortest_qualid] functions given an object with [user_name]
   Coq.A.B.x, try to find the shortest among x, B.x, A.B.x and
   Coq.A.B.x that denotes the same object. *)

val shortest_qualid_of_module : module_path -> qualid
val shortest_qualid_of_modtype : module_path -> qualid


(*
type frozen

val freeze : unit -> frozen
val unfreeze : frozen -> unit
*)
