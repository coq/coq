(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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
   [full_user_name] (and its suffixes according to [visibility])

   \item [exists : full_user_name -> bool] 
   
   Is the [full_user_name] already atributed as an absolute user name
   of some object? 

   \item [locate : qualid -> object_reference]

   Finds the object referred to by [qualid] or raises Not_found 
   
   \item [name_of] : object_reference -> user_name

   The [user_name] can be for example the shortest non ambiguous [qualid] or 
   the [full_user_name] or [identifier]. Such a function can also have a 
   local context argument. 
*)
   
  

(* Finds the real name of a global (e.g. fetch the constructor names
   from the inductive name and constructor number) *)
val sp_of_global : Sign.named_context option -> global_reference -> section_path
val sp_of_syntactic_definition : kernel_name -> section_path

(* Turns an absolute name into a qualified name denoting the same name *)
val full_name : global_reference -> section_path
val shortest_qualid_of_global : Sign.named_context option -> global_reference -> qualid
val id_of_global : Sign.named_context option -> global_reference -> identifier

(* Printing of global references using names as short as possible *)
val pr_global_env : Sign.named_context option -> global_reference -> std_ppcmds

val shortest_qualid_of_module : module_path -> qualid
val shortest_qualid_of_modtype : kernel_name -> qualid

exception GlobalizationError of qualid
exception GlobalizationConstantError of qualid

(* Raises a globalization error *)
val error_global_not_found_loc : loc -> qualid -> 'a
val error_global_not_found     : qualid -> 'a
val error_global_constant_not_found_loc : loc -> qualid -> 'a

(*s Register visibility of things *)

(* The visibility can be registered either for all suffixes not
   shorter then a given int - when the object is loaded inside a module,
   or for a precise suffix, when the module containing (the module
   containing ...) the object is open (imported) *)

type visibility = Until of int | Exactly of int

val push : visibility -> section_path -> global_reference -> unit
val push_syntactic_definition : 
  visibility -> section_path -> kernel_name -> unit
val push_modtype : visibility -> section_path -> kernel_name -> unit
val push_dir : visibility -> dir_path -> global_dir_reference -> unit
val push_object : visibility -> section_path -> unit
val push_tactic : visibility -> section_path -> unit

(*s The following functions perform globalization of qualified names *)

(* This returns the section path of a constant or fails with [Not_found] *)
val locate : qualid -> global_reference

(* This function is used to transform a qualified identifier into a
   global reference, with a nice error message in case of failure *)
val global : qualid located -> global_reference

(* The same for inductive types *)
val global_inductive : qualid located -> inductive

(* This locates also syntactic definitions *)
val extended_locate : qualid -> extended_global_reference

val locate_obj : qualid -> section_path

val locate_constant : qualid -> constant
val locate_mind : qualid -> mutual_inductive
val locate_section : qualid -> dir_path
val locate_modtype : qualid -> kernel_name
val locate_syntactic_definition : qualid -> kernel_name

val locate_tactic : qualid -> section_path
val locate_dir : qualid -> global_dir_reference
val locate_module : qualid -> module_path

(* [exists sp] tells if [sp] is already bound to a cci term *)
val exists_cci : section_path -> bool
val exists_modtype : section_path -> bool

(* Those three functions are the same *)
val exists_dir : dir_path -> bool
val exists_section : dir_path -> bool (* deprecated *)
val exists_module : dir_path -> bool (* deprecated *)

val full_name_modtype : qualid -> section_path

(*s Roots of the space of absolute names *)

(* This turns a "user" absolute name into a global reference;
   especially, constructor/inductive names are turned into internal
   references inside a block of mutual inductive *)
val absolute_reference : section_path -> global_reference

(* [locate_in_absolute_module dir id] finds [id] in module [dir] or in
   one of its section/subsection *)
val locate_in_absolute_module : dir_path -> identifier -> global_reference

val locate_loaded_library : qualid -> dir_path

type frozen

val freeze : unit -> frozen
val unfreeze : frozen -> unit

