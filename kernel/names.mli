(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Identifier
(*i*)

(*s Directory paths = section names paths *)

type dir_path = identifier list

val make_dirpath : identifier list -> dir_path
val repr_dirpath : dir_path -> identifier list

(* Give the immediate prefix of a dir_path *)
val dirpath_prefix : dir_path -> dir_path 

(* Give the immediate prefix and basename of a dir_path *)
val split_dirpath : dir_path -> dir_path * identifier

(* Printing of directory paths as ["coq_root.module.submodule"] *)
val string_of_dirpath : dir_path -> string
val pr_dirpath : dir_path -> std_ppcmds

(* [is_dirpath_prefix p1 p2=true] if [p1] is a prefix of or is equal to [p2] *)
val is_dirpath_prefix_of : dir_path -> dir_path -> bool

(* This file implements long names *)

type mod_str_id

val msid_of_string : string -> mod_str_id

type mod_bound_id

(* These two functions are NOT bijections *)
val mbid_of_string : string -> mod_bound_id
val string_of_mbid : mod_bound_id -> string

type module_path =
  | MPcomp of dir_path
  | MPbid of mod_bound_id
  | MPsid of mod_str_id 
  | MPdot of module_path * label
(*i  | MPapply of module_path * module_path    in the future (maybe) i*)

(* [subst_modpath_*id id by_path in_path] replaces bound/structure ident 
   [id] with [by_path] in [in_path]. They quarantee that whenever 
   [id] does not occur in [in_path], the result is [==] equal to 
   [in_path] *)

val subst_modpath_msid : 
  mod_str_id -> module_path -> module_path -> module_path
val subst_modpath_mbid : 
  mod_bound_id -> module_path -> module_path -> module_path

(* [occur_*id id mp] returns true iff [id] occurs in [mp] *)

val occur_msid : mod_str_id -> module_path -> bool
val occur_mbid : mod_bound_id -> module_path -> bool

(* debugging *)
val string_of_modpath : module_path -> string
val pr_modpath : module_path -> std_ppcmds

val top_msid : mod_str_id
val top_path : module_path

module MPmap : Map.S with type key = module_path

(* Long names of constants,... *)

type long_name = module_path * label

val make_ln : module_path -> label -> long_name

val modname : long_name -> module_path
val label : long_name -> label
val basename : long_name -> identifier

(* substitutions *)

val subst_longname_msid : 
  mod_str_id -> module_path -> long_name -> long_name
val subst_longname_mbid : 
  mod_bound_id -> module_path -> long_name -> long_name

(* debugging *)
val string_of_long_name : long_name -> string
val pr_ln : long_name -> std_ppcmds

module LNmap : Map.S with type key = long_name


(*s Specific paths for declarations *)
 
type variable_path = identifier
type constant_path = long_name
type inductive_path = long_name * int
type constructor_path = inductive_path * int
type mutual_inductive_path = long_name

(* type of global reference *)

type global_reference =
  | VarRef of variable_path
  | ConstRef of constant_path
  | IndRef of inductive_path
  | ConstructRef of constructor_path

