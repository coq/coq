(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Util
open Names
open Term
open Mod_subst
(*i*)

(*s Global reference is a kernel side type for all references together *)
type global_reference =
  | VarRef of variable
  | ConstRef of constant
  | IndRef of inductive
  | ConstructRef of constructor

val isVarRef : global_reference -> bool

val subst_constructor : substitution -> constructor -> constructor * constr
val subst_global : substitution -> global_reference -> global_reference * constr

(* Turn a global reference into a construction *)
val constr_of_global : global_reference -> constr

(* Turn a construction denoting a global reference into a global reference;
   raise [Not_found] if not a global reference *)
val global_of_constr : constr -> global_reference

(* Obsolete synonyms for constr_of_global and global_of_constr *)
val constr_of_reference : global_reference -> constr
val reference_of_constr : constr -> global_reference

module Refset : Set.S with type elt = global_reference 
module Refmap : Map.S with type key = global_reference

(*s Extended global references *)

type syndef_name = kernel_name

type extended_global_reference =
  | TrueGlobal of global_reference
  | SynDef of syndef_name

(*s Dirpaths *)
val pr_dirpath : dir_path -> Pp.std_ppcmds

val dirpath_of_string : string -> dir_path
val string_of_dirpath : dir_path -> string

(* Pop the suffix of a [dir_path] *)
val pop_dirpath : dir_path -> dir_path 

(* Pop the suffix n times *)
val pop_dirpath_n : int -> dir_path -> dir_path

(* Give the immediate prefix and basename of a [dir_path] *)
val split_dirpath : dir_path -> dir_path * identifier

val add_dirpath_suffix : dir_path -> module_ident -> dir_path
val add_dirpath_prefix : module_ident -> dir_path -> dir_path

val chop_dirpath : int -> dir_path -> dir_path * dir_path
val append_dirpath : dir_path -> dir_path -> dir_path

val drop_dirpath_prefix : dir_path -> dir_path -> dir_path
val is_dirpath_prefix_of : dir_path -> dir_path -> bool

module Dirset : Set.S with type elt = dir_path
module Dirmap : Map.S with type key = dir_path

(*s Full paths are {\em absolute} paths of declarations *)
type full_path

(* Constructors of [full_path] *)
val make_path : dir_path -> identifier -> full_path

(* Destructors of [full_path] *)
val repr_path : full_path -> dir_path * identifier
val dirpath : full_path -> dir_path
val basename : full_path -> identifier

(* Parsing and printing of section path as ["coq_root.module.id"] *)
val path_of_string : string -> full_path
val string_of_path : full_path -> string
val pr_path : full_path -> std_ppcmds

module Sppred : Predicate.S with type elt = full_path
module Spmap  : Map.S with type key = full_path

val restrict_path : int -> full_path -> full_path

(*s Temporary function to brutally form kernel names from section paths *)

val encode_kn : dir_path -> identifier -> kernel_name
val decode_kn : kernel_name -> dir_path * identifier
val encode_con : dir_path -> identifier -> constant
val decode_con : constant -> dir_path * identifier


(*s A [qualid] is a partially qualified ident; it includes fully
    qualified names (= absolute names) and all intermediate partial
    qualifications of absolute names, including single identifiers.
    The [qualid] are used to access the name table. *)

type qualid

val make_qualid : dir_path -> identifier -> qualid
val repr_qualid : qualid -> dir_path * identifier

val pr_qualid : qualid -> std_ppcmds
val string_of_qualid : qualid -> string
val qualid_of_string : string -> qualid

(* Turns an absolute name, a dirpath, or an identifier into a
   qualified name denoting the same name *)

val qualid_of_path : full_path -> qualid
val qualid_of_dirpath : dir_path -> qualid
val qualid_of_ident : identifier -> qualid

(* Both names are passed to objects: a "semantic" [kernel_name], which
   can be substituted and a "syntactic" [full_path] which can be printed
*)

type object_name = full_path * kernel_name

type object_prefix = dir_path * (module_path * dir_path)

val make_oname : object_prefix -> identifier -> object_name

(* to this type are mapped [dir_path]'s in the nametab *)
type global_dir_reference = 
  | DirOpenModule of object_prefix
  | DirOpenModtype of object_prefix
  | DirOpenSection of object_prefix
  | DirModule of object_prefix
  | DirClosedSection of dir_path
      (* this won't last long I hope! *)

(*s A [reference] is the user-level notion of name. It denotes either a
    global name (referred either by a qualified name or by a single
    name) or a variable *)

type reference = 
  | Qualid of qualid located
  | Ident of identifier located

val qualid_of_reference : reference -> qualid located
val string_of_reference : reference -> string
val pr_reference : reference -> std_ppcmds
val loc_of_reference : reference -> loc

(*s Popping one level of section in global names *)

val pop_con : constant -> constant
val pop_kn : kernel_name -> kernel_name
val pop_global_reference : global_reference -> global_reference
