(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s Identifiers *)

type identifier
type name = Name of identifier | Anonymous
(* Parsing and printing of identifiers *)
val string_of_id : identifier -> string
val id_of_string : string -> identifier

(* Identifiers sets and maps *)
module Idset  : Set.S with type elt = identifier
module Idpred : Predicate.S with type elt = identifier
module Idmap  : Map.S with type key = identifier

(*s Directory paths = section names paths *)
type module_ident = identifier
module ModIdmap : Map.S with type key = module_ident

type dir_path

(* Inner modules idents on top of list (to improve sharing).
   For instance: A.B.C is ["C";"B";"A"] *)
val make_dirpath : module_ident list -> dir_path
val repr_dirpath : dir_path -> module_ident list

(* Printing of directory paths as ["coq_root.module.submodule"] *)
val string_of_dirpath : dir_path -> string


(*s Section paths are {\em absolute} names *)
type section_path

(* Constructors of [section_path] *)
val make_path : dir_path -> identifier -> section_path

(* Destructors of [section_path] *)
val repr_path : section_path -> dir_path * identifier

(* Parsing and printing of section path as ["coq_root.module.id"] *)
val string_of_path : section_path -> string

module Spset  : Set.S with type elt = section_path
module Sppred : Predicate.S with type elt = section_path
module Spmap  : Map.S with type key = section_path

(*s********************************************************************)
(* type of global reference *)

type variable = identifier
type constant = section_path
(* Beware: first inductive has index 0 *)
type inductive = section_path * int
(* Beware: first constructor has index 1 *)
type constructor = inductive * int
type mutual_inductive = section_path

val ith_mutual_inductive : inductive -> int -> inductive

val ith_constructor_of_inductive : inductive -> int -> constructor
val inductive_of_constructor : constructor -> inductive
val index_of_constructor : constructor -> int

(* Hash-consing *)
val hcons_names : unit ->
  (section_path -> section_path) * (dir_path -> dir_path) *
  (name -> name) * (identifier -> identifier) * (string -> string)
