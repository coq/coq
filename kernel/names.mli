(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*s Identifiers *)

type identifier
type name = Name of identifier | Anonymous
(* Parsing and printing of identifiers *)
val string_of_id : identifier -> string
val id_of_string : string -> identifier

val id_ord : identifier -> identifier -> int

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

val empty_dirpath : dir_path

(* Printing of directory paths as ["coq_root.module.submodule"] *)
val string_of_dirpath : dir_path -> string


(*s Unique identifier to be used as "self" in structures and 
  signatures - invisible for users *)
  
type mod_self_id

(* The first argument is a file name - to prevent conflict between 
   different files *)
val make_msid : dir_path -> string -> mod_self_id
val id_of_msid : mod_self_id -> identifier
val debug_string_of_msid : mod_self_id -> string

(*s Unique names for bound modules *)
type mod_bound_id

val make_mbid : dir_path -> string -> mod_bound_id
val id_of_mbid : mod_bound_id -> identifier
val debug_string_of_mbid : mod_bound_id -> string

(*s Names of structure elements *)
type label
val mk_label : string -> label
val string_of_label : label -> string

val label_of_id : identifier -> label
val id_of_label : label -> identifier

module Labset : Set.S with type elt = label
module Labmap : Map.S with type key = label

(*s The module part of the kernel name *)
type module_path =
  | MPfile of dir_path
  | MPbound of mod_bound_id
  | MPself of mod_self_id 
  | MPdot of module_path * label
(*i  | MPapply of module_path * module_path    in the future (maybe) i*)


val string_of_mp : module_path -> string

module MPset : Set.S with type elt = module_path
module MPmap : Map.S with type key = module_path


(*s Substitutions *)

type substitution

val empty_subst : substitution

val add_msid : 
  mod_self_id -> module_path -> substitution -> substitution
val add_mbid : 
  mod_bound_id -> module_path -> substitution -> substitution

val map_msid : mod_self_id -> module_path -> substitution
val map_mbid : mod_bound_id -> module_path -> substitution

(* sequential composition: 
   [substitute (join sub1 sub2) t = substitute sub2 (substitute sub1 t)]
*)
val join : substitution -> substitution -> substitution

(*i debugging *)
val debug_string_of_subst : substitution -> string
val debug_pr_subst : substitution -> Pp.std_ppcmds
(*i*)

(* [subst_mp sub mp] guarantees that whenever the result of the
   substitution is structutally equal [mp], it is equal by pointers 
   as well [==] *) 

val subst_mp : 
  substitution -> module_path -> module_path

(* [occur_*id id sub] returns true iff [id] occurs in [sub] 
   on either side *)

val occur_msid : mod_self_id -> substitution -> bool
val occur_mbid : mod_bound_id -> substitution -> bool
     

(* Name of the toplevel structure *)
val initial_msid : mod_self_id
val initial_path : module_path (* [= MPself initial_msid] *)

(* Initial "seed" of the unique identifier generator *)
val initial_dir : dir_path

(*s The absolute names of objects seen by kernel *)

type kernel_name

(* Constructor and destructor *)
val make_kn : module_path -> dir_path -> label -> kernel_name
val repr_kn : kernel_name -> module_path * dir_path * label

val modpath : kernel_name -> module_path
val label : kernel_name -> label

val string_of_kn : kernel_name -> string
val pr_kn : kernel_name -> Pp.std_ppcmds
val subst_kn : substitution -> kernel_name -> kernel_name


module KNset  : Set.S with type elt = kernel_name
module KNpred : Predicate.S with type elt = kernel_name
module KNmap  : Map.S with type key = kernel_name


(*s Specific paths for declarations *)

type variable = identifier
type constant = kernel_name
type mutual_inductive = kernel_name
(* Beware: first inductive has index 0 *)
type inductive = mutual_inductive * int
(* Beware: first constructor has index 1 *)
type constructor = inductive * int

val ith_mutual_inductive : inductive -> int -> inductive
val ith_constructor_of_inductive : inductive -> int -> constructor
val inductive_of_constructor : constructor -> inductive
val index_of_constructor : constructor -> int

(* Better to have it here that in Closure, since required in grammar.cma *)
type evaluable_global_reference =
  | EvalVarRef of identifier
  | EvalConstRef of constant

(* Hash-consing *)
val hcons_names : unit ->
  (kernel_name -> kernel_name) * (dir_path -> dir_path) *
  (name -> name) * (identifier -> identifier) * (string -> string)
