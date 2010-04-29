(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(** {6 Identifiers } *)

type identifier
type name = Name of identifier | Anonymous

(** Parsing and printing of identifiers *)
val string_of_id : identifier -> string
val id_of_string : string -> identifier

val id_ord : identifier -> identifier -> int

(** Identifiers sets and maps *)
module Idset  : Set.S with type elt = identifier
module Idpred : Predicate.S with type elt = identifier
module Idmap  : Map.S with type key = identifier

(** {6 Directory paths = section names paths } *)
type module_ident = identifier
module ModIdmap : Map.S with type key = module_ident

type dir_path

(** Inner modules idents on top of list (to improve sharing).
   For instance: A.B.C is ["C";"B";"A"] *)
val make_dirpath : module_ident list -> dir_path
val repr_dirpath : dir_path -> module_ident list

val empty_dirpath : dir_path

(** Printing of directory paths as ["coq_root.module.submodule"] *)
val string_of_dirpath : dir_path -> string


(** {6 ... } *)
(** Unique identifier to be used as "self" in structures and
  signatures - invisible for users *)
type label
type mod_self_id

(** The first argument is a file name - to prevent conflict between
   different files *)
val make_msid : dir_path -> string -> mod_self_id
val repr_msid : mod_self_id -> int * string * dir_path
val id_of_msid : mod_self_id -> identifier
val label_of_msid : mod_self_id -> label
val refresh_msid : mod_self_id -> mod_self_id
val debug_string_of_msid : mod_self_id -> string
val string_of_msid : mod_self_id -> string

(** {6 Unique names for bound modules } *)
type mod_bound_id

val make_mbid : dir_path -> string -> mod_bound_id
val repr_mbid : mod_bound_id -> int * string * dir_path
val id_of_mbid : mod_bound_id -> identifier
val label_of_mbid : mod_bound_id -> label
val debug_string_of_mbid : mod_bound_id -> string
val string_of_mbid : mod_bound_id -> string

(** {6 Names of structure elements } *)

val mk_label : string -> label
val string_of_label : label -> string

val label_of_id : identifier -> label
val id_of_label : label -> identifier

module Labset : Set.S with type elt = label
module Labmap : Map.S with type key = label

(** {6 The module part of the kernel name } *)
type module_path =
  | MPfile of dir_path
  | MPbound of mod_bound_id
 (** | MPapp of module_path * module_path  very soon *)
  | MPdot of module_path * label


val check_bound_mp : module_path -> bool

val string_of_mp : module_path -> string

module MPset : Set.S with type elt = module_path
module MPmap : Map.S with type key = module_path

(** Name of the toplevel structure *)
val initial_msid : mod_self_id
val initial_path : module_path (** [= MPself initial_msid] *)

(** Initial "seed" of the unique identifier generator *)
val initial_dir : dir_path

(** {6 The absolute names of objects seen by kernel } *)

type kernel_name

(** Constructor and destructor *)
val make_kn : module_path -> dir_path -> label -> kernel_name
val repr_kn : kernel_name -> module_path * dir_path * label

val modpath : kernel_name -> module_path
val label : kernel_name -> label

val string_of_kn : kernel_name -> string
val pr_kn : kernel_name -> Pp.std_ppcmds


module KNset  : Set.S with type elt = kernel_name
module KNpred : Predicate.S with type elt = kernel_name
module KNmap  : Map.S with type key = kernel_name


(** {6 Specific paths for declarations } *)

type variable = identifier
type constant
type mutual_inductive

(** Beware: first inductive has index 0 *)
type inductive = mutual_inductive * int

(** Beware: first constructor has index 1 *)
type constructor = inductive * int

(** *_env modules consider an order on user part of names
   the others consider an order on canonical part of names*)
module Cmap  : Map.S with type key = constant
module Cmap_env  : Map.S with type key = constant
module Cpred  : Predicate.S with type elt = constant
module Cset  : Set.S with type elt = constant
module Cset_env  : Set.S with type elt = constant
module Mindmap : Map.S with type key = mutual_inductive
module Mindmap_env : Map.S with type key = mutual_inductive
module Mindset : Set.S with type elt = mutual_inductive
module Indmap : Map.S with type key = inductive
module Constrmap : Map.S with type key = constructor
module Indmap_env : Map.S with type key = inductive
module Constrmap_env : Map.S with type key = constructor

val constant_of_kn : kernel_name -> constant
val constant_of_kn_equiv : kernel_name -> kernel_name -> constant
val make_con : module_path -> dir_path -> label -> constant
val make_con_equiv : module_path -> module_path -> dir_path 
  -> label -> constant
val user_con : constant -> kernel_name
val canonical_con : constant -> kernel_name
val repr_con : constant -> module_path * dir_path * label
val eq_constant : constant -> constant -> bool

val string_of_con : constant -> string
val con_label : constant -> label
val con_modpath : constant -> module_path
val pr_con : constant -> Pp.std_ppcmds
val debug_pr_con : constant -> Pp.std_ppcmds
val debug_string_of_con : constant -> string



val mind_of_kn : kernel_name -> mutual_inductive
val mind_of_kn_equiv : kernel_name -> kernel_name -> mutual_inductive
val make_mind : module_path -> dir_path -> label -> mutual_inductive
val make_mind_equiv : module_path -> module_path -> dir_path 
  -> label -> mutual_inductive
val user_mind : mutual_inductive -> kernel_name
val canonical_mind : mutual_inductive -> kernel_name
val repr_mind : mutual_inductive -> module_path * dir_path * label
val eq_mind : mutual_inductive -> mutual_inductive -> bool

val string_of_mind : mutual_inductive -> string
val mind_label : mutual_inductive -> label
val mind_modpath : mutual_inductive -> module_path
val pr_mind : mutual_inductive -> Pp.std_ppcmds
val debug_pr_mind : mutual_inductive -> Pp.std_ppcmds
val debug_string_of_mind : mutual_inductive -> string



val ind_modpath : inductive -> module_path
val constr_modpath : constructor -> module_path

val ith_mutual_inductive : inductive -> int -> inductive
val ith_constructor_of_inductive : inductive -> int -> constructor
val inductive_of_constructor : constructor -> inductive
val index_of_constructor : constructor -> int
val eq_ind : inductive -> inductive -> bool
val eq_constructor : constructor -> constructor -> bool

(** Better to have it here that in Closure, since required in grammar.cma *)
type evaluable_global_reference =
  | EvalVarRef of identifier
  | EvalConstRef of constant

val eq_egr : evaluable_global_reference ->  evaluable_global_reference
  -> bool

(** Hash-consing *)
val hcons_names : unit ->
  (constant -> constant) *
  (mutual_inductive -> mutual_inductive) * (dir_path -> dir_path) *
  (name -> name) * (identifier -> identifier) * (string -> string)


(******)

type 'a tableKey =
  | ConstKey of constant
  | VarKey of identifier
  | RelKey of 'a

type transparent_state = Idpred.t * Cpred.t

val empty_transparent_state : transparent_state
val full_transparent_state : transparent_state
val var_full_transparent_state : transparent_state
val cst_full_transparent_state : transparent_state

type inv_rel_key = int (** index in the [rel_context] part of environment
			  starting by the end, {e inverse}
			  of de Bruijn indice *)

type id_key = inv_rel_key tableKey

val eq_id_key : id_key -> id_key -> bool

(*equalities on constant and inductive 
  names for the checker*)

val eq_con_chk : constant -> constant -> bool
val eq_ind_chk : inductive -> inductive -> bool

