(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {6 Identifiers } *)

module Id :
sig
  type t
  (** Type of identifiers *)

  val equal : t -> t -> bool
  (** Equality over identifiers *)

  val compare : t -> t -> int
  (** Comparison over identifiers *)

  val check : string -> unit
  (** Check that a string may be converted to an identifier. Raise an exception
      related to the problem when this is not the case. *)

  val check_soft : string -> unit
  (** As [check], but may raise a warning instead of failing when the string is
      not an identifier, but is a well-formed string. *)

  val of_string : string -> t
  (** Converts a string into an identifier. *)

  val to_string : t -> string
  (** Converts a identifier into an string. *)

  val print : t -> Pp.std_ppcmds
  (** Pretty-printer. *)

  module Set : Set.S with type elt = t
  (** Finite sets of identifiers. *)

  module Map : sig
    include Map.S with type key = t
    (** FIXME: this is included in OCaml 3.12 *)
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val singleton : key -> 'a -> 'a t
  end
  (** Finite maps of identifiers. *)

  module Pred : Predicate.S with type elt = t
  (** Predicates over identifiers. *)

  val hcons : t -> t
  (** Hashconsing of identifiers. *)

end

module Name :
sig
  type t = Name of Id.t | Anonymous
  (** A name is either undefined, either an identifier. *)

  val equal : t -> t -> bool
  (** Equality over names. *)

  val hcons : t -> t
  (** Hashconsing over names. *)

end

(** {6 Type aliases} *)

type name = Name.t = Name of Id.t | Anonymous
type variable = Id.t
type module_ident = Id.t

(** {6 Directory paths = section names paths } *)

module Dir_path :
sig
  type t
  (** Type of directory paths. Essentially a list of module identifiers. The
      order is reversed to improve sharing. E.g. A.B.C is ["C";"B";"A"] *)

  val equal : t -> t -> bool
  (** Equality over directory paths. *)

  val compare : t -> t -> int
  (** Comparison over directory paths. *)

  val make : module_ident list -> t
  (** Create a directory path. (The list must be reversed). *)

  val repr : t -> module_ident list
  (** Represent a directory path. (The result list is reversed). *)

  val empty : t
  (** The empty directory path. *)

  val is_empty : t -> bool
  (** Test whether a directory path is empty. *)

  val to_string : t -> string
  (** Print directory paths as ["coq_root.module.submodule"] *)

  val initial : t
  (** Initial "seed" of the unique identifier generator *)

  val hcons : t -> t
  (** Hashconsing of directory paths. *)

end

(** {6 Names of structure elements } *)

module Label :
sig
  type t
  (** Type of labels *)

  val equal : t -> t -> bool
  (** Equality over labels *)

  val make : string -> t
  (** Create a label out of a string. *)

  val to_string : t -> string
  (** Conversion to string. *)

  val of_id : Id.t -> t
  (** Conversion from an identifier. *)

  val to_id : t -> Id.t
  (** Conversion to an identifier. *)

  val print : t -> Pp.std_ppcmds
  (** Pretty-printer. *)

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t

end

(** {6 Unique names for bound modules} *)

module MBId :
sig
  type t
  (** Unique names for bound modules. Each call to [make] constructs a fresh
      unique identifier. *)

  val equal : t -> t -> bool
  (** Equality over unique bound names. *)

  val compare : t -> t -> int
  (** Comparison over unique bound names. *)

  val make : Dir_path.t -> Id.t -> t
  (** The first argument is a file name, to prevent conflict between different
      files. *)

  val repr : t -> int * Id.t * Dir_path.t
  (** Reverse of [make]. *)

  val to_id : t -> Id.t
  (** Return the identifier contained in the argument. *)

  val to_string : t -> string
  (** Conversion to a string. *)

  val debug_to_string : t -> string
  (** Same as [to_string], but outputs information related to debug. *)

end

module ModIdmap : Map.S with type key = module_ident

(** {6 The module part of the kernel name } *)

type module_path =
  | MPfile of Dir_path.t
  | MPbound of MBId.t
  | MPdot of module_path * Label.t

val mp_ord : module_path -> module_path -> int
val mp_eq : module_path -> module_path -> bool

val check_bound_mp : module_path -> bool

val string_of_mp : module_path -> string

module MPset : Set.S with type elt = module_path
module MPmap : Map.S with type key = module_path

(** Name of the toplevel structure *)
val initial_path : module_path (** [= MPfile initial_dir] *)

(** {6 The absolute names of objects seen by kernel } *)

type kernel_name

(** Constructor and destructor *)
val make_kn : module_path -> Dir_path.t -> Label.t -> kernel_name
val repr_kn : kernel_name -> module_path * Dir_path.t * Label.t

val modpath : kernel_name -> module_path
val label : kernel_name -> Label.t

val string_of_kn : kernel_name -> string
val pr_kn : kernel_name -> Pp.std_ppcmds

val kn_ord : kernel_name -> kernel_name -> int

module KNset  : Set.S with type elt = kernel_name
module KNpred : Predicate.S with type elt = kernel_name
module KNmap  : Map.S with type key = kernel_name


(** {6 Specific paths for declarations } *)

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
val make_con : module_path -> Dir_path.t -> Label.t -> constant
val make_con_equiv : module_path -> module_path -> Dir_path.t 
  -> Label.t -> constant
val user_con : constant -> kernel_name
val canonical_con : constant -> kernel_name
val repr_con : constant -> module_path * Dir_path.t * Label.t
val eq_constant : constant -> constant -> bool
val con_with_label : constant -> Label.t -> constant

val string_of_con : constant -> string
val con_label : constant -> Label.t
val con_modpath : constant -> module_path
val pr_con : constant -> Pp.std_ppcmds
val debug_pr_con : constant -> Pp.std_ppcmds
val debug_string_of_con : constant -> string



val mind_of_kn : kernel_name -> mutual_inductive
val mind_of_kn_equiv : kernel_name -> kernel_name -> mutual_inductive
val make_mind : module_path -> Dir_path.t -> Label.t -> mutual_inductive
val make_mind_equiv : module_path -> module_path -> Dir_path.t 
  -> Label.t -> mutual_inductive
val user_mind : mutual_inductive -> kernel_name
val canonical_mind : mutual_inductive -> kernel_name
val repr_mind : mutual_inductive -> module_path * Dir_path.t * Label.t
val eq_mind : mutual_inductive -> mutual_inductive -> bool

val string_of_mind : mutual_inductive -> string
val mind_label : mutual_inductive -> Label.t
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
  | EvalVarRef of Id.t
  | EvalConstRef of constant

val eq_egr : evaluable_global_reference ->  evaluable_global_reference
  -> bool

(** {6 Hash-consing } *)

val hcons_con : constant -> constant
val hcons_mind : mutual_inductive -> mutual_inductive
val hcons_ind : inductive -> inductive
val hcons_construct : constructor -> constructor

(******)

type 'a tableKey =
  | ConstKey of constant
  | VarKey of Id.t
  | RelKey of 'a

type transparent_state = Id.Pred.t * Cpred.t

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

(** {6 Deprecated functions. For backward compatibility.} *)

(** {5 Identifiers} *)

type identifier = Id.t
(** @deprecated Alias for [Id.t] *)

val check_ident : string -> unit
(** @deprecated Same as [Id.check]. *)

val check_ident_soft : string -> unit
(** @deprecated Same as [Id.check_soft]. *)

val string_of_id : identifier -> string
(** @deprecated Same as [Id.to_string]. *)

val id_of_string : string -> identifier
(** @deprecated Same as [Id.of_string]. *)

val id_ord : identifier -> identifier -> int
(** @deprecated Same as [Id.compare]. *)

val id_eq : identifier -> identifier -> bool
(** @deprecated Same as [Id.equal]. *)

module Idset  : Set.S with type elt = identifier and type t = Id.Set.t
(** @deprecated Same as [Id.Set]. *)

module Idpred : Predicate.S with type elt = identifier and type t = Id.Pred.t
(** @deprecated Same as [Id.Pred]. *)

module Idmap  : sig
  include Map.S with type key = identifier
  val exists : (identifier -> 'a -> bool) -> 'a t -> bool
  val singleton : key -> 'a -> 'a t
end
(** @deprecated Same as [Id.Map]. *)

(** {5 Directory paths} *)

type dir_path = Dir_path.t
(** @deprecated Alias for [Dir_path.t]. *)

val dir_path_ord : dir_path -> dir_path -> int
(** @deprecated Same as [Dir_path.compare]. *)

val dir_path_eq : dir_path -> dir_path -> bool
(** @deprecated Same as [Dir_path.equal]. *)

val make_dirpath : module_ident list -> dir_path
(** @deprecated Same as [Dir_path.make]. *)

val repr_dirpath : dir_path -> module_ident list
(** @deprecated Same as [Dir_path.repr]. *)

val empty_dirpath : dir_path
(** @deprecated Same as [Dir_path.empty]. *)

val is_empty_dirpath : dir_path -> bool
(** @deprecated Same as [Dir_path.is_empty]. *)

val string_of_dirpath : dir_path -> string
(** @deprecated Same as [Dir_path.to_string]. *)

val initial_dir : Dir_path.t
(** @deprecated Same as [Dir_path.initial]. *)

(** {5 Labels} *)

type label = Label.t
(** Alias type *)

val mk_label : string -> label
(** @deprecated Same as [Label.make]. *)

val string_of_label : label -> string
(** @deprecated Same as [Label.to_string]. *)

val pr_label : label -> Pp.std_ppcmds
(** @deprecated Same as [Label.print]. *)

val label_of_id : Id.t -> label
(** @deprecated Same as [Label.of_id]. *)

val id_of_label : label -> Id.t
(** @deprecated Same as [Label.to_id]. *)

val eq_label : label -> label -> bool
(** @deprecated Same as [Label.equal]. *)

(** {5 Unique bound module names} *)

type mod_bound_id = MBId.t
(** Alias type. *)

val mod_bound_id_ord : mod_bound_id -> mod_bound_id -> int
(** @deprecated Same as [MBId.compare]. *)

val mod_bound_id_eq : mod_bound_id -> mod_bound_id -> bool
(** @deprecated Same as [MBId.equal]. *)

val make_mbid : Dir_path.t -> Id.t -> mod_bound_id
(** @deprecated Same as [MBId.make]. *)

val repr_mbid : mod_bound_id -> int * Id.t * Dir_path.t
(** @deprecated Same as [MBId.repr]. *)

val id_of_mbid : mod_bound_id -> Id.t
(** @deprecated Same as [MBId.to_id]. *)

val string_of_mbid : mod_bound_id -> string
(** @deprecated Same as [MBId.to_string]. *)

val debug_string_of_mbid : mod_bound_id -> string
(** @deprecated Same as [MBId.debug_to_string]. *)

(** {5 Names} *)

val name_eq : name -> name -> bool
(** @deprecated Same as [Name.equal]. *)
