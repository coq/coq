(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util

(** {6 Identifiers } *)

module Id :
sig
  type t
  (** Type of identifiers *)

  val equal : t -> t -> bool
  (** Equality over identifiers *)

  val compare : t -> t -> int
  (** Comparison over identifiers *)

  val hash : t -> int
  (** Hash over identifiers *)

  val is_valid : string -> bool
  (** Check that a string may be converted to an identifier. *)

  val of_string : string -> t
  (** Converts a string into an identifier. May raise [UserError _] if the
      string is not valid. *)

  val to_string : t -> string
  (** Converts a identifier into an string. *)

  val print : t -> Pp.std_ppcmds
  (** Pretty-printer. *)

  module Set : Set.S with type elt = t
  (** Finite sets of identifiers. *)

  module Map : Map.ExtS with type key = t and module Set := Set
  (** Finite maps of identifiers. *)

  module Pred : Predicate.S with type elt = t
  (** Predicates over identifiers. *)

  module List : List.MonoS with type elt = t
  (** Operations over lists of identifiers. *)

  val hcons : t -> t
  (** Hashconsing of identifiers. *)

end

module Name :
sig
  type t = Name of Id.t | Anonymous
  (** A name is either undefined, either an identifier. *)

  val compare : t -> t -> int
  (** Comparison over names. *)

  val equal : t -> t -> bool
  (** Equality over names. *)

  val hash : t -> int
  (** Hash over names. *)

  val hcons : t -> t
  (** Hashconsing over names. *)

end

(** {6 Type aliases} *)

type name = Name.t = Name of Id.t | Anonymous
type variable = Id.t
type module_ident = Id.t

module ModIdset : Set.S with type elt = module_ident
module ModIdmap : Map.ExtS with type key = module_ident and module Set := ModIdset

(** {6 Directory paths = section names paths } *)

module DirPath :
sig
  type t
  (** Type of directory paths. Essentially a list of module identifiers. The
      order is reversed to improve sharing. E.g. A.B.C is ["C";"B";"A"] *)

  val equal : t -> t -> bool
  (** Equality over directory paths. *)

  val compare : t -> t -> int
  (** Comparison over directory paths. *)

  val hash : t -> int
  (** Hash over directory paths. *)

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

  val compare : t -> t -> int
  (** Comparison over labels. *)

  val hash : t -> int
  (** Hash over labels. *)

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
  module Map : Map.ExtS with type key = t and module Set := Set

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

  val hash : t -> int
  (** Hash over unique bound names. *)

  val make : DirPath.t -> Id.t -> t
  (** The first argument is a file name, to prevent conflict between different
      files. *)

  val repr : t -> int * Id.t * DirPath.t
  (** Reverse of [make]. *)

  val to_id : t -> Id.t
  (** Return the identifier contained in the argument. *)

  val to_string : t -> string
  (** Conversion to a string. *)

  val debug_to_string : t -> string
  (** Same as [to_string], but outputs information related to debug. *)

end

module MBIset : Set.S with type elt = MBId.t
module MBImap : Map.ExtS with type key = MBId.t and module Set := MBIset

(** {6 The module part of the kernel name } *)

module ModPath :
sig
  type t =
    | MPfile of DirPath.t
    | MPbound of MBId.t
    | MPdot of t * Label.t

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int

  val is_bound : t -> bool

  val to_string : t -> string

  val initial : t
  (** Name of the toplevel structure ([= MPfile initial_dir]) *)

  val dp : t -> DirPath.t

end

module MPset : Set.S with type elt = ModPath.t
module MPmap : Map.ExtS with type key = ModPath.t and module Set := MPset

(** {6 The absolute names of objects seen by kernel } *)

module KerName :
sig
  type t

  (** Constructor and destructor *)
  val make : ModPath.t -> DirPath.t -> Label.t -> t
  val make2 : ModPath.t -> Label.t -> t
  val repr : t -> ModPath.t * DirPath.t * Label.t

  (** Projections *)
  val modpath : t -> ModPath.t
  val label : t -> Label.t

  (** Display *)
  val to_string : t -> string
  val print : t -> Pp.std_ppcmds

  (** Comparisons *)
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end

module KNset  : CSig.SetS with type elt = KerName.t
module KNpred : Predicate.S with type elt = KerName.t
module KNmap  : Map.ExtS with type key = KerName.t and module Set := KNset


(** {6 Constant Names } *)

module Constant:
sig
  type t

  (** Constructors *)

  val make : KerName.t -> KerName.t -> t
  (** Builds a constant name from a user and a canonical kernel name. *)

  val make1 : KerName.t -> t
  (** Special case of [make] where the user name is canonical.  *)

  val make2 : ModPath.t -> Label.t -> t
  (** Shortcut for [(make1 (KerName.make2 ...))] *)

  val make3 : ModPath.t -> DirPath.t -> Label.t -> t
  (** Shortcut for [(make1 (KerName.make ...))] *)

  (** Projections *)

  val user : t -> KerName.t
  val canonical : t -> KerName.t

  val repr3 : t -> ModPath.t * DirPath.t * Label.t
  (** Shortcut for [KerName.repr (user ...)] *)

  val modpath : t -> ModPath.t
  (** Shortcut for [KerName.modpath (user ...)] *)

  val label : t -> Label.t
  (** Shortcut for [KerName.label (user ...)] *)

  (** Comparisons *)

  module CanOrd : sig
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int
  end

  module UserOrd : sig
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int
  end

  val equal : t -> t -> bool
  (** Default comparison, alias for [CanOrd.equal] *)

  val hash : t -> int
  (** Hashing function *)

  val change_label : t -> Label.t -> t
  (** Builds a new constant name with a different label *)

  (** Displaying *)

  val to_string : t -> string
  val print : t -> Pp.std_ppcmds
  val debug_to_string : t -> string
  val debug_print : t -> Pp.std_ppcmds

end

(** The [*_env] modules consider an order on user part of names
   the others consider an order on canonical part of names*)
module Cpred : Predicate.S with type elt = Constant.t
module Cset : CSig.SetS with type elt = Constant.t
module Cset_env  : CSig.SetS with type elt = Constant.t
module Cmap : Map.ExtS with type key = Constant.t and module Set := Cset
module Cmap_env : Map.ExtS with type key = Constant.t  and module Set := Cset_env

(** {6 Inductive names} *)

module MutInd :
sig
  type t

  (** Constructors *)

  val make : KerName.t -> KerName.t -> t
  (** Builds a mutual inductive name from a user and a canonical kernel name. *)

  val make1 : KerName.t -> t
  (** Special case of [make] where the user name is canonical.  *)

  val make2 : ModPath.t -> Label.t -> t
  (** Shortcut for [(make1 (KerName.make2 ...))] *)

  val make3 : ModPath.t -> DirPath.t -> Label.t -> t
  (** Shortcut for [(make1 (KerName.make ...))] *)

  (** Projections *)

  val user : t -> KerName.t
  val canonical : t -> KerName.t

  val repr3 : t -> ModPath.t * DirPath.t * Label.t
  (** Shortcut for [KerName.repr (user ...)] *)

  val modpath : t -> ModPath.t
  (** Shortcut for [KerName.modpath (user ...)] *)

  val label : t -> Label.t
  (** Shortcut for [KerName.label (user ...)] *)

  (** Comparisons *)

  module CanOrd : sig
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int
  end

  module UserOrd : sig
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int
  end

  val equal : t -> t -> bool
  (** Default comparison, alias for [CanOrd.equal] *)

  val hash : t -> int

  (** Displaying *)

  val to_string : t -> string
  val print : t -> Pp.std_ppcmds
  val debug_to_string : t -> string
  val debug_print : t -> Pp.std_ppcmds

end

module Mindset : CSig.SetS with type elt = MutInd.t
module Mindmap : Map.ExtS with type key = MutInd.t and module Set := Mindset
module Mindmap_env : Map.S with type key = MutInd.t

(** Beware: first inductive has index 0 *)
type inductive = MutInd.t * int

(** Beware: first constructor has index 1 *)
type constructor = inductive * int

module Indmap : Map.S with type key = inductive
module Constrmap : Map.S with type key = constructor
module Indmap_env : Map.S with type key = inductive
module Constrmap_env : Map.S with type key = constructor

val ind_modpath : inductive -> ModPath.t
val constr_modpath : constructor -> ModPath.t

val ith_mutual_inductive : inductive -> int -> inductive
val ith_constructor_of_inductive : inductive -> int -> constructor
val inductive_of_constructor : constructor -> inductive
val index_of_constructor : constructor -> int
val eq_ind : inductive -> inductive -> bool
val eq_user_ind : inductive -> inductive -> bool
val ind_ord : inductive -> inductive -> int
val ind_hash : inductive -> int
val ind_user_ord : inductive -> inductive -> int
val ind_user_hash : inductive -> int
val eq_constructor : constructor -> constructor -> bool
val eq_user_constructor : constructor -> constructor -> bool
val constructor_ord : constructor -> constructor -> int
val constructor_user_ord : constructor -> constructor -> int
val constructor_hash : constructor -> int
val constructor_user_hash : constructor -> int

(** Better to have it here that in Closure, since required in grammar.cma *)
type evaluable_global_reference =
  | EvalVarRef of Id.t
  | EvalConstRef of Constant.t

val eq_egr : evaluable_global_reference ->  evaluable_global_reference
  -> bool

(** {6 Hash-consing } *)

val hcons_con : Constant.t -> Constant.t
val hcons_mind : MutInd.t -> MutInd.t
val hcons_ind : inductive -> inductive
val hcons_construct : constructor -> constructor

(******)

type 'a tableKey =
  | ConstKey of 'a
  | VarKey of Id.t
  | RelKey of Int.t

(** Sets of names *)
type transparent_state = Id.Pred.t * Cpred.t

val empty_transparent_state : transparent_state
val full_transparent_state : transparent_state
val var_full_transparent_state : transparent_state
val cst_full_transparent_state : transparent_state

type inv_rel_key = int (** index in the [rel_context] part of environment
			  starting by the end, {e inverse}
			  of de Bruijn indice *)

val eq_table_key : ('a -> 'a -> bool) -> 'a tableKey -> 'a tableKey -> bool
val eq_constant_key : Constant.t -> Constant.t -> bool

(** equalities on constant and inductive names (for the checker) *)

val eq_con_chk : Constant.t -> Constant.t -> bool
val eq_ind_chk : inductive -> inductive -> bool

(** {6 Deprecated functions. For backward compatibility.} *)

(** {5 Identifiers} *)

type identifier = Id.t
(** @deprecated Alias for [Id.t] *)

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

module Idmap : module type of Id.Map
(** @deprecated Same as [Id.Map]. *)

(** {5 Directory paths} *)

type dir_path = DirPath.t
(** @deprecated Alias for [DirPath.t]. *)

val dir_path_ord : dir_path -> dir_path -> int
(** @deprecated Same as [DirPath.compare]. *)

val dir_path_eq : dir_path -> dir_path -> bool
(** @deprecated Same as [DirPath.equal]. *)

val make_dirpath : module_ident list -> dir_path
(** @deprecated Same as [DirPath.make]. *)

val repr_dirpath : dir_path -> module_ident list
(** @deprecated Same as [DirPath.repr]. *)

val empty_dirpath : dir_path
(** @deprecated Same as [DirPath.empty]. *)

val is_empty_dirpath : dir_path -> bool
(** @deprecated Same as [DirPath.is_empty]. *)

val string_of_dirpath : dir_path -> string
(** @deprecated Same as [DirPath.to_string]. *)

val initial_dir : DirPath.t
(** @deprecated Same as [DirPath.initial]. *)

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

val make_mbid : DirPath.t -> Id.t -> mod_bound_id
(** @deprecated Same as [MBId.make]. *)

val repr_mbid : mod_bound_id -> int * Id.t * DirPath.t
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

(** {5 Module paths} *)

type module_path = ModPath.t =
  | MPfile of DirPath.t
  | MPbound of MBId.t
  | MPdot of module_path * Label.t
(** @deprecated Alias type *)

val mp_ord : module_path -> module_path -> int
(** @deprecated Same as [ModPath.compare]. *)

val mp_eq : module_path -> module_path -> bool
(** @deprecated Same as [ModPath.equal]. *)

val check_bound_mp : module_path -> bool
(** @deprecated Same as [ModPath.is_bound]. *)

val string_of_mp : module_path -> string
(** @deprecated Same as [ModPath.to_string]. *)

val initial_path : module_path
(** @deprecated Same as [ModPath.initial]. *)

(** {5 Kernel names} *)

type kernel_name = KerName.t
(** @deprecated Alias type *)

val make_kn : ModPath.t -> DirPath.t -> Label.t -> kernel_name
(** @deprecated Same as [KerName.make]. *)

val repr_kn : kernel_name -> module_path * DirPath.t * Label.t
(** @deprecated Same as [KerName.repr]. *)

val modpath : kernel_name -> module_path
(** @deprecated Same as [KerName.modpath]. *)

val label : kernel_name -> Label.t
(** @deprecated Same as [KerName.label]. *)

val string_of_kn : kernel_name -> string
(** @deprecated Same as [KerName.to_string]. *)

val pr_kn : kernel_name -> Pp.std_ppcmds
(** @deprecated Same as [KerName.print]. *)

val kn_ord : kernel_name -> kernel_name -> int
(** @deprecated Same as [KerName.compare]. *)

(** {5 Constant names} *)

type constant = Constant.t
(** @deprecated Alias type *)

module Projection : sig
  type t
    
  val make : constant -> bool -> t

  val constant : t -> constant
  val unfolded : t -> bool
  val unfold : t -> t

  val equal : t -> t -> bool
  val hash : t -> int
  val hcons : t -> t
  (** Hashconsing of projections. *)

  val compare : t -> t -> int
    
  val map : (constant -> constant) -> t -> t
end

type projection = Projection.t

val constant_of_kn_equiv : KerName.t -> KerName.t -> constant
(** @deprecated Same as [Constant.make] *)

val constant_of_kn : KerName.t -> constant
(** @deprecated Same as [Constant.make1] *)

val make_con : ModPath.t -> DirPath.t -> Label.t -> constant
(** @deprecated Same as [Constant.make3] *)

val repr_con : constant -> ModPath.t * DirPath.t * Label.t
(** @deprecated Same as [Constant.repr3] *)

val user_con : constant -> KerName.t
(** @deprecated Same as [Constant.user] *)

val canonical_con : constant -> KerName.t
(** @deprecated Same as [Constant.canonical] *)

val con_modpath : constant -> ModPath.t
(** @deprecated Same as [Constant.modpath] *)

val con_label : constant -> Label.t
(** @deprecated Same as [Constant.label] *)

val eq_constant : constant -> constant -> bool
(** @deprecated Same as [Constant.equal] *)

val con_ord : constant -> constant -> int
(** @deprecated Same as [Constant.CanOrd.compare] *)

val con_user_ord : constant -> constant -> int
(** @deprecated Same as [Constant.UserOrd.compare] *)

val con_with_label : constant -> Label.t -> constant
(** @deprecated Same as [Constant.change_label] *)

val string_of_con : constant -> string
(** @deprecated Same as [Constant.to_string] *)

val pr_con : constant -> Pp.std_ppcmds
(** @deprecated Same as [Constant.print] *)

val debug_pr_con : constant -> Pp.std_ppcmds
(** @deprecated Same as [Constant.debug_print] *)

val debug_string_of_con : constant -> string
(** @deprecated Same as [Constant.debug_to_string] *)

(** {5 Mutual Inductive names} *)

type mutual_inductive = MutInd.t
(** @deprecated Alias type *)

val mind_of_kn : KerName.t -> mutual_inductive
(** @deprecated Same as [MutInd.make1] *)

val mind_of_kn_equiv : KerName.t -> KerName.t -> mutual_inductive
(** @deprecated Same as [MutInd.make2] *)

val make_mind : ModPath.t -> DirPath.t -> Label.t -> mutual_inductive
(** @deprecated Same as [MutInd.make3] *)

val user_mind : mutual_inductive -> KerName.t
(** @deprecated Same as [MutInd.user] *)

val canonical_mind : mutual_inductive -> KerName.t
(** @deprecated Same as [MutInd.canonical] *)

val repr_mind : mutual_inductive -> ModPath.t * DirPath.t * Label.t
(** @deprecated Same as [MutInd.repr3] *)

val eq_mind : mutual_inductive -> mutual_inductive -> bool
(** @deprecated Same as [MutInd.equal] *)

val mind_ord : mutual_inductive -> mutual_inductive -> int
(** @deprecated Same as [MutInd.CanOrd.compare] *)

val mind_user_ord : mutual_inductive -> mutual_inductive -> int
(** @deprecated Same as [MutInd.UserOrd.compare] *)

val mind_label : mutual_inductive -> Label.t
(** @deprecated Same as [MutInd.label] *)

val mind_modpath : mutual_inductive -> ModPath.t
(** @deprecated Same as [MutInd.modpath] *)

val string_of_mind : mutual_inductive -> string
(** @deprecated Same as [MutInd.to_string] *)

val pr_mind : mutual_inductive -> Pp.std_ppcmds
(** @deprecated Same as [MutInd.print] *)

val debug_pr_mind : mutual_inductive -> Pp.std_ppcmds
(** @deprecated Same as [MutInd.debug_print] *)

val debug_string_of_mind : mutual_inductive -> string
(** @deprecated Same as [MutInd.debug_to_string] *)
