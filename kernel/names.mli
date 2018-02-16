(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file defines a lot of different notions of names used pervasively in
    the kernel as well as in other places. The essential datatypes exported by
    this API are:

    - Id.t is the type of identifiers, that is morally a subset of strings which
      only contains Unicode characters of the Letter kind (and a few more).
    - Name.t is an ad-hoc variant of Id.t option allowing to handle optionally
      named objects.
    - DirPath.t represents generic paths as sequences of identifiers.
    - Label.t is an equivalent of Id.t made distinct for semantical purposes.
    - ModPath.t are module paths.
    - KerName.t are absolute names of objects in Coq.
*)

open Util

(** {6 Identifiers } *)

(** Representation and operations on identifiers. *)
module Id :
sig
  type t
  (** Values of this type represent (Coq) identifiers. *)

  val equal : t -> t -> bool
  (** Equality over identifiers. *)

  val compare : t -> t -> int
  (** Comparison over identifiers. *)

  val hash : t -> int
  (** Hash over identifiers. *)

  val is_valid : string -> bool
  (** Check that a string may be converted to an identifier. *)

  val of_bytes : bytes -> t
  val of_string : string -> t
  (** Converts a string into an identifier.
      @raise UserError if the string is invalid as an identifier. *)

  val of_string_soft : string -> t
  (** Same as {!of_string} except that any string made of supported UTF-8 characters is accepted.
      @raise UserError if the string is invalid as an UTF-8 string. *)

  val to_string : t -> string
  (** Converts a identifier into an string. *)

  val print : t -> Pp.t
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

(** Representation and operations on identifiers that are allowed to be anonymous
    (i.e. "_" in concrete syntax). *)
module Name :
sig
  type t = Anonymous     (** anonymous identifier *)
	 | Name of Id.t  (** non-anonymous identifier *)

  val mk_name : Id.t -> t
  (** constructor *)

  val is_anonymous : t -> bool
  (** Return [true] iff a given name is [Anonymous]. *)

  val is_name : t -> bool
  (** Return [true] iff a given name is [Name _]. *)

  val compare : t -> t -> int
  (** Comparison over names. *)

  val equal : t -> t -> bool
  (** Equality over names. *)

  val hash : t -> int
  (** Hash over names. *)

  val hcons : t -> t
  (** Hashconsing over names. *)

  val print : t -> Pp.t
  (** Pretty-printer (print "_" for [Anonymous]. *)

end

(** {6 Type aliases} *)

type name = Name.t = Anonymous | Name of Id.t
[@@ocaml.deprecated "Use Name.t"]

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

  val print : t -> Pp.t
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

  val print : t -> Pp.t
  (** Pretty-printer. *)

  module Set : Set.S with type elt = t
  module Map : Map.ExtS with type key = t and module Set := Set

  val hcons : t -> t

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

  val debug_to_string : t -> string
  (** Same as [to_string], but outputs information related to debug. *)

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

  val debug_to_string : t -> string
  (** Same as [to_string], but outputs information related to debug. *)

  val print : t -> Pp.t

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

  module SyntacticOrd : sig
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
  val print : t -> Pp.t
  val debug_to_string : t -> string
  val debug_print : t -> Pp.t

end

(** The [*_env] modules consider an order on user part of names
   the others consider an order on canonical part of names*)
module Cpred : Predicate.S with type elt = Constant.t
module Cset : CSig.SetS with type elt = Constant.t
module Cset_env  : CSig.SetS with type elt = Constant.t

module Cmap : Map.ExtS with type key = Constant.t and module Set := Cset
(** A map whose keys are constants (values of the {!Constant.t} type).
    Keys are ordered wrt. "canonical form" of the constant. *)

module Cmap_env : Map.ExtS with type key = Constant.t and module Set := Cset_env
(** A map whose keys are constants (values of the {!Constant.t} type).
    Keys are ordered wrt. "user form" of the constant. *)

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

  module SyntacticOrd : sig
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int
  end

  val equal : t -> t -> bool
  (** Default comparison, alias for [CanOrd.equal] *)

  val hash : t -> int

  (** Displaying *)

  val to_string : t -> string
  val print : t -> Pp.t
  val debug_to_string : t -> string
  val debug_print : t -> Pp.t

end

module Mindset : CSig.SetS with type elt = MutInd.t
module Mindmap : Map.ExtS with type key = MutInd.t and module Set := Mindset
module Mindmap_env : CSig.MapS with type key = MutInd.t

(** Designation of a (particular) inductive type. *)
type inductive = MutInd.t      (* the name of the inductive type *)
               * int           (* the position of this inductive type
                                  within the block of mutually-recursive inductive types.
                                  BEWARE: indexing starts from 0. *)

(** Designation of a (particular) constructor of a (particular) inductive type. *)
type constructor = inductive   (* designates the inductive type *)
                 * int         (* the index of the constructor
                                  BEWARE: indexing starts from 1. *)

module Indmap : CSig.MapS with type key = inductive
module Constrmap : CSig.MapS with type key = constructor
module Indmap_env : CSig.MapS with type key = inductive
module Constrmap_env : CSig.MapS with type key = constructor

val ind_modpath : inductive -> ModPath.t
val constr_modpath : constructor -> ModPath.t

val ith_mutual_inductive : inductive -> int -> inductive
val ith_constructor_of_inductive : inductive -> int -> constructor
val inductive_of_constructor : constructor -> inductive
val index_of_constructor : constructor -> int
val eq_ind : inductive -> inductive -> bool
val eq_user_ind : inductive -> inductive -> bool
val eq_syntactic_ind : inductive -> inductive -> bool
val ind_ord : inductive -> inductive -> int
val ind_hash : inductive -> int
val ind_user_ord : inductive -> inductive -> int
val ind_user_hash : inductive -> int
val ind_syntactic_ord : inductive -> inductive -> int
val ind_syntactic_hash : inductive -> int
val eq_constructor : constructor -> constructor -> bool
val eq_user_constructor : constructor -> constructor -> bool
val eq_syntactic_constructor : constructor -> constructor -> bool
val constructor_ord : constructor -> constructor -> int
val constructor_hash : constructor -> int
val constructor_user_ord : constructor -> constructor -> int
val constructor_user_hash : constructor -> int
val constructor_syntactic_ord : constructor -> constructor -> int
val constructor_syntactic_hash : constructor -> int

(** {6 Global reference is a kernel side type for all references together } *)
type global_reference =
  | VarRef of variable           (** A reference to the section-context. *)
  | ConstRef of Constant.t       (** A reference to the environment. *)
  | IndRef of inductive          (** A reference to an inductive type. *)
  | ConstructRef of constructor  (** A reference to a constructor of an inductive type. *)

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
[@@ocaml.deprecated "Alias for [Id.t]"]

val string_of_id : Id.t -> string
[@@ocaml.deprecated "Same as [Id.to_string]."]

val id_of_string : string -> Id.t
[@@ocaml.deprecated "Same as [Id.of_string]."]

val id_ord : Id.t -> Id.t -> int
[@@ocaml.deprecated "Same as [Id.compare]."]

val id_eq : Id.t -> Id.t -> bool
[@@ocaml.deprecated "Same as [Id.equal]."]

module Idset  : Set.S with type elt = Id.t and type t = Id.Set.t
[@@ocaml.deprecated "Same as [Id.Set]."]

module Idpred : Predicate.S with type elt = Id.t and type t = Id.Pred.t
[@@ocaml.deprecated "Same as [Id.Pred]."]

module Idmap : module type of Id.Map
[@@ocaml.deprecated "Same as [Id.Map]."]

(** {5 Directory paths} *)

type dir_path = DirPath.t
[@@ocaml.deprecated "Alias for [DirPath.t]."]

val dir_path_ord : DirPath.t -> DirPath.t -> int
[@@ocaml.deprecated "Same as [DirPath.compare]."]

val dir_path_eq : DirPath.t -> DirPath.t -> bool
[@@ocaml.deprecated "Same as [DirPath.equal]."]

val make_dirpath : module_ident list -> DirPath.t
[@@ocaml.deprecated "Same as [DirPath.make]."]

val repr_dirpath : DirPath.t -> module_ident list
[@@ocaml.deprecated "Same as [DirPath.repr]."]

val empty_dirpath : DirPath.t
[@@ocaml.deprecated "Same as [DirPath.empty]."]

val is_empty_dirpath : DirPath.t -> bool
[@@ocaml.deprecated "Same as [DirPath.is_empty]."]

val string_of_dirpath : DirPath.t -> string
[@@ocaml.deprecated "Same as [DirPath.to_string]."]

val initial_dir : DirPath.t
[@@ocaml.deprecated "Same as [DirPath.initial]."]

(** {5 Labels} *)

type label = Label.t
[@@ocaml.deprecated "Same as [Label.t]."]
(** Alias type *)

val mk_label : string -> Label.t
[@@ocaml.deprecated "Same as [Label.make]."]

val string_of_label : Label.t -> string
[@@ocaml.deprecated "Same as [Label.to_string]."]

val pr_label : Label.t -> Pp.t
[@@ocaml.deprecated "Same as [Label.print]."]

val label_of_id : Id.t -> Label.t
[@@ocaml.deprecated "Same as [Label.of_id]."]

val id_of_label : Label.t -> Id.t
[@@ocaml.deprecated "Same as [Label.to_id]."]

val eq_label : Label.t -> Label.t -> bool
[@@ocaml.deprecated "Same as [Label.equal]."]

(** {5 Unique bound module names} *)

type mod_bound_id = MBId.t
(** Alias type. *)

val mod_bound_id_ord : mod_bound_id -> mod_bound_id -> int
[@@ocaml.deprecated "Same as [MBId.compare]."]

val mod_bound_id_eq : mod_bound_id -> mod_bound_id -> bool
[@@ocaml.deprecated "Same as [MBId.equal]."]

val make_mbid : DirPath.t -> Id.t -> mod_bound_id
[@@ocaml.deprecated "Same as [MBId.make]."]

val repr_mbid : mod_bound_id -> int * Id.t * DirPath.t
[@@ocaml.deprecated "Same as [MBId.repr]."]

val id_of_mbid : mod_bound_id -> Id.t
[@@ocaml.deprecated "Same as [MBId.to_id]."]

val string_of_mbid : mod_bound_id -> string
[@@ocaml.deprecated "Same as [MBId.to_string]."]

val debug_string_of_mbid : mod_bound_id -> string
[@@ocaml.deprecated "Same as [MBId.debug_to_string]."]

(** {5 Names} *)

val name_eq : Name.t -> Name.t -> bool
[@@ocaml.deprecated "Same as [Name.equal]."]

(** {5 Module paths} *)

type module_path = ModPath.t =
  | MPfile of DirPath.t
  | MPbound of MBId.t
  | MPdot of ModPath.t * Label.t
[@@ocaml.deprecated "Alias type"]

val mp_ord : ModPath.t -> ModPath.t -> int
[@@ocaml.deprecated "Same as [ModPath.compare]."]

val mp_eq : ModPath.t -> ModPath.t -> bool
[@@ocaml.deprecated "Same as [ModPath.equal]."]

val check_bound_mp : ModPath.t -> bool
[@@ocaml.deprecated "Same as [ModPath.is_bound]."]

val string_of_mp : ModPath.t -> string
[@@ocaml.deprecated "Same as [ModPath.to_string]."]

val initial_path : ModPath.t
[@@ocaml.deprecated "Same as [ModPath.initial]."]

(** {5 Kernel names} *)

type kernel_name = KerName.t
[@@ocaml.deprecated "Alias type"]

val make_kn : ModPath.t -> DirPath.t -> Label.t -> KerName.t
[@@ocaml.deprecated "Same as [KerName.make]."]

val repr_kn : KerName.t -> ModPath.t * DirPath.t * Label.t
[@@ocaml.deprecated "Same as [KerName.repr]."]

val modpath : KerName.t -> ModPath.t
[@@ocaml.deprecated "Same as [KerName.modpath]."]

val label : KerName.t -> Label.t
[@@ocaml.deprecated "Same as [KerName.label]."]

val string_of_kn : KerName.t -> string
[@@ocaml.deprecated "Same as [KerName.to_string]."]

val pr_kn : KerName.t -> Pp.t
[@@ocaml.deprecated "Same as [KerName.print]."]

val kn_ord : KerName.t -> KerName.t -> int
[@@ocaml.deprecated "Same as [KerName.compare]."]

(** {5 Constant names} *)

type constant = Constant.t
[@@ocaml.deprecated "Alias type"]

module Projection : sig
  type t

  val make : Constant.t -> bool -> t

  module SyntacticOrd : sig
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int
  end

  val constant : t -> Constant.t
  val unfolded : t -> bool
  val unfold : t -> t

  val equal : t -> t -> bool
  val hash : t -> int
  val hcons : t -> t
  (** Hashconsing of projections. *)

  val compare : t -> t -> int

  val map : (Constant.t -> Constant.t) -> t -> t

  val to_string : t -> string
  val print : t -> Pp.t

end

type projection = Projection.t

val constant_of_kn_equiv : KerName.t -> KerName.t -> Constant.t
[@@ocaml.deprecated "Same as [Constant.make]"]

val constant_of_kn : KerName.t -> Constant.t
[@@ocaml.deprecated "Same as [Constant.make1]"]

val make_con : ModPath.t -> DirPath.t -> Label.t -> Constant.t
[@@ocaml.deprecated "Same as [Constant.make3]"]

val repr_con : Constant.t -> ModPath.t * DirPath.t * Label.t
[@@ocaml.deprecated "Same as [Constant.repr3]"]

val user_con : Constant.t -> KerName.t
[@@ocaml.deprecated "Same as [Constant.user]"]

val canonical_con : Constant.t -> KerName.t
[@@ocaml.deprecated "Same as [Constant.canonical]"]

val con_modpath : Constant.t -> ModPath.t
[@@ocaml.deprecated "Same as [Constant.modpath]"]

val con_label : Constant.t -> Label.t
[@@ocaml.deprecated "Same as [Constant.label]"]

val eq_constant : Constant.t -> Constant.t -> bool
[@@ocaml.deprecated "Same as [Constant.equal]"]

val con_ord : Constant.t -> Constant.t -> int
[@@ocaml.deprecated "Same as [Constant.CanOrd.compare]"]

val con_user_ord : Constant.t -> Constant.t -> int
[@@ocaml.deprecated "Same as [Constant.UserOrd.compare]"]

val con_with_label : Constant.t -> Label.t -> Constant.t
[@@ocaml.deprecated "Same as [Constant.change_label]"]

val string_of_con : Constant.t -> string
[@@ocaml.deprecated "Same as [Constant.to_string]"]

val pr_con : Constant.t -> Pp.t
[@@ocaml.deprecated "Same as [Constant.print]"]

val debug_pr_con : Constant.t -> Pp.t
[@@ocaml.deprecated "Same as [Constant.debug_print]"]

val debug_string_of_con : Constant.t -> string
[@@ocaml.deprecated "Same as [Constant.debug_to_string]"]

(** {5 Mutual Inductive names} *)

type mutual_inductive = MutInd.t
[@@ocaml.deprecated "Alias type"]

val mind_of_kn : KerName.t -> MutInd.t
[@@ocaml.deprecated "Same as [MutInd.make1]"]

val mind_of_kn_equiv : KerName.t -> KerName.t -> MutInd.t
[@@ocaml.deprecated "Same as [MutInd.make]"]

val make_mind : ModPath.t -> DirPath.t -> Label.t -> MutInd.t
[@@ocaml.deprecated "Same as [MutInd.make3]"]

val user_mind : MutInd.t -> KerName.t
[@@ocaml.deprecated "Same as [MutInd.user]"]

val canonical_mind : MutInd.t -> KerName.t
[@@ocaml.deprecated "Same as [MutInd.canonical]"]

val repr_mind : MutInd.t -> ModPath.t * DirPath.t * Label.t
[@@ocaml.deprecated "Same as [MutInd.repr3]"]

val eq_mind : MutInd.t -> MutInd.t -> bool
[@@ocaml.deprecated "Same as [MutInd.equal]"]

val mind_ord : MutInd.t -> MutInd.t -> int
[@@ocaml.deprecated "Same as [MutInd.CanOrd.compare]"]

val mind_user_ord : MutInd.t -> MutInd.t -> int
[@@ocaml.deprecated "Same as [MutInd.UserOrd.compare]"]

val mind_label : MutInd.t -> Label.t
[@@ocaml.deprecated "Same as [MutInd.label]"]

val mind_modpath : MutInd.t -> ModPath.t
[@@ocaml.deprecated "Same as [MutInd.modpath]"]

val string_of_mind : MutInd.t -> string
[@@ocaml.deprecated "Same as [MutInd.to_string]"]

val pr_mind : MutInd.t -> Pp.t
[@@ocaml.deprecated "Same as [MutInd.print]"]

val debug_pr_mind : MutInd.t -> Pp.t
[@@ocaml.deprecated "Same as [MutInd.debug_print]"]

val debug_string_of_mind : MutInd.t -> string
[@@ocaml.deprecated "Same as [MutInd.debug_to_string]"]
