(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Warning, this file should respect the dependency order established
   in Coq. To see such order issue the comand:

   ```
   bash -c 'for i in kernel intf library engine pretyping interp proofs parsing printing tactics vernac stm toplevel; do echo -e "\n## $i files" && cat ${i}/${i}.mllib; done && echo -e "\n## highparsing files" && cat parsing/highparsing.mllib' > API/link
   ```

   Note however that files in intf/ are located manually now as their
   conceptual linking order in the Coq codebase is incorrect (but it
   works due to these files being implementation-free.

   See below in the file for their concrete position.
*)

(************************************************************************)
(* Modules from config/                                                 *)
(************************************************************************)
module Coq_config :
sig
  val exec_extension : string
end

(************************************************************************)
(* Modules from kernel/                                                 *)
(************************************************************************)
module Names :
sig

  open Util

  module Id :
  sig
    type t
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int
    val is_valid : string -> bool
    val of_bytes : bytes -> t
    val of_string : string -> t
    val of_string_soft : string -> t
    val to_string : t -> string
    val print : t -> Pp.std_ppcmds

    module Set  : Set.S with type elt = t
    module Map  : Map.ExtS with type key = t and module Set := Set
    module Pred : Predicate.S with type elt = t
    module List : List.MonoS with type elt = t
    val hcons : t -> t
  end

  module Name :
  sig
    type t = Anonymous     (** anonymous identifier *)
	   | Name of Id.t  (** non-anonymous identifier *)
    val mk_name : Id.t -> t
    val is_anonymous : t -> bool
    val is_name : t -> bool
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int
    val hcons : t -> t
    val print : t -> Pp.std_ppcmds
  end

  type name = Name.t =
    | Anonymous
    | Name of Id.t
  [@@ocaml.deprecated "alias of API.Name.t"]

  module DirPath :
  sig
    type t
    val empty : t
    val make : Id.t list -> t
    val repr : t -> Id.t list
    val equal : t -> t -> bool
    val to_string : t -> string
  end

  module MBId : sig
    type t
    val equal : t -> t -> bool
    val to_id : t -> Id.t
    val repr : t -> int * Id.t * DirPath.t
    val debug_to_string : t -> string
  end

  module Label :
  sig
    type t
    val make : string -> t
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val of_id : Id.t -> t
    val to_id : t -> Id.t
    val to_string : t -> string
  end

  module ModPath :
  sig
    type t =
      | MPfile of DirPath.t
      | MPbound of MBId.t
      | MPdot of t * Label.t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int
    val initial : t
    val to_string : t -> string
    val debug_to_string : t -> string
  end

  module KerName :
  sig
    type t
    val make : ModPath.t -> DirPath.t -> Label.t -> t
    val make2 : ModPath.t -> Label.t -> t
    val modpath : t -> ModPath.t
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val label : t -> Label.t
    val repr : t -> ModPath.t * DirPath.t * Label.t
    val print : t -> Pp.std_ppcmds
    val to_string : t -> string
  end

  type kernel_name = KerName.t
  [@@ocaml.deprecated "alias of API.Names.KerName.t"]

  module Constant :
  sig
    type t
    val equal : t -> t -> bool
    val make1 : KerName.t -> t
    val make2 : ModPath.t -> Label.t -> t
    val make3 : ModPath.t -> DirPath.t -> Label.t -> t
    val repr3 : t -> ModPath.t * DirPath.t * Label.t
    val canonical : t -> KerName.t
    val user : t -> KerName.t
    val label : t -> Label.t
  end

  module MutInd :
  sig
    type t
    val make1 : KerName.t -> t
    val make2 : ModPath.t -> Label.t -> t
    val equal : t -> t -> bool
    val repr3 : t -> ModPath.t * DirPath.t * Label.t
    val canonical : t -> KerName.t
    val modpath : t -> ModPath.t
    val label : t -> Label.t
    val user : t -> KerName.t
    val print : t -> Pp.std_ppcmds
  end

  module Projection :
  sig
    type t
    val make : Constant.t -> bool -> t
    val map : (Constant.t -> Constant.t) -> t -> t
    val constant : t -> Constant.t
    val equal : t -> t -> bool
  end

  type evaluable_global_reference =
    | EvalVarRef of Id.t
    | EvalConstRef of Constant.t

  type inductive = MutInd.t * int
  val eq_ind : inductive -> inductive -> bool

  type constructor = inductive * int
  val eq_constructor : constructor -> constructor -> bool
  val constructor_hash : constructor -> int

  module MPset : Set.S with type elt = ModPath.t
  module MPmap : Map.ExtS with type key = ModPath.t and module Set := MPset

  module KNset  : CSig.SetS with type elt = KerName.t
  module KNpred : Predicate.S with type elt = KerName.t
  module KNmap  : Map.ExtS with type key = KerName.t and module Set := KNset

  module Cpred : Predicate.S with type elt = Constant.t
  module Cset : CSig.SetS with type elt = Constant.t
  module Cset_env  : CSig.SetS with type elt = Constant.t

  module Cmap : Map.ExtS with type key = Constant.t and module Set := Cset
  module Cmap_env : Map.ExtS with type key = Constant.t and module Set := Cset_env

  module Mindset : CSig.SetS with type elt = MutInd.t
  module Mindmap : Map.ExtS with type key = MutInd.t and module Set := Mindset
  module Mindmap_env : CSig.MapS with type key = MutInd.t

  module Indmap : CSig.MapS with type key = inductive
  module Constrmap : CSig.MapS with type key = constructor
  module Indmap_env : CSig.MapS with type key = inductive
  module Constrmap_env : CSig.MapS with type key = constructor

  type transparent_state = Id.Pred.t * Cpred.t

  val empty_transparent_state : transparent_state
  val full_transparent_state : transparent_state
  val var_full_transparent_state : transparent_state
  val cst_full_transparent_state : transparent_state

  val pr_kn : KerName.t -> Pp.std_ppcmds
  [@@ocaml.deprecated "alias of API.Names.KerName.print"]

  val eq_constant : Constant.t -> Constant.t -> bool
  [@@ocaml.deprecated "alias of API.Names.Constant.equal"]

  type module_path = ModPath.t
  [@@ocaml.deprecated "alias of API.Names.ModPath.t"]

  type variable = Id.t

  type 'a tableKey =
    | ConstKey of 'a
    | VarKey of Id.t
    | RelKey of Int.t

  val id_of_string : string -> Id.t
  [@@ocaml.deprecated "alias of API.Names.Id.of_string"]

  val string_of_id : Id.t -> string
  [@@ocaml.deprecated "alias of API.Names.Id.to_string"]

  type mutual_inductive = MutInd.t
  [@@ocaml.deprecated "alias of API.Names.MutInd.t"]

  val eq_mind : MutInd.t -> MutInd.t -> bool
  [@@ocaml.deprecated "alias of API.Names.MutInd.equal"]

  val repr_con : Constant.t -> ModPath.t * DirPath.t * Label.t
  [@@ocaml.deprecated "alias of API.Names.Constant.repr3"]

  val repr_mind : MutInd.t -> ModPath.t * DirPath.t * Label.t
  [@@ocaml.deprecated "alias of API.Names.MutInd.repr3"]

  val initial_path : ModPath.t
  [@@ocaml.deprecated "alias of API.Names.ModPath.initial"]

  val con_label : Constant.t -> Label.t
  [@@ocaml.deprecated "alias of API.Names.Constant.label"]

  val mind_label : MutInd.t -> Label.t
  [@@ocaml.deprecated "alias of API.Names.MutInd.label"]

  val string_of_mp : ModPath.t -> string
  [@@ocaml.deprecated "alias of API.Names.ModPath.to_string"]

  val mind_of_kn : KerName.t -> MutInd.t
  [@@ocaml.deprecated "alias of API.Names.MutInd.make1"]

  type constant = Constant.t
  [@@ocaml.deprecated "alias of API.Names.Constant.t"]

  val mind_modpath : MutInd.t -> ModPath.t
  [@@ocaml.deprecated "alias of API.Names.MutInd.modpath"]

  val canonical_mind : MutInd.t -> KerName.t
  [@@ocaml.deprecated "alias of API.Names.MutInd.canonical"]

  val user_mind : MutInd.t -> KerName.t
  [@@ocaml.deprecated "alias of API.Names.MutInd.user"]

  val repr_kn : KerName.t -> ModPath.t * DirPath.t * Label.t
  [@@ocaml.deprecated "alias of API.Names.KerName.repr"]

  val constant_of_kn : KerName.t -> Constant.t
  [@@ocaml.deprecated "alias of API.Names.Constant.make1"]

  val user_con : Constant.t -> KerName.t
  [@@ocaml.deprecated "alias of API.Names.Constant.user"]

  val modpath : KerName.t -> ModPath.t
  [@@ocaml.deprecated "alias of API.Names.KerName.modpath"]

  val canonical_con : Constant.t -> KerName.t
  [@@ocaml.deprecated "alias of API.Names.Constant.canonical"]

  val make_kn : ModPath.t -> DirPath.t -> Label.t -> KerName.t
  [@@ocaml.deprecated "alias of API.Names.KerName.make"]

  val make_con : ModPath.t -> DirPath.t -> Label.t -> Constant.t
  [@@ocaml.deprecated "alias of API.Names.Constant.make3"]

  val debug_pr_con : Constant.t -> Pp.std_ppcmds

  val debug_pr_mind : MutInd.t -> Pp.std_ppcmds

  val pr_con : Constant.t -> Pp.std_ppcmds

  val string_of_con : Constant.t -> string

  val string_of_mind : MutInd.t -> string

  val debug_string_of_mind : MutInd.t -> string

  val debug_string_of_con : Constant.t -> string

  type identifier = Id.t
  module Idset  : Set.S with type elt = identifier and type t = Id.Set.t

end

module Univ :
sig

  module Level :
  sig
    type t
    val set : t
    val pr : t -> Pp.std_ppcmds
  end

  type universe_level = Level.t

  module LSet :
  sig
    include CSig.SetS with type elt = universe_level
    val pr : (Level.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds
  end

  module Universe :
  sig
    type t
    val pr : t -> Pp.std_ppcmds
  end

  type universe = Universe.t

  module Instance :
  sig
    type t
    val empty : t
    val of_array : Level.t array -> t
    val to_array : t -> Level.t array
    val pr : (Level.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds
  end

  type 'a puniverses = 'a * Instance.t

  val out_punivs : 'a puniverses -> 'a

  type constraint_type = Lt | Le | Eq

  type univ_constraint = universe_level * constraint_type * universe_level

  module Constraint : sig
    include Set.S with type elt = univ_constraint
  end

  type 'a constrained = 'a * Constraint.t

  module UContext :
  sig
    type t
    val empty : t
  end

  type universe_context = UContext.t

  module AUContext :
  sig
    type t
    val empty : t
  end

  type abstract_universe_context = AUContext.t

  module CumulativityInfo :
  sig
    type t
  end

  type cumulativity_info = CumulativityInfo.t

  module ACumulativityInfo :
  sig
    type t
  end
  type abstract_cumulativity_info = ACumulativityInfo.t

  module ContextSet :
  sig
    type t
    val empty : t
    val of_context : UContext.t -> t
    val to_context : t -> UContext.t
  end

  type 'a in_universe_context_set = 'a * ContextSet.t
  type 'a in_universe_context = 'a * UContext.t

  type universe_context_set = ContextSet.t

  type universe_set = LSet.t

  type 'a constraint_function = 'a -> 'a -> Constraint.t -> Constraint.t

  module LMap :
  sig
    include CMap.ExtS with type key = universe_level and module Set := LSet

    val union : 'a t -> 'a t -> 'a t
    val diff : 'a t -> 'a t -> 'a t
    val subst_union : 'a option t -> 'a option t -> 'a option t
    val pr : ('a -> Pp.std_ppcmds) -> 'a t -> Pp.std_ppcmds
  end

  type 'a universe_map = 'a LMap.t
  type universe_subst = universe universe_map
  type universe_level_subst = universe_level universe_map

  val enforce_leq : Universe.t constraint_function
  val pr_uni : Universe.t -> Pp.std_ppcmds
  val pr_universe_context : (Level.t -> Pp.std_ppcmds) -> UContext.t -> Pp.std_ppcmds
  val pr_universe_context_set : (Level.t -> Pp.std_ppcmds) -> ContextSet.t -> Pp.std_ppcmds
  val pr_universe_subst : universe_subst -> Pp.std_ppcmds
  val pr_universe_level_subst : universe_level_subst -> Pp.std_ppcmds
  val pr_constraints : (Level.t -> Pp.std_ppcmds) -> Constraint.t -> Pp.std_ppcmds
end

module UGraph :
sig
  type t
  val pr_universes : (Univ.Level.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds
end

module Esubst :
sig
  type 'a subs
  val subs_id : int -> 'a subs
end

module Sorts :
sig
  type contents = Pos | Null
  type t =
         | Prop of contents
         | Type of Univ.Universe.t
  val is_prop : t -> bool
  val hash : t -> int

  type family = InProp | InSet | InType
  val family : t -> family
end

module Evar :
sig
  (** Unique identifier of some {i evar} *)
  type t

  (** Recover the underlying integer. *)
  val repr : t -> int

  val equal : t -> t -> bool

  (** a set of unique identifiers of some {i evars} *)
  module Set : Set.S with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set

end

module Constr :
sig
  open Names

  type t

  type constr = t
  type types = t

  type cast_kind =
                 | VMcast
                 | NATIVEcast
                 | DEFAULTcast
                 | REVERTcast

  type metavariable = int

  type existential_key = Evar.t
  type 'constr pexistential = existential_key * 'constr array

  type 'a puniverses = 'a Univ.puniverses
  type pconstant = Constant.t puniverses
  type pinductive = inductive puniverses
  type pconstructor = constructor puniverses

  type ('constr, 'types) prec_declaration =
    Name.t array * 'types array * 'constr array

  type ('constr, 'types) pfixpoint =
    (int array * int) * ('constr, 'types) prec_declaration

  type ('constr, 'types) pcofixpoint =
    int * ('constr, 'types) prec_declaration

  type case_style =
      LetStyle | IfStyle | LetPatternStyle | MatchStyle
    | RegularStyle (** infer printing form from number of constructor *)

  type case_printing =
    { ind_tags : bool list; (** tell whether letin or lambda in the arity of the inductive type *)
      cstr_tags : bool list array; (** tell whether letin or lambda in the signature of each constructor *)
      style     : case_style }

  type case_info =
    { ci_ind        : inductive;      (* inductive type to which belongs the value that is being matched *)
      ci_npar       : int;            (* number of parameters of the above inductive type *)
      ci_cstr_ndecls : int array;     (* For each constructor, the corresponding integer determines
                                         the number of values that can be bound in a match-construct.
                                         NOTE: parameters of the inductive type are therefore excluded from the count *)
      ci_cstr_nargs : int array;      (* for each constructor, the corresponding integers determines
                                         the number of values that can be applied to the constructor,
                                         in addition to the parameters of the related inductive type
                                         NOTE: "lets" are therefore excluded from the count
                                         NOTE: parameters of the inductive type are also excluded from the count *)
      ci_pp_info    : case_printing   (* not interpreted by the kernel *)
    }

  type ('constr, 'types, 'sort, 'univs) kind_of_term =
     | Rel       of int
     | Var       of Id.t
     | Meta      of metavariable
     | Evar      of 'constr pexistential
     | Sort      of 'sort
     | Cast      of 'constr * cast_kind * 'types
     | Prod      of Name.t * 'types * 'types
     | Lambda    of Name.t * 'types * 'constr
     | LetIn     of Name.t * 'constr * 'types * 'constr
     | App       of 'constr * 'constr array
     | Const     of (Constant.t * 'univs)
     | Ind       of (inductive * 'univs)
     | Construct of (constructor * 'univs)
     | Case      of case_info * 'constr * 'constr * 'constr array
     | Fix       of ('constr, 'types) pfixpoint
     | CoFix     of ('constr, 'types) pcofixpoint
     | Proj      of Projection.t * 'constr

  val equal : t -> t -> bool
  val eq_constr_nounivs : t -> t -> bool
  val compare : t -> t -> int

  val hash : t -> int

  val mkRel : int -> t
  val mkVar : Id.t -> t
  val mkMeta : metavariable -> t
  type existential = existential_key * constr array
  val mkEvar : existential -> t
  val mkSort : Sorts.t -> t
  val mkProp : t
  val mkSet  : t
  val mkType : Univ.Universe.t -> t
  val mkCast : t * cast_kind * t -> t
  val mkProd : Name.t * types * types -> types
  val mkLambda : Name.t * types * t -> t
  val mkLetIn : Name.t * t * types * t -> t
  val mkApp : t * t array -> t
  val map_puniverses : ('a -> 'b) -> 'a puniverses -> 'b puniverses

  val mkConst : Constant.t -> t
  val mkConstU : pconstant -> t

  val mkProj : (Projection.t * t) -> t

  val mkInd : inductive -> t
  val mkIndU : pinductive -> t

  val mkConstruct : constructor -> t
  val mkConstructU : pconstructor -> t
  val mkConstructUi : pinductive * int -> t

  val mkCase : case_info * t * t * t array -> t

end

module Context :
sig
  module Rel :
  sig
    module Declaration :
    sig
      (* local declaration *)
      (* local declaration *)
      type ('constr, 'types) pt =
        | LocalAssum of Names.Name.t * 'types            (** name, type *)
        | LocalDef of Names.Name.t * 'constr * 'types    (** name, value, type *)

      type t = (Constr.constr, Constr.types) pt

      (** Return the name bound by a given declaration. *)
      val get_name : ('c, 't) pt -> Names.Name.t

      (** Return the type of the name bound by a given declaration. *)
      val get_type : ('c, 't) pt -> 't

      (** Set the name that is bound by a given declaration. *)
      val set_name : Names.Name.t -> ('c, 't) pt -> ('c, 't) pt

      (** Set the type of the bound variable in a given declaration. *)
      val set_type : 't -> ('c, 't) pt -> ('c, 't) pt

      (** Return [true] iff a given declaration is a local assumption. *)
      val is_local_assum : ('c, 't) pt -> bool

      (** Return [true] iff a given declaration is a local definition. *)
      val is_local_def : ('c, 't) pt -> bool

      (** Check whether the two given declarations are equal. *)
      val equal : ('c -> 'c -> bool) -> ('c, 'c) pt -> ('c, 'c) pt -> bool

      (** Map the name bound by a given declaration. *)
      val map_name : (Names.Name.t -> Names.Name.t) -> ('c, 't) pt -> ('c, 't) pt

      (** For local assumptions, this function returns the original local assumptions.
        For local definitions, this function maps the value in the local definition. *)
      val map_value : ('c -> 'c) -> ('c, 't) pt -> ('c, 't) pt

      (** Map the type of the name bound by a given declaration. *)
      val map_type : ('t -> 't) -> ('c, 't) pt -> ('c, 't) pt

      (** Map all terms in a given declaration. *)
      val map_constr : ('c -> 'c) -> ('c, 'c) pt -> ('c, 'c) pt

      (** Perform a given action on all terms in a given declaration. *)
      val iter_constr : ('c -> unit) -> ('c, 'c) pt -> unit

      (** Reduce all terms in a given declaration to a single value. *)
      val fold_constr : ('c -> 'a -> 'a) -> ('c, 'c) pt -> 'a -> 'a
    end

    (** Rel-context is represented as a list of declarations.
        Inner-most declarations are at the beginning of the list.
        Outer-most declarations are at the end of the list. *)
    type ('constr, 'types) pt = ('constr, 'types) Declaration.pt list
    type t = Declaration.t list

    (** empty rel-context *)
    val empty : ('c, 't) pt

    (** Return a new rel-context enriched by with a given inner-most declaration. *)
    val add : ('c, 't) Declaration.pt -> ('c, 't) pt -> ('c, 't) pt

    (** Return the number of {e local declarations} in a given context. *)
    val length : ('c, 't) pt -> int

    (** Check whether given two rel-contexts are equal. *)
    val equal : ('c -> 'c -> bool) -> ('c, 'c) pt -> ('c, 'c) pt -> bool

    (** Return the number of {e local assumptions} in a given rel-context. *)
    val nhyps : ('c, 't) pt -> int

    (** Return a declaration designated by a given de Bruijn index.
      @raise Not_found if the designated de Bruijn index outside the range. *)
    val lookup : int -> ('c, 't) pt -> ('c, 't) Declaration.pt

    (** Map all terms in a given rel-context. *)
    val map : ('c -> 'c) -> ('c, 'c) pt -> ('c, 'c) pt

    (** Perform a given action on every declaration in a given rel-context. *)
    val iter : ('c -> unit) -> ('c, 'c) pt -> unit

    (** Reduce all terms in a given rel-context to a single value.
      Innermost declarations are processed first. *)
    val fold_inside : ('a -> ('c, 't) Declaration.pt -> 'a) -> init:'a -> ('c, 't) pt -> 'a

    (** Reduce all terms in a given rel-context to a single value.
      Outermost declarations are processed first. *)
    val fold_outside : (('c, 't) Declaration.pt -> 'a -> 'a) -> ('c, 't) pt -> init:'a -> 'a

    (** [extended_vect n Γ] does the same, returning instead an array. *)
    val to_extended_vect : (int -> 'r) -> int -> ('c, 't) pt -> 'r array
  end
  module Named :
  sig
    module Declaration :
    sig
      (** local declaration *)
      type ('constr, 'types) pt =
        | LocalAssum of Names.Id.t * 'types             (** identifier, type *)
        | LocalDef of Names.Id.t * 'constr * 'types     (** identifier, value, type *)

      type t = (Constr.constr, Constr.types) pt

      (** Return the identifier bound by a given declaration. *)
      val get_id : ('c, 't) pt -> Names.Id.t

      (** Return the type of the name bound by a given declaration. *)
      val get_type : ('c, 't) pt -> 't

      (** Set the identifier that is bound by a given declaration. *)
      val set_id : Names.Id.t -> ('c, 't) pt -> ('c, 't) pt

      (** Set the type of the bound variable in a given declaration. *)
      val set_type : 't -> ('c, 't) pt -> ('c, 't) pt

      (** Return [true] iff a given declaration is a local assumption. *)
      val is_local_assum : ('c, 't) pt -> bool

      (** Return [true] iff a given declaration is a local definition. *)
      val is_local_def : ('c, 't) pt -> bool

      (** Check whether any term in a given declaration satisfies a given predicate. *)
      val exists : ('c -> bool) -> ('c, 'c) pt -> bool

      (** Check whether all terms in a given declaration satisfy a given predicate. *)
      val for_all : ('c -> bool) -> ('c, 'c) pt -> bool

      (** Check whether the two given declarations are equal. *)
      val equal : ('c -> 'c -> bool) -> ('c, 'c) pt -> ('c, 'c) pt -> bool

      (** Map the identifier bound by a given declaration. *)
      val map_id : (Names.Id.t -> Names.Id.t) -> ('c, 't) pt -> ('c, 't) pt

      (** For local assumptions, this function returns the original local assumptions.
        For local definitions, this function maps the value in the local definition. *)
      val map_value : ('c -> 'c) -> ('c, 't) pt -> ('c, 't) pt

      (** Map the type of the name bound by a given declaration. *)
      val map_type : ('t -> 't) -> ('c, 't) pt -> ('c, 't) pt

      (** Map all terms in a given declaration. *)
      val map_constr : ('c -> 'c) -> ('c, 'c) pt -> ('c, 'c) pt

      (** Perform a given action on all terms in a given declaration. *)
      val iter_constr : ('c -> unit) -> ('c, 'c) pt -> unit

      (** Reduce all terms in a given declaration to a single value. *)
      val fold_constr : ('c -> 'a -> 'a) -> ('c, 'c) pt -> 'a -> 'a

      val to_rel_decl : ('c, 't) pt -> ('c, 't) Rel.Declaration.pt
    end
    (** Named-context is represented as a list of declarations.
      Inner-most declarations are at the beginning of the list.
      Outer-most declarations are at the end of the list. *)
    type ('constr, 'types) pt = ('constr, 'types) Declaration.pt list
    type t = Declaration.t list

    (** empty named-context *)
    val empty : ('c, 't) pt

    (** Return a new named-context enriched by with a given inner-most declaration. *)
    val add : ('c, 't) Declaration.pt -> ('c, 't) pt -> ('c, 't) pt

    (** Return the number of {e local declarations} in a given named-context. *)
    val length : ('c, 't) pt -> int

    (** Return a declaration designated by an identifier of the variable bound in that declaration.
      @raise Not_found if the designated identifier is not bound in a given named-context. *)
    val lookup : Names.Id.t -> ('c, 't) pt -> ('c, 't) Declaration.pt

    (** Check whether given two named-contexts are equal. *)
    val equal : ('c -> 'c -> bool) -> ('c, 'c) pt -> ('c, 'c) pt -> bool

    (** Map all terms in a given named-context. *)
    val map : ('c -> 'c) -> ('c, 'c) pt -> ('c, 'c) pt

    (** Perform a given action on every declaration in a given named-context. *)
    val iter : ('c -> unit) -> ('c, 'c) pt -> unit

    (** Reduce all terms in a given named-context to a single value.
      Innermost declarations are processed first. *)
    val fold_inside : ('a -> ('c, 't) Declaration.pt -> 'a) -> init:'a -> ('c, 't) pt -> 'a

    (** Reduce all terms in a given named-context to a single value.
      Outermost declarations are processed first. *)
    val fold_outside : (('c, 't) Declaration.pt -> 'a -> 'a) -> ('c, 't) pt -> init:'a -> 'a

    (** Return the set of all identifiers bound in a given named-context. *)
    val to_vars : ('c, 't) pt -> Names.Id.Set.t

    (** [to_instance Ω] builds an instance [args] such
      that [Ω ⊢ args:Ω] where [Ω] is a named-context and with the local
      definitions of [Ω] skipped. Example: for [id1:T,id2:=c,id3:U], it
      gives [Var id1, Var id3]. All [idj] are supposed distinct. *)
    val to_instance : (Names.Id.t -> 'r) -> ('c, 't) pt -> 'r list
  end
end

module Vars :
sig
  type substl = Constr.t list

  val substl : substl -> Constr.t -> Constr.t

  val subst1 : Constr.t -> Constr.t -> Constr.t

  val lift : int -> Constr.t -> Constr.t

  val closed0 : Constr.t -> bool

  val closedn : int -> Constr.t -> bool

  val replace_vars : (Names.Id.t * Constr.t) list -> Constr.t -> Constr.t

  val noccurn : int -> Constr.t -> bool
  val subst_var : Names.Id.t -> Constr.t -> Constr.t
  val subst_vars : Names.Id.t list -> Constr.t -> Constr.t
  val substnl : substl -> int -> Constr.t -> Constr.t
end

module Term :
sig

  type sorts_family = Sorts.family = InProp | InSet | InType

  type contents = Sorts.contents = Pos | Null

  type sorts = Sorts.t =
    | Prop of contents
    | Type of Univ.Universe.t
  [@@ocaml.deprecated "alias of API.Sorts.t"]

  type constr = Constr.t
  type types = Constr.t

  type metavariable = int

  type ('constr, 'types) prec_declaration = Names.Name.t array * 'types array * 'constr array

  type 'constr pexistential = 'constr Constr.pexistential
  type cast_kind = Constr.cast_kind =
                 | VMcast
                 | NATIVEcast
                 | DEFAULTcast
                 | REVERTcast

  type 'a puniverses = 'a Univ.puniverses
  type pconstant = Names.Constant.t puniverses
  type pinductive = Names.inductive puniverses
  type pconstructor = Names.constructor puniverses
  type case_style =
                  | LetStyle
                  | IfStyle
                  | LetPatternStyle
                  | MatchStyle
                  | RegularStyle

  type case_printing =
    { ind_tags  : bool list;
      cstr_tags : bool list array;
      style     : case_style
    }

  type case_info = Constr.case_info

  type ('constr, 'types) pfixpoint =
    (int array * int) * ('constr, 'types) prec_declaration

  type ('constr, 'types) pcofixpoint =
    int * ('constr, 'types) prec_declaration

  type ('constr, 'types, 'sort, 'univs) kind_of_term = ('constr, 'types, 'sort, 'univs) Constr.kind_of_term =
     | Rel       of int
     | Var       of Names.Id.t
     | Meta      of Constr.metavariable
     | Evar      of 'constr pexistential
     | Sort      of 'sort
     | Cast      of 'constr * cast_kind * 'types
     | Prod      of Names.Name.t * 'types * 'types
     | Lambda    of Names.Name.t * 'types * 'constr
     | LetIn     of Names.Name.t * 'constr * 'types * 'constr
     | App       of 'constr * 'constr array
     | Const     of (Names.Constant.t * 'univs)
     | Ind       of (Names.inductive * 'univs)
     | Construct of (Names.constructor * 'univs)
     | Case      of case_info * 'constr * 'constr * 'constr array
     | Fix       of ('constr, 'types) pfixpoint
     | CoFix     of ('constr, 'types) pcofixpoint
     | Proj      of Names.Projection.t * 'constr
  type existential = Constr.existential_key * constr array
  type rec_declaration = Names.Name.t array * constr array * constr array
  type fixpoint = (int array * int) * rec_declaration
  type cofixpoint = int * rec_declaration
  val kind_of_term : constr -> (constr, types, Sorts.t, Univ.Instance.t) kind_of_term
  val applistc : constr -> constr list -> constr

  val applist : constr * constr list -> constr
  [@@ocaml.deprecated "(sort of an) alias of API.Term.applistc"]

  val mkArrow : types -> types -> constr
  val mkRel : int -> constr
  val mkVar : Names.Id.t -> constr

  val mkMeta : Constr.metavariable -> constr

  val mkEvar : existential -> constr
  val mkSort : Sorts.t -> types
  val mkProp : types
  val mkSet  : types
  val mkType : Univ.Universe.t -> types
  val mkCast : constr * cast_kind * constr -> constr
  val mkProd : Names.Name.t * types * types -> types
  val mkLambda : Names.Name.t * types * constr -> constr
  val mkLetIn : Names.Name.t * constr * types * constr -> constr
  val mkApp : constr * constr array -> constr
  val mkConst : Names.Constant.t -> constr
  val mkProj : Names.Projection.t * constr -> constr
  val mkInd : Names.inductive -> constr
  val mkConstruct : Names.constructor -> constr
  val mkConstructU : Names.constructor puniverses -> constr
  val mkConstructUi : (pinductive * int) -> constr
  val mkCase : case_info * constr * constr * constr array -> constr
  val mkFix : fixpoint -> constr
  val mkCoFix : cofixpoint -> constr
  val mkNamedLambda : Names.Id.t -> types -> constr -> constr
  val mkNamedLetIn : Names.Id.t -> constr -> types -> constr -> constr
  val mkNamedProd : Names.Id.t -> types -> types -> types

  val decompose_app : constr -> constr * constr list
  val decompose_prod : constr -> (Names.Name.t*constr) list * constr
  val decompose_prod_n : int -> constr -> (Names.Name.t * constr) list * constr
  val decompose_prod_assum : types -> Context.Rel.t * types
  val decompose_lam : constr -> (Names.Name.t * constr) list * constr
  val decompose_lam_n : int -> constr -> (Names.Name.t * constr) list * constr
  val decompose_prod_n_assum : int -> types -> Context.Rel.t * types

  val compose_prod : (Names.Name.t * constr) list -> constr -> constr
  val compose_lam : (Names.Name.t * constr) list -> constr -> constr

  val destSort : constr -> Sorts.t
  val destVar : constr -> Names.Id.t
  val destApp : constr -> constr * constr array
  val destProd : types -> Names.Name.t * types * types
  val destLetIn : constr -> Names.Name.t * constr * types * constr
  val destEvar : constr -> existential
  val destRel : constr -> int
  val destConst : constr -> Names.Constant.t puniverses
  val destCast : constr -> constr * cast_kind * constr
  val destLambda : constr -> Names.Name.t * types * constr

  val isRel : constr -> bool
  val isVar  : constr -> bool
  val isEvar : constr -> bool
  val isLetIn : constr -> bool
  val isLambda : constr -> bool
  val isConst : constr -> bool
  val isEvar_or_Meta : constr -> bool
  val isCast : constr -> bool
  val isMeta : constr -> bool
  val isApp : constr -> bool

  val fold_constr : ('a -> constr -> 'a) -> 'a -> constr -> 'a

  val eq_constr : constr -> constr -> bool

  val hash_constr : constr -> int
  val it_mkLambda_or_LetIn : constr -> Context.Rel.t -> constr
  val it_mkProd_or_LetIn : types -> Context.Rel.t -> types
  val prod_applist : constr -> constr list -> constr
  exception DestKO
  val map_constr : (constr -> constr) -> constr -> constr

  val mkIndU : pinductive -> constr
  val mkConstU : pconstant -> constr
  val map_constr_with_binders :
    ('a -> 'a) -> ('a -> constr -> constr) -> 'a -> constr -> constr
  val iter_constr : (constr -> unit) -> constr -> unit

  (* Quotients away universes: really needed?
   * Can't we just call eq_c_univs_infer and discard the inferred csts?
   *)
  val eq_constr_nounivs : constr -> constr -> bool

  type ('constr, 'types) kind_of_type =
    | SortType   of Sorts.t
    | CastType   of 'types * 'types
    | ProdType   of Names.Name.t * 'types * 'types
    | LetInType  of Names.Name.t * 'constr * 'types * 'types
    | AtomicType of 'constr * 'constr array

  val kind_of_type : types -> (constr, types) kind_of_type

  val is_prop_sort : Sorts.t -> bool
  [@@ocaml.deprecated "alias of API.Sorts.is_prop"]

  type existential_key = Constr.existential_key

  val family_of_sort : Sorts.t -> Sorts.family

  val compare : constr -> constr -> int

  val constr_ord : constr -> constr -> int
  [@@ocaml.deprecated "alias of API.Term.compare"]

  val destInd : constr -> Names.inductive puniverses
  val univ_of_sort : Sorts.t -> Univ.Universe.t

  val strip_lam : constr -> constr
  val strip_prod_assum : types -> types

  val decompose_lam_assum : constr -> Context.Rel.t * constr
  val destFix : constr -> fixpoint

  val compare_constr : (constr -> constr -> bool) -> constr -> constr -> bool
end

module Mod_subst :
sig

  type delta_resolver
  type substitution
  type 'a substituted

  val force_constr : Constr.t substituted -> Constr.t

  val empty_delta_resolver : delta_resolver
  val constant_of_delta_kn : delta_resolver -> Names.KerName.t -> Names.Constant.t
  val mind_of_delta_kn : delta_resolver -> Names.KerName.t -> Names.MutInd.t
  val subst_kn : substitution -> Names.KerName.t -> Names.KerName.t
  val subst_evaluable_reference :
    substitution -> Names.evaluable_global_reference -> Names.evaluable_global_reference
  val subst_mps : substitution -> Constr.t -> Constr.t
  val subst_constant : substitution -> Names.Constant.t -> Names.Constant.t
  val subst_ind : substitution -> Names.inductive -> Names.inductive
  val debug_pr_subst : substitution -> Pp.std_ppcmds
  val debug_pr_delta : delta_resolver -> Pp.std_ppcmds
end

module Opaqueproof :
sig
  type opaquetab
  type opaque
  val empty_opaquetab : opaquetab
  val force_proof : opaquetab -> opaque -> Constr.t
end

module Cbytecodes :
sig
  type tag = int
  type reloc_table = (tag * int) array
end

module Cemitcodes :
sig
  type to_patch_substituted
end


module Decl_kinds :
sig
  type polymorphic = bool
  type cumulative_inductive_flag = bool
  type recursivity_kind =
    | Finite
    | CoFinite
    | BiFinite

  type locality =
    | Discharge
    | Local
    | Global

  type definition_object_kind =
    | Definition
    | Coercion
    | SubClass
    | CanonicalStructure
    | Example
    | Fixpoint
    | CoFixpoint
    | Scheme
    | StructureComponent
    | IdentityCoercion
    | Instance
    | Method
  type theorem_kind =
    | Theorem
    | Lemma
    | Fact
    | Remark
    | Property
    | Proposition
    | Corollary
  type goal_object_kind =
    | DefinitionBody of definition_object_kind
    | Proof of theorem_kind
  type goal_kind = locality * polymorphic * goal_object_kind
  type assumption_object_kind =
    | Definitional
    | Logical
    | Conjectural
  type logical_kind =
    | IsAssumption of assumption_object_kind
    | IsDefinition of definition_object_kind
    | IsProof of theorem_kind
  type binding_kind =
    | Explicit
    | Implicit
  type private_flag = bool
  type definition_kind = locality * polymorphic * definition_object_kind
end


module Retroknowledge :
sig
  type action
  type nat_field =
    | NatType
    | NatPlus
    | NatTimes
  type n_field =
    | NPositive
    | NType
    | NTwice
    | NTwicePlusOne
    | NPhi
    | NPhiInv
    | NPlus
    | NTimes
  type int31_field =
    | Int31Bits
    | Int31Type
    | Int31Constructor
    | Int31Twice
    | Int31TwicePlusOne
    | Int31Phi
    | Int31PhiInv
    | Int31Plus
    | Int31PlusC
    | Int31PlusCarryC
    | Int31Minus
    | Int31MinusC
    | Int31MinusCarryC
    | Int31Times
    | Int31TimesC
    | Int31Div21
    | Int31Div
    | Int31Diveucl
    | Int31AddMulDiv
    | Int31Compare
    | Int31Head0
    | Int31Tail0
    | Int31Lor
    | Int31Land
    | Int31Lxor
  type field =
    | KInt31 of string * int31_field
end

module Conv_oracle :
sig
  type level
end

module Declarations :
sig

  open Names

  type recarg =
    | Norec
    | Mrec of Names.inductive
    | Imbr of Names.inductive
  type wf_paths = recarg Rtree.t
  type inline = int option
  type constant_def =
                    | Undef of inline
                    | Def of Constr.t Mod_subst.substituted
                    | OpaqueDef of Opaqueproof.opaque
  type template_arity = {
    template_param_levels : Univ.Level.t option list;
    template_level : Univ.Universe.t;
  }

  type ('a, 'b) declaration_arity =
    | RegularArity of 'a
    | TemplateArity of 'b

  type constant_type = (Constr.types, Context.Rel.t * template_arity) declaration_arity

  type constant_universes =
    | Monomorphic_const of Univ.universe_context
    | Polymorphic_const of Univ.abstract_universe_context

  type projection_body = {
        proj_ind : Names.MutInd.t;
        proj_npars : int;
        proj_arg : int;
        proj_type : Constr.types;
        proj_eta  : Constr.t * Constr.types;
        proj_body : Constr.t;
      }

  type typing_flags = {
    check_guarded : bool;
    check_universes : bool;
  }

  type constant_body = {
        const_hyps : Context.Named.t;
        const_body : constant_def;
        const_type : constant_type;
        const_body_code : Cemitcodes.to_patch_substituted option;
        const_universes : constant_universes;
        const_proj : projection_body option;
        const_inline_code : bool;
        const_typing_flags : typing_flags;
      }

  type regular_inductive_arity = {
    mind_user_arity : Constr.types;
    mind_sort : Sorts.t;
  }

  type inductive_arity = (regular_inductive_arity, template_arity) declaration_arity

  type one_inductive_body = {
        mind_typename : Names.Id.t;
        mind_arity_ctxt : Context.Rel.t;
        mind_arity : inductive_arity;
        mind_consnames : Names.Id.t array;
        mind_user_lc : Constr.types array;
        mind_nrealargs : int;
        mind_nrealdecls : int;
        mind_kelim : Sorts.family list;
        mind_nf_lc : Constr.types array;
        mind_consnrealargs : int array;
        mind_consnrealdecls : int array;
        mind_recargs : wf_paths;
        mind_nb_constant : int;
        mind_nb_args : int;
        mind_reloc_tbl :  Cbytecodes.reloc_table;
      }

  type ('ty,'a) functorize =
                           | NoFunctor of 'a
                           | MoreFunctor of Names.MBId.t * 'ty * ('ty,'a) functorize

  type with_declaration =
                        | WithMod of Names.Id.t list * Names.ModPath.t
                        | WithDef of Names.Id.t list * Constr.t Univ.in_universe_context

  type module_alg_expr =
                       | MEident of Names.ModPath.t
                       | MEapply of module_alg_expr * Names.ModPath.t
                       | MEwith of module_alg_expr * with_declaration

  type abstract_inductive_universes =
  | Monomorphic_ind of Univ.universe_context
  | Polymorphic_ind of Univ.abstract_universe_context
  | Cumulative_ind of Univ.abstract_cumulativity_info

  type record_body = (Id.t * Constant.t array * projection_body array) option
  
  type mutual_inductive_body = {
        mind_packets : one_inductive_body array;
        mind_record : record_body option;
        mind_finite : Decl_kinds.recursivity_kind;
        mind_ntypes : int;
        mind_hyps : Context.Named.t;
        mind_nparams : int;
        mind_nparams_rec : int;
        mind_params_ctxt : Context.Rel.t;
        mind_universes : abstract_inductive_universes;
        mind_private : bool option;
        mind_typing_flags : typing_flags;
      }
   and module_expression = (module_type_body,module_alg_expr) functorize
   and module_implementation =
                             | Abstract
                               | Algebraic of module_expression
                             | Struct of module_signature
                             | FullStruct
   and module_body =
                       { mod_mp : Names.ModPath.t;
                         mod_expr : module_implementation;
                         mod_type : module_signature;
                         mod_type_alg : module_expression option;
                         mod_constraints : Univ.ContextSet.t;
                         mod_delta : Mod_subst.delta_resolver;
                         mod_retroknowledge : Retroknowledge.action list
                       }
   and module_signature = (module_type_body,structure_body) functorize
   and module_type_body = module_body
   and structure_body = (Names.Label.t * structure_field_body) list
   and structure_field_body =
                            | SFBconst of constant_body
                            | SFBmind of mutual_inductive_body
                            | SFBmodule of module_body
                            | SFBmodtype of module_type_body
end

module Declareops :
sig
  val constant_has_body : Declarations.constant_body -> bool
  val is_opaque : Declarations.constant_body -> bool
  val eq_recarg : Declarations.recarg -> Declarations.recarg -> bool
end

module Entries :
sig

  open Names
  open Constr

  type local_entry =
    | LocalDefEntry   of constr
    | LocalAssumEntry of constr

  type inductive_universes =
    | Monomorphic_ind_entry of Univ.universe_context
    | Polymorphic_ind_entry of Univ.universe_context
    | Cumulative_ind_entry of Univ.cumulativity_info

  type one_inductive_entry = {
    mind_entry_typename : Id.t;
    mind_entry_arity : constr;
    mind_entry_template : bool; (* Use template polymorphism *)
    mind_entry_consnames : Id.t list;
    mind_entry_lc : constr list }

  type mutual_inductive_entry = {
    mind_entry_record : (Names.Id.t option) option;
    (** Some (Some id): primitive record with id the binder name of the record
        in projections.
        Some None: non-primitive record *)
    mind_entry_finite : Decl_kinds.recursivity_kind;
    mind_entry_params : (Id.t * local_entry) list;
    mind_entry_inds : one_inductive_entry list;
    mind_entry_universes : inductive_universes;
    (* universe constraints and the constraints for subtyping of
       inductive types in the block. *)
    mind_entry_private : bool option;
  }

  type inline = int option
  type 'a proof_output = Constr.t Univ.in_universe_context_set * 'a
  type 'a const_entry_body = 'a proof_output Future.computation
  type 'a definition_entry =
                               { const_entry_body   : 'a const_entry_body;
                                 (* List of section variables *)
                                 const_entry_secctx : Context.Named.t option;
                                 (* State id on which the completion of type checking is reported *)
                                 const_entry_feedback    : Stateid.t option;
                                 const_entry_type        : Constr.types option;
                                 const_entry_polymorphic : bool;
                                 const_entry_universes   : Univ.UContext.t;
                                 const_entry_opaque      : bool;
                                 const_entry_inline_code : bool }
  type parameter_entry = Context.Named.t option * bool * Constr.types Univ.in_universe_context * inline

  type projection_entry = {
    proj_entry_ind : MutInd.t;
    proj_entry_arg : int }

  type 'a constant_entry =
                         | DefinitionEntry of 'a definition_entry
                         | ParameterEntry of parameter_entry
                         | ProjectionEntry of projection_entry
end

module Environ :
sig
  type env
  type named_context_val

  type ('constr, 'types) punsafe_judgment =
    {
      uj_val : 'constr;
      uj_type : 'types
    }
  type 'types punsafe_type_judgment = {
    utj_val : 'types;
    utj_type : Sorts.t }

  type unsafe_type_judgment = Term.types punsafe_type_judgment
  val empty_env : env
  val lookup_mind : Names.MutInd.t -> env -> Declarations.mutual_inductive_body
  val push_rel : Context.Rel.Declaration.t -> env -> env
  val push_rel_context : Context.Rel.t -> env -> env
  val push_rec_types : Term.rec_declaration -> env -> env
  val lookup_rel : int -> env -> Context.Rel.Declaration.t
  val lookup_named : Names.Id.t -> env -> Context.Named.Declaration.t
  val lookup_named_val : Names.Id.t -> named_context_val -> Context.Named.Declaration.t
  val lookup_constant : Names.Constant.t -> env -> Declarations.constant_body
  val opaque_tables : env -> Opaqueproof.opaquetab
  val is_projection : Names.Constant.t -> env -> bool
  val lookup_projection : Names.Projection.t -> env -> Declarations.projection_body
  val named_context_of_val : named_context_val -> Context.Named.t
  val push_named : Context.Named.Declaration.t -> env -> env
  val named_context : env -> Context.Named.t
  val named_context_val : env -> named_context_val
  val push_named_context_val : Context.Named.Declaration.t -> named_context_val -> named_context_val
  val reset_with_named_context : named_context_val -> env -> env
  val rel_context : env -> Context.Rel.t
  val constant_value_in : env -> Names.Constant.t Univ.puniverses -> Constr.t
  val named_type : Names.Id.t -> env -> Constr.types
  val constant_opt_value_in : env -> Names.Constant.t Univ.puniverses -> Constr.t option
  val fold_named_context_reverse :
    ('a -> Context.Named.Declaration.t -> 'a) -> init:'a -> env -> 'a
  val evaluable_named  : Names.Id.t -> env -> bool
  val push_context_set : ?strict:bool -> Univ.ContextSet.t -> env -> env
end

module CClosure :
sig

  type table_key = Names.Constant.t Univ.puniverses Names.tableKey

  type fconstr

  type fterm =
    | FRel of int
    | FAtom of Constr.t (** Metas and Sorts *)
    | FCast of fconstr * Constr.cast_kind * fconstr
    | FFlex of table_key
    | FInd of Names.inductive Univ.puniverses
    | FConstruct of Names.constructor Univ.puniverses
    | FApp of fconstr * fconstr array
    | FProj of Names.Projection.t * fconstr
    | FFix of Term.fixpoint * fconstr Esubst.subs
    | FCoFix of Term.cofixpoint * fconstr Esubst.subs
    | FCaseT of Term.case_info * Constr.t * fconstr * Constr.t array * fconstr Esubst.subs (* predicate and branches are closures *)
    | FLambda of int * (Names.Name.t * Constr.t) list * Constr.t * fconstr Esubst.subs
    | FProd of Names.Name.t * fconstr * fconstr
    | FLetIn of Names.Name.t * fconstr * fconstr * Constr.t * fconstr Esubst.subs
    | FEvar of Term.existential * fconstr Esubst.subs
    | FLIFT of int * fconstr
    | FCLOS of Constr.t * fconstr Esubst.subs
    | FLOCKED

  module RedFlags : sig
    type reds
    type red_kind
    val mkflags : red_kind list -> reds
    val fBETA : red_kind
    val fCOFIX : red_kind
    val fCONST : Names.Constant.t -> red_kind
    val fFIX : red_kind
    val fMATCH : red_kind
    val fZETA : red_kind
    val red_add_transparent : reds -> Names.transparent_state -> reds
  end

  type 'a infos_cache
  type 'a infos = {
    i_flags : RedFlags.reds;
    i_cache : 'a infos_cache }

  type clos_infos = fconstr infos

  val mk_clos : fconstr Esubst.subs -> Constr.t -> fconstr
  val mk_atom : Constr.t -> fconstr
  val mk_clos_deep :
    (fconstr Esubst.subs -> Constr.t -> fconstr) ->
    fconstr Esubst.subs -> Constr.t -> fconstr
  val mk_red : fterm -> fconstr
  val all : RedFlags.reds
  val beta : RedFlags.reds
  val betaiota : RedFlags.reds
  val betaiotazeta : RedFlags.reds

  val create_clos_infos : ?evars:(Term.existential -> Constr.t option) -> RedFlags.reds -> Environ.env -> clos_infos

  val whd_val : clos_infos -> fconstr -> Constr.t

  val inject : Constr.t -> fconstr

  val kl : clos_infos -> fconstr -> Constr.t
  val term_of_fconstr : fconstr -> Constr.t
end

module Reduction :
sig
  exception NotConvertible
  type conv_pb =
               | CONV
               | CUMUL

  val whd_all : Environ.env -> Constr.t -> Constr.t

  val whd_betaiotazeta : Environ.env -> Constr.t -> Constr.t

  val is_arity : Environ.env -> Term.types -> bool

  val dest_prod : Environ.env -> Term.types -> Context.Rel.t * Term.types

  type 'a extended_conversion_function =
    ?l2r:bool -> ?reds:Names.transparent_state -> Environ.env ->
    ?evars:((Term.existential->Constr.t option) * UGraph.t) ->
    'a -> 'a -> unit
  val conv : Constr.t extended_conversion_function
end

module Type_errors :
sig

  open Names
  open Term
  open Environ

  type 'constr pguard_error =
    (** Fixpoints *)
    | NotEnoughAbstractionInFixBody
    | RecursionNotOnInductiveType of 'constr
    | RecursionOnIllegalTerm of int * (env * 'constr) * int list * int list
    | NotEnoughArgumentsForFixCall of int
    (** CoFixpoints *)
    | CodomainNotInductiveType of 'constr
    | NestedRecursiveOccurrences
    | UnguardedRecursiveCall of 'constr
    | RecCallInTypeOfAbstraction of 'constr
    | RecCallInNonRecArgOfConstructor of 'constr
    | RecCallInTypeOfDef of 'constr
    | RecCallInCaseFun of 'constr
    | RecCallInCaseArg of 'constr
    | RecCallInCasePred of 'constr
    | NotGuardedForm of 'constr
    | ReturnPredicateNotCoInductive of 'constr

  type arity_error =
    | NonInformativeToInformative
    | StrongEliminationOnNonSmallType
    | WrongArity

  type ('constr, 'types) ptype_error =
    | UnboundRel of int
    | UnboundVar of variable
    | NotAType of ('constr, 'types) punsafe_judgment
    | BadAssumption of ('constr, 'types) punsafe_judgment
    | ReferenceVariables of identifier * 'constr
    | ElimArity of pinductive * sorts_family list * 'constr * ('constr, 'types) punsafe_judgment
                   * (sorts_family * sorts_family * arity_error) option
    | CaseNotInductive of ('constr, 'types) punsafe_judgment
    | WrongCaseInfo of pinductive * case_info
    | NumberBranches of ('constr, 'types) punsafe_judgment * int
    | IllFormedBranch of 'constr * pconstructor * 'constr * 'constr
    | Generalization of (Name.t * 'types) * ('constr, 'types) punsafe_judgment
    | ActualType of ('constr, 'types) punsafe_judgment * 'types
    | CantApplyBadType of
        (int * 'constr * 'constr) * ('constr, 'types) punsafe_judgment * ('constr, 'types) punsafe_judgment array
    | CantApplyNonFunctional of ('constr, 'types) punsafe_judgment * ('constr, 'types) punsafe_judgment array
    | IllFormedRecBody of 'constr pguard_error * Name.t array * int * env * ('constr, 'types) punsafe_judgment array
    | IllTypedRecBody of
        int * Name.t array * ('constr, 'types) punsafe_judgment array * 'types array
    | UnsatisfiedConstraints of Univ.Constraint.t

  type type_error = (constr, types) ptype_error

  exception TypeError of Environ.env * type_error
end

module Modops :
sig
  val destr_nofunctor : ('ty,'a) Declarations.functorize -> 'a
  val add_structure :
    Names.ModPath.t -> Declarations.structure_body -> Mod_subst.delta_resolver ->
    Environ.env -> Environ.env
  val add_module_type : Names.ModPath.t -> Declarations.module_type_body -> Environ.env -> Environ.env
end

module Inductive :
sig
  type mind_specif = Declarations.mutual_inductive_body * Declarations.one_inductive_body
  val type_of_inductive : Environ.env -> mind_specif Univ.puniverses -> Term.types
  exception SingletonInductiveBecomesProp of Names.Id.t
  val lookup_mind_specif : Environ.env -> Names.inductive -> mind_specif
  val find_inductive  : Environ.env -> Term.types -> Term.pinductive * Constr.t list
end

module Typeops :
sig
  val infer_type : Environ.env -> Term.types -> Environ.unsafe_type_judgment
  val type_of_constant_type : Environ.env -> Declarations.constant_type -> Term.types
  val type_of_constant_in : Environ.env -> Term.pconstant -> Term.types
end

module Mod_typing :
sig
  type 'alg translation =
    Declarations.module_signature * 'alg * Mod_subst.delta_resolver * Univ.ContextSet.t
  val translate_mse :
    Environ.env -> Names.ModPath.t option -> Entries.inline -> Declarations.module_alg_expr ->
    Declarations.module_alg_expr translation
end

module Safe_typing :
sig
  type private_constants
  val mk_pure_proof : Constr.t -> private_constants Entries.proof_output
end

(************************************************************************)
(* End of modules from kernel/                                          *)
(************************************************************************)
