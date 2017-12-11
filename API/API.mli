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
   bash -c 'for i in kernel intf library engine pretyping interp proofs parsing printing tactics vernac stm toplevel; do echo -e "\n## $i files" && cat ${i}/${i}.mllib; done > API/link
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
    val print : t -> Pp.t

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
    val print : t -> Pp.t
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
    val print : t -> Pp.t
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
    val print : t -> Pp.t
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
    val print : t -> Pp.t
  end

  module Projection :
  sig
    type t
    val make : Constant.t -> bool -> t
    val map : (Constant.t -> Constant.t) -> t -> t
    val constant : t -> Constant.t
    val equal : t -> t -> bool
    val unfolded : t -> bool
    val unfold : t -> t
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

  val pr_kn : KerName.t -> Pp.t
  [@@ocaml.deprecated "alias of API.Names.KerName.print"]

  val eq_constant : Constant.t -> Constant.t -> bool
  [@@ocaml.deprecated "alias of API.Names.Constant.equal"]

  type module_path = ModPath.t =
    | MPfile of DirPath.t
    | MPbound of MBId.t
    | MPdot of ModPath.t * Label.t
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

  val debug_pr_con : Constant.t -> Pp.t
  [@@ocaml.deprecated "Alias of Names"]

  val debug_pr_mind : MutInd.t -> Pp.t
  [@@ocaml.deprecated "Alias of Names"]

  val pr_con : Constant.t -> Pp.t
  [@@ocaml.deprecated "Alias of Names"]

  val string_of_con : Constant.t -> string
  [@@ocaml.deprecated "Alias of Names"]

  val string_of_mind : MutInd.t -> string
  [@@ocaml.deprecated "Alias of Names"]

  val debug_string_of_mind : MutInd.t -> string
  [@@ocaml.deprecated "Alias of Names"]

  val debug_string_of_con : Constant.t -> string
  [@@ocaml.deprecated "Alias of Names"]

  type identifier = Id.t
  [@@ocaml.deprecated "Alias of Names"]

  module Idset  : Set.S with type elt = Id.t and type t = Id.Set.t
  [@@ocaml.deprecated "Alias of Id.Set.t"]

end

module Univ :
sig

  module Level :
  sig
    type t
    val set : t
    val pr : t -> Pp.t
  end

  type universe_level = Level.t
  [@@ocaml.deprecated "Deprecated form, see univ.ml"]

  module LSet :
  sig
    include CSig.SetS with type elt = Level.t
    val pr : (Level.t -> Pp.t) -> t -> Pp.t
  end

  module Universe :
  sig
    type t
    val pr : t -> Pp.t
  end

  type universe = Universe.t
  [@@ocaml.deprecated "Deprecated form, see univ.ml"]

  module Instance :
  sig
    type t
    val empty : t
    val of_array : Level.t array -> t
    val to_array : t -> Level.t array
    val pr : (Level.t -> Pp.t) -> t -> Pp.t
  end

  type 'a puniverses = 'a * Instance.t

  val out_punivs : 'a puniverses -> 'a

  type constraint_type = Lt | Le | Eq

  type univ_constraint = Level.t * constraint_type * Level.t

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
  [@@ocaml.deprecated "Deprecated form, see univ.ml"]

  module AUContext :
  sig
    type t
    val empty : t
  end

  type abstract_universe_context = AUContext.t
  [@@ocaml.deprecated "Deprecated form, see univ.ml"]

  module CumulativityInfo :
  sig
    type t
  end

  type cumulativity_info = CumulativityInfo.t
  [@@ocaml.deprecated "Deprecated form, see univ.ml"]

  module ACumulativityInfo :
  sig
    type t
  end
  type abstract_cumulativity_info = ACumulativityInfo.t
  [@@ocaml.deprecated "Deprecated form, see univ.ml"]

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
  [@@ocaml.deprecated "Deprecated form, see univ.ml"]

  type universe_set = LSet.t
  [@@ocaml.deprecated "Deprecated form, see univ.ml"]

  type 'a constraint_function = 'a -> 'a -> Constraint.t -> Constraint.t

  module LMap :
  sig
    include CMap.ExtS with type key = Level.t and module Set := LSet

    val union : 'a t -> 'a t -> 'a t
    val diff : 'a t -> 'a t -> 'a t
    val subst_union : 'a option t -> 'a option t -> 'a option t
    val pr : ('a -> Pp.t) -> 'a t -> Pp.t
  end

  type 'a universe_map = 'a LMap.t
  type universe_subst = Universe.t universe_map
  type universe_level_subst = Level.t universe_map

  val enforce_leq : Universe.t constraint_function
  val pr_uni : Universe.t -> Pp.t
  val pr_universe_context : (Level.t -> Pp.t) -> UContext.t -> Pp.t
  val pr_universe_context_set : (Level.t -> Pp.t) -> ContextSet.t -> Pp.t
  val pr_universe_subst : universe_subst -> Pp.t
  val pr_universe_level_subst : universe_level_subst -> Pp.t
  val pr_constraints : (Level.t -> Pp.t) -> Constraint.t -> Pp.t
end

module UGraph :
sig
  type t
  val pr_universes : (Univ.Level.t -> Pp.t) -> t -> Pp.t
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
  val univ_of_sort : t -> Univ.Universe.t
end

module Evar :
sig
  (** Unique identifier of some {i evar} *)
  type t

  (** Recover the underlying integer. *)
  val repr : t -> int

  val equal : t -> t -> bool

  val print : t -> Pp.t

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
  [@@ocaml.deprecated "use Evar.t"]

  type 'constr pexistential = Evar.t * 'constr array

  type 'a puniverses = 'a Univ.puniverses
  [@@ocaml.deprecated "use Univ.puniverses"]

  type pconstant = Constant.t Univ.puniverses
  type pinductive = inductive Univ.puniverses
  type pconstructor = constructor Univ.puniverses

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

  val kind : constr -> (constr, types, Sorts.t, Univ.Instance.t) kind_of_term
  val of_kind : (constr, types, Sorts.t, Univ.Instance.t) kind_of_term -> constr

  val map_with_binders :
    ('a -> 'a) -> ('a -> constr -> constr) -> 'a -> constr -> constr
  val map : (constr -> constr) -> constr -> constr

  val fold : ('a -> constr -> 'a) -> 'a -> constr -> 'a
  val iter : (constr -> unit) -> constr -> unit
  val compare_head : (constr -> constr -> bool) -> constr -> constr -> bool

  val equal : t -> t -> bool
  val eq_constr_nounivs : t -> t -> bool
  val compare : t -> t -> int

  val hash : t -> int

  val mkRel : int -> t
  val mkVar : Id.t -> t
  val mkMeta : metavariable -> t
  type existential = Evar.t * constr array
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
  val map_puniverses : ('a -> 'b) -> 'a Univ.puniverses -> 'b Univ.puniverses

  type rec_declaration = Name.t array * types array * constr array
  type fixpoint = (int array * int) * rec_declaration
  val mkFix : fixpoint -> constr

  val mkConst : Constant.t -> t
  val mkConstU : pconstant -> t

  val mkProj : (Projection.t * t) -> t

  val mkInd : inductive -> t
  val mkIndU : pinductive -> t

  val mkConstruct : constructor -> t
  val mkConstructU : pconstructor -> t
  val mkConstructUi : pinductive * int -> t

  val mkCase : case_info * t * t * t array -> t

  (** {6 Simple case analysis} *)
  val isRel  : constr -> bool
  val isRelN : int -> constr -> bool
  val isVar  : constr -> bool
  val isVarId : Id.t -> constr -> bool
  val isInd  : constr -> bool
  val isEvar : constr -> bool
  val isMeta : constr -> bool
  val isEvar_or_Meta : constr -> bool
  val isSort : constr -> bool
  val isCast : constr -> bool
  val isApp : constr -> bool
  val isLambda : constr -> bool
  val isLetIn : constr -> bool
  val isProd : constr -> bool
  val isConst : constr -> bool
  val isConstruct : constr -> bool
  val isFix : constr -> bool
  val isCoFix : constr -> bool
  val isCase : constr -> bool
  val isProj : constr -> bool

  val is_Prop : constr -> bool
  val is_Set  : constr -> bool
  val isprop : constr -> bool
  val is_Type : constr -> bool
  val iskind : constr -> bool
  val is_small : Sorts.t -> bool

  (** {6 Term destructors } *)
  (** Destructor operations are partial functions and
      @raise DestKO if the term has not the expected form. *)

  exception DestKO

  (** Destructs a de Bruijn index *)
  val destRel : constr -> int

  (** Destructs an existential variable *)
  val destMeta : constr -> metavariable

  (** Destructs a variable *)
  val destVar : constr -> Id.t

  (** Destructs a sort. [is_Prop] recognizes the sort {% \textsf{%}Prop{% }%}, whether
      [isprop] recognizes both {% \textsf{%}Prop{% }%} and {% \textsf{%}Set{% }%}. *)
  val destSort : constr -> Sorts.t

  (** Destructs a casted term *)
  val destCast : constr -> constr * cast_kind * constr

  (** Destructs the product {% $ %}(x:t_1)t_2{% $ %} *)
  val destProd : types -> Name.t * types * types

  (** Destructs the abstraction {% $ %}[x:t_1]t_2{% $ %} *)
  val destLambda : constr -> Name.t * types * constr

  (** Destructs the let {% $ %}[x:=b:t_1]t_2{% $ %} *)
  val destLetIn : constr -> Name.t * constr * types * constr

  (** Destructs an application *)
  val destApp : constr -> constr * constr array

  (** Decompose any term as an applicative term; the list of args can be empty *)
  val decompose_app : constr -> constr * constr list

  (** Same as [decompose_app], but returns an array. *)
  val decompose_appvect : constr -> constr * constr array

  (** Destructs a constant *)
  val destConst : constr -> Constant.t Univ.puniverses

  (** Destructs an existential variable *)
  val destEvar : constr -> existential

  (** Destructs a (co)inductive type *)
  val destInd : constr -> inductive Univ.puniverses

  (** Destructs a constructor *)
  val destConstruct : constr -> constructor Univ.puniverses

  (** Destructs a [match c as x in I args return P with ... |
      Ci(...yij...) => ti | ... end] (or [let (..y1i..) := c as x in I args
      return P in t1], or [if c then t1 else t2])
      @return [(info,c,fun args x => P,[|...|fun yij => ti| ...|])]
      where [info] is pretty-printing information *)
  val destCase : constr -> case_info * constr * constr * constr array

  (** Destructs a projection *)
  val destProj : constr -> Projection.t * constr

  (** Destructs the {% $ %}i{% $ %}th function of the block
      [Fixpoint f{_ 1} ctx{_ 1} = b{_ 1}
      with    f{_ 2} ctx{_ 2} = b{_ 2}
      ...
      with    f{_ n} ctx{_ n} = b{_ n}],
      where the length of the {% $ %}j{% $ %}th context is {% $ %}ij{% $ %}.
  *)
  val destFix : constr -> fixpoint

  type cofixpoint = int * rec_declaration
  val destCoFix : constr -> cofixpoint

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

  open Constr
  type sorts_family = Sorts.family = InProp | InSet | InType
  [@@ocaml.deprecated "Alias of Sorts.family"]

  type contents = Sorts.contents = Pos | Null
  [@@ocaml.deprecated "Alias of Sorts.contents"]

  type sorts = Sorts.t =
    | Prop of Sorts.contents
    | Type of Univ.Universe.t
  [@@ocaml.deprecated "alias of API.Sorts.t"]

  type metavariable = int
  [@@ocaml.deprecated "Alias of Constr.metavariable"]

  type ('constr, 'types) prec_declaration = Names.Name.t array * 'types array * 'constr array
  [@@ocaml.deprecated "Alias of Constr.prec_declaration"]

  type 'constr pexistential = 'constr Constr.pexistential
  [@@ocaml.deprecated "Alias of Constr.pexistential"]

  type cast_kind = Constr.cast_kind =
                 | VMcast
                 | NATIVEcast
                 | DEFAULTcast
                 | REVERTcast
  [@@ocaml.deprecated "Alias of Constr.cast_kind"]

  type 'a puniverses = 'a Univ.puniverses
  [@@ocaml.deprecated "Alias of Constr.puniverses"]
  type pconstant = Names.Constant.t Univ.puniverses
  [@@ocaml.deprecated "Alias of Constr.pconstant"]
  type pinductive = Names.inductive Univ.puniverses
  [@@ocaml.deprecated "Alias of Constr.pinductive"]
  type pconstructor = Names.constructor Univ.puniverses
  [@@ocaml.deprecated "Alias of Constr.pconstructor"]
  type case_style = Constr.case_style =
    | LetStyle
    | IfStyle
    | LetPatternStyle
    | MatchStyle
    | RegularStyle
  [@@ocaml.deprecated "Alias of Constr.case_style"]

  type case_printing = Constr.case_printing =
    { ind_tags  : bool list;
      cstr_tags : bool list array;
      style     : Constr.case_style
    }
  [@@ocaml.deprecated "Alias of Constr.case_printing"]

  type case_info = Constr.case_info =
    { ci_ind        : Names.inductive;
      ci_npar       : int;
      ci_cstr_ndecls: int array;
      ci_cstr_nargs : int array;
      ci_pp_info    : Constr.case_printing
    }
  [@@ocaml.deprecated "Alias of Constr.case_info"]

  type ('constr, 'types) pfixpoint =
    (int array * int) * ('constr, 'types) Constr.prec_declaration
  [@@ocaml.deprecated "Alias of Constr.pfixpoint"]

  type ('constr, 'types) pcofixpoint =
    int * ('constr, 'types) Constr.prec_declaration
  [@@ocaml.deprecated "Alias of Constr.pcofixpoint"]

  type ('constr, 'types, 'sort, 'univs) kind_of_term = ('constr, 'types, 'sort, 'univs) Constr.kind_of_term =
     | Rel       of int
     | Var       of Names.Id.t
     | Meta      of Constr.metavariable
     | Evar      of 'constr Constr.pexistential
     | Sort      of 'sort
     | Cast      of 'constr * Constr.cast_kind * 'types
     | Prod      of Names.Name.t * 'types * 'types
     | Lambda    of Names.Name.t * 'types * 'constr
     | LetIn     of Names.Name.t * 'constr * 'types * 'constr
     | App       of 'constr * 'constr array
     | Const     of (Names.Constant.t * 'univs)
     | Ind       of (Names.inductive * 'univs)
     | Construct of (Names.constructor * 'univs)
     | Case      of Constr.case_info * 'constr * 'constr * 'constr array
     | Fix       of ('constr, 'types) Constr.pfixpoint
     | CoFix     of ('constr, 'types) Constr.pcofixpoint
     | Proj      of Names.Projection.t * 'constr
  [@@ocaml.deprecated "Alias of Constr.kind_of_term"]
  type existential = Evar.t * Constr.constr array
  [@@ocaml.deprecated "Alias of Constr.existential"]
  type rec_declaration = Names.Name.t array * Constr.constr array * Constr.constr array
  [@@ocaml.deprecated "Alias of Constr.rec_declaration"]
  val kind_of_term : Constr.constr -> (Constr.constr, Constr.types, Sorts.t, Univ.Instance.t) Constr.kind_of_term
  [@@ocaml.deprecated "Alias of Constr.kind"]
  val applistc : Constr.constr -> Constr.constr list -> Constr.constr

  val applist : constr * constr list -> constr
  [@@ocaml.deprecated "(sort of an) alias of API.Term.applistc"]

  val mkArrow : types -> types -> constr
  val mkRel : int -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkVar : Names.Id.t -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]

  val mkMeta : Constr.metavariable -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]

  val mkEvar : Constr.existential -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkSort : Sorts.t -> types
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkProp : types
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkSet  : types
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkType : Univ.Universe.t -> types
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkCast : constr * Constr.cast_kind * constr -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkProd : Names.Name.t * types * types -> types
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkLambda : Names.Name.t * types * constr -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkLetIn : Names.Name.t * constr * types * constr -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkApp : constr * constr array -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkConst : Names.Constant.t -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkProj : Names.Projection.t * constr -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkInd : Names.inductive -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkConstruct : Names.constructor -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkConstructU : Names.constructor Univ.puniverses -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkConstructUi : (Constr.pinductive * int) -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkCase : Constr.case_info * constr * constr * constr array -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkFix : fixpoint -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]
  val mkCoFix : cofixpoint -> constr
  [@@ocaml.deprecated "Alias of similarly named Constr function"]

  val mkNamedLambda : Names.Id.t -> types -> constr -> constr
  val mkNamedLetIn : Names.Id.t -> constr -> types -> constr -> constr
  val mkNamedProd : Names.Id.t -> types -> types -> types

  val decompose_app : constr -> constr * constr list
  [@@ocaml.deprecated "Alias for the function in [Constr]"]

  val decompose_prod : constr -> (Names.Name.t*constr) list * constr
  val decompose_prod_n : int -> constr -> (Names.Name.t * constr) list * constr
  val decompose_prod_assum : types -> Context.Rel.t * types
  val decompose_lam : constr -> (Names.Name.t * constr) list * constr
  val decompose_lam_n : int -> constr -> (Names.Name.t * constr) list * constr
  val decompose_prod_n_assum : int -> types -> Context.Rel.t * types

  val compose_prod : (Names.Name.t * constr) list -> constr -> constr
  val compose_lam : (Names.Name.t * constr) list -> constr -> constr

  val destSort : constr -> Sorts.t
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val destVar : constr -> Names.Id.t
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val destApp : constr -> constr * constr array
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val destProd : types -> Names.Name.t * types * types
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val destLetIn : constr -> Names.Name.t * constr * types * constr
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val destEvar : constr -> Constr.existential
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val destRel : constr -> int
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val destConst : constr -> Names.Constant.t Univ.puniverses
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val destCast : constr -> constr * Constr.cast_kind * constr
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val destLambda : constr -> Names.Name.t * types * constr
  [@@ocaml.deprecated "Alias for the function in [Constr]"]

  val isRel : constr -> bool
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val isVar  : constr -> bool
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val isEvar : constr -> bool
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val isLetIn : constr -> bool
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val isLambda : constr -> bool
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val isConst : constr -> bool
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val isEvar_or_Meta : constr -> bool
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val isCast : constr -> bool
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val isMeta : constr -> bool
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val isApp : constr -> bool
  [@@ocaml.deprecated "Alias for the function in [Constr]"]

  val fold_constr : ('a -> constr -> 'a) -> 'a -> constr -> 'a
  [@@ocaml.deprecated "Alias of Constr.fold"]

  val eq_constr : constr -> constr -> bool
  [@@ocaml.deprecated "Alias of Constr.equal"]

  val hash_constr : constr -> int
  [@@ocaml.deprecated "Alias of Constr.hash"]

  val it_mkLambda_or_LetIn : constr -> Context.Rel.t -> constr
  val it_mkProd_or_LetIn : types -> Context.Rel.t -> types
  val prod_applist : constr -> constr list -> constr

  val map_constr : (constr -> constr) -> constr -> constr
  [@@ocaml.deprecated "Alias of Constr.map"]

  val mkIndU : Constr.pinductive -> constr
  [@@ocaml.deprecated "Alias of Constr.mkIndU"]
  val mkConstU : Constr.pconstant -> constr
  [@@ocaml.deprecated "Alias of Constr.mkConstU"]
  val map_constr_with_binders :
    ('a -> 'a) -> ('a -> constr -> constr) -> 'a -> constr -> constr
  [@@ocaml.deprecated "Alias of Constr.map_with_binders"]

  val iter_constr : (constr -> unit) -> constr -> unit
  [@@ocaml.deprecated "Alias of Constr.iter."]

  (* Quotients away universes: really needed?
   * Can't we just call eq_c_univs_infer and discard the inferred csts?
   *)
  val eq_constr_nounivs : constr -> constr -> bool
  [@@ocaml.deprecated "Alias of Constr.qe_constr_nounivs."]

  type ('constr, 'types) kind_of_type =
    | SortType   of Sorts.t
    | CastType   of 'types * 'types
    | ProdType   of Names.Name.t * 'types * 'types
    | LetInType  of Names.Name.t * 'constr * 'types * 'types
    | AtomicType of 'constr * 'constr array

  val kind_of_type : types -> (constr, types) kind_of_type

  val is_prop_sort : Sorts.t -> bool
  [@@ocaml.deprecated "alias of API.Sorts.is_prop"]

  type existential_key = Evar.t
  [@@ocaml.deprecated "Alias of Constr.existential_key"]

  val family_of_sort : Sorts.t -> Sorts.family
  [@@ocaml.deprecated "Alias of Sorts.family"]

  val compare : constr -> constr -> int
  [@@ocaml.deprecated "Alias of Constr.compare."]

  val constr_ord : constr -> constr -> int
  [@@ocaml.deprecated "alias of Term.compare"]

  val destInd : constr -> Names.inductive Univ.puniverses
  [@@ocaml.deprecated "Alias for the function in [Constr]"]
  val univ_of_sort : Sorts.t -> Univ.Universe.t
  [@@ocaml.deprecated "Alias for the function in [Constr]"]

  val strip_lam : constr -> constr
  val strip_prod_assum : types -> types

  val decompose_lam_assum : constr -> Context.Rel.t * constr
  val destFix : constr -> fixpoint
  [@@ocaml.deprecated "Alias for the function in [Constr]"]

  val compare_constr : (constr -> constr -> bool) -> constr -> constr -> bool
  [@@ocaml.deprecated "Alias of Constr.compare_head."]

  type constr = Constr.t
  [@@ocaml.deprecated "Alias of Constr.t"]
  type types = Constr.t
  [@@ocaml.deprecated "Alias of Constr.types"]

  type fixpoint = (int array * int) * Constr.rec_declaration
  [@@ocaml.deprecated "Alias of Constr.Constr.fixpoint"]
  type cofixpoint = int * Constr.rec_declaration
  [@@ocaml.deprecated "Alias of Constr.cofixpoint"]

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
  val debug_pr_subst : substitution -> Pp.t
  val debug_pr_delta : delta_resolver -> Pp.t
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

  type constant_universes =
    | Monomorphic_const of Univ.ContextSet.t
    | Polymorphic_const of Univ.AUContext.t

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
        const_type : Constr.types;
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
  | Monomorphic_ind of Univ.ContextSet.t
  | Polymorphic_ind of Univ.AUContext.t
  | Cumulative_ind of Univ.ACumulativityInfo.t

  type record_body = (Id.t * Constant.t array * projection_body array) option

  type recursivity_kind =
    | Finite
    | CoFinite
    | BiFinite

  type mutual_inductive_body = {
        mind_packets : one_inductive_body array;
        mind_record : record_body option;
        mind_finite : recursivity_kind;
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
   and 'a generic_module_body =
                       { mod_mp : Names.ModPath.t;
                         mod_expr : 'a;
                         mod_type : module_signature;
                         mod_type_alg : module_expression option;
                         mod_constraints : Univ.ContextSet.t;
                         mod_delta : Mod_subst.delta_resolver;
                         mod_retroknowledge : 'a module_retroknowledge;
                       }
   and module_signature = (module_type_body,structure_body) functorize
   and module_body = module_implementation generic_module_body
   and module_type_body = unit generic_module_body
   and structure_body = (Names.Label.t * structure_field_body) list
   and structure_field_body =
                            | SFBconst of constant_body
                            | SFBmind of mutual_inductive_body
                            | SFBmodule of module_body
                            | SFBmodtype of module_type_body
  and _ module_retroknowledge =
  | ModBodyRK :
    Retroknowledge.action list -> module_implementation module_retroknowledge
  | ModTypeRK : unit module_retroknowledge
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
    | Monomorphic_ind_entry of Univ.ContextSet.t
    | Polymorphic_ind_entry of Univ.UContext.t
    | Cumulative_ind_entry of Univ.CumulativityInfo.t

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
    mind_entry_finite : Declarations.recursivity_kind;
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
  type constant_universes_entry =
    | Monomorphic_const_entry of Univ.ContextSet.t
    | Polymorphic_const_entry of Univ.UContext.t
  type 'a in_constant_universes_entry = 'a * constant_universes_entry
  type 'a definition_entry =
                               { const_entry_body   : 'a const_entry_body;
                                 (* List of section variables *)
                                 const_entry_secctx : Context.Named.t option;
                                 (* State id on which the completion of type checking is reported *)
                                 const_entry_feedback    : Stateid.t option;
                                 const_entry_type        : Constr.types option;
                                 const_entry_universes   : constant_universes_entry;
                                 const_entry_opaque      : bool;
                                 const_entry_inline_code : bool }
  type parameter_entry = Context.Named.t option * Constr.types in_constant_universes_entry * inline

  type projection_entry = {
    proj_entry_ind : MutInd.t;
    proj_entry_arg : int }

  type 'a constant_entry =
                         | DefinitionEntry of 'a definition_entry
                         | ParameterEntry of parameter_entry
                         | ProjectionEntry of projection_entry
  type module_struct_entry = Declarations.module_alg_expr
  type module_params_entry =
    (Names.MBId.t * module_struct_entry) list
  type module_type_entry = module_params_entry * module_struct_entry
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

  type unsafe_type_judgment = Constr.types punsafe_type_judgment
  val empty_env : env
  val lookup_mind : Names.MutInd.t -> env -> Declarations.mutual_inductive_body
  val push_rel : Context.Rel.Declaration.t -> env -> env
  val push_rel_context : Context.Rel.t -> env -> env
  val push_rec_types : Constr.rec_declaration -> env -> env
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
    | FFix of Constr.fixpoint * fconstr Esubst.subs
    | FCoFix of Constr.cofixpoint * fconstr Esubst.subs
    | FCaseT of Constr.case_info * Constr.t * fconstr * Constr.t array * fconstr Esubst.subs (* predicate and branches are closures *)
    | FLambda of int * (Names.Name.t * Constr.t) list * Constr.t * fconstr Esubst.subs
    | FProd of Names.Name.t * fconstr * fconstr
    | FLetIn of Names.Name.t * fconstr * fconstr * Constr.t * fconstr Esubst.subs
    | FEvar of Constr.existential * fconstr Esubst.subs
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

  val create_clos_infos : ?evars:(Constr.existential -> Constr.t option) -> RedFlags.reds -> Environ.env -> clos_infos

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

  val is_arity : Environ.env -> Constr.types -> bool

  val dest_prod : Environ.env -> Constr.types -> Context.Rel.t * Constr.types

  type 'a extended_conversion_function =
    ?l2r:bool -> ?reds:Names.transparent_state -> Environ.env ->
    ?evars:((Constr.existential->Constr.t option) * UGraph.t) ->
    'a -> 'a -> unit
  val conv : Constr.t extended_conversion_function
end

module Type_errors :
sig

  open Names
  open Constr
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
    | ReferenceVariables of Id.t * 'constr
    | ElimArity of pinductive * Sorts.family list * 'constr * ('constr, 'types) punsafe_judgment
                   * (Sorts.family * Sorts.family * arity_error) option
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
  val type_of_inductive : Environ.env -> mind_specif Univ.puniverses -> Constr.types
  exception SingletonInductiveBecomesProp of Names.Id.t
  val lookup_mind_specif : Environ.env -> Names.inductive -> mind_specif
  val find_inductive  : Environ.env -> Constr.types -> Constr.pinductive * Constr.t list
end

module Typeops :
sig
  val infer_type : Environ.env -> Constr.types -> Environ.unsafe_type_judgment
  val type_of_constant_in : Environ.env -> Constr.pconstant -> Constr.types
end

module Mod_typing :
sig
  type 'alg translation =
    Declarations.module_signature * 'alg * Mod_subst.delta_resolver * Univ.ContextSet.t
  val translate_modtype :
    Environ.env -> Names.ModPath.t -> Entries.inline ->
     Entries.module_type_entry -> Declarations.module_type_body
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

(************************************************************************)
(* Modules from intf/                                                   *)
(************************************************************************)

module Libnames :
sig

  open Util
  open Names

  type full_path
  val pr_path : full_path -> Pp.t
  val make_path : Names.DirPath.t -> Names.Id.t -> full_path
  val eq_full_path : full_path -> full_path -> bool
  val repr_path : full_path -> Names.DirPath.t * Names.Id.t
  val dirpath : full_path -> Names.DirPath.t
  val path_of_string : string -> full_path

  type qualid
  val make_qualid : Names.DirPath.t -> Names.Id.t -> qualid
  val qualid_eq : qualid -> qualid -> bool
  val repr_qualid : qualid -> Names.DirPath.t * Names.Id.t
  val pr_qualid : qualid -> Pp.t
  val string_of_qualid : qualid -> string
  val qualid_of_string : string -> qualid
  val qualid_of_path : full_path -> qualid
  val qualid_of_dirpath : Names.DirPath.t -> qualid
  val qualid_of_ident : Names.Id.t -> qualid

  type reference =
    | Qualid of qualid Loc.located
    | Ident of Names.Id.t Loc.located
  val loc_of_reference : reference -> Loc.t option
  val qualid_of_reference : reference -> qualid Loc.located
  val pr_reference : reference -> Pp.t

  val is_dirpath_prefix_of : Names.DirPath.t -> Names.DirPath.t -> bool
  val split_dirpath : Names.DirPath.t -> Names.DirPath.t * Names.Id.t
  val dirpath_of_string : string -> Names.DirPath.t
  val pr_dirpath : Names.DirPath.t -> Pp.t
  [@@ocaml.deprecated "Alias for DirPath.print"]

  val string_of_path : full_path -> string

  val basename : full_path -> Names.Id.t

  type object_name = full_path * Names.KerName.t
  type object_prefix = {
    obj_dir : DirPath.t;
    obj_mp  : ModPath.t;
    obj_sec : DirPath.t;
  }

  module Dirset : Set.S with type elt = DirPath.t
  module Dirmap : Map.ExtS with type key = DirPath.t and module Set := Dirset
  module Spmap  : CSig.MapS with type key = full_path
end

module Misctypes :
sig
  type evars_flag = bool
  type clear_flag = bool option
  type advanced_flag = bool
  type rec_flag = bool

  type 'a or_by_notation =
    | AN of 'a
    | ByNotation of (string * string option) Loc.located

  type 'a or_var =
                 | ArgArg of 'a
                 | ArgVar of Names.Id.t Loc.located

  type 'a and_short_name = 'a * Names.Id.t Loc.located option

  type 'a glob_sort_gen =
    | GProp (** representation of [Prop] literal *)
    | GSet  (** representation of [Set] literal *)
    | GType of 'a (** representation of [Type] literal *)

  type 'a universe_kind =
    | UAnonymous
    | UUnknown
    | UNamed of 'a

  type level_info = Libnames.reference universe_kind
  type glob_level = level_info glob_sort_gen

  type sort_info = (Libnames.reference * int) option list
  type glob_sort = sort_info glob_sort_gen

  type ('a, 'b) gen_universe_decl = {
    univdecl_instance : 'a; (* Declared universes *)
    univdecl_extensible_instance : bool; (* Can new universes be added *)
    univdecl_constraints : 'b; (* Declared constraints *)
    univdecl_extensible_constraints : bool (* Can new constraints be added *) }

  type glob_constraint = glob_level * Univ.constraint_type * glob_level

  type case_style = Constr.case_style =
    | LetStyle
    | IfStyle
    | LetPatternStyle
    | MatchStyle
    | RegularStyle (** infer printing form from number of constructor *)
  [@@ocaml.deprecated "Alias for Constr.case_style."]

  type 'a cast_type =
                    | CastConv of 'a
                    | CastVM of 'a
                    | CastCoerce
                    | CastNative of 'a

  type 'constr intro_pattern_expr =
    | IntroForthcoming of bool
    | IntroNaming of intro_pattern_naming_expr
    | IntroAction of 'constr intro_pattern_action_expr
  and intro_pattern_naming_expr =
    | IntroIdentifier of Names.Id.t
    | IntroFresh of Names.Id.t
    | IntroAnonymous
  and 'constr intro_pattern_action_expr =
    | IntroWildcard
    | IntroOrAndPattern of 'constr or_and_intro_pattern_expr
    | IntroInjection of ('constr intro_pattern_expr) Loc.located list
    | IntroApplyOn of 'constr Loc.located * 'constr intro_pattern_expr Loc.located
    | IntroRewrite of bool
  and 'constr or_and_intro_pattern_expr =
    | IntroOrPattern of ('constr intro_pattern_expr) Loc.located list list
    | IntroAndPattern of ('constr intro_pattern_expr) Loc.located list

  type quantified_hypothesis =
    | AnonHyp of int
    | NamedHyp of Names.Id.t

  type 'a explicit_bindings = (quantified_hypothesis * 'a) Loc.located list

  type 'a bindings =
    | ImplicitBindings of 'a list
    | ExplicitBindings of 'a explicit_bindings
    | NoBindings

  type 'a with_bindings = 'a * 'a bindings

  type 'a core_destruction_arg =
    | ElimOnConstr of 'a
    | ElimOnIdent of Names.Id.t Loc.located
    | ElimOnAnonHyp of int

  type inversion_kind =
    | SimpleInversion
    | FullInversion
    | FullInversionClear

  type multi =
    | Precisely of int
    | UpTo of int
    | RepeatStar
    | RepeatPlus
  type 'id move_location =
    | MoveAfter of 'id
    | MoveBefore of 'id
    | MoveFirst
    | MoveLast

  type 'a destruction_arg = clear_flag * 'a core_destruction_arg

end

module Locus :
sig
  type 'a occurrences_gen =
  | AllOccurrences
  | AllOccurrencesBut of 'a list (** non-empty *)
  | NoOccurrences
  | OnlyOccurrences of 'a list (** non-empty *)
  type occurrences = int occurrences_gen
  type occurrences_expr = (int Misctypes.or_var) occurrences_gen
  type 'a with_occurrences = occurrences_expr * 'a
  type hyp_location_flag =
                             InHyp | InHypTypeOnly | InHypValueOnly
  type 'a hyp_location_expr = 'a with_occurrences * hyp_location_flag
  type 'id clause_expr =
  { onhyps : 'id hyp_location_expr list option;
    concl_occs : occurrences_expr }
  type clause = Names.Id.t clause_expr
  type hyp_location = Names.Id.t * hyp_location_flag
  type goal_location = hyp_location option
end

(************************************************************************)
(* End Modules from intf/                                               *)
(************************************************************************)

(************************************************************************)
(* Modules from library/                                                *)
(************************************************************************)

module Univops :
sig
  val universes_of_constr : Environ.env -> Constr.constr -> Univ.LSet.t
  val restrict_universe_context : Univ.ContextSet.t -> Univ.LSet.t -> Univ.ContextSet.t
end

module Nameops :
sig

  open Names

  val atompart_of_id : Names.Id.t -> string

  val pr_id : Names.Id.t -> Pp.t
  [@@ocaml.deprecated "alias of API.Names.Id.print"]

  val pr_name : Names.Name.t -> Pp.t
  [@@ocaml.deprecated "alias of API.Names.Name.print"]

  module Name : sig
    include module type of struct include Name end

    val map : (Id.t -> Id.t) -> Name.t -> t
    val get_id : t -> Names.Id.t
    val fold_right : (Names.Id.t -> 'a -> 'a) -> t -> 'a -> 'a

  end

  val name_fold : (Id.t -> 'a -> 'a) -> Name.t -> 'a -> 'a
  [@@ocaml.deprecated "alias of API.Names"]

  val name_app : (Id.t -> Id.t) -> Name.t -> Name.t
  [@@ocaml.deprecated "alias of API.Names"]

  val add_suffix : Id.t -> string -> Id.t
  val increment_subscript : Id.t -> Id.t
  val make_ident : string -> int option -> Id.t
  val out_name : Name.t -> Id.t
  [@@ocaml.deprecated "alias of API.Names"]
  val pr_lab : Label.t -> Pp.t
  [@@ocaml.deprecated "alias of API.Names"]
end

module Globnames :
sig

  open Util

  type global_reference =
    | VarRef of Names.Id.t
    | ConstRef of Names.Constant.t
    | IndRef of Names.inductive
    | ConstructRef of Names.constructor

  type extended_global_reference =
                                 | TrueGlobal of global_reference
                                 | SynDef of Names.KerName.t

  (* Long term: change implementation so that only 1 kind of order is needed.
   * Today: _env ones are fine grained, which one to pick depends.  Eg.
   *   - conversion rule are implemented by the non_env ones
   *   - pretty printing (of user provided names/aliases) are implemented by
   *     the _env ones
   *)
  module Refset : CSig.SetS with type elt = global_reference
  module Refmap : Map.ExtS
    with type key = global_reference and module Set := Refset

  module Refset_env : CSig.SetS with type elt = global_reference
  module Refmap_env : Map.ExtS
    with type key = global_reference and module Set := Refset_env

  module RefOrdered :
  sig
    type t = global_reference
    val compare : t -> t -> int
  end

  val pop_global_reference : global_reference -> global_reference
  val eq_gr : global_reference -> global_reference -> bool
  val destIndRef : global_reference -> Names.inductive

  val encode_mind : Names.DirPath.t -> Names.Id.t -> Names.MutInd.t
  val encode_con : Names.DirPath.t -> Names.Id.t -> Names.Constant.t

  val global_of_constr : Constr.t -> global_reference

  val subst_global : Mod_subst.substitution -> global_reference -> global_reference * Constr.t
  val destConstructRef : global_reference -> Names.constructor

  val reference_of_constr : Constr.t -> global_reference
  [@@ocaml.deprecated "alias of API.Globnames.global_of_constr"]

  val is_global : global_reference -> Constr.t -> bool
end

(******************************************************************************)
(* XXX: Moved from intf *)
(******************************************************************************)
module Pattern :
sig

  type case_info_pattern =
    { cip_style : Constr.case_style;
      cip_ind : Names.inductive option;
      cip_ind_tags : bool list option; (** indicates LetIn/Lambda in arity *)
      cip_extensible : bool (** does this match end with _ => _ ? *) }

  type constr_pattern =
    | PRef of Globnames.global_reference
    | PVar of Names.Id.t
    | PEvar of Evar.t * constr_pattern array
    | PRel of int
    | PApp of constr_pattern * constr_pattern array
    | PSoApp of Names.Id.t * constr_pattern list
    | PProj of Names.Projection.t * constr_pattern
    | PLambda of Names.Name.t * constr_pattern * constr_pattern
    | PProd of Names.Name.t * constr_pattern * constr_pattern
    | PLetIn of Names.Name.t * constr_pattern * constr_pattern option * constr_pattern
    | PSort of Misctypes.glob_sort
    | PMeta of Names.Id.t option
    | PIf of constr_pattern * constr_pattern * constr_pattern
    | PCase of case_info_pattern * constr_pattern * constr_pattern *
                 (int * bool list * constr_pattern) list (** index of constructor, nb of args *)
    | PFix of Constr.fixpoint
    | PCoFix of Constr.cofixpoint

end

module Evar_kinds :
sig
  type obligation_definition_status =
    | Define of bool
    | Expand

  type matching_var_kind =
    | FirstOrderPatVar of Names.Id.t
    | SecondOrderPatVar of Names.Id.t

  type t =
         | ImplicitArg of Globnames.global_reference * (int * Names.Id.t option)
                          * bool (** Force inference *)
         | BinderType of Names.Name.t
         | NamedHole of Names.Id.t (* coming from some ?[id] syntax *)
         | QuestionMark of obligation_definition_status * Names.Name.t
         | CasesType of bool (* true = a subterm of the type *)
         | InternalHole
         | TomatchTypeParameter of Names.inductive * int
         | GoalEvar
         | ImpossibleCase
         | MatchingVar of matching_var_kind
         | VarInstance of Names.Id.t
         | SubEvar of Evar.t
end

module Decl_kinds :
sig
  type polymorphic = bool
  type cumulative_inductive_flag = bool
  type recursivity_kind = Declarations.recursivity_kind =
    | Finite
    | CoFinite
    | BiFinite
  [@@ocaml.deprecated "Please use [Declarations.recursivity_kind"]

  type discharge =
    | DoDischarge
    | NoDischarge

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
    | Let
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

module Glob_term :
sig
  type 'a cases_pattern_r =
    | PatVar  of Names.Name.t
    | PatCstr of Names.constructor * 'a cases_pattern_g list * Names.Name.t
  and 'a cases_pattern_g = ('a cases_pattern_r, 'a) DAst.t
  type cases_pattern = [ `any ] cases_pattern_g
  type existential_name = Names.Id.t
  type 'a glob_constr_r =
    | GRef of Globnames.global_reference * Misctypes.glob_level list option
        (** An identifier that represents a reference to an object defined
            either in the (global) environment or in the (local) context. *)
    | GVar of Names.Id.t
        (** An identifier that cannot be regarded as "GRef".
            Bound variables are typically represented this way. *)
    | GEvar   of existential_name * (Names.Id.t * 'a glob_constr_g) list
    | GPatVar of Evar_kinds.matching_var_kind
    | GApp    of 'a glob_constr_g * 'a glob_constr_g list
    | GLambda of Names.Name.t * Decl_kinds.binding_kind *  'a glob_constr_g * 'a glob_constr_g
    | GProd   of Names.Name.t * Decl_kinds.binding_kind * 'a glob_constr_g * 'a glob_constr_g
    | GLetIn  of Names.Name.t * 'a glob_constr_g * 'a glob_constr_g option * 'a glob_constr_g
    | GCases  of Constr.case_style * 'a glob_constr_g option * 'a tomatch_tuples_g * 'a cases_clauses_g
    | GLetTuple of Names.Name.t list * (Names.Name.t * 'a glob_constr_g option) * 'a glob_constr_g * 'a glob_constr_g
    | GIf   of 'a glob_constr_g * (Names.Name.t * 'a glob_constr_g option) * 'a glob_constr_g * 'a glob_constr_g
    | GRec  of 'a fix_kind_g * Names.Id.t array * 'a glob_decl_g list array *
               'a glob_constr_g array * 'a glob_constr_g array
    | GSort of Misctypes.glob_sort
    | GHole of Evar_kinds.t * Misctypes.intro_pattern_naming_expr * Genarg.glob_generic_argument option
    | GCast of 'a glob_constr_g * 'a glob_constr_g Misctypes.cast_type

   and 'a glob_constr_g = ('a glob_constr_r, 'a) DAst.t

   and 'a glob_decl_g = Names.Name.t * Decl_kinds.binding_kind * 'a glob_constr_g option * 'a glob_constr_g

   and 'a fix_recursion_order_g =
     | GStructRec
     | GWfRec of 'a glob_constr_g
     | GMeasureRec of 'a glob_constr_g * 'a glob_constr_g option

   and 'a fix_kind_g =
     | GFix of ((int option * 'a fix_recursion_order_g) array * int)
     | GCoFix of int

   and 'a predicate_pattern_g =
     Names.Name.t * (Names.inductive * Names.Name.t list) Loc.located option

   and 'a tomatch_tuple_g = ('a glob_constr_g * 'a predicate_pattern_g)

   and 'a tomatch_tuples_g = 'a tomatch_tuple_g list

   and 'a cases_clause_g = (Names.Id.t list * 'a cases_pattern_g list * 'a glob_constr_g) Loc.located
   and 'a cases_clauses_g = 'a cases_clause_g list

   type glob_constr = [ `any ] glob_constr_g
   type tomatch_tuple = [ `any ] tomatch_tuple_g
   type tomatch_tuples = [ `any ] tomatch_tuples_g
   type cases_clause = [ `any ] cases_clause_g
   type cases_clauses = [ `any ] cases_clauses_g
   type glob_decl = [ `any ] glob_decl_g
   type fix_kind = [ `any ] fix_kind_g
   type predicate_pattern = [ `any ] predicate_pattern_g
   type any_glob_constr =
   | AnyGlobConstr : 'r glob_constr_g -> any_glob_constr

end

module Notation_term :
sig
  type scope_name = string
  type notation_var_instance_type =
                                  | NtnTypeConstr | NtnTypeOnlyBinder | NtnTypeConstrList | NtnTypeBinderList
  type tmp_scope_name = scope_name

  type subscopes = tmp_scope_name option * scope_name list
  type notation_constr =
                       | NRef of Globnames.global_reference
                       | NVar of Names.Id.t
                       | NApp of notation_constr * notation_constr list
                       | NHole of Evar_kinds.t * Misctypes.intro_pattern_naming_expr * Genarg.glob_generic_argument option
                       | NList of Names.Id.t * Names.Id.t * notation_constr * notation_constr * bool
                       | NLambda of Names.Name.t * notation_constr * notation_constr
                       | NProd of Names.Name.t * notation_constr * notation_constr
                       | NBinderList of Names.Id.t * Names.Id.t * notation_constr * notation_constr
                       | NLetIn of Names.Name.t * notation_constr * notation_constr option * notation_constr
                       | NCases of Constr.case_style * notation_constr option *
                                     (notation_constr * (Names.Name.t * (Names.inductive * Names.Name.t list) option)) list *
                                       (Glob_term.cases_pattern list * notation_constr) list
                       | NLetTuple of Names.Name.t list * (Names.Name.t * notation_constr option) *
                                        notation_constr * notation_constr
                       | NIf of notation_constr * (Names.Name.t * notation_constr option) *
                                  notation_constr * notation_constr
                       | NRec of Glob_term.fix_kind * Names.Id.t array *
                                   (Names.Name.t * notation_constr option * notation_constr) list array *
                                     notation_constr array * notation_constr array
                       | NSort of Misctypes.glob_sort
                       | NCast of notation_constr * notation_constr Misctypes.cast_type
  type interpretation = (Names.Id.t * (subscopes * notation_var_instance_type)) list *
    notation_constr
  type precedence = int
  type parenRelation =
    | L | E | Any | Prec of precedence
  type tolerability = precedence * parenRelation
end

module Constrexpr :
sig

  type binder_kind =
                   | Default of Decl_kinds.binding_kind
                   | Generalized of Decl_kinds.binding_kind * Decl_kinds.binding_kind * bool

  type explicitation =
                     | ExplByPos of int * Names.Id.t option
                     | ExplByName of Names.Id.t
  type sign = bool
  type raw_natural_number = string
  type prim_token =
    | Numeral of raw_natural_number * sign
    | String of string

  type notation = string
  type instance_expr = Misctypes.glob_level list
  type proj_flag = int option
  type abstraction_kind =
    | AbsLambda
    | AbsPi

  type cases_pattern_expr_r =
    | CPatAlias of cases_pattern_expr * Names.Id.t
    | CPatCstr  of Libnames.reference
      * cases_pattern_expr list option * cases_pattern_expr list
    (** [CPatCstr (_, c, Some l1, l2)] represents (@c l1) l2 *)
    | CPatAtom of Libnames.reference option
    | CPatOr   of cases_pattern_expr list
    | CPatNotation of notation * cases_pattern_notation_substitution
                      * cases_pattern_expr list
    | CPatPrim   of prim_token
    | CPatRecord of (Libnames.reference * cases_pattern_expr) list
    | CPatDelimiters of string * cases_pattern_expr
    | CPatCast   of cases_pattern_expr * constr_expr
   and cases_pattern_expr = cases_pattern_expr_r CAst.t

   and cases_pattern_notation_substitution =
     cases_pattern_expr list * cases_pattern_expr list list

   and constr_expr_r =
     | CRef     of Libnames.reference * instance_expr option
     | CFix     of Names.Id.t Loc.located * fix_expr list
     | CCoFix   of Names.Id.t Loc.located * cofix_expr list
     | CProdN   of binder_expr list * constr_expr
     | CLambdaN of binder_expr list * constr_expr
     | CLetIn   of Names.Name.t Loc.located * constr_expr * constr_expr option * constr_expr
     | CAppExpl of (proj_flag * Libnames.reference * instance_expr option) * constr_expr list
     | CApp     of (proj_flag * constr_expr) *
                   (constr_expr * explicitation Loc.located option) list
     | CRecord  of (Libnames.reference * constr_expr) list
     | CCases of Constr.case_style
               * constr_expr option
               * case_expr list
               * branch_expr list
     | CLetTuple of Names.Name.t Loc.located list * (Names.Name.t Loc.located option * constr_expr option) *
                    constr_expr * constr_expr
     | CIf of constr_expr * (Names.Name.t Loc.located option * constr_expr option)
            * constr_expr * constr_expr
     | CHole   of Evar_kinds.t option * Misctypes.intro_pattern_naming_expr * Genarg.raw_generic_argument option
     | CPatVar of Names.Id.t
     | CEvar   of Names.Id.t * (Names.Id.t * constr_expr) list
     | CSort   of Misctypes.glob_sort
     | CCast   of constr_expr * constr_expr Misctypes.cast_type
     | CNotation of notation * constr_notation_substitution
     | CGeneralization of Decl_kinds.binding_kind * abstraction_kind option * constr_expr
     | CPrim of prim_token
     | CDelimiters of string * constr_expr
   and constr_expr = constr_expr_r CAst.t

   and case_expr = constr_expr * Names.Name.t Loc.located option * cases_pattern_expr option

   and branch_expr =
     (cases_pattern_expr list Loc.located list * constr_expr) Loc.located

   and binder_expr =
     Names.Name.t Loc.located list * binder_kind * constr_expr

   and fix_expr =
     Names.Id.t Loc.located * (Names.Id.t Loc.located option * recursion_order_expr) *
       local_binder_expr list * constr_expr * constr_expr

   and cofix_expr =
     Names.Id.t Loc.located * local_binder_expr list * constr_expr * constr_expr

   and recursion_order_expr =
                            | CStructRec
                              | CWfRec of constr_expr
                            | CMeasureRec of constr_expr * constr_expr option

   and local_binder_expr =
     | CLocalAssum   of Names.Name.t Loc.located list * binder_kind * constr_expr
     | CLocalDef     of Names.Name.t Loc.located * constr_expr * constr_expr option
     | CLocalPattern of (cases_pattern_expr * constr_expr option) Loc.located

   and constr_notation_substitution =
     constr_expr list *
       constr_expr list list *
         local_binder_expr list list

  type constr_pattern_expr = constr_expr
end

module Genredexpr :
sig

  (** The parsing produces initially a list of [red_atom] *)
  type 'a red_atom =
    | FBeta
    | FMatch
    | FFix
    | FCofix
    | FZeta
    | FConst of 'a list
    | FDeltaBut of 'a list

  (** This list of atoms is immediately converted to a [glob_red_flag] *)
  type 'a glob_red_flag = {
      rBeta : bool;
      rMatch : bool;
      rFix : bool;
      rCofix : bool;
      rZeta : bool;
      rDelta : bool; (** true = delta all but rConst; false = delta only on rConst*)
      rConst : 'a list
    }

  (** Generic kinds of reductions *)
  type ('a,'b,'c) red_expr_gen =
    | Red of bool
    | Hnf
    | Simpl of 'b glob_red_flag*('b,'c) Util.union Locus.with_occurrences option
    | Cbv of 'b glob_red_flag
    | Cbn of 'b glob_red_flag
    | Lazy of 'b glob_red_flag
    | Unfold of 'b Locus.with_occurrences list
    | Fold of 'a list
    | Pattern of 'a Locus.with_occurrences list
    | ExtraRedExpr of string
    | CbvVm of ('b,'c) Util.union Locus.with_occurrences option
    | CbvNative of ('b,'c) Util.union Locus.with_occurrences option

  type ('a,'b,'c) may_eval =
    | ConstrTerm of 'a
    | ConstrEval of ('a,'b,'c) red_expr_gen * 'a
    | ConstrContext of Names.Id.t Loc.located * 'a
    | ConstrTypeOf of 'a

  type r_trm = Constrexpr.constr_expr
  type r_pat = Constrexpr.constr_pattern_expr
  type r_cst = Libnames.reference Misctypes.or_by_notation
  type raw_red_expr = (r_trm, r_cst, r_pat) red_expr_gen
end

(******************************************************************************)
(* XXX: end of moved from intf                                                *)
(******************************************************************************)

module Libobject :
sig
  type obj
  type 'a substitutivity =
                         | Dispose
                           | Substitute of 'a
                         | Keep of 'a
                         | Anticipate of 'a

  type 'a object_declaration =   {
                                   object_name : string;
                                   cache_function : Libnames.object_name * 'a -> unit;
                                   load_function : int -> Libnames.object_name * 'a -> unit;
                                   open_function : int -> Libnames.object_name * 'a -> unit;
                                   classify_function : 'a -> 'a substitutivity;
                                   subst_function :  Mod_subst.substitution * 'a -> 'a;
                                   discharge_function : Libnames.object_name * 'a -> 'a option;
                                   rebuild_function : 'a -> 'a
                                 }
  val declare_object : 'a object_declaration -> ('a -> obj)
  val default_object : string -> 'a object_declaration
  val object_tag : obj -> string
end

module Summary :
sig

  type frozen

  type marshallable =
    [ `Yes       (* Full data will be marshalled to disk                        *)
    | `No        (* Full data will be store in memory, e.g. for Undo            *)
    | `Shallow ] (* Only part of the data will be marshalled to a slave process *)

  type 'a summary_declaration =
    { freeze_function : marshallable -> 'a;
      unfreeze_function : 'a -> unit;
      init_function : unit -> unit; }

  val ref : ?freeze:(marshallable -> 'a -> 'a) -> name:string -> 'a -> 'a ref
  val declare_summary : string -> 'a summary_declaration -> unit
  module Local :
  sig
    type 'a local_ref
    val ref : ?freeze:('a -> 'a) -> name:string -> 'a -> 'a local_ref
    val (:=) : 'a local_ref -> 'a -> unit
    val (!) : 'a local_ref -> 'a
  end
end

module Nametab :
sig
  exception GlobalizationError of Libnames.qualid

  val global : Libnames.reference -> Globnames.global_reference
  val global_of_path : Libnames.full_path -> Globnames.global_reference
  val shortest_qualid_of_global : Names.Id.Set.t -> Globnames.global_reference -> Libnames.qualid
  val path_of_global : Globnames.global_reference -> Libnames.full_path
  val locate_extended : Libnames.qualid -> Globnames.extended_global_reference
  val full_name_module : Libnames.qualid -> Names.DirPath.t
  val pr_global_env : Names.Id.Set.t -> Globnames.global_reference -> Pp.t
  val basename_of_global : Globnames.global_reference -> Names.Id.t

  type visibility =
    | Until of int
    | Exactly of int

  val error_global_not_found : ?loc:Loc.t -> Libnames.qualid -> 'a
  val shortest_qualid_of_module : Names.ModPath.t -> Libnames.qualid
  val dirpath_of_module : Names.ModPath.t -> Names.DirPath.t
  val locate_module : Libnames.qualid -> Names.ModPath.t
  val dirpath_of_global : Globnames.global_reference -> Names.DirPath.t
  val locate : Libnames.qualid -> Globnames.global_reference
  val locate_constant : Libnames.qualid -> Names.Constant.t

  (** NOT FOR PUBLIC USE YET. Plugin writers, please do not rely on this API. *)

  module type UserName = sig
    type t
    val equal : t -> t -> bool
    val to_string : t -> string
    val repr : t ->  Names.Id.t * Names.Id.t list
  end

  module type EqualityType =
  sig
    type t
    val equal : t -> t -> bool
  end

  module type NAMETREE = sig
    type elt
    type t
    type user_name

    val empty : t
    val push : visibility -> user_name -> elt -> t -> t
    val locate : Libnames.qualid -> t -> elt
    val find : user_name -> t -> elt
    val exists : user_name -> t -> bool
    val user_name : Libnames.qualid -> t -> user_name
    val shortest_qualid : Names.Id.Set.t -> user_name -> t -> Libnames.qualid
    val find_prefixes : Libnames.qualid -> t -> elt list
  end

  module Make (U : UserName) (E : EqualityType) :
    NAMETREE with type user_name = U.t and type elt = E.t

end

module Global :
sig
  val env : unit -> Environ.env
  val lookup_mind : Names.MutInd.t -> Declarations.mutual_inductive_body
  val lookup_constant  : Names.Constant.t -> Declarations.constant_body
  val lookup_module    : Names.ModPath.t -> Declarations.module_body
  val lookup_modtype   : Names.ModPath.t -> Declarations.module_type_body
  val lookup_inductive : Names.inductive -> Declarations.mutual_inductive_body * Declarations.one_inductive_body
  val constant_of_delta_kn : Names.KerName.t -> Names.Constant.t
  val register :
    Retroknowledge.field -> Constr.t -> Constr.t -> unit
  val env_of_context : Environ.named_context_val -> Environ.env
  val is_polymorphic : Globnames.global_reference -> bool

  val constr_of_global_in_context : Environ.env ->
    Globnames.global_reference -> Constr.types * Univ.AUContext.t

  val type_of_global_in_context : Environ.env ->
    Globnames.global_reference -> Constr.types * Univ.AUContext.t

  val current_dirpath : unit -> Names.DirPath.t
  val body_of_constant_body : Declarations.constant_body -> (Constr.t * Univ.AUContext.t) option
  val body_of_constant : Names.Constant.t -> (Constr.t * Univ.AUContext.t) option
  val add_constraints : Univ.Constraint.t -> unit
end

module Lib : sig
  type is_type = bool
  type export = bool option
  type node =
            | Leaf of Libobject.obj (* FIX: horrible hack (wrt. Enrico) *)
            | CompilingLibrary of Libnames.object_prefix
            | OpenedModule of is_type * export * Libnames.object_prefix * Summary.frozen
            | ClosedModule  of library_segment
            | OpenedSection of Libnames.object_prefix * Summary.frozen
            | ClosedSection of library_segment

   and library_segment = (Libnames.object_name * node) list

  val current_mp : unit -> Names.ModPath.t
  val is_modtype : unit -> bool
  val is_module : unit -> bool
  val sections_are_opened : unit -> bool
  val add_anonymous_leaf : ?cache_first:bool -> Libobject.obj -> unit
  val contents : unit -> library_segment
  val cwd : unit -> Names.DirPath.t
  val add_leaf : Names.Id.t -> Libobject.obj -> Libnames.object_name
  val make_kn : Names.Id.t -> Names.KerName.t
  val make_path : Names.Id.t -> Libnames.full_path
  val discharge_con : Names.Constant.t -> Names.Constant.t
  val discharge_inductive : Names.inductive -> Names.inductive
end

module Declaremods :
sig

  val append_end_library_hook : (unit -> unit) -> unit

end

module Library :
sig
  val library_is_loaded : Names.DirPath.t -> bool
  val loaded_libraries : unit -> Names.DirPath.t list
end

module States :
sig
  type state

  val with_state_protection : ('a -> 'b) -> 'a -> 'b
end

module Kindops :
sig
  val logical_kind_of_goal_kind : Decl_kinds.goal_object_kind -> Decl_kinds.logical_kind
end

module Goptions :
sig
  type option_name = string list
  type 'a option_sig =
    {
      optdepr  : bool;
      optname  : string;
      optkey   : option_name;
      optread  : unit -> 'a;
      optwrite : 'a -> unit
    }

  type 'a write_function = 'a -> unit

  val declare_bool_option  : ?preprocess:(bool -> bool) ->
                             bool option_sig   -> bool write_function
  val declare_int_option   : ?preprocess:(int option -> int option) ->
                             int option option_sig -> int option write_function
  val declare_string_option: ?preprocess:(string -> string) ->
                             string option_sig -> string write_function
  val set_bool_option_value : option_name -> bool -> unit
end

module Keys :
sig
  type key
  val constr_key : ('a -> ('a, 't, 'u, 'i) Constr.kind_of_term) -> 'a -> key option
  val declare_equiv_keys : key -> key -> unit
  val pr_keys : (Globnames.global_reference -> Pp.t) -> Pp.t
end

module Coqlib :
sig

  type coq_eq_data = { eq   : Globnames.global_reference;
                       ind  : Globnames.global_reference;
                       refl : Globnames.global_reference;
                       sym  : Globnames.global_reference;
                       trans: Globnames.global_reference;
                       congr: Globnames.global_reference;
                     }

  type coq_sigma_data = {
      proj1 : Globnames.global_reference;
      proj2 : Globnames.global_reference;
      elim  : Globnames.global_reference;
      intro : Globnames.global_reference;
      typ   : Globnames.global_reference }
  val find_reference : string -> string list -> string -> Globnames.global_reference
  val check_required_library : string list -> unit
  val logic_module_name : string list
  val glob_true : Globnames.global_reference
  val glob_false : Globnames.global_reference
  val glob_O : Globnames.global_reference
  val glob_S : Globnames.global_reference
  val nat_path : Libnames.full_path
  val datatypes_module_name : string list
  val glob_eq : Globnames.global_reference
  val build_coq_eq_sym : Globnames.global_reference Util.delayed
  val build_coq_False : Globnames.global_reference Util.delayed
  val build_coq_not : Globnames.global_reference Util.delayed
  val build_coq_eq : Globnames.global_reference Util.delayed
  val build_coq_eq_data : coq_eq_data Util.delayed
  val path_of_O : Names.constructor
  val path_of_S : Names.constructor
  val build_prod : coq_sigma_data Util.delayed
  val build_coq_True : Globnames.global_reference Util.delayed
  val coq_iff_ref : Globnames.global_reference lazy_t
  val build_coq_iff_left_proj : Globnames.global_reference Util.delayed
  val build_coq_iff_right_proj : Globnames.global_reference Util.delayed
  val init_modules : string list list
  val build_coq_eq_refl  : Globnames.global_reference Util.delayed
  val arith_modules : string list list
  val zarith_base_modules : string list list
  val gen_reference_in_modules : string -> string list list-> string -> Globnames.global_reference
  val jmeq_module_name : string list
  val coq_eq_ref : Globnames.global_reference lazy_t
  val coq_not_ref : Globnames.global_reference lazy_t
  val coq_or_ref : Globnames.global_reference lazy_t
  val build_coq_and : Globnames.global_reference Util.delayed
  val build_coq_or : Globnames.global_reference Util.delayed
  val build_coq_I : Globnames.global_reference Util.delayed
  val coq_reference : string -> string list -> string -> Globnames.global_reference
end

(************************************************************************)
(* End of modules from library/                                         *)
(************************************************************************)

(************************************************************************)
(* Modules from engine/                                                 *)
(************************************************************************)

module Universes :
sig
  type universe_binders
  type universe_opt_subst
  val fresh_inductive_instance : Environ.env -> Names.inductive -> Constr.pinductive Univ.in_universe_context_set
  val new_Type : unit -> Constr.types
  val type_of_global : Globnames.global_reference -> Constr.types Univ.in_universe_context_set
  val constr_of_global : Globnames.global_reference -> Constr.t
  val new_univ_level : unit -> Univ.Level.t
  val new_sort_in_family : Sorts.family -> Sorts.t
  val pr_with_global_universes : Univ.Level.t -> Pp.t
  val pr_universe_opt_subst : universe_opt_subst -> Pp.t
  type universe_constraint

  module Constraints :
  sig
    type t
    val pr : t -> Pp.t
  end

  type universe_constraints = Constraints.t
  [@@ocaml.deprecated "Use Constraints.t"]

end

module UState :
sig
  type t
  val context : t -> Univ.UContext.t
  val context_set : t -> Univ.ContextSet.t
  val of_context_set : Univ.ContextSet.t -> t

  val const_univ_entry : poly:bool -> t -> Entries.constant_universes_entry
  val ind_univ_entry : poly:bool -> t -> Entries.inductive_universes

  type rigid =
    | UnivRigid
    | UnivFlexible of bool

end

module Evd :
sig

  type evar = Evar.t
  [@@ocaml.deprecated "use Evar.t"]

  val string_of_existential : Evar.t -> string
  [@@ocaml.deprecated "use Evar.print"]

  type evar_constraint = Reduction.conv_pb * Environ.env * Constr.t * Constr.t

  (* --------------------------------- *)

  (* evar info *)

  module Store :
  sig
    type t
    val empty : t
  end

  module Filter :
  sig
    type t
    val repr : t -> bool list option
  end

  (** This value defines the refinement of a given {i evar} *)
  type evar_body =
              | Evar_empty (** given {i evar} was not yet refined *)
              | Evar_defined of Constr.t (** given {i var} was refined to the indicated term *)

  (** all the information we have concerning some {i evar} *)
  type evar_info =
    {
      evar_concl : Constr.t;
      evar_hyps : Environ.named_context_val;
      evar_body : evar_body;
      evar_filter : Filter.t;
      evar_source : Evar_kinds.t Loc.located;
      evar_candidates : Constr.t list option; (* if not None, list of allowed instances *)
      evar_extra : Store.t
    }

  val evar_concl : evar_info -> Constr.t
  val evar_body : evar_info -> evar_body
  val evar_context : evar_info -> Context.Named.t
  val instantiate_evar_array : evar_info -> Constr.t -> Constr.t array -> Constr.t
  val evar_filtered_env : evar_info -> Environ.env
  val evar_hyps : evar_info -> Environ.named_context_val

  (* ------------------------------------ *)

  (* evar map *)

  type evar_map
  type open_constr = evar_map * Constr.t

  open Util

  module Metaset : Set.S with type elt = Constr.metavariable

  type rigid = UState.rigid =
    | UnivRigid
    | UnivFlexible of bool

    type 'a freelisted = {
          rebus : 'a;
          freemetas : Metaset.t
        }

    type instance_constraint = IsSuperType | IsSubType | Conv

    type instance_typing_status =
        CoerceToType | TypeNotProcessed | TypeProcessed

    type instance_status = instance_constraint * instance_typing_status

    type clbinding =
      | Cltyp of Names.Name.t * Constr.t freelisted
      | Clval of Names.Name.t * (Constr.t freelisted * instance_status) * Constr.t freelisted

    val empty : evar_map
    val from_env : Environ.env -> evar_map
    val find : evar_map -> Evar.t -> evar_info
    val find_undefined : evar_map -> Evar.t -> evar_info
    val is_defined : evar_map -> Evar.t -> bool
    val mem : evar_map -> Evar.t -> bool
    val add : evar_map -> Evar.t -> evar_info -> evar_map
    val evar_universe_context : evar_map -> UState.t
    val set_universe_context : evar_map -> UState.t -> evar_map
    val universes : evar_map -> UGraph.t
    val define : Evar.t -> Constr.t -> evar_map -> evar_map
    val fold : (Evar.t -> evar_info -> 'a -> 'a) -> evar_map -> 'a -> 'a
    val evar_key : Names.Id.t -> evar_map -> Evar.t

    val create_evar_defs : evar_map -> evar_map

    val meta_declare : Constr.metavariable -> Constr.types -> ?name:Names.Name.t -> evar_map -> evar_map

    val clear_metas : evar_map -> evar_map

    (** Allocates a new evar that represents a {i sort}. *)
    val new_sort_variable : ?loc:Loc.t -> ?name:Names.Id.t -> rigid -> evar_map -> evar_map * Sorts.t

    val remove : evar_map -> Evar.t -> evar_map
    val fresh_global : ?loc:Loc.t -> ?rigid:rigid -> ?names:Univ.Instance.t -> Environ.env ->
                       evar_map -> Globnames.global_reference -> evar_map * Constr.t
    val evar_filtered_context : evar_info -> Context.Named.t
    val fresh_inductive_instance : ?loc:Loc.t -> Environ.env -> evar_map -> Names.inductive -> evar_map * Constr.pinductive
    val fold_undefined : (Evar.t -> evar_info -> 'a -> 'a) -> evar_map -> 'a -> 'a

    val universe_context_set : evar_map -> Univ.ContextSet.t
    val evar_ident : Evar.t -> evar_map -> Names.Id.t option
    val extract_all_conv_pbs : evar_map -> evar_map * evar_constraint list
    val universe_binders : evar_map -> Universes.universe_binders
    val nf_constraints : evar_map -> evar_map
    val from_ctx : UState.t -> evar_map

    val to_universe_context : evar_map -> Univ.UContext.t
    val const_univ_entry : poly:bool -> evar_map -> Entries.constant_universes_entry
    val ind_univ_entry : poly:bool -> evar_map -> Entries.inductive_universes

    val meta_list : evar_map -> (Constr.metavariable * clbinding) list

    val meta_defined : evar_map -> Constr.metavariable -> bool

    val meta_name : evar_map -> Constr.metavariable -> Names.Name.t

    module MonadR :
    sig
      module List :
      sig
        val map_right : ('a -> evar_map -> evar_map * 'b) -> 'a list -> evar_map -> evar_map * 'b list
      end
    end

  type 'a sigma = {
        it : 'a ;
        sigma : evar_map
      }

  val sig_sig : 'a sigma -> evar_map

  val sig_it  : 'a sigma -> 'a

  type 'a in_evar_universe_context = 'a * UState.t

  val univ_flexible : rigid
  val univ_flexible_alg : rigid
  val empty_evar_universe_context : UState.t
  val union_evar_universe_context : UState.t -> UState.t -> UState.t
  val merge_universe_context : evar_map -> UState.t -> evar_map

  type unsolvability_explanation =
    | SeveralInstancesFound of int

  (** Return {i ids} of all {i evars} that occur in a given term. *)
  val evars_of_term : Constr.t -> Evar.Set.t

  val evar_universe_context_of : Univ.ContextSet.t -> UState.t
  [@@ocaml.deprecated "alias of API.UState.of_context_set"]

  val evar_context_universe_context : UState.t -> Univ.UContext.t
  [@@ocaml.deprecated "alias of API.UState.context"]

  type evar_universe_context = UState.t
  [@@ocaml.deprecated "alias of API.UState.t"]

  val existential_opt_value : evar_map -> Constr.existential -> Constr.t option
  val existential_value : evar_map -> Constr.existential -> Constr.t

  exception NotInstantiatedEvar

  val fresh_sort_in_family : ?loc:Loc.t -> ?rigid:rigid -> Environ.env -> evar_map -> Sorts.family -> evar_map * Sorts.t
end

module EConstr :
sig
  type t
  type constr = t
  type types = t
  type unsafe_judgment = (constr, types) Environ.punsafe_judgment
  type named_declaration = (constr, types) Context.Named.Declaration.pt
  type named_context = (constr, types) Context.Named.pt
  type rel_context = (constr, types) Context.Rel.pt
  type rel_declaration = (constr, types) Context.Rel.Declaration.pt
  type existential = constr Constr.pexistential
  module ESorts :
  sig
    type t
    (** Type of sorts up-to universe unification. Essentially a wrapper around
      Sorts.t so that normalization is ensured statically. *)

    val make : Sorts.t -> t
    (** Turn a sort into an up-to sort. *)

    val kind : Evd.evar_map -> t -> Sorts.t
    (** Returns the view into the current sort. Note that the kind of a variable
        may change if the unification state of the evar map changes. *)

  end

  module EInstance :
  sig
    type t
    (** Type of universe instances up-to universe unification. Similar to
      {ESorts.t} for {Univ.Instance.t}. *)

    val make : Univ.Instance.t -> t
    val kind : Evd.evar_map -> t -> Univ.Instance.t
    val empty : t
    val is_empty : t -> bool
  end

  val of_constr : Constr.t -> constr

  val kind : Evd.evar_map -> constr -> (constr, constr, ESorts.t, EInstance.t) Constr.kind_of_term

  val mkArrow : constr -> constr -> constr
  val mkInd : Names.inductive -> t
  val mkProp : constr
  val mkProd : Names.Name.t * constr * constr -> constr
  val mkRel : int -> constr
  val mkSort : Sorts.t -> constr
  val mkVar : Names.Id.t -> constr
  val mkLambda : Names.Name.t * constr * constr -> constr
  val mkLambda_or_LetIn : rel_declaration -> constr -> constr
  val mkApp : constr * constr array -> constr
  val mkEvar : constr Constr.pexistential -> constr

  val mkMeta : Constr.metavariable -> constr

  val mkConstructU : Names.constructor * EInstance.t -> constr
  val mkLetIn : Names.Name.t * constr * constr * constr -> constr
  val mkProd_or_LetIn : rel_declaration -> constr -> constr
  val mkCast : constr * Constr.cast_kind * constr -> constr
  val mkNamedLambda : Names.Id.t -> types -> constr -> constr
  val mkNamedProd : Names.Id.t -> types -> types -> types

  val isCast : Evd.evar_map -> t -> bool
  val isEvar : Evd.evar_map -> constr -> bool
  val isInd  : Evd.evar_map -> constr -> bool
  val isRel : Evd.evar_map -> constr -> bool
  val isSort : Evd.evar_map -> constr -> bool
  val isVar : Evd.evar_map -> constr -> bool
  val isConst : Evd.evar_map -> constr -> bool
  val isConstruct : Evd.evar_map -> constr -> bool

  val destInd : Evd.evar_map -> constr -> Names.inductive * EInstance.t
  val destVar : Evd.evar_map -> constr -> Names.Id.t
  val destEvar : Evd.evar_map -> constr -> constr Constr.pexistential
  val destRel : Evd.evar_map -> constr -> int
  val destProd : Evd.evar_map -> constr -> Names.Name.t * types * types
  val destLambda : Evd.evar_map -> constr -> Names.Name.t * types * constr
  val destApp : Evd.evar_map -> constr -> constr * constr array
  val destConst : Evd.evar_map -> constr -> Names.Constant.t * EInstance.t
  val destConstruct : Evd.evar_map -> constr -> Names.constructor * EInstance.t
  val destFix : Evd.evar_map -> t -> (t, t) Constr.pfixpoint
  val destCast : Evd.evar_map -> t -> t * Constr.cast_kind * t

  val mkConstruct : Names.constructor -> constr

  val compose_lam : (Names.Name.t * constr) list -> constr -> constr

  val decompose_lam : Evd.evar_map -> constr -> (Names.Name.t * constr) list * constr
  val decompose_lam_n_assum : Evd.evar_map -> int -> constr -> rel_context * constr
  val decompose_app : Evd.evar_map -> constr -> constr * constr list
  val decompose_prod : Evd.evar_map -> constr -> (Names.Name.t * constr) list * constr
  val decompose_prod_assum : Evd.evar_map -> constr -> rel_context * constr

  val applist : constr * constr list -> constr

  val to_constr : Evd.evar_map -> constr -> Constr.t

  val push_rel : rel_declaration -> Environ.env -> Environ.env

  module Unsafe :
  sig
    val to_constr : constr -> Constr.t

    val to_rel_decl : (constr, types) Context.Rel.Declaration.pt -> (Constr.constr, Constr.types) Context.Rel.Declaration.pt

    (** Physical identity. Does not care for defined evars. *)

    val to_named_decl : (constr, types) Context.Named.Declaration.pt -> (Constr.constr, Constr.types) Context.Named.Declaration.pt

    val to_instance : EInstance.t -> Univ.Instance.t
  end

  module Vars :
  sig
    val substnl : t list -> int -> t -> t
    val noccurn : Evd.evar_map -> int -> constr -> bool
    val closed0 : Evd.evar_map -> constr -> bool
    val subst1 : constr -> constr -> constr
    val substl : constr list -> constr -> constr
    val lift : int -> constr -> constr
    val liftn : int -> int -> t -> t
    val subst_var : Names.Id.t -> t -> t
    val subst_vars : Names.Id.t list -> t -> t
  end

  val fresh_global :
    ?loc:Loc.t -> ?rigid:UState.rigid -> ?names:Univ.Instance.t -> Environ.env ->
    Evd.evar_map -> Globnames.global_reference -> Evd.evar_map * t

  val of_named_decl : (Constr.t, Constr.types) Context.Named.Declaration.pt -> (constr, types) Context.Named.Declaration.pt
  val of_rel_decl : (Constr.t, Constr.types) Context.Rel.Declaration.pt -> (constr, types) Context.Rel.Declaration.pt
  val kind_of_type : Evd.evar_map -> constr -> (constr, constr) Term.kind_of_type
  val to_lambda : Evd.evar_map -> int -> constr -> constr
  val it_mkLambda_or_LetIn : constr -> rel_context -> constr
  val push_rel_context : rel_context -> Environ.env -> Environ.env
  val eq_constr : Evd.evar_map -> constr -> constr -> bool
  val iter_with_binders : Evd.evar_map -> ('a -> 'a) -> ('a -> constr -> unit) -> 'a -> constr -> unit
  val fold : Evd.evar_map -> ('a -> constr -> 'a) -> 'a -> constr -> 'a
  val existential_type : Evd.evar_map -> existential -> types
  val iter : Evd.evar_map -> (constr -> unit) -> constr -> unit
  val eq_constr_universes : Evd.evar_map -> constr -> constr -> Universes.Constraints.t option
  val eq_constr_nounivs : Evd.evar_map -> constr -> constr -> bool
  val compare_constr : Evd.evar_map -> (constr -> constr -> bool) -> constr -> constr -> bool
  val isApp : Evd.evar_map -> constr -> bool
  val it_mkProd_or_LetIn : constr -> rel_context -> constr
  val push_named : named_declaration -> Environ.env -> Environ.env
  val destCase : Evd.evar_map -> constr -> Constr.case_info * constr * constr * constr array
  val decompose_lam_assum : Evd.evar_map -> constr -> rel_context * constr
  val mkConst : Names.Constant.t -> constr
  val mkCase : Constr.case_info * constr * constr * constr array -> constr
  val named_context : Environ.env -> named_context
  val val_of_named_context : named_context -> Environ.named_context_val
  val mkFix : (t, t) Constr.pfixpoint -> t
  val decompose_prod_n_assum : Evd.evar_map -> int -> t -> rel_context * t
  val isMeta : Evd.evar_map -> t -> bool

  val destMeta : Evd.evar_map -> t -> Constr.metavariable

  val map_with_binders : Evd.evar_map -> ('a -> 'a) -> ('a -> t -> t) -> 'a -> t -> t
  val mkNamedLetIn : Names.Id.t -> constr -> types -> constr -> constr
  val map : Evd.evar_map -> (t -> t) -> t -> t
  val mkConstU : Names.Constant.t * EInstance.t -> t
  val isProd : Evd.evar_map -> t -> bool
  val mkConstructUi : (Names.inductive * EInstance.t) * int -> t
  val isLambda : Evd.evar_map -> t -> bool
end

module Namegen :
sig
  (** *)

  (** [next_ident_away original_id unwanted_ids] returns a new identifier as close as possible
      to the [original_id] while avoiding all [unwanted_ids].

      In particular:
      {ul {- if [original_id] does not appear in the list of [unwanted_ids], then [original_id] is returned.}
          {- if [original_id] appears in the list of [unwanted_ids],
             then this function returns a new id that:
             {ul {- has the same {i root} as the [original_id],}
                 {- does not occur in the list of [unwanted_ids],}
                 {- has the smallest possible {i subscript}.}}}}

      where by {i subscript} of some identifier we mean last part of it that is composed
      only from (decimal) digits and by {i root} of some identifier we mean
      the whole identifier except for the {i subscript}.

      E.g. if we take [foo42], then [42] is the {i subscript}, and [foo] is the root. *)
  val next_ident_away : Names.Id.t -> Names.Id.Set.t -> Names.Id.t

  val hdchar : Environ.env -> Evd.evar_map -> EConstr.types -> string
  val id_of_name_using_hdchar : Environ.env -> Evd.evar_map -> EConstr.types -> Names.Name.t -> Names.Id.t
  val next_ident_away_in_goal : Names.Id.t -> Names.Id.Set.t -> Names.Id.t
  val default_dependent_ident : Names.Id.t
  val next_global_ident_away : Names.Id.t -> Names.Id.Set.t -> Names.Id.t
  val rename_bound_vars_as_displayed :
    Evd.evar_map -> Names.Id.Set.t -> Names.Name.t list -> EConstr.types -> EConstr.types
end

module Termops :
sig
  val it_mkLambda_or_LetIn : Constr.t -> Context.Rel.t -> Constr.t
  val local_occur_var : Evd.evar_map -> Names.Id.t -> EConstr.constr -> bool
  val occur_var : Environ.env -> Evd.evar_map -> Names.Id.t -> EConstr.constr -> bool
  val pr_evar_info : Evd.evar_info -> Pp.t

  val print_constr : EConstr.constr -> Pp.t
  val pr_sort_family : Sorts.family -> Pp.t

  (** [dependent m t] tests whether [m] is a subterm of [t] *)
  val dependent : Evd.evar_map -> EConstr.constr -> EConstr.constr -> bool

  (** [pop c] returns a copy of [c] with decremented De Bruijn indexes *)
  val pop : EConstr.constr -> EConstr.constr

  (** Does a given term contain an existential variable? *)
  val occur_existential : Evd.evar_map -> EConstr.constr -> bool

  (** [map_constr_with_binders_left_to_right g f acc c] maps [f updated_acc] on all the immediate subterms of [c].
      {ul {- if a given immediate subterm of [c] is not below a binder, then [updated_acc] is the same as [acc].}
          {- if a given immediate subterm of [c] is below a binder [b], then [updated_acc] is computed as [g b acc].}} *)
  val map_constr_with_binders_left_to_right :
    Evd.evar_map -> (EConstr.rel_declaration -> 'a -> 'a) -> ('a -> EConstr.constr -> EConstr.constr) -> 'a -> EConstr.constr -> EConstr.constr

  (** Remove the outer-most {!Constr.kind_of_term.Cast} from a given term. *)
  val strip_outer_cast : Evd.evar_map -> EConstr.constr -> EConstr.constr

  (** [nb_lam] ⟦[fun (x1:t1)...(xn:tn) => c]⟧ where [c] is not an abstraction gives [n].
      Casts are ignored. *)
  val nb_lam : Evd.evar_map -> EConstr.constr -> int

  (** [push_rel_assum env_assumtion env] adds a given {i env assumption} to the {i env context} of a given {i environment}. *)
  val push_rel_assum : Names.Name.t * EConstr.types -> Environ.env -> Environ.env

  (** [push_rels_assum env_assumptions env] adds given {i env assumptions} to the {i env context} of a given {i environment}. *)
  val push_rels_assum : (Names.Name.t * Constr.types) list -> Environ.env -> Environ.env

  type meta_value_map = (Constr.metavariable * Constr.t) list

  val last_arg : Evd.evar_map -> EConstr.constr -> EConstr.constr
  val assums_of_rel_context : ('c, 't) Context.Rel.pt -> (Names.Name.t * 't) list
  val prod_applist : Evd.evar_map -> EConstr.constr -> EConstr.constr list -> EConstr.constr
  val nb_prod : Evd.evar_map -> EConstr.constr -> int
  val is_section_variable : Names.Id.t -> bool
  val ids_of_rel_context : ('c, 't) Context.Rel.pt -> Names.Id.t list
  val subst_term : Evd.evar_map -> EConstr.constr -> EConstr.constr -> EConstr.constr
  val global_vars_set_of_decl : Environ.env -> Evd.evar_map -> EConstr.named_declaration -> Names.Id.Set.t
  val vars_of_env: Environ.env -> Names.Id.Set.t
  val ids_of_named_context : ('c, 't) Context.Named.pt -> Names.Id.t list
  val ids_of_context : Environ.env -> Names.Id.t list
  val global_of_constr : Evd.evar_map -> EConstr.constr -> Globnames.global_reference * EConstr.EInstance.t
  val print_named_context : Environ.env -> Pp.t
  val print_constr_env : Environ.env -> Evd.evar_map -> EConstr.constr -> Pp.t
  val clear_named_body : Names.Id.t -> Environ.env -> Environ.env
  val is_Prop : Evd.evar_map -> EConstr.constr -> bool
  val is_Set : Evd.evar_map -> EConstr.constr -> bool
  val is_Type : Evd.evar_map -> EConstr.constr -> bool
  val is_global : Evd.evar_map -> Globnames.global_reference -> EConstr.constr -> bool

  val eq_constr : Evd.evar_map -> EConstr.constr -> EConstr.constr -> bool

  val occur_var_in_decl :
    Environ.env -> Evd.evar_map ->
    Names.Id.t -> EConstr.named_declaration -> bool

  val subst_meta : meta_value_map -> Constr.t -> Constr.t

  val free_rels : Evd.evar_map -> EConstr.constr -> Int.Set.t

  val occur_term : Evd.evar_map -> EConstr.constr -> EConstr.constr -> bool
  [@@ocaml.deprecated "alias of API.Termops.dependent"]

  val replace_term : Evd.evar_map -> EConstr.constr -> EConstr.constr -> EConstr.constr -> EConstr.constr
  val map_named_decl : ('a -> 'b) -> ('a, 'a) Context.Named.Declaration.pt -> ('b, 'b) Context.Named.Declaration.pt
  val map_rel_decl : ('a -> 'b) -> ('a, 'a) Context.Rel.Declaration.pt -> ('b, 'b) Context.Rel.Declaration.pt
  val pr_metaset : Evd.Metaset.t -> Pp.t
  val pr_evar_map : ?with_univs:bool -> int option -> Evd.evar_map -> Pp.t
  val pr_evar_universe_context : UState.t -> Pp.t
end

module Proofview_monad :
sig
  type lazy_msg = unit -> Pp.t
  module Info :
  sig
    type tree
  end
end

module Evarutil :
sig
  val e_new_global : Evd.evar_map ref -> Globnames.global_reference -> EConstr.constr

  val nf_evars_and_universes : Evd.evar_map -> Evd.evar_map * (Constr.t -> Constr.t)
  val nf_evar : Evd.evar_map -> EConstr.constr -> EConstr.constr
  val nf_evar_info : Evd.evar_map -> Evd.evar_info -> Evd.evar_info

  val mk_new_meta : unit -> EConstr.constr

  (** [new_meta] is a generator of unique meta variables *)
  val new_meta : unit -> Constr.metavariable

  val new_Type : ?rigid:Evd.rigid -> Environ.env -> Evd.evar_map -> Evd.evar_map * EConstr.constr
  val new_global : Evd.evar_map -> Globnames.global_reference -> Evd.evar_map * EConstr.constr

  val new_evar :
    Environ.env -> Evd.evar_map -> ?src:Evar_kinds.t Loc.located -> ?filter:Evd.Filter.t ->
    ?candidates:EConstr.constr list -> ?store:Evd.Store.t ->
    ?naming:Misctypes.intro_pattern_naming_expr ->
    ?principal:bool -> EConstr.types -> Evd.evar_map * EConstr.constr

  val new_evar_instance :
    Environ.named_context_val -> Evd.evar_map -> EConstr.types ->
    ?src:Evar_kinds.t Loc.located -> ?filter:Evd.Filter.t -> ?candidates:EConstr.constr list ->
    ?store:Evd.Store.t -> ?naming:Misctypes.intro_pattern_naming_expr ->
    ?principal:bool ->
    EConstr.constr list -> Evd.evar_map * EConstr.constr

  val clear_hyps_in_evi : Environ.env -> Evd.evar_map ref -> Environ.named_context_val ->
                          EConstr.types -> Names.Id.Set.t -> Environ.named_context_val * EConstr.types

  type clear_dependency_error =
    | OccurHypInSimpleClause of Names.Id.t option
    | EvarTypingBreak of Constr.existential

  exception ClearDependencyError of Names.Id.t * clear_dependency_error
  val undefined_evars_of_term : Evd.evar_map -> EConstr.constr -> Evar.Set.t
  val has_undefined_evars : Evd.evar_map -> EConstr.constr -> bool
  val e_new_evar :
      Environ.env -> Evd.evar_map ref -> ?src:Evar_kinds.t Loc.located -> ?filter:Evd.Filter.t ->
      ?candidates:EConstr.constr list -> ?store:Evd.Store.t ->
      ?naming:Misctypes.intro_pattern_naming_expr ->
      ?principal:bool -> EConstr.types -> EConstr.constr
  val new_type_evar :
    Environ.env -> Evd.evar_map -> ?src:Evar_kinds.t Loc.located -> ?filter:Evd.Filter.t ->
    ?naming:Misctypes.intro_pattern_naming_expr -> ?principal:bool -> Evd.rigid ->
    Evd.evar_map * (EConstr.constr * Sorts.t)
  val nf_evars_universes : Evd.evar_map -> Constr.t -> Constr.t
  val safe_evar_value : Evd.evar_map -> Constr.existential -> Constr.t option
  val evd_comb1 : (Evd.evar_map -> 'b -> Evd.evar_map * 'a) -> Evd.evar_map ref -> 'b -> 'a
end

module Proofview :
sig
  type proofview
  type entry
  type +'a tactic
  type telescope =
    | TNil of Evd.evar_map
    | TCons of Environ.env * Evd.evar_map * EConstr.types * (Evd.evar_map -> EConstr.constr -> telescope)

  module NonLogical :
  sig
    type +'a t
    val make : (unit -> 'a) -> 'a t
    val return : 'a -> 'a t
    val ( >> ) : unit t -> 'a t -> 'a t
    val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
    val print_char : char -> unit t
    val print_debug : Pp.t -> unit t
    val print_warning : Pp.t -> unit t
    val print_notice : Pp.t -> unit t
    val print_info : Pp.t -> unit t
    val run : 'a t -> 'a
    type 'a ref
    val ref : 'a -> 'a ref t
    val ( := ) : 'a ref -> 'a -> unit t
    val ( ! ) : 'a ref -> 'a t
    val raise : ?info:Exninfo.info -> exn -> 'a t
    val catch : 'a t -> (Exninfo.iexn -> 'a t) -> 'a t
    val read_line : string t
  end
  val proofview : proofview -> Evar.t list * Evd.evar_map
  val cycle : int -> unit tactic
  val swap : int -> int -> unit tactic
  val revgoals : unit tactic
  val give_up : unit tactic
  val init : Evd.evar_map -> (Environ.env * EConstr.types) list -> entry * proofview
  val shelve : unit tactic
  val tclZERO : ?info:Exninfo.info -> exn -> 'a tactic
  val tclUNIT : 'a -> 'a tactic
  val tclBIND : 'a tactic -> ('a -> 'b tactic) -> 'b tactic
  val tclORELSE : 'a tactic -> (Util.iexn -> 'a tactic) -> 'a tactic
  val tclFOCUS : int -> int -> 'a tactic -> 'a tactic
  val tclEVARMAP : Evd.evar_map tactic
  val tclTHEN : unit tactic -> 'a tactic -> 'a tactic
  val tclLIFT : 'a NonLogical.t -> 'a tactic
  val tclOR : 'a tactic -> (Exninfo.iexn -> 'a tactic) -> 'a tactic
  val tclIFCATCH : 'a tactic -> ('a -> 'b tactic) -> (Exninfo.iexn -> 'b tactic) -> 'b tactic
  val tclINDEPENDENT : unit tactic -> unit tactic
  val tclDISPATCH : unit tactic list -> unit tactic
  val tclEXTEND : unit tactic list -> unit tactic -> unit tactic list -> unit tactic
  val tclBREAK : (Exninfo.iexn -> Exninfo.iexn option) -> 'a tactic -> 'a tactic
  val tclENV : Environ.env tactic
  val tclONCE : 'a tactic -> 'a tactic
  val tclPROGRESS : 'a tactic -> 'a tactic
  val shelve_unifiable : unit tactic
  val apply : Environ.env -> 'a tactic -> proofview -> 'a
                                                     * proofview
                                                     * (bool * Evar.t list * Evar.t list)
                                                     * Proofview_monad.Info.tree
  val numgoals : int tactic
  val with_shelf : 'a tactic -> (Evar.t list * 'a) tactic

  module Unsafe :
  sig
    val tclEVARS : Evd.evar_map -> unit tactic

    val tclGETGOALS : Evar.t list tactic

    val tclSETGOALS : Evar.t list -> unit tactic

    val tclNEWGOALS : Evar.t list -> unit tactic
  end

  module Goal :
  sig
    type 'a t
    val enter : ([ `LZ ] t -> unit tactic) -> unit tactic
    val hyps : 'a t -> EConstr.named_context
    val nf_enter : ([ `NF ] t -> unit tactic) -> unit tactic
    val enter_one : ([ `LZ ] t -> 'a tactic) -> 'a tactic
    val concl : 'a t -> EConstr.constr
    val sigma : 'a t -> Evd.evar_map
    val goal : [ `NF ] t -> Evar.t
    val env : 'a t -> Environ.env
    val assume : 'a t -> [ `NF ] t
  end

  module Notations :
  sig
    val (>>=) : 'a tactic -> ('a -> 'b tactic) -> 'b tactic
    val (<*>) : unit tactic -> 'a tactic -> 'a tactic
    val (<+>) : 'a tactic -> 'a tactic -> 'a tactic
  end
  module V82 :
  sig
    type tac = Evar.t Evd.sigma -> Evar.t list Evd.sigma

    val tactic : tac -> unit tactic

    val of_tactic : 'a tactic -> tac

    val nf_evar_goals : unit tactic

    val wrap_exceptions : (unit -> 'a tactic) -> 'a tactic

    val catchable_exception : exn -> bool
  end
  module Trace :
  sig
    val name_tactic : Proofview_monad.lazy_msg -> 'a tactic -> 'a tactic
    val log : Proofview_monad.lazy_msg -> unit tactic
  end
end

module Ftactic :
sig
  type +'a focus
  type +'a t = 'a focus Proofview.tactic
  val return : 'a -> 'a t
  val run : 'a t -> ('a -> unit Proofview.tactic) -> unit Proofview.tactic
  val enter : ([ `LZ ] Proofview.Goal.t -> 'a t) -> 'a t
  val nf_enter : ([ `NF ] Proofview.Goal.t -> 'a t) -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
  val lift : 'a Proofview.tactic -> 'a t
  val with_env : 'a t -> (Environ.env * 'a) t
  module List :
  sig
    val map : ('a -> 'b t) -> 'a list -> 'b list t
    val map_right : ('a -> 'b t) -> 'a list -> 'b list t
  end
  module Notations :
  sig
    val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
    val (<*>) : unit t -> 'a t -> 'a t
  end
end

module Geninterp :
sig
  module Val :
  sig
    type 'a typ
    type t = Dyn : 'a typ * 'a -> t
    type 'a tag =
                | Base : 'a typ -> 'a tag
                | List : 'a tag -> 'a list tag
                | Opt : 'a tag -> 'a option tag
                | Pair : 'a tag * 'b tag -> ('a * 'b) tag
    val create : string -> 'a typ
    val pr : 'a typ -> Pp.t
    val eq : 'a typ -> 'b typ -> ('a, 'b) CSig.eq option
    val typ_list : t list typ
    val typ_opt : t option typ
    val typ_pair : (t * t) typ
    val repr : 'a typ -> string
    val inject : 'a tag -> 'a -> t
  end
  module TacStore :
  sig
    type t
    type 'a field
    val empty : t
    val field : unit -> 'a field
    val get : t -> 'a field -> 'a option
    val set : t -> 'a field -> 'a -> t
    val remove : t -> 'a field -> t
    val merge : t -> t -> t
  end
  type interp_sign = {
    lfun : Val.t Names.Id.Map.t;
    extra : TacStore.t
  }
  type ('glb, 'top) interp_fun = interp_sign -> 'glb -> 'top Ftactic.t
  val register_interp0 :
    ('raw, 'glb, 'top) Genarg.genarg_type -> ('glb, Val.t) interp_fun -> unit
  val register_val0 : ('raw, 'glb, 'top) Genarg.genarg_type -> 'top Val.tag option -> unit
  val val_tag : 'a Genarg.typed_abstract_argument_type -> 'a Val.tag
  val interp : ('raw, 'glb, 'top) Genarg.genarg_type -> ('glb, Val.t) interp_fun
end

(************************************************************************)
(* End of modules from engine/                                          *)
(************************************************************************)

(************************************************************************)
(* Modules from pretyping/                                              *)
(************************************************************************)

module Ltac_pretype :
sig
open Names
open Glob_term

(** {5 Maps of pattern variables} *)

(** Type [constr_under_binders] is for representing the term resulting
    of a matching. Matching can return terms defined in a some context
    of named binders; in the context, variable names are ordered by
    (<) and referred to by index in the term Thanks to the canonical
    ordering, a matching problem like

    [match ... with [(fun x y => ?p,fun y x => ?p)] => [forall x y => p]]

    will be accepted. Thanks to the reference by index, a matching
    problem like

    [match ... with [(fun x => ?p)] => [forall x => p]]

    will work even if [x] is also the name of an existing goal
    variable.

    Note: we do not keep types in the signature. Besides simplicity,
    the main reason is that it would force to close the signature over
    binders that occur only in the types of effective binders but not
    in the term itself (e.g. for a term [f x] with [f:A -> True] and
    [x:A]).

    On the opposite side, by not keeping the types, we loose
    opportunity to propagate type informations which otherwise would
    not be inferable, as e.g. when matching [forall x, x = 0] with
    pattern [forall x, ?h = 0] and using the solution "x|-h:=x" in
    expression [forall x, h = x] where nothing tells how the type of x
    could be inferred. We also loose the ability of typing ltac
    variables before calling the right-hand-side of ltac matching clauses. *)

type constr_under_binders = Id.t list * EConstr.constr

(** Types of substitutions with or w/o bound variables *)

type patvar_map = EConstr.constr Id.Map.t
type extended_patvar_map = constr_under_binders Id.Map.t

(** A globalised term together with a closure representing the value
    of its free variables. Intended for use when these variables are taken
    from the Ltac environment. *)
type closure = {
  idents:Id.t Id.Map.t;
  typed: constr_under_binders Id.Map.t ;
  untyped:closed_glob_constr Id.Map.t }
and closed_glob_constr = {
  closure: closure;
  term: glob_constr }

(** Ltac variable maps *)
type var_map = constr_under_binders Id.Map.t
type uconstr_var_map = closed_glob_constr Id.Map.t
type unbound_ltac_var_map = Geninterp.Val.t Id.Map.t

type ltac_var_map = {
  ltac_constrs : var_map;
  (** Ltac variables bound to constrs *)
  ltac_uconstrs : uconstr_var_map;
  (** Ltac variables bound to untyped constrs *)
  ltac_idents: Id.t Id.Map.t;
  (** Ltac variables bound to identifiers *)
  ltac_genargs : unbound_ltac_var_map;
  (** Ltac variables bound to other kinds of arguments *)
}

end

module Locusops :
sig
  val clause_with_generic_occurrences : 'a Locus.clause_expr -> bool
  val nowhere : 'a Locus.clause_expr
  val allHypsAndConcl : 'a Locus.clause_expr
  val is_nowhere : 'a Locus.clause_expr -> bool
  val occurrences_map :
    ('a list -> 'b list) -> 'a Locus.occurrences_gen -> 'b Locus.occurrences_gen
  val convert_occs : Locus.occurrences -> bool * int list
  val onConcl : 'a Locus.clause_expr
  val onHyp : 'a -> 'a Locus.clause_expr
end

module Pretype_errors :
sig
  type unification_error
  type subterm_unification_error

  type type_error = (EConstr.t, EConstr.types) Type_errors.ptype_error

  type pretype_error =
    | CantFindCaseType of EConstr.constr
    | ActualTypeNotCoercible of EConstr.unsafe_judgment * EConstr.types * unification_error
    | UnifOccurCheck of Evar.t * EConstr.constr
    | UnsolvableImplicit of Evar.t * Evd.unsolvability_explanation option
    | CannotUnify of EConstr.constr * EConstr.constr * unification_error option
    | CannotUnifyLocal of EConstr.constr * EConstr.constr * EConstr.constr
    | CannotUnifyBindingType of EConstr.constr * EConstr.constr
    | CannotGeneralize of EConstr.constr
    | NoOccurrenceFound of EConstr.constr * Names.Id.t option
    | CannotFindWellTypedAbstraction of EConstr.constr * EConstr.constr list * (Environ.env * type_error) option
    | WrongAbstractionType of Names.Name.t * EConstr.constr * EConstr.types * EConstr.types
    | AbstractionOverMeta of Names.Name.t * Names.Name.t
    | NonLinearUnification of Names.Name.t * EConstr.constr
    | VarNotFound of Names.Id.t
    | UnexpectedType of EConstr.constr * EConstr.constr
    | NotProduct of EConstr.constr
    | TypingError of type_error
    | CannotUnifyOccurrences of subterm_unification_error
    | UnsatisfiableConstraints of
        (Evar.t * Evar_kinds.t) option * Evar.Set.t option

  exception PretypeError of Environ.env * Evd.evar_map * pretype_error
  val error_var_not_found : ?loc:Loc.t -> Names.Id.t -> 'b
  val precatchable_exception : exn -> bool
end

module Reductionops :
sig
  type local_reduction_function = Evd.evar_map -> EConstr.constr -> EConstr.constr

  type reduction_function = Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr

  type local_stack_reduction_function =
    Evd.evar_map -> EConstr.constr -> EConstr.constr * EConstr.constr list

  type e_reduction_function = Environ.env -> Evd.evar_map -> EConstr.constr -> Evd.evar_map * EConstr.constr
  type state

  val clos_whd_flags : CClosure.RedFlags.reds -> reduction_function
  val nf_beta : local_reduction_function
  val nf_betaiota : local_reduction_function
  val splay_prod : Environ.env ->  Evd.evar_map -> EConstr.constr ->
                   (Names.Name.t * EConstr.constr) list * EConstr.constr
  val splay_prod_n : Environ.env ->  Evd.evar_map -> int -> EConstr.constr -> EConstr.rel_context * EConstr.constr
  val whd_all :  reduction_function
  val whd_beta : local_reduction_function

  val whd_betaiotazeta : local_reduction_function

  val whd_betaiota_stack : local_stack_reduction_function

  val clos_norm_flags : CClosure.RedFlags.reds -> reduction_function
  val is_conv : ?reds:Names.transparent_state -> Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr -> bool
  val beta_applist : Evd.evar_map -> EConstr.constr * EConstr.constr list -> EConstr.constr
  val sort_of_arity : Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.ESorts.t
  val is_conv_leq : ?reds:Names.transparent_state -> Environ.env ->  Evd.evar_map -> EConstr.constr -> EConstr.constr -> bool
  val whd_betaiota : local_reduction_function
  val is_arity : Environ.env ->  Evd.evar_map -> EConstr.constr -> bool
  val nf_evar : Evd.evar_map -> EConstr.constr -> EConstr.constr
  val nf_meta : Evd.evar_map -> EConstr.constr -> EConstr.constr
  val hnf_prod_appvect : Environ.env ->  Evd.evar_map -> EConstr.constr -> EConstr.constr array -> EConstr.constr
  val pr_state : state -> Pp.t
  module Stack :
  sig
    type 'a t
    val pr : ('a -> Pp.t) -> 'a t -> Pp.t
  end
  module Cst_stack :
  sig
    type t
    val pr : t -> Pp.t
  end
end

module Inductiveops :
sig
  type inductive_family
  type inductive_type =
    | IndType of inductive_family * EConstr.constr list
  type constructor_summary =
    {
      cs_cstr : Constr.pconstructor;
      cs_params : Constr.t list;
      cs_nargs : int;
      cs_args : Context.Rel.t;
      cs_concl_realargs : Constr.t array;
    }

  val arities_of_constructors : Environ.env -> Constr.pinductive -> Constr.types array
  val constructors_nrealargs_env : Environ.env -> Names.inductive -> int array
  val constructor_nallargs_env : Environ.env -> Names.constructor -> int

  val inductive_nparams : Names.inductive -> int

  val inductive_nparamdecls : Names.inductive -> int

  val type_of_constructors : Environ.env -> Constr.pinductive -> Constr.types array
  val find_mrectype : Environ.env -> Evd.evar_map -> EConstr.types -> (Names.inductive * EConstr.EInstance.t) * EConstr.constr list
  val mis_is_recursive :
    Names.inductive * Declarations.mutual_inductive_body * Declarations.one_inductive_body -> bool
  val nconstructors : Names.inductive -> int
  val find_rectype : Environ.env -> Evd.evar_map -> EConstr.types -> inductive_type
  val get_constructors : Environ.env -> inductive_family -> constructor_summary array
  val dest_ind_family : inductive_family -> Names.inductive Univ.puniverses * Constr.t list
  val find_inductive   : Environ.env -> Evd.evar_map -> EConstr.types -> (Names.inductive * EConstr.EInstance.t) * Constr.t list
  val type_of_inductive : Environ.env -> Constr.pinductive -> Constr.types
end

module Impargs :
sig
  type implicit_status
  type implicit_side_condition
  type implicits_list = implicit_side_condition * implicit_status list
  type manual_explicitation = Constrexpr.explicitation * (bool * bool * bool)
  type manual_implicits = manual_explicitation list
  val is_status_implicit : implicit_status -> bool
  val name_of_implicit : implicit_status -> Names.Id.t
  val implicits_of_global : Globnames.global_reference -> implicits_list list
  val declare_manual_implicits : bool -> Globnames.global_reference -> ?enriching:bool ->
                                 manual_implicits list -> unit
  val is_implicit_args : unit -> bool
  val is_strict_implicit_args : unit -> bool
  val is_contextual_implicit_args : unit -> bool
  val make_implicit_args : bool -> unit
  val make_strict_implicit_args : bool -> unit
  val make_contextual_implicit_args : bool -> unit
end

module Retyping :  (* reconstruct the type of a term knowing that it was already typechecked *)
sig
  val get_type_of : ?polyprop:bool -> ?lax:bool -> Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.types
  val get_sort_family_of : ?truncation_style:bool -> ?polyprop:bool -> Environ.env -> Evd.evar_map -> EConstr.types -> Sorts.family
  val expand_projection : Environ.env -> Evd.evar_map -> Names.Projection.t -> EConstr.constr -> EConstr.constr list -> EConstr.constr
  val get_sort_of :
    ?polyprop:bool -> Environ.env -> Evd.evar_map -> EConstr.types -> Sorts.t
end

module Find_subterm :
sig
  val error_invalid_occurrence : int list -> 'a
end

module Evarsolve :
sig
  val refresh_universes :
    ?status:Evd.rigid -> ?onlyalg:bool -> ?refreshset:bool -> bool option ->
    Environ.env -> Evd.evar_map -> EConstr.types -> Evd.evar_map * EConstr.types
end

module Recordops :
sig

  type cs_pattern =
                  | Const_cs of Globnames.global_reference
                  | Prod_cs
                  | Sort_cs of Sorts.family
                  | Default_cs

  type obj_typ = {
        o_DEF : Constr.t;
        o_CTX : Univ.AUContext.t;
        o_INJ : int option;      (** position of trivial argument *)
        o_TABS : Constr.t list;    (** ordered *)
        o_TPARAMS : Constr.t list; (** ordered *)
        o_NPARAMS : int;
        o_TCOMPS : Constr.t list }

  val lookup_projections : Names.inductive -> Names.Constant.t option list
  val lookup_canonical_conversion : (Globnames.global_reference * cs_pattern) -> Constr.t * obj_typ
  val find_projection_nparams : Globnames.global_reference -> int
end

module Evarconv :
sig
  val e_conv : Environ.env -> ?ts:Names.transparent_state -> Evd.evar_map ref -> EConstr.constr -> EConstr.constr -> bool
  val the_conv_x : Environ.env -> ?ts:Names.transparent_state -> EConstr.constr -> EConstr.constr -> Evd.evar_map -> Evd.evar_map
  val the_conv_x_leq : Environ.env -> ?ts:Names.transparent_state -> EConstr.constr -> EConstr.constr -> Evd.evar_map -> Evd.evar_map
  val solve_unif_constraints_with_heuristics : Environ.env -> ?ts:Names.transparent_state -> Evd.evar_map -> Evd.evar_map
end

module Typing :
sig
  val e_sort_of : Environ.env -> Evd.evar_map ref -> EConstr.types -> Sorts.t

  val type_of : ?refresh:bool -> Environ.env -> Evd.evar_map -> EConstr.constr -> Evd.evar_map * EConstr.types
  val e_solve_evars : Environ.env -> Evd.evar_map ref -> EConstr.constr -> EConstr.constr

  val unsafe_type_of : Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.types

  val e_check : Environ.env -> Evd.evar_map ref -> EConstr.constr -> EConstr.types -> unit

  val e_type_of : ?refresh:bool -> Environ.env -> Evd.evar_map ref -> EConstr.constr -> EConstr.types
end

module Miscops :
sig
  val map_red_expr_gen : ('a -> 'd) -> ('b -> 'e) -> ('c -> 'f) ->
                         ('a,'b,'c) Genredexpr.red_expr_gen -> ('d,'e,'f) Genredexpr.red_expr_gen
  val map_cast_type : ('a -> 'b) -> 'a Misctypes.cast_type -> 'b Misctypes.cast_type
end

module Glob_ops :
sig
  val map_glob_constr_left_to_right : (Glob_term.glob_constr -> Glob_term.glob_constr) -> Glob_term.glob_constr -> Glob_term.glob_constr
  val loc_of_glob_constr : Glob_term.glob_constr -> Loc.t option
  val glob_constr_eq : Glob_term.glob_constr -> Glob_term.glob_constr -> bool
  val bound_glob_vars : Glob_term.glob_constr -> Names.Id.Set.t

  (** Conversion from glob_constr to cases pattern, if possible

    Take the current alias as parameter,
    @raise Not_found if translation is impossible *)
  val cases_pattern_of_glob_constr : Names.Name.t -> Glob_term.glob_constr -> Glob_term.cases_pattern
  val map_glob_constr :
    (Glob_term.glob_constr -> Glob_term.glob_constr) -> Glob_term.glob_constr -> Glob_term.glob_constr

  val empty_lvar : Ltac_pretype.ltac_var_map

end

module Redops :
sig
  val all_flags : 'a Genredexpr.glob_red_flag
  val make_red_flag : 'a Genredexpr.red_atom list -> 'a Genredexpr.glob_red_flag
end

module Patternops :
sig
  val pattern_of_glob_constr : Glob_term.glob_constr -> Names.Id.t list * Pattern.constr_pattern
  val subst_pattern : Mod_subst.substitution -> Pattern.constr_pattern -> Pattern.constr_pattern
  val pattern_of_constr : Environ.env -> Evd.evar_map -> Constr.t -> Pattern.constr_pattern
  val instantiate_pattern : Environ.env ->
    Evd.evar_map -> Ltac_pretype.extended_patvar_map ->
    Pattern.constr_pattern -> Pattern.constr_pattern
end

module Constr_matching :
sig
  val special_meta : Constr.metavariable

  type binding_bound_vars = Names.Id.Set.t
  type bound_ident_map = Names.Id.t Names.Id.Map.t
  val is_matching : Environ.env -> Evd.evar_map -> Pattern.constr_pattern -> EConstr.constr -> bool
  val extended_matches :
    Environ.env -> Evd.evar_map -> binding_bound_vars * Pattern.constr_pattern ->
    EConstr.constr -> bound_ident_map * Ltac_pretype.extended_patvar_map
  exception PatternMatchingFailure
  type matching_result =
    { m_sub : bound_ident_map * Ltac_pretype.patvar_map;
      m_ctx : EConstr.constr }
  val match_subterm_gen : Environ.env -> Evd.evar_map ->
                          bool ->
                          binding_bound_vars * Pattern.constr_pattern -> EConstr.constr ->
                          matching_result IStream.t
  val matches : Environ.env -> Evd.evar_map -> Pattern.constr_pattern -> EConstr.constr -> Ltac_pretype.patvar_map
end

module Tacred :
sig
  val try_red_product : Reductionops.reduction_function
  val simpl : Reductionops.reduction_function
  val unfoldn :
    (Locus.occurrences * Names.evaluable_global_reference) list ->  Reductionops.reduction_function
  val hnf_constr : Reductionops.reduction_function
  val red_product : Reductionops.reduction_function
  val is_evaluable : Environ.env -> Names.evaluable_global_reference -> bool
  val evaluable_of_global_reference :
    Environ.env -> Globnames.global_reference -> Names.evaluable_global_reference
  val error_not_evaluable : Globnames.global_reference -> 'a
  val reduce_to_quantified_ref :
    Environ.env ->  Evd.evar_map -> Globnames.global_reference -> EConstr.types -> EConstr.types
  val pattern_occs : (Locus.occurrences * EConstr.constr) list -> Reductionops.e_reduction_function
  val cbv_norm_flags : CClosure.RedFlags.reds -> Reductionops.reduction_function
end

(* XXX: Located manually from intf *)
module Tok :
sig

  type t =
  | KEYWORD of string
  | PATTERNIDENT of string
  | IDENT of string
  | FIELD of string
  | INT of string
  | STRING of string
  | LEFTQMARK
  | BULLET of string
  | EOI

end

module CLexer :
sig
  val add_keyword : string -> unit
  val remove_keyword : string -> unit
  val is_keyword : string -> bool
  val keywords : unit -> CString.Set.t

  type keyword_state
  val set_keyword_state : keyword_state -> unit
  val get_keyword_state : unit -> keyword_state

  val check_ident : string -> unit
  val terminal : string -> Tok.t

  include Grammar.GLexerType with type te = Tok.t
end

module Extend :
sig

  type gram_assoc = NonA | RightA | LeftA

  type gram_position =
    | First
    | Last
    | Before of string
    | After of string
    | Level of string

  type production_level =
    | NextLevel
    | NumLevel of int

  type 'a entry = 'a Grammar.GMake(CLexer).Entry.e

  type 'a user_symbol =
    | Ulist1 of 'a user_symbol
    | Ulist1sep of 'a user_symbol * string
    | Ulist0 of 'a user_symbol
    | Ulist0sep of 'a user_symbol * string
    | Uopt of 'a user_symbol
    | Uentry of 'a
    | Uentryl of 'a * int

  type ('self, 'a) symbol =
    | Atoken : Tok.t -> ('self, string) symbol
    | Alist1 : ('self, 'a) symbol -> ('self, 'a list) symbol
    | Alist1sep : ('self, 'a) symbol * ('self, _) symbol -> ('self, 'a list) symbol
    | Alist0 : ('self, 'a) symbol -> ('self, 'a list) symbol
    | Alist0sep : ('self, 'a) symbol * ('self, _) symbol -> ('self, 'a list) symbol
    | Aopt : ('self, 'a) symbol -> ('self, 'a option) symbol
    | Aself : ('self, 'self) symbol
    | Anext : ('self, 'self) symbol
    | Aentry : 'a entry -> ('self, 'a) symbol
    | Aentryl : 'a entry * int -> ('self, 'a) symbol
    | Arules : 'a rules list -> ('self, 'a) symbol

  and ('self, _, 'r) rule =
    | Stop : ('self, 'r, 'r) rule
    | Next : ('self, 'a, 'r) rule * ('self, 'b) symbol -> ('self, 'b -> 'a, 'r) rule

  and ('a, 'r) norec_rule = { norec_rule : 's. ('s, 'a, 'r) rule }

  and 'a rules =
    | Rules : ('act, Loc.t -> 'a) norec_rule * 'act -> 'a rules

  type ('lev,'pos) constr_entry_key_gen =
    | ETName | ETReference | ETBigint
    | ETBinder of bool
    | ETConstr of ('lev * 'pos)
    | ETPattern
    | ETOther of string * string
    | ETConstrList of ('lev * 'pos) * Tok.t list
    | ETBinderList of bool * Tok.t list

  type side = Left | Right

  type production_position =
    | BorderProd of side * gram_assoc option
    | InternalProd

  type constr_prod_entry_key =
    (production_level,production_position) constr_entry_key_gen

  type simple_constr_prod_entry_key =
    (production_level,unit) constr_entry_key_gen

  type 'a production_rule =
    | Rule : ('a, 'act, Loc.t -> 'a) rule * 'act -> 'a production_rule

  type 'a single_extend_statment =
    string option *
    (** Level *)
    gram_assoc option *
    (** Associativity *)
    'a production_rule list
  (** Symbol list with the interpretation function *)

  type 'a extend_statment =
    gram_position option *
    'a single_extend_statment list
end

(* XXX: Located manually from intf *)
module Vernacexpr :
sig
  open Misctypes
  open Constrexpr
  open Libnames

  type instance_flag  = bool option
  type coercion_flag = bool
  type inductive_flag = Declarations.recursivity_kind
  type lname = Names.Name.t Loc.located
  type lident = Names.Id.t Loc.located
  type opacity_flag =
                    | Opaque
                    | Transparent
  type locality_flag = bool
  type inductive_kind =
    | Inductive_kw | CoInductive | Variant | Record | Structure | Class of bool

  type vernac_type =
                   | VtStartProof of vernac_start
                   | VtSideff of vernac_sideff_type
                   | VtQed of vernac_qed_type
                   | VtProofStep of proof_step
                   | VtProofMode of string
                   | VtQuery of vernac_part_of_script * Feedback.route_id
                   | VtMeta
                   | VtUnknown
   and vernac_qed_type =
     | VtKeep
     | VtKeepAsAxiom
     | VtDrop
   and vernac_start = string * opacity_guarantee * Names.Id.t list
   and vernac_sideff_type = Names.Id.t list
   and vernac_part_of_script = bool
   and opacity_guarantee =
     | GuaranteesOpacity
     | Doesn'tGuaranteeOpacity
   and proof_step = {
     parallel : [ `Yes of solving_tac * anon_abstracting_tac | `No ];
     proof_block_detection : proof_block_name option
   }
   and solving_tac = bool
   and anon_abstracting_tac = bool
   and proof_block_name = string

  type vernac_when =
    | VtNow
    | VtLater

  type verbose_flag = bool

  type universe_decl_expr = (lident list, Misctypes.glob_constraint list) gen_universe_decl

  type ident_decl = lident * universe_decl_expr option

  type lstring
  type 'a with_coercion = coercion_flag * 'a
  type scope_name = string
  type decl_notation = lstring * Constrexpr.constr_expr * scope_name option
  type constructor_expr = (lident * Constrexpr.constr_expr) with_coercion
  type 'a with_notation = 'a * decl_notation list

  type local_decl_expr =
    | AssumExpr of lname * Constrexpr.constr_expr
    | DefExpr of lname * Constrexpr.constr_expr * Constrexpr.constr_expr option

  type 'a with_priority = 'a * int option
  type 'a with_instance = instance_flag * 'a
  type constructor_list_or_record_decl_expr =
    | Constructors of constructor_expr list
    | RecordDecl of lident option * local_decl_expr with_instance with_priority with_notation list

  type inductive_expr = ident_decl with_coercion * Constrexpr.local_binder_expr list * Constrexpr.constr_expr option * inductive_kind * constructor_list_or_record_decl_expr

  type syntax_modifier =
    | SetItemLevel of string list * Extend.production_level
    | SetLevel of int
    | SetAssoc of Extend.gram_assoc
    | SetEntryType of string * Extend.simple_constr_prod_entry_key
    | SetOnlyParsing
    | SetOnlyPrinting
    | SetCompatVersion of Flags.compat_version
    | SetFormat of string * string Loc.located

  type class_rawexpr = FunClass | SortClass | RefClass of reference or_by_notation

  type typeclass_constraint = (Names.Name.t Loc.located * universe_decl_expr option) * Decl_kinds.binding_kind * constr_expr

  type definition_expr =
    | ProveBody of local_binder_expr list * constr_expr
    | DefineBody of local_binder_expr list * Genredexpr.raw_red_expr option * constr_expr
                    * constr_expr option
  type proof_expr =
    ident_decl option * (local_binder_expr list * constr_expr)

  type proof_end =
    | Admitted
    | Proved of opacity_flag * lident option

  type fixpoint_expr = ident_decl * (Names.Id.t Loc.located option * Constrexpr.recursion_order_expr) * Constrexpr.local_binder_expr list * Constrexpr.constr_expr * Constrexpr.constr_expr option

  type cofixpoint_expr

  type scheme

  type section_subset_expr

  type module_binder

  type vernac_argument_status
  type vernac_implicit_status
  type module_ast_inl
  type extend_name = string * int
  type simple_binder
  type option_value
  type showable
  type bullet
  type comment
  type register_kind
  type locatable
  type search_restriction
  type searchable
  type printable
  type option_ref_value
  type onlyparsing_flag
  type reference_or_constr

  type hint_mode

  type 'a hint_info_gen =
    { hint_priority : int option;
      hint_pattern : 'a option }

  type hint_info_expr = Constrexpr.constr_pattern_expr hint_info_gen

  type hints_expr =
    | HintsResolve of (hint_info_expr * bool * reference_or_constr) list
    | HintsImmediate of reference_or_constr list
    | HintsUnfold of Libnames.reference list
    | HintsTransparency of Libnames.reference list * bool
    | HintsMode of Libnames.reference * hint_mode list
    | HintsConstructors of Libnames.reference list
    | HintsExtern of int * Constrexpr.constr_expr option * Genarg.raw_generic_argument

  type 'a module_signature =
    | Enforce of 'a (** ... : T *)
    | Check of 'a list (** ... <: T1 <: T2, possibly empty *)

  type inline =
    | NoInline
    | DefaultInline
    | InlineAt of int

  type cumulative_inductive_parsing_flag =
    | GlobalCumulativity
    | GlobalNonCumulativity
    | LocalCumulativity
    | LocalNonCumulativity

  type vernac_expr =
  | VernacLoad of verbose_flag * string
  | VernacTime of vernac_expr Loc.located
  | VernacRedirect of string * vernac_expr Loc.located
  | VernacTimeout of int * vernac_expr
  | VernacFail of vernac_expr
  | VernacSyntaxExtension of bool * (lstring * syntax_modifier list)
  | VernacOpenCloseScope of bool * scope_name
  | VernacDelimiters of scope_name * string option
  | VernacBindScope of scope_name * class_rawexpr list
  | VernacInfix of (lstring * syntax_modifier list) *
      Constrexpr.constr_expr * scope_name option
  | VernacNotation of
      Constrexpr.constr_expr * (lstring * syntax_modifier list) *
      scope_name option
  | VernacNotationAddFormat of string * string * string
  | VernacDefinition of (Decl_kinds.discharge * Decl_kinds.definition_object_kind) * ident_decl * definition_expr
  | VernacStartTheoremProof of Decl_kinds.theorem_kind * proof_expr list
  | VernacEndProof of proof_end
  | VernacExactProof of Constrexpr.constr_expr
  | VernacAssumption of (Decl_kinds.discharge * Decl_kinds.assumption_object_kind) *
      inline * (ident_decl list * Constrexpr.constr_expr) with_coercion list
  | VernacInductive of cumulative_inductive_parsing_flag * Decl_kinds.private_flag * inductive_flag * (inductive_expr * decl_notation list) list
  | VernacFixpoint of
      Decl_kinds.discharge * (fixpoint_expr * decl_notation list) list
  | VernacCoFixpoint of
      Decl_kinds.discharge * (cofixpoint_expr * decl_notation list) list
  | VernacScheme of (lident option * scheme) list
  | VernacCombinedScheme of lident * lident list
  | VernacUniverse of lident list
  | VernacConstraint of (Misctypes.glob_level * Univ.constraint_type * Misctypes.glob_level) list
  | VernacBeginSection of lident
  | VernacEndSegment of lident
  | VernacRequire of
      Libnames.reference option * bool option * Libnames.reference list
  | VernacImport of bool * Libnames.reference list
  | VernacCanonical of Libnames.reference Misctypes.or_by_notation
  | VernacCoercion of Libnames.reference Misctypes.or_by_notation *
      class_rawexpr * class_rawexpr
  | VernacIdentityCoercion of lident *
      class_rawexpr * class_rawexpr
  | VernacNameSectionHypSet of lident * section_subset_expr
  | VernacInstance of
      bool *
      Constrexpr.local_binder_expr list *
        typeclass_constraint *
          (bool * Constrexpr.constr_expr) option *
      hint_info_expr
  | VernacContext of Constrexpr.local_binder_expr list
  | VernacDeclareInstances of
    (Libnames.reference * hint_info_expr) list
  | VernacDeclareClass of Libnames.reference
  | VernacDeclareModule of bool option * lident *
      module_binder list * module_ast_inl
  | VernacDefineModule of bool option * lident * module_binder list *
      module_ast_inl module_signature * module_ast_inl list
  | VernacDeclareModuleType of lident *
      module_binder list * module_ast_inl list * module_ast_inl list
  | VernacInclude of module_ast_inl list
  | VernacSolveExistential of int * Constrexpr.constr_expr
  | VernacAddLoadPath of bool * string * Names.DirPath.t option
  | VernacRemoveLoadPath of string
  | VernacAddMLPath of bool * string
  | VernacDeclareMLModule of string list
  | VernacChdir of string option
  | VernacWriteState of string
  | VernacRestoreState of string
  | VernacResetName of lident
  | VernacResetInitial
  | VernacBack of int
  | VernacBackTo of int
  | VernacCreateHintDb of string * bool
  | VernacRemoveHints of string list * Libnames.reference list
  | VernacHints of string list * hints_expr
  | VernacSyntacticDefinition of Names.Id.t Loc.located * (Names.Id.t list * Constrexpr.constr_expr) *
      onlyparsing_flag
  | VernacDeclareImplicits of Libnames.reference Misctypes.or_by_notation *
                                (Constrexpr.explicitation * bool * bool) list list
  | VernacArguments of Libnames.reference Misctypes.or_by_notation *
      vernac_argument_status list *
        (Names.Name.t * vernac_implicit_status) list list *
      int option *
        [ `ReductionDontExposeCase | `ReductionNeverUnfold | `Rename |
          `ExtraScopes | `Assert | `ClearImplicits | `ClearScopes |
          `DefaultImplicits ] list
  | VernacArgumentsScope of Libnames.reference Misctypes.or_by_notation *
      scope_name option list
  | VernacReserve of simple_binder list
  | VernacGeneralizable of (lident list) option
  | VernacSetOpacity of (Conv_oracle.level * Libnames.reference Misctypes.or_by_notation list)
  | VernacSetStrategy of
      (Conv_oracle.level * Libnames.reference Misctypes.or_by_notation list) list
  | VernacUnsetOption of Goptions.option_name
  | VernacSetOption of Goptions.option_name * option_value
  | VernacSetAppendOption of Goptions.option_name * string
  | VernacAddOption of Goptions.option_name * option_ref_value list
  | VernacRemoveOption of Goptions.option_name * option_ref_value list
  | VernacMemOption of Goptions.option_name * option_ref_value list
  | VernacPrintOption of Goptions.option_name
  | VernacCheckMayEval of Genredexpr.raw_red_expr option * goal_selector option * Constrexpr.constr_expr
  | VernacGlobalCheck of Constrexpr.constr_expr
  | VernacDeclareReduction of string * Genredexpr.raw_red_expr
  | VernacPrint of printable
  | VernacSearch of searchable * goal_selector option * search_restriction
  | VernacLocate of locatable
  | VernacRegister of lident * register_kind
  | VernacComments of comment list
  | VernacGoal of Constrexpr.constr_expr
  | VernacAbort of lident option
  | VernacAbortAll
  | VernacRestart
  | VernacUndo of int
  | VernacUndoTo of int
  | VernacBacktrack of int*int*int
  | VernacFocus of int option
  | VernacUnfocus
  | VernacUnfocused
  | VernacBullet of bullet
  | VernacSubproof of int option
  | VernacEndSubproof
  | VernacShow of showable
  | VernacCheckGuard
  | VernacProof of Genarg.raw_generic_argument option * section_subset_expr option
  | VernacProofMode of string
  | VernacToplevelControl of exn
  | VernacExtend of extend_name * Genarg.raw_generic_argument list
  | VernacProgram of vernac_expr
  | VernacPolymorphic of bool * vernac_expr
  | VernacLocal of bool * vernac_expr
  and goal_selector =
    | SelectNth of int
    | SelectList of (int * int) list
    | SelectId of Names.Id.t
    | SelectAll
  and vernac_classification = vernac_type * vernac_when
  and one_inductive_expr =
    ident_decl * Constrexpr.local_binder_expr list * Constrexpr.constr_expr option * constructor_expr list
end
(* XXX: end of moved from intf *)

module Typeclasses :
sig
  type typeclass = {
    cl_univs : Univ.AUContext.t;
    cl_impl : Globnames.global_reference;
    cl_context : (Globnames.global_reference * bool) option list * Context.Rel.t;
    cl_props : Context.Rel.t;
    cl_projs : (Names.Name.t * (direction * Vernacexpr.hint_info_expr) option
                * Names.Constant.t option) list;
    cl_strict : bool;
    cl_unique : bool;
  }
  and direction

  type instance
  type evar_filter = Evar.t -> Evar_kinds.t -> bool

  val resolve_typeclasses : ?fast_path:bool -> ?filter:evar_filter -> ?unique:bool ->
                            ?split:bool -> ?fail:bool -> Environ.env -> Evd.evar_map -> Evd.evar_map
  val set_resolvable : Evd.Store.t -> bool -> Evd.Store.t
  val resolve_one_typeclass : ?unique:bool -> Environ.env -> Evd.evar_map -> EConstr.types -> Evd.evar_map * EConstr.constr
  val class_info : Globnames.global_reference -> typeclass
  val mark_resolvables : ?filter:evar_filter -> Evd.evar_map -> Evd.evar_map
  val add_instance : instance -> unit
  val new_instance : typeclass -> Vernacexpr.hint_info_expr -> bool -> Decl_kinds.polymorphic ->
                     Globnames.global_reference -> instance
end

module Classops :
sig
  type coe_index
  type inheritance_path = coe_index list
  type cl_index

  val hide_coercion : Globnames.global_reference -> int option
  val lookup_path_to_sort_from : Environ.env -> Evd.evar_map -> EConstr.types ->
                                 EConstr.types * inheritance_path
  val get_coercion_value : coe_index -> Constr.t
  val coercions : unit -> coe_index list
  val pr_cl_index : cl_index -> Pp.t
end

module Detyping :
sig
  type 'a delay =
  | Now : 'a delay
  | Later : [ `thunk ] delay
  val print_universes : bool ref
  val print_evar_arguments : bool ref
  val detype : 'a delay -> ?lax:bool -> bool -> Names.Id.Set.t -> Environ.env -> Evd.evar_map -> EConstr.constr -> 'a Glob_term.glob_constr_g
  val subst_glob_constr : Mod_subst.substitution -> Glob_term.glob_constr -> Glob_term.glob_constr
  val set_detype_anonymous : (?loc:Loc.t -> int -> Names.Id.t) -> unit
end

module Indrec :
sig
  type dep_flag = bool
  val lookup_eliminator : Names.inductive -> Sorts.family -> Globnames.global_reference
  val build_case_analysis_scheme : Environ.env -> Evd.evar_map -> Constr.pinductive ->
                                   dep_flag -> Sorts.family -> Evd.evar_map * Constr.t
  val make_elimination_ident : Names.Id.t -> Sorts.family -> Names.Id.t
  val build_mutual_induction_scheme :
    Environ.env -> Evd.evar_map -> (Constr.pinductive * dep_flag * Sorts.family) list -> Evd.evar_map * Constr.t list
  val build_case_analysis_scheme_default : Environ.env -> Evd.evar_map -> Constr.pinductive ->
      Sorts.family -> Evd.evar_map * Constr.t
end

module Pretyping :
sig
  type typing_constraint =
    | OfType of EConstr.types
    | IsType
    | WithoutTypeConstraint

  type inference_hook = Environ.env -> Evd.evar_map -> Evar.t -> Evd.evar_map * EConstr.constr

  type inference_flags = {
      use_typeclasses : bool;
      solve_unification_constraints : bool;
      use_hook : inference_hook option;
      fail_evar : bool;
      expand_evars : bool
    }

  val understand_ltac : inference_flags ->
                        Environ.env -> Evd.evar_map -> Ltac_pretype.ltac_var_map ->
                        typing_constraint -> Glob_term.glob_constr -> Evd.evar_map * EConstr.t
  val understand_tcc : ?flags:inference_flags -> Environ.env -> Evd.evar_map ->
                       ?expected_type:typing_constraint -> Glob_term.glob_constr -> Evd.evar_map * EConstr.constr
  val understand : ?flags:inference_flags -> ?expected_type:typing_constraint ->
                   Environ.env -> Evd.evar_map -> Glob_term.glob_constr -> Constr.t Evd.in_evar_universe_context
  val check_evars : Environ.env -> Evd.evar_map -> Evd.evar_map -> EConstr.constr -> unit
  val register_constr_interp0 :
    ('r, 'g, 't) Genarg.genarg_type ->
    (Ltac_pretype.unbound_ltac_var_map -> Environ.env -> Evd.evar_map -> EConstr.types -> 'g -> EConstr.constr * Evd.evar_map) -> unit
  val all_and_fail_flags : inference_flags
  val ise_pretype_gen :
    inference_flags -> Environ.env -> Evd.evar_map ->
    Ltac_pretype.ltac_var_map -> typing_constraint -> Glob_term.glob_constr -> Evd.evar_map * EConstr.constr
end

module Unification :
sig
  type core_unify_flags = {
    modulo_conv_on_closed_terms : Names.transparent_state option;
    use_metas_eagerly_in_conv_on_closed_terms : bool;
    use_evars_eagerly_in_conv_on_closed_terms : bool;
    modulo_delta : Names.transparent_state;
    modulo_delta_types : Names.transparent_state;
    check_applied_meta_types : bool;
    use_pattern_unification : bool;
    use_meta_bound_pattern_unification : bool;
    frozen_evars : Evar.Set.t;
    restrict_conv_on_strict_subterms : bool;
    modulo_betaiota : bool;
    modulo_eta : bool;
  }
  type unify_flags =
    {
      core_unify_flags : core_unify_flags;
      merge_unify_flags : core_unify_flags;
      subterm_unify_flags : core_unify_flags;
      allow_K_in_toplevel_higher_order_unification : bool;
      resolve_evars : bool
    }
  val default_no_delta_unify_flags : unit -> unify_flags
  val w_unify : Environ.env -> Evd.evar_map -> Reduction.conv_pb -> ?flags:unify_flags -> EConstr.constr -> EConstr.constr -> Evd.evar_map
  val elim_flags : unit -> unify_flags
  val w_unify_to_subterm :
    Environ.env -> Evd.evar_map -> ?flags:unify_flags -> EConstr.constr * EConstr.constr -> Evd.evar_map * EConstr.constr
end

module Univdecls :
sig
  type universe_decl =
    (Names.Id.t Loc.located list, Univ.Constraint.t) Misctypes.gen_universe_decl

  val interp_univ_decl : Environ.env -> Vernacexpr.universe_decl_expr ->
                         Evd.evar_map * universe_decl
  val interp_univ_decl_opt : Environ.env -> Vernacexpr.universe_decl_expr option ->
                             Evd.evar_map * universe_decl
  val default_univ_decl : universe_decl
end

(************************************************************************)
(* End of modules from pretyping/                                       *)
(************************************************************************)

(************************************************************************)
(* Modules from interp/                                              *)
(************************************************************************)

module Tactypes :
sig
  type glob_constr_and_expr = Glob_term.glob_constr * Constrexpr.constr_expr option
  type glob_constr_pattern_and_expr = Names.Id.Set.t * glob_constr_and_expr * Pattern.constr_pattern
  type 'a delayed_open = Environ.env -> Evd.evar_map -> Evd.evar_map * 'a
  type delayed_open_constr = EConstr.constr delayed_open
  type delayed_open_constr_with_bindings = EConstr.constr Misctypes.with_bindings delayed_open
  type intro_pattern = delayed_open_constr Misctypes.intro_pattern_expr Loc.located
  type intro_patterns = delayed_open_constr Misctypes.intro_pattern_expr Loc.located list
  type intro_pattern_naming = Misctypes.intro_pattern_naming_expr Loc.located
  type or_and_intro_pattern = delayed_open_constr Misctypes.or_and_intro_pattern_expr Loc.located
end

module Genintern :
sig
  open Genarg

  module Store : Store.S

  type glob_sign = {
    ltacvars : Names.Id.Set.t;
    genv : Environ.env;
    extra : Store.t;
  }

  val empty_glob_sign : Environ.env -> glob_sign

  type ('raw, 'glb) intern_fun = glob_sign -> 'raw -> glob_sign * 'glb


  val generic_intern : (raw_generic_argument, glob_generic_argument) intern_fun

  type 'glb subst_fun = Mod_subst.substitution -> 'glb -> 'glb
  val generic_substitute : Genarg.glob_generic_argument subst_fun

  type 'glb ntn_subst_fun = Tactypes.glob_constr_and_expr Names.Id.Map.t -> 'glb -> 'glb

  val register_intern0 : ('raw, 'glb, 'top) genarg_type ->
    ('raw, 'glb) intern_fun -> unit

  val register_subst0 : ('raw, 'glb, 'top) genarg_type ->
    'glb subst_fun -> unit

  val register_ntn_subst0 : ('raw, 'glb, 'top) genarg_type ->
    'glb ntn_subst_fun -> unit

end

module Stdarg :
sig
  val loc_of_or_by_notation : ('a -> Loc.t option) -> 'a Misctypes.or_by_notation -> Loc.t option
  val wit_unit : unit Genarg.uniform_genarg_type
  val wit_int : int Genarg.uniform_genarg_type
  val wit_var : (Names.Id.t Loc.located, Names.Id.t Loc.located, Names.Id.t) Genarg.genarg_type
  val wit_bool : bool Genarg.uniform_genarg_type
  val wit_string : string Genarg.uniform_genarg_type
  val wit_pre_ident : string Genarg.uniform_genarg_type
  val wit_global : (Libnames.reference, Globnames.global_reference Loc.located Misctypes.or_var, Globnames.global_reference) Genarg.genarg_type
  val wit_ident : Names.Id.t Genarg.uniform_genarg_type
  val wit_integer : int Genarg.uniform_genarg_type
  val wit_sort_family : (Sorts.family, unit, unit) Genarg.genarg_type
  val wit_constr : (Constrexpr.constr_expr, Tactypes.glob_constr_and_expr, EConstr.constr) Genarg.genarg_type
  val wit_open_constr : (Constrexpr.constr_expr, Tactypes.glob_constr_and_expr, EConstr.constr) Genarg.genarg_type
  val wit_intro_pattern : (Constrexpr.constr_expr Misctypes.intro_pattern_expr Loc.located, Tactypes.glob_constr_and_expr Misctypes.intro_pattern_expr Loc.located, Tactypes.intro_pattern) Genarg.genarg_type
  val wit_int_or_var : (int Misctypes.or_var, int Misctypes.or_var, int) Genarg.genarg_type
  val wit_ref : (Libnames.reference, Globnames.global_reference Loc.located Misctypes.or_var, Globnames.global_reference) Genarg.genarg_type
  val wit_clause_dft_concl :  (Names.Id.t Loc.located Locus.clause_expr,Names.Id.t Loc.located Locus.clause_expr,Names.Id.t Locus.clause_expr) Genarg.genarg_type
  val wit_uconstr : (Constrexpr.constr_expr , Tactypes.glob_constr_and_expr, Ltac_pretype.closed_glob_constr) Genarg.genarg_type
  val wit_red_expr :
    ((Constrexpr.constr_expr,Libnames.reference Misctypes.or_by_notation,Constrexpr.constr_expr) Genredexpr.red_expr_gen,
     (Tactypes.glob_constr_and_expr,Names.evaluable_global_reference Misctypes.and_short_name Misctypes.or_var,Tactypes.glob_constr_pattern_and_expr) Genredexpr.red_expr_gen,
     (EConstr.constr,Names.evaluable_global_reference,Pattern.constr_pattern) Genredexpr.red_expr_gen) Genarg.genarg_type
  val wit_quant_hyp : Misctypes.quantified_hypothesis Genarg.uniform_genarg_type
  val wit_bindings :
    (Constrexpr.constr_expr Misctypes.bindings,
     Tactypes.glob_constr_and_expr Misctypes.bindings,
     EConstr.constr Misctypes.bindings Tactypes.delayed_open) Genarg.genarg_type
  val wit_constr_with_bindings :
    (Constrexpr.constr_expr Misctypes.with_bindings,
     Tactypes.glob_constr_and_expr Misctypes.with_bindings,
     EConstr.constr Misctypes.with_bindings Tactypes.delayed_open) Genarg.genarg_type
  val wit_intropattern : (Constrexpr.constr_expr Misctypes.intro_pattern_expr Loc.located, Tactypes.glob_constr_and_expr Misctypes.intro_pattern_expr Loc.located, Tactypes.intro_pattern) Genarg.genarg_type
  val wit_quantified_hypothesis : Misctypes.quantified_hypothesis Genarg.uniform_genarg_type
  val wit_clause :  (Names.Id.t Loc.located Locus.clause_expr,Names.Id.t Loc.located Locus.clause_expr,Names.Id.t Locus.clause_expr) Genarg.genarg_type
  val wit_preident : string Genarg.uniform_genarg_type
  val wit_reference : (Libnames.reference, Globnames.global_reference Loc.located Misctypes.or_var, Globnames.global_reference) Genarg.genarg_type
  val wit_open_constr_with_bindings :
    (Constrexpr.constr_expr Misctypes.with_bindings,
     Tactypes.glob_constr_and_expr Misctypes.with_bindings,
     EConstr.constr Misctypes.with_bindings Tactypes.delayed_open) Genarg.genarg_type
end

module Constrexpr_ops :
sig
  val mkIdentC : Names.Id.t -> Constrexpr.constr_expr
  val mkAppC : Constrexpr.constr_expr * Constrexpr.constr_expr list -> Constrexpr.constr_expr
  val names_of_local_assums : Constrexpr.local_binder_expr list -> Names.Name.t Loc.located list
  val coerce_reference_to_id : Libnames.reference -> Names.Id.t
  val coerce_to_id : Constrexpr.constr_expr -> Names.Id.t Loc.located
  val constr_loc : Constrexpr.constr_expr -> Loc.t option
  val mkRefC : Libnames.reference -> Constrexpr.constr_expr
  val mkLambdaC : Names.Name.t Loc.located list * Constrexpr.binder_kind * Constrexpr.constr_expr * Constrexpr.constr_expr -> Constrexpr.constr_expr
  val default_binder_kind : Constrexpr.binder_kind
  val mkLetInC : Names.Name.t Loc.located * Constrexpr.constr_expr * Constrexpr.constr_expr option * Constrexpr.constr_expr -> Constrexpr.constr_expr
  val mkCProdN : ?loc:Loc.t -> Constrexpr.local_binder_expr list -> Constrexpr.constr_expr -> Constrexpr.constr_expr
  val replace_vars_constr_expr :
    Names.Id.t Names.Id.Map.t -> Constrexpr.constr_expr -> Constrexpr.constr_expr
end

module Notation_ops :
sig
  val glob_constr_of_notation_constr : ?loc:Loc.t -> Notation_term.notation_constr -> Glob_term.glob_constr
  val glob_constr_of_notation_constr_with_binders : ?loc:Loc.t ->
                                                    ('a -> Names.Name.t -> 'a * Names.Name.t) ->
                                                    ('a -> Notation_term.notation_constr -> Glob_term.glob_constr) ->
                                                    'a -> Notation_term.notation_constr -> Glob_term.glob_constr
end

module Notation :
sig
  type cases_pattern_status = bool
  type required_module = Libnames.full_path * string list
  type 'a prim_token_interpreter = ?loc:Loc.t -> 'a -> Glob_term.glob_constr
  type 'a prim_token_uninterpreter = Glob_term.glob_constr list * (Glob_term.any_glob_constr -> 'a option) * cases_pattern_status
  type delimiters = string
  type local_scopes = Notation_term.tmp_scope_name option * Notation_term.scope_name list
  type notation_location = (Names.DirPath.t * Names.DirPath.t) * string
  val declare_string_interpreter : Notation_term.scope_name -> required_module ->
                                   string prim_token_interpreter -> string prim_token_uninterpreter -> unit
  val declare_numeral_interpreter : Notation_term.scope_name -> required_module ->
                                    Bigint.bigint prim_token_interpreter -> Bigint.bigint prim_token_uninterpreter -> unit
  val interp_notation_as_global_reference : ?loc:Loc.t -> (Globnames.global_reference -> bool) ->
                                            Constrexpr.notation -> delimiters option -> Globnames.global_reference
  val locate_notation : (Glob_term.glob_constr -> Pp.t) -> Constrexpr.notation ->
                        Notation_term.scope_name option -> Pp.t
  val find_delimiters_scope : ?loc:Loc.t -> delimiters -> Notation_term.scope_name
  val pr_scope : (Glob_term.glob_constr -> Pp.t) -> Notation_term.scope_name -> Pp.t
  val pr_scopes : (Glob_term.glob_constr -> Pp.t) -> Pp.t
  val interp_notation : ?loc:Loc.t -> Constrexpr.notation -> local_scopes ->
                        Notation_term.interpretation * (notation_location * Notation_term.scope_name option)
  val uninterp_prim_token : Glob_term.glob_constr -> Notation_term.scope_name * Constrexpr.prim_token
end

module Dumpglob :
sig
  val add_glob : ?loc:Loc.t -> Globnames.global_reference -> unit
  val pause : unit -> unit
  val continue : unit -> unit
end

module Smartlocate :
sig
  val locate_global_with_alias : ?head:bool -> Libnames.qualid Loc.located -> Globnames.global_reference
  val global_with_alias : ?head:bool -> Libnames.reference -> Globnames.global_reference
  val global_of_extended_global : Globnames.extended_global_reference -> Globnames.global_reference
  val loc_of_smart_reference : Libnames.reference Misctypes.or_by_notation -> Loc.t option
  val smart_global : ?head:bool -> Libnames.reference Misctypes.or_by_notation -> Globnames.global_reference
end

module Topconstr :
sig

  val replace_vars_constr_expr :
    Names.Id.t Names.Id.Map.t -> Constrexpr.constr_expr -> Constrexpr.constr_expr
  [@@ocaml.deprecated "use Constrexpr_ops.free_vars_of_constr_expr"]

end

module Constrintern :
sig
  type ltac_sign = {
    ltac_vars : Names.Id.Set.t;
    ltac_bound : Names.Id.Set.t;
    ltac_extra : Genintern.Store.t;
  }

  type var_internalization_data

  type var_internalization_type =
    | Inductive of Names.Id.t list * bool
    | Recursive
    | Method
    | Variable
  type internalization_env = var_internalization_data Names.Id.Map.t

  val interp_constr_evars : Environ.env -> Evd.evar_map ref ->
                            ?impls:internalization_env -> Constrexpr.constr_expr -> EConstr.constr

  val interp_type_evars : Environ.env -> Evd.evar_map ref ->
                          ?impls:internalization_env -> Constrexpr.constr_expr -> EConstr.types

  val empty_ltac_sign : ltac_sign
  val intern_gen : Pretyping.typing_constraint -> Environ.env ->
                   ?impls:internalization_env -> ?pattern_mode:bool -> ?ltacvars:ltac_sign ->
                   Constrexpr.constr_expr -> Glob_term.glob_constr
  val intern_constr_pattern :
    Environ.env -> ?as_type:bool -> ?ltacvars:ltac_sign ->
    Constrexpr.constr_pattern_expr -> Names.Id.t list * Pattern.constr_pattern
  val intern_constr : Environ.env -> Constrexpr.constr_expr -> Glob_term.glob_constr
  val for_grammar : ('a -> 'b) -> 'a -> 'b
  val interp_reference : ltac_sign -> Libnames.reference -> Glob_term.glob_constr
  val interp_constr : Environ.env -> Evd.evar_map -> ?impls:internalization_env ->
                      Constrexpr.constr_expr -> Constr.t Evd.in_evar_universe_context
  val interp_open_constr : Environ.env -> Evd.evar_map -> Constrexpr.constr_expr -> Evd.evar_map * EConstr.constr
  val locate_reference :  Libnames.qualid -> Globnames.global_reference
  val interp_type : Environ.env -> Evd.evar_map -> ?impls:internalization_env ->
                    Constrexpr.constr_expr -> Constr.types Evd.in_evar_universe_context
  val interp_context_evars :
    ?global_level:bool -> ?impl_env:internalization_env -> ?shift:int ->
    Environ.env -> Evd.evar_map ref -> Constrexpr.local_binder_expr list ->
    internalization_env * ((Environ.env * EConstr.rel_context) * Impargs.manual_implicits)
  val compute_internalization_data : Environ.env -> var_internalization_type ->
                                     Constr.types -> Impargs.manual_explicitation list -> var_internalization_data
  val empty_internalization_env : internalization_env
  val global_reference : Names.Id.t -> Globnames.global_reference
end

module Constrextern :
sig
  val extern_glob_constr : Names.Id.Set.t -> Glob_term.glob_constr -> Constrexpr.constr_expr
  val extern_glob_type : Names.Id.Set.t -> Glob_term.glob_constr -> Constrexpr.constr_expr
  val extern_constr : ?lax:bool -> bool -> Environ.env -> Evd.evar_map -> EConstr.t -> Constrexpr.constr_expr
  val without_symbols : ('a -> 'b) -> 'a -> 'b
  val print_universes : bool ref
  val extern_type : bool -> Environ.env -> Evd.evar_map -> EConstr.t -> Constrexpr.constr_expr
  val with_universes : ('a -> 'b) -> 'a -> 'b
  val set_extern_reference :
    (?loc:Loc.t -> Names.Id.Set.t -> Globnames.global_reference -> Libnames.reference) -> unit
end

module Declare :
sig
  type internal_flag =
    | UserAutomaticRequest
    | InternalTacticRequest
    | UserIndividualRequest

  type constant_declaration = Safe_typing.private_constants Entries.constant_entry * Decl_kinds.logical_kind

  type section_variable_entry =
    | SectionLocalDef of Safe_typing.private_constants Entries.definition_entry
    | SectionLocalAssum of Constr.types Univ.in_universe_context_set * Decl_kinds.polymorphic * bool

  type variable_declaration = Names.DirPath.t * section_variable_entry * Decl_kinds.logical_kind

  val declare_constant :
    ?internal:internal_flag -> ?local:bool -> Names.Id.t -> ?export_seff:bool -> constant_declaration -> Names.Constant.t

  val declare_universe_context : Decl_kinds.polymorphic -> Univ.ContextSet.t -> unit

  val declare_definition :
    ?internal:internal_flag -> ?opaque:bool -> ?kind:Decl_kinds.definition_object_kind ->
    ?local:bool -> Names.Id.t -> ?types:Constr.t ->
    Constr.t Entries.in_constant_universes_entry -> Names.Constant.t
  val definition_entry : ?fix_exn:Future.fix_exn ->
    ?opaque:bool -> ?inline:bool -> ?types:Constr.types ->
    ?univs:Entries.constant_universes_entry ->
    ?eff:Safe_typing.private_constants -> Constr.t -> Safe_typing.private_constants Entries.definition_entry
  val definition_message : Names.Id.t -> unit
  val declare_variable : Names.Id.t -> variable_declaration -> Libnames.object_name
end

(************************************************************************)
(* End of modules from interp/                                       *)
(************************************************************************)

(************************************************************************)
(* Modules from proofs/                                                 *)
(************************************************************************)

module Miscprint :
sig
  val pr_or_and_intro_pattern :
    ('a -> Pp.t) -> 'a Misctypes.or_and_intro_pattern_expr -> Pp.t
  val pr_intro_pattern_naming : Misctypes.intro_pattern_naming_expr -> Pp.t
  val pr_intro_pattern :
    ('a -> Pp.t) -> 'a Misctypes.intro_pattern_expr Loc.located -> Pp.t
  val pr_bindings :
    ('a -> Pp.t) ->
    ('a -> Pp.t) -> 'a Misctypes.bindings -> Pp.t
  val pr_bindings_no_with :
    ('a -> Pp.t) ->
    ('a -> Pp.t) -> 'a Misctypes.bindings -> Pp.t
  val pr_with_bindings :
    ('a -> Pp.t) ->
    ('a -> Pp.t) -> 'a * 'a Misctypes.bindings -> Pp.t
end

(* All items in the Goal modules are deprecated. *)
module Goal :
sig
  type goal = Evar.t

  val pr_goal : goal -> Pp.t

  module V82 :
  sig
    val new_goal_with : Evd.evar_map -> goal -> Context.Named.t -> goal Evd.sigma

    val nf_hyps : Evd.evar_map -> goal -> Environ.named_context_val

    val env : Evd.evar_map -> goal -> Environ.env

    val concl : Evd.evar_map -> goal -> EConstr.constr

    val mk_goal : Evd.evar_map ->
                  Environ.named_context_val ->
                  EConstr.constr ->
                  Evd.Store.t ->
                  goal * EConstr.constr * Evd.evar_map

    val extra : Evd.evar_map -> goal -> Evd.Store.t

    val partial_solution_to : Evd.evar_map -> goal -> goal -> EConstr.constr -> Evd.evar_map

    val partial_solution : Evd.evar_map -> goal -> EConstr.constr -> Evd.evar_map

    val hyps : Evd.evar_map -> goal -> Environ.named_context_val

    val abstract_type : Evd.evar_map -> goal -> EConstr.types
  end
end

module Evar_refiner :
sig
  type glob_constr_ltac_closure = Ltac_pretype.ltac_var_map * Glob_term.glob_constr

  val w_refine : Evar.t * Evd.evar_info ->
                 glob_constr_ltac_closure -> Evd.evar_map -> Evd.evar_map
end


module Proof_type :
sig
  type prim_rule = Refine of Constr.t

  type tactic = Goal.goal Evd.sigma -> Goal.goal list Evd.sigma
end

module Logic :
sig
  type refiner_error =
  | BadType of Constr.t * Constr.t * Constr.t
  | UnresolvedBindings of Names.Name.t list
  | CannotApply of Constr.t * Constr.t
  | NotWellTyped of Constr.t
  | NonLinearProof of Constr.t
  | MetaInType of EConstr.constr
  | IntroNeedsProduct
  | DoesNotOccurIn of Constr.t * Names.Id.t
  | NoSuchHyp of Names.Id.t
  exception RefinerError of refiner_error
  val catchable_exception : exn -> bool
end

module Refine :
sig
  val refine : typecheck:bool -> (Evd.evar_map -> Evd.evar_map * EConstr.t) -> unit Proofview.tactic
  val solve_constraints : unit Proofview.tactic
end

module Proof :
sig
  type t
  type proof = t
  [@@ocaml.deprecated "please use [Proof.t]"]

  type 'a focus_kind
  val proof : t ->
    Goal.goal list * (Goal.goal list * Goal.goal list) list *
    Goal.goal list * Goal.goal list * Evd.evar_map

  val run_tactic : Environ.env ->
                   unit Proofview.tactic -> t -> t * (bool * Proofview_monad.Info.tree)
  val unshelve : t -> t
  val maximal_unfocus : 'a focus_kind -> t -> t
  val pr_proof : t -> Pp.t

  module V82 :
  sig
    val grab_evars : t -> t

    val subgoals : t -> Goal.goal list Evd.sigma
    [@@ocaml.deprecated "Use the first and fifth argument of [Proof.proof]"]

  end
end

module Proof_bullet :
sig
  val get_default_goal_selector : unit -> Vernacexpr.goal_selector
end

module Proof_global :
sig

  type t
  type state = t
  [@@ocaml.deprecated "please use [Proof_global.t]"]

  type proof_mode = {
      name : string;
      set : unit -> unit ;
      reset : unit -> unit
    }
  type proof_object = {
    id : Names.Id.t;
    entries : Safe_typing.private_constants Entries.definition_entry list;
    persistence : Decl_kinds.goal_kind;
    universes: UState.t;
  }

  type proof_ending =
  | Admitted of Names.Id.t * Decl_kinds.goal_kind * Entries.parameter_entry *
                  UState.t
  | Proved of Vernacexpr.opacity_flag *
              Vernacexpr.lident option *
              proof_object

  type proof_terminator
  type lemma_possible_guards
  type closed_proof = proof_object * proof_terminator

  val make_terminator : (proof_ending -> unit) -> proof_terminator
  val start_dependent_proof :
    Names.Id.t -> ?pl:Univdecls.universe_decl -> Decl_kinds.goal_kind ->
    Proofview.telescope -> proof_terminator -> unit
  val with_current_proof :
    (unit Proofview.tactic -> Proof.t -> Proof.t * 'a) -> 'a
  val simple_with_current_proof :
    (unit Proofview.tactic -> Proof.t -> Proof.t) -> unit
  val compact_the_proof : unit -> unit
  val register_proof_mode : proof_mode -> unit

  exception NoCurrentProof
  val give_me_the_proof : unit -> Proof.t
  (** @raise NoCurrentProof when outside proof mode. *)

  val discard_all : unit -> unit
  val discard_current : unit -> unit
  val get_current_proof_name : unit -> Names.Id.t
end

module Redexpr :
sig
  type red_expr =
    (EConstr.constr, Names.evaluable_global_reference, Pattern.constr_pattern) Genredexpr.red_expr_gen
  val reduction_of_red_expr :
    Environ.env -> red_expr -> Reductionops.e_reduction_function * Constr.cast_kind
  val declare_reduction : string -> Reductionops.reduction_function -> unit
end

module Refiner :
sig
  val project : 'a Evd.sigma -> Evd.evar_map

  val unpackage : 'a Evd.sigma -> Evd.evar_map ref * 'a

  val repackage : Evd.evar_map ref -> 'a -> 'a Evd.sigma

  val tclSHOWHYPS : Proof_type.tactic -> Proof_type.tactic
  exception FailError of int * Pp.t Lazy.t

  val tclEVARS : Evd.evar_map -> Proof_type.tactic
  val tclMAP : ('a -> Proof_type.tactic) -> 'a list -> Proof_type.tactic
  val tclREPEAT : Proof_type.tactic -> Proof_type.tactic
  val tclORELSE        : Proof_type.tactic -> Proof_type.tactic -> Proof_type.tactic
  val tclFAIL : int -> Pp.t -> Proof_type.tactic
  val tclIDTAC : Proof_type.tactic
  val tclTHEN : Proof_type.tactic -> Proof_type.tactic -> Proof_type.tactic
  val tclTHENLIST : Proof_type.tactic list -> Proof_type.tactic
  val tclTRY : Proof_type.tactic -> Proof_type.tactic
  val tclAT_LEAST_ONCE : Proof_type.tactic -> Proof_type.tactic
end

module Tacmach :
sig

  type tactic = Proof_type.tactic

  type 'a sigma = 'a Evd.sigma
  [@@ocaml.deprecated "alias of API.Evd.sigma"]

  val re_sig : 'a -> Evd.evar_map -> 'a Evd.sigma

  val pf_reduction_of_red_expr : Goal.goal Evd.sigma -> Redexpr.red_expr -> EConstr.constr -> Evd.evar_map * EConstr.constr

  val pf_unsafe_type_of : Goal.goal Evd.sigma -> EConstr.constr -> EConstr.types

  val pf_get_new_id  : Names.Id.t -> Goal.goal Evd.sigma -> Names.Id.t

  val pf_env : Goal.goal Evd.sigma -> Environ.env

  val pf_concl : Goal.goal Evd.sigma -> EConstr.types

  val pf_apply : (Environ.env -> Evd.evar_map -> 'a) -> Goal.goal Evd.sigma -> 'a

  val pf_get_hyp            : Goal.goal Evd.sigma -> Names.Id.t -> EConstr.named_declaration
  val pf_get_hyp_typ        : Goal.goal Evd.sigma -> Names.Id.t -> EConstr.types
  val project : Goal.goal Evd.sigma -> Evd.evar_map
  val refine : EConstr.constr -> Proof_type.tactic
  val refine_no_check : EConstr.constr -> Proof_type.tactic
  val pf_type_of : Goal.goal Evd.sigma -> EConstr.constr -> Evd.evar_map * EConstr.types

  val pf_hyps : Goal.goal Evd.sigma -> EConstr.named_context

  val pf_ids_of_hyps : Goal.goal Evd.sigma -> Names.Id.t list

  val pf_reduce_to_atomic_ind : Goal.goal Evd.sigma -> EConstr.types -> (Names.inductive * EConstr.EInstance.t) * EConstr.types

  val pf_reduce_to_quantified_ind : Goal.goal Evd.sigma -> EConstr.types -> (Names.inductive * EConstr.EInstance.t) * EConstr.types

  val pf_eapply : (Environ.env -> Evd.evar_map -> 'a -> Evd.evar_map * 'b) ->
                  Evar.t Evd.sigma -> 'a -> Evar.t Evd.sigma * 'b

  val pf_unfoldn : (Locus.occurrences * Names.evaluable_global_reference) list
                   -> Goal.goal Evd.sigma -> EConstr.constr -> EConstr.constr

  val pf_reduce : (Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr) -> Goal.goal Evd.sigma -> EConstr.constr -> EConstr.constr

  val pf_conv_x : Goal.goal Evd.sigma -> EConstr.constr -> EConstr.constr -> bool

  val pf_hyps_types : Goal.goal Evd.sigma -> (Names.Id.t * EConstr.types) list

  val pr_gls    : Goal.goal Evd.sigma -> Pp.t

  val pf_nf_betaiota : Goal.goal Evd.sigma -> EConstr.constr -> EConstr.constr

  val pf_last_hyp : Goal.goal Evd.sigma -> EConstr.named_declaration

  val pf_nth_hyp_id : Goal.goal Evd.sigma -> int -> Names.Id.t

  val sig_it : 'a Evd.sigma -> 'a

  module New :
  sig
    val pf_apply : (Environ.env -> Evd.evar_map -> 'a) -> 'b Proofview.Goal.t -> 'a
    val project : 'a Proofview.Goal.t -> Evd.evar_map
    val pf_unsafe_type_of : 'a Proofview.Goal.t -> EConstr.constr -> EConstr.types
    val of_old : (Goal.goal Evd.sigma -> 'a) -> [ `NF ] Proofview.Goal.t -> 'a

    val pf_env : 'a Proofview.Goal.t -> Environ.env
    val pf_ids_of_hyps : 'a Proofview.Goal.t -> Names.Id.t list
    val pf_ids_set_of_hyps : 'a Proofview.Goal.t -> Names.Id.Set.t
    val pf_concl : 'a Proofview.Goal.t -> EConstr.types
    val pf_get_new_id  : Names.Id.t -> 'a Proofview.Goal.t -> Names.Id.t
    val pf_get_hyp : Names.Id.t -> 'a Proofview.Goal.t -> EConstr.named_declaration
    val pf_get_hyp_typ : Names.Id.t -> 'a Proofview.Goal.t -> EConstr.types
    val pf_get_type_of : 'a Proofview.Goal.t -> EConstr.constr -> EConstr.types
    val pf_global : Names.Id.t -> 'a Proofview.Goal.t -> Globnames.global_reference
    val pf_hyps_types : 'a Proofview.Goal.t -> (Names.Id.t * EConstr.types) list
  end
end

module Pfedit :
sig
  val solve_by_implicit_tactic : unit -> Pretyping.inference_hook option
  val refine_by_tactic : Environ.env -> Evd.evar_map -> EConstr.types -> unit Proofview.tactic ->
                         Constr.t * Evd.evar_map
  val declare_implicit_tactic : unit Proofview.tactic -> unit
  val clear_implicit_tactic : unit -> unit
  val by : unit Proofview.tactic -> bool
  val solve : ?with_end_tac:unit Proofview.tactic ->
      Vernacexpr.goal_selector -> int option -> unit Proofview.tactic ->
      Proof.t -> Proof.t * bool
  val cook_proof :
    unit -> (Names.Id.t * (Safe_typing.private_constants Entries.definition_entry * UState.t * Decl_kinds.goal_kind))

  val get_current_context : unit -> Evd.evar_map * Environ.env
  val current_proof_statement : unit -> Names.Id.t * Decl_kinds.goal_kind * EConstr.types
end

module Clenv :
sig

  type hole = {
    hole_evar : EConstr.constr;
    hole_type : EConstr.types;
    hole_deps  : bool;
    hole_name : Names.Name.t;
  }

  type clause = {
    cl_holes : hole list;
    cl_concl : EConstr.types;
  }

  val make_evar_clause : Environ.env -> Evd.evar_map -> ?len:int -> EConstr.types ->
                         (Evd.evar_map * clause)
  val solve_evar_clause : Environ.env -> Evd.evar_map -> bool -> clause -> EConstr.constr Misctypes.bindings ->
                          Evd.evar_map
  type clausenv
  val pr_clenv : clausenv -> Pp.t
end

(************************************************************************)
(* End of modules from proofs/                                          *)
(************************************************************************)

(************************************************************************)
(* Modules from parsing/                                                *)
(************************************************************************)

module Pcoq :
sig

  open Loc
  open Names
  open Extend
  open Vernacexpr
  open Genarg
  open Constrexpr
  open Libnames
  open Misctypes
  open Genredexpr

  module Gram : sig
    include Grammar.S with type te = Tok.t

    type 'a entry = 'a Entry.e
    type internal_entry = Tok.t Gramext.g_entry
    type symbol = Tok.t Gramext.g_symbol
    type action = Gramext.g_action
    type production_rule = symbol list * action
    type single_extend_statment =
      string option * Gramext.g_assoc option * production_rule list
    type extend_statment =
      Gramext.position option * single_extend_statment list

    type coq_parsable

    val parsable : ?file:Loc.source -> char Stream.t -> coq_parsable
    val action : 'a -> action
    val entry_create : string -> 'a entry
    val entry_parse : 'a entry -> coq_parsable -> 'a
    val entry_print : Format.formatter -> 'a entry -> unit
    val with_parsable : coq_parsable -> ('a -> 'b) -> 'a -> 'b

    (* Apparently not used *)
    val srules' : production_rule list -> symbol
    val parse_tokens_after_filter : 'a entry -> Tok.t Stream.t -> 'a

  end with type 'a Entry.e = 'a Grammar.GMake(CLexer).Entry.e

  val parse_string : 'a Gram.entry -> string -> 'a
  val eoi_entry : 'a Gram.entry -> 'a Gram.entry
  val map_entry : ('a -> 'b) -> 'a Gram.entry -> 'b Gram.entry

  type gram_universe

  val uprim   : gram_universe
  val uconstr : gram_universe
  val utactic : gram_universe
  val uvernac : gram_universe

  val register_grammar : ('raw, 'glb, 'top) genarg_type -> 'raw Gram.entry -> unit

  val genarg_grammar : ('raw, 'glb, 'top) genarg_type -> 'raw Gram.entry

  val create_generic_entry : gram_universe -> string ->
    ('a, rlevel) abstract_argument_type -> 'a Gram.entry

  module Prim :
  sig
    open Names
    open Libnames
    val preident : string Gram.entry
    val ident : Id.t Gram.entry
    val name : Name.t located Gram.entry
    val identref : Id.t located Gram.entry
    val pattern_ident : Id.t Gram.entry
    val pattern_identref : Id.t located Gram.entry
    val base_ident : Id.t Gram.entry
    val natural : int Gram.entry
    val bigint : Constrexpr.raw_natural_number Gram.entry
    val integer : int Gram.entry
    val string : string Gram.entry
    val lstring : string located Gram.entry
    val qualid : qualid located Gram.entry
    val fullyqualid : Id.t list located Gram.entry
    val reference : reference Gram.entry
    val by_notation : (string * string option) Loc.located Gram.entry
    val smart_global : reference or_by_notation Gram.entry
    val dirpath : DirPath.t Gram.entry
    val ne_string : string Gram.entry
    val ne_lstring : string located Gram.entry
    val var : Id.t located Gram.entry
  end

  module Constr :
  sig
    val constr : constr_expr Gram.entry
    val constr_eoi : constr_expr Gram.entry
    val lconstr : constr_expr Gram.entry
    val binder_constr : constr_expr Gram.entry
    val operconstr : constr_expr Gram.entry
    val ident : Id.t Gram.entry
    val global : reference Gram.entry
    val universe_level : glob_level Gram.entry
    val sort : glob_sort Gram.entry
    val sort_family : Sorts.family Gram.entry
    val pattern : cases_pattern_expr Gram.entry
    val constr_pattern : constr_expr Gram.entry
    val lconstr_pattern : constr_expr Gram.entry
    val closed_binder : local_binder_expr list Gram.entry
    val binder : local_binder_expr list Gram.entry (* closed_binder or variable *)
    val binders : local_binder_expr list Gram.entry (* list of binder *)
    val open_binders : local_binder_expr list Gram.entry
    val binders_fixannot : (local_binder_expr list * (Id.t located option * recursion_order_expr)) Gram.entry
    val typeclass_constraint : (Name.t located * bool * constr_expr) Gram.entry
    val record_declaration : constr_expr Gram.entry
    val appl_arg : (constr_expr * explicitation located option) Gram.entry
  end

  module Vernac_ :
  sig
    val gallina : vernac_expr Gram.entry
    val gallina_ext : vernac_expr Gram.entry
    val command : vernac_expr Gram.entry
    val syntax : vernac_expr Gram.entry
    val vernac : vernac_expr Gram.entry
    val rec_definition : (fixpoint_expr * decl_notation list) Gram.entry
    val vernac_eoi : vernac_expr Gram.entry
    val noedit_mode : vernac_expr Gram.entry
    val command_entry : vernac_expr Gram.entry
    val red_expr : raw_red_expr Gram.entry
    val hint_info : Vernacexpr.hint_info_expr Gram.entry
  end

  val epsilon_value : ('a -> 'self) -> ('self, 'a) Extend.symbol -> 'self option

  val get_command_entry : unit -> vernac_expr Gram.entry
  val set_command_entry : vernac_expr Gram.entry -> unit

  type gram_reinit = gram_assoc * gram_position
  val grammar_extend : 'a Gram.entry -> gram_reinit option ->
    'a Extend.extend_statment -> unit

  module GramState : Store.S

  type 'a grammar_command

  type extend_rule =
    | ExtendRule : 'a Gram.entry * gram_reinit option * 'a extend_statment -> extend_rule

  type 'a grammar_extension = 'a -> GramState.t -> extend_rule list * GramState.t

  val create_grammar_command : string -> 'a grammar_extension -> 'a grammar_command

  val extend_grammar_command : 'a grammar_command -> 'a -> unit
  val recover_grammar_command : 'a grammar_command -> 'a list
  val with_grammar_rule_protection : ('a -> 'b) -> 'a -> 'b

  val to_coqloc : Ploc.t -> Loc.t
  val (!@) : Ploc.t -> Loc.t

end

module Egramml :
sig
  open Vernacexpr

  type 's grammar_prod_item =
    | GramTerminal of string
    | GramNonTerminal : ('a Genarg.raw_abstract_argument_type option *
                         ('s, 'a) Extend.symbol) Loc.located -> 's grammar_prod_item

  val extend_vernac_command_grammar :
    extend_name -> vernac_expr Pcoq.Gram.entry option ->
    vernac_expr grammar_prod_item list -> unit

  val make_rule :
    (Loc.t -> Genarg.raw_generic_argument list -> 'a) ->
    'a grammar_prod_item list -> 'a Extend.production_rule

end

module G_vernac :
sig

  val def_body : Vernacexpr.definition_expr Pcoq.Gram.entry
  val section_subset_expr : Vernacexpr.section_subset_expr Pcoq.Gram.entry
  val query_command : (Vernacexpr.goal_selector option -> Vernacexpr.vernac_expr) Pcoq.Gram.entry

end

module G_proofs :
sig

  val hint : Vernacexpr.hints_expr Pcoq.Gram.entry

end

(************************************************************************)
(* End of modules from parsing/                                         *)
(************************************************************************)

(************************************************************************)
(* Modules from printing/                                               *)
(************************************************************************)

module Genprint :
sig
  type 'a with_level =
    { default_already_surrounded : Notation_term.tolerability;
      default_ensure_surrounded : Notation_term.tolerability;
      printer : 'a }
  type printer_result =
| PrinterBasic of (unit -> Pp.t)
| PrinterNeedsLevel of (Notation_term.tolerability -> Pp.t) with_level
  type printer_fun_with_level = Environ.env -> Evd.evar_map -> Notation_term.tolerability -> Pp.t
  type top_printer_result =
    | TopPrinterBasic of (unit -> Pp.t)
    | TopPrinterNeedsContext of (Environ.env -> Evd.evar_map -> Pp.t)
    | TopPrinterNeedsContextAndLevel of printer_fun_with_level with_level
  type 'a printer = 'a -> printer_result
  type 'a top_printer = 'a -> top_printer_result
  val register_print0 : ('raw, 'glb, 'top) Genarg.genarg_type ->
                        'raw printer -> 'glb printer -> 'top top_printer -> unit
  val register_vernac_print0 : ('raw, 'glb, 'top) Genarg.genarg_type ->
                        'raw printer -> unit
  val register_val_print0 : 'top Geninterp.Val.typ -> 'top top_printer -> unit
  val generic_top_print : Genarg.tlevel Genarg.generic_argument top_printer
  val generic_val_print : Geninterp.Val.t top_printer
end

module Pputils :
sig
  val pr_with_occurrences : ('a -> Pp.t) -> (string -> Pp.t) -> 'a Locus.with_occurrences -> Pp.t
  val pr_red_expr :
    ('a -> Pp.t) * ('a -> Pp.t) * ('b -> Pp.t) * ('c -> Pp.t) ->
    (string -> Pp.t) ->
    ('a,'b,'c) Genredexpr.red_expr_gen -> Pp.t
  val pr_raw_generic : Environ.env -> Genarg.rlevel Genarg.generic_argument -> Pp.t
  val pr_glb_generic : Environ.env -> Genarg.glevel Genarg.generic_argument -> Pp.t
  val pr_or_var : ('a -> Pp.t) -> 'a Misctypes.or_var -> Pp.t
  val pr_or_by_notation : ('a -> Pp.t) -> 'a Misctypes.or_by_notation -> Pp.t
end

module Ppconstr :
sig
  val pr_name : Names.Name.t -> Pp.t
  [@@ocaml.deprecated "alias of API.Names.Name.print"]

  val lsimpleconstr : Notation_term.tolerability
  val ltop : Notation_term.tolerability
  val pr_id : Names.Id.t -> Pp.t
  val pr_or_var : ('a -> Pp.t) -> 'a Misctypes.or_var -> Pp.t
  val pr_with_comments : ?loc:Loc.t -> Pp.t -> Pp.t
  val pr_lident : Names.Id.t Loc.located -> Pp.t
  val pr_lname : Names.Name.t Loc.located -> Pp.t
  val prec_less : int -> int * Notation_term.parenRelation -> bool
  val pr_constr_expr : Constrexpr.constr_expr -> Pp.t
  val pr_lconstr_expr : Constrexpr.constr_expr -> Pp.t
  val pr_constr_pattern_expr : Constrexpr.constr_pattern_expr -> Pp.t
  val pr_lconstr_pattern_expr : Constrexpr.constr_pattern_expr -> Pp.t
  val pr_binders : Constrexpr.local_binder_expr list -> Pp.t
  val pr_glob_sort : Misctypes.glob_sort -> Pp.t
end

module Printer :
sig
  val pr_named_context : Environ.env -> Evd.evar_map -> Context.Named.t -> Pp.t
  val pr_rel_context : Environ.env -> Evd.evar_map -> Context.Rel.t -> Pp.t
  val pr_goal : Goal.goal Evd.sigma -> Pp.t

  val pr_constr_env : Environ.env -> Evd.evar_map -> Constr.t -> Pp.t
  val pr_lconstr_env : Environ.env -> Evd.evar_map -> Constr.t -> Pp.t

  val pr_constr : Constr.t -> Pp.t
  [@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

  val pr_lconstr : Constr.t -> Pp.t
  [@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

  val pr_econstr : EConstr.constr -> Pp.t
  [@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

  val pr_glob_constr : Glob_term.glob_constr -> Pp.t
  [@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

  val pr_constr_pattern : Pattern.constr_pattern -> Pp.t
  [@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

  val pr_glob_constr_env : Environ.env -> Glob_term.glob_constr -> Pp.t
  val pr_lglob_constr_env : Environ.env -> Glob_term.glob_constr -> Pp.t
  val pr_econstr_n_env : Environ.env -> Evd.evar_map -> Notation_term.tolerability -> EConstr.constr -> Pp.t
  val pr_econstr_env : Environ.env -> Evd.evar_map -> EConstr.constr -> Pp.t
  val pr_constr_pattern_env : Environ.env -> Evd.evar_map -> Pattern.constr_pattern -> Pp.t
  val pr_lconstr_pattern_env : Environ.env -> Evd.evar_map -> Pattern.constr_pattern -> Pp.t
  val pr_closed_glob : Ltac_pretype.closed_glob_constr -> Pp.t
  [@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]
  val pr_lglob_constr : Glob_term.glob_constr -> Pp.t
  [@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]
  val pr_leconstr_env : Environ.env -> Evd.evar_map -> EConstr.constr -> Pp.t
  val pr_leconstr : EConstr.constr -> Pp.t
  [@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

  val pr_global : Globnames.global_reference -> Pp.t
  val pr_lconstr_under_binders : Ltac_pretype.constr_under_binders -> Pp.t
  [@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

  val pr_lconstr_under_binders_env : Environ.env -> Evd.evar_map -> Ltac_pretype.constr_under_binders -> Pp.t

  val pr_constr_under_binders_env : Environ.env -> Evd.evar_map -> Ltac_pretype.constr_under_binders -> Pp.t
  val pr_closed_glob_n_env : Environ.env -> Evd.evar_map -> Notation_term.tolerability -> Ltac_pretype.closed_glob_constr -> Pp.t
  val pr_closed_glob_env : Environ.env -> Evd.evar_map -> Ltac_pretype.closed_glob_constr -> Pp.t
  val pr_rel_context_of : Environ.env -> Evd.evar_map -> Pp.t
  val pr_named_context_of : Environ.env -> Evd.evar_map -> Pp.t
  val pr_ltype : Constr.types -> Pp.t
  [@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]
  val pr_ljudge : EConstr.unsafe_judgment -> Pp.t * Pp.t
  [@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

  val pr_idpred : Names.Id.Pred.t -> Pp.t
  val pr_cpred : Names.Cpred.t -> Pp.t
  val pr_transparent_state : Names.transparent_state -> Pp.t
end

module Prettyp :
sig
  type 'a locatable_info = {
    locate : Libnames.qualid -> 'a option;
    locate_all : Libnames.qualid -> 'a list;
    shortest_qualid : 'a -> Libnames.qualid;
    name : 'a -> Pp.t;
    print : 'a -> Pp.t;
    about : 'a -> Pp.t;
  }

  val register_locatable : string -> 'a locatable_info -> unit
  val print_located_other : string -> Libnames.reference -> Pp.t
end

(************************************************************************)
(* End of modules from printing/                                        *)
(************************************************************************)

(************************************************************************)
(* Modules from tactics/                                                *)
(************************************************************************)

module Tacticals :
sig
  open Proof_type

  val tclORELSE        : tactic -> tactic -> tactic
  val tclDO : int -> tactic -> tactic
  val tclIDTAC : tactic
  val tclFAIL : int -> Pp.t -> tactic
  val tclTHEN : tactic -> tactic -> tactic
  val tclTHENLIST      : tactic list -> tactic
  val pf_constr_of_global :
    Globnames.global_reference -> (EConstr.constr -> Proof_type.tactic) -> Proof_type.tactic
  val tclMAP : ('a -> tactic) -> 'a list -> tactic
  val tclTRY           : tactic -> tactic
  val tclCOMPLETE      : tactic -> tactic
  val tclTHENS : tactic -> tactic list -> tactic
  val tclFIRST         : tactic list -> tactic
  val tclTHENFIRST     : tactic -> tactic -> tactic
  val tclTHENLAST      : tactic -> tactic -> tactic
  val tclTHENSFIRSTn   : tactic -> tactic array -> tactic -> tactic
  val tclTHENSLASTn    : tactic -> tactic -> tactic array -> tactic
  val tclSOLVE         : tactic list -> tactic

  val onClause   : (Names.Id.t option -> tactic) -> Locus.clause -> tactic
  val onAllHypsAndConcl : (Names.Id.t option -> tactic) -> tactic
  val onLastHypId : (Names.Id.t -> tactic) -> tactic
  val onNthHypId : int -> (Names.Id.t -> tactic) -> tactic
  val onNLastHypsId : int -> (Names.Id.t list -> tactic) -> tactic

  val tclTHENSEQ : tactic list -> tactic
  [@@ocaml.deprecated "alias of API.Tacticals.tclTHENLIST"]

  val nLastDecls : int -> Goal.goal Evd.sigma -> EConstr.named_context

  val tclTHEN_i : tactic -> (int -> tactic) -> tactic

  val tclPROGRESS : tactic -> tactic

  val elimination_sort_of_goal : Goal.goal Evd.sigma -> Sorts.family

  module New :
  sig
    open Proofview
    val tclORELSE0 : unit tactic -> unit tactic -> unit tactic
    val tclFAIL : int -> Pp.t -> 'a tactic
    val pf_constr_of_global : Globnames.global_reference -> EConstr.constr tactic
    val tclTHEN : unit tactic -> unit tactic -> unit tactic
    val tclTHENS : unit tactic -> unit tactic list -> unit tactic
    val tclFIRST : unit tactic list -> unit tactic
    val tclZEROMSG : ?loc:Loc.t -> Pp.t -> 'a tactic
    val tclORELSE  : unit tactic -> unit tactic -> unit tactic
    val tclREPEAT : unit tactic -> unit tactic
    val tclTRY : unit tactic -> unit tactic
    val tclTHENFIRST : unit tactic -> unit tactic -> unit tactic
    val tclPROGRESS :  unit Proofview.tactic -> unit Proofview.tactic
    val tclTHENS3PARTS : unit tactic -> unit tactic array -> unit tactic -> unit tactic array -> unit tactic
    val tclDO : int -> unit tactic -> unit tactic
    val tclTIMEOUT : int -> unit tactic -> unit tactic
    val tclTIME : string option -> 'a tactic -> 'a tactic
    val tclOR : unit tactic -> unit tactic -> unit tactic
    val tclONCE : unit tactic -> unit tactic
    val tclEXACTLY_ONCE : unit tactic -> unit tactic
    val tclIFCATCH :
      unit tactic  ->
      (unit -> unit tactic) ->
      (unit -> unit tactic) -> unit tactic
    val tclSOLVE : unit tactic list -> unit tactic
    val tclCOMPLETE : 'a tactic -> 'a tactic
    val tclSELECT : Vernacexpr.goal_selector -> 'a tactic -> 'a tactic
    val tclWITHHOLES : bool -> 'a tactic -> Evd.evar_map -> 'a tactic
    val tclDELAYEDWITHHOLES : bool -> 'a Tactypes.delayed_open -> ('a -> unit tactic) -> unit tactic
    val tclTHENLIST : unit tactic list -> unit tactic
    val tclTHENLAST  : unit tactic -> unit tactic -> unit tactic
    val tclMAP : ('a -> unit tactic) -> 'a list -> unit tactic
    val tclIDTAC : unit tactic
    val tclIFTHENELSE : unit tactic -> unit tactic -> unit tactic -> unit tactic
    val tclIFTHENSVELSE : unit tactic -> unit tactic array -> unit tactic -> unit tactic
  end
end

module Hipattern :
sig
  exception NoEquationFound
  type 'a matching_function = Evd.evar_map -> EConstr.constr -> 'a option
  type testing_function = Evd.evar_map -> EConstr.constr -> bool
  val is_disjunction : ?strict:bool -> ?onlybinary:bool -> testing_function
  val match_with_disjunction : ?strict:bool -> ?onlybinary:bool -> (EConstr.constr * EConstr.constr list) matching_function
  val match_with_equality_type : (EConstr.constr * EConstr.constr list) matching_function
  val is_empty_type : testing_function
  val is_unit_type : testing_function
  val is_unit_or_eq_type : testing_function
  val is_conjunction : ?strict:bool -> ?onlybinary:bool -> testing_function
  val match_with_conjunction : ?strict:bool -> ?onlybinary:bool -> (EConstr.constr * EConstr.constr list) matching_function
  val match_with_imp_term : (EConstr.constr * EConstr.constr) matching_function
  val match_with_forall_term : (Names.Name.t * EConstr.constr * EConstr.constr) matching_function
  val match_with_nodep_ind : (EConstr.constr * EConstr.constr list * int) matching_function
  val match_with_sigma_type : (EConstr.constr * EConstr.constr list) matching_function
end

module Ind_tables :
sig
  type individual
  type 'a scheme_kind

  val check_scheme : 'a scheme_kind -> Names.inductive -> bool
  val find_scheme : ?mode:Declare.internal_flag -> 'a scheme_kind -> Names.inductive -> Names.Constant.t * Safe_typing.private_constants
  val pr_scheme_kind : 'a scheme_kind -> Pp.t
end

module Elimschemes :
sig
  val case_scheme_kind_from_prop : Ind_tables.individual Ind_tables.scheme_kind
  val case_dep_scheme_kind_from_type_in_prop : Ind_tables.individual Ind_tables.scheme_kind
  val case_scheme_kind_from_type : Ind_tables.individual Ind_tables.scheme_kind
  val case_dep_scheme_kind_from_type : Ind_tables.individual Ind_tables.scheme_kind
  val case_dep_scheme_kind_from_prop : Ind_tables.individual Ind_tables.scheme_kind
end

module Tactics :
sig
  open Proofview

  type change_arg = Ltac_pretype.patvar_map -> Evd.evar_map -> Evd.evar_map * EConstr.constr
  type tactic_reduction = Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr

  type elim_scheme =
    {
      elimc: EConstr.constr Misctypes.with_bindings option;
      elimt: EConstr.types;
      indref: Globnames.global_reference option;
      params: EConstr.rel_context;
      nparams: int;
      predicates: EConstr.rel_context;
      npredicates: int;
      branches: EConstr.rel_context;
      nbranches: int;
      args: EConstr.rel_context;
      nargs: int;
      indarg: EConstr.rel_declaration option;
      concl: EConstr.types;
      indarg_in_concl: bool;
      farg_in_concl: bool;
    }

  val unify : ?state:Names.transparent_state -> EConstr.constr -> EConstr.constr -> unit Proofview.tactic
  val intro_then : (Names.Id.t -> unit Proofview.tactic) -> unit Proofview.tactic
  val reflexivity : unit tactic
  val change_concl : EConstr.constr -> unit tactic
  val apply : EConstr.constr -> unit tactic
  val normalise_vm_in_concl : unit tactic
  val assert_before : Names.Name.t -> EConstr.types -> unit tactic
  val exact_check : EConstr.constr -> unit tactic
  val simplest_elim : EConstr.constr -> unit tactic
  val introf : unit tactic
  val cut : EConstr.types -> unit tactic
  val convert_concl : ?check:bool -> EConstr.types -> Constr.cast_kind -> unit tactic
  val intro_using : Names.Id.t -> unit tactic
  val intro : unit tactic
  val fresh_id_in_env : Names.Id.Set.t -> Names.Id.t -> Environ.env -> Names.Id.t
  val is_quantified_hypothesis : Names.Id.t -> 'a Goal.t -> bool
  val tclABSTRACT : ?opaque:bool -> Names.Id.t option -> unit Proofview.tactic -> unit Proofview.tactic
  val intro_patterns : bool -> Tactypes.intro_patterns -> unit Proofview.tactic
  val apply_with_delayed_bindings_gen :
    Misctypes.advanced_flag -> Misctypes.evars_flag -> (Misctypes.clear_flag * Tactypes.delayed_open_constr_with_bindings Loc.located) list -> unit Proofview.tactic
  val apply_delayed_in :
    Misctypes.advanced_flag -> Misctypes.evars_flag -> Names.Id.t ->
    (Misctypes.clear_flag * Tactypes.delayed_open_constr_with_bindings Loc.located) list ->
    Tactypes.intro_pattern option -> unit Proofview.tactic
  val elim :
    Misctypes.evars_flag -> Misctypes.clear_flag -> EConstr.constr Misctypes.with_bindings -> EConstr.constr Misctypes.with_bindings option -> unit Proofview.tactic
  val general_case_analysis : Misctypes.evars_flag -> Misctypes.clear_flag -> EConstr.constr Misctypes.with_bindings ->  unit Proofview.tactic
  val mutual_fix :
    Names.Id.t -> int -> (Names.Id.t * int * EConstr.constr) list -> int -> unit Proofview.tactic
  val mutual_cofix : Names.Id.t -> (Names.Id.t * EConstr.constr) list -> int -> unit Proofview.tactic
  val forward   : bool -> unit Proofview.tactic option option ->
                  Tactypes.intro_pattern option -> EConstr.constr -> unit Proofview.tactic
  val generalize_gen : (EConstr.constr Locus.with_occurrences * Names.Name.t) list -> unit Proofview.tactic
  val letin_tac : (bool * Tactypes.intro_pattern_naming) option ->
                  Names.Name.t -> EConstr.constr -> EConstr.types option -> Locus.clause -> unit Proofview.tactic
  val letin_pat_tac : Misctypes.evars_flag ->
                      (bool * Tactypes.intro_pattern_naming) option ->
                      Names.Name.t ->
                      Evd.evar_map * EConstr.constr ->
                      Locus.clause -> unit Proofview.tactic
  val induction_destruct : Misctypes.rec_flag -> Misctypes.evars_flag ->
                           (Tactypes.delayed_open_constr_with_bindings Misctypes.destruction_arg
                            * (Tactypes.intro_pattern_naming option * Tactypes.or_and_intro_pattern option)
                            * Locus.clause option) list *
                             EConstr.constr Misctypes.with_bindings option -> unit Proofview.tactic
  val reduce : Redexpr.red_expr -> Locus.clause -> unit Proofview.tactic
  val change : Pattern.constr_pattern option -> change_arg -> Locus.clause -> unit Proofview.tactic
  val intros_reflexivity : unit Proofview.tactic
  val exact_no_check : EConstr.constr -> unit Proofview.tactic
  val assumption : unit Proofview.tactic
  val intros_transitivity : EConstr.constr option -> unit Proofview.tactic
  val vm_cast_no_check : EConstr.constr -> unit Proofview.tactic
  val native_cast_no_check : EConstr.constr -> unit Proofview.tactic
  val case_type : EConstr.types -> unit Proofview.tactic
  val elim_type : EConstr.types -> unit Proofview.tactic
  val cut_and_apply : EConstr.constr -> unit Proofview.tactic
  val left_with_bindings  : Misctypes.evars_flag -> EConstr.constr Misctypes.bindings -> unit Proofview.tactic
  val right_with_bindings : Misctypes.evars_flag -> EConstr.constr Misctypes.bindings -> unit Proofview.tactic
  val any_constructor : Misctypes.evars_flag -> unit Proofview.tactic option -> unit Proofview.tactic
  val constructor_tac : Misctypes.evars_flag -> int option -> int ->
                        EConstr.constr Misctypes.bindings -> unit Proofview.tactic
  val specialize : EConstr.constr Misctypes.with_bindings -> Tactypes.intro_pattern option -> unit Proofview.tactic
  val intros_symmetry : Locus.clause -> unit Proofview.tactic
  val split_with_bindings : Misctypes.evars_flag -> EConstr.constr Misctypes.bindings list -> unit Proofview.tactic
  val intros_until : Misctypes.quantified_hypothesis -> unit Proofview.tactic
  val intro_move : Names.Id.t option -> Names.Id.t Misctypes.move_location -> unit Proofview.tactic
  val move_hyp : Names.Id.t -> Names.Id.t Misctypes.move_location -> unit Proofview.tactic
  val rename_hyp : (Names.Id.t * Names.Id.t) list -> unit Proofview.tactic
  val revert : Names.Id.t list -> unit Proofview.tactic
  val simple_induct : Misctypes.quantified_hypothesis -> unit Proofview.tactic
  val simple_destruct : Misctypes.quantified_hypothesis -> unit Proofview.tactic
  val fix : Names.Id.t option -> int -> unit Proofview.tactic
  val cofix : Names.Id.t option -> unit Proofview.tactic
  val keep : Names.Id.t list -> unit Proofview.tactic
  val clear : Names.Id.t list -> unit Proofview.tactic
  val clear_body : Names.Id.t list -> unit Proofview.tactic
  val generalize_dep  : ?with_let:bool (** Don't lose let bindings *) -> EConstr.constr  -> unit Proofview.tactic
  val force_destruction_arg : Misctypes.evars_flag -> Environ.env -> Evd.evar_map ->
    Tactypes.delayed_open_constr_with_bindings Misctypes.destruction_arg ->
    Evd.evar_map * EConstr.constr Misctypes.with_bindings Misctypes.destruction_arg
  val apply_with_bindings   : EConstr.constr Misctypes.with_bindings -> unit Proofview.tactic
  val abstract_generalize : ?generalize_vars:bool -> ?force_dep:bool -> Names.Id.t -> unit Proofview.tactic
  val specialize_eqs : Names.Id.t -> unit Proofview.tactic
  val generalize : EConstr.constr list -> unit Proofview.tactic
  val simplest_case : EConstr.constr -> unit Proofview.tactic
  val introduction : ?check:bool -> Names.Id.t -> unit Proofview.tactic
  val convert_concl_no_check : EConstr.types -> Constr.cast_kind -> unit Proofview.tactic
  val reduct_in_concl : tactic_reduction * Constr.cast_kind -> unit Proofview.tactic
  val reduct_in_hyp : ?check:bool -> tactic_reduction -> Locus.hyp_location -> unit Proofview.tactic
  val convert_hyp_no_check : EConstr.named_declaration -> unit Proofview.tactic
  val reflexivity_red : bool -> unit Proofview.tactic
  val symmetry_red : bool -> unit Proofview.tactic
  val eapply : EConstr.constr -> unit Proofview.tactic
  val transitivity_red : bool -> EConstr.constr option -> unit Proofview.tactic
  val assert_after_replacing : Names.Id.t -> EConstr.types -> unit Proofview.tactic
  val intros : unit Proofview.tactic
  val setoid_reflexivity : unit Proofview.tactic Hook.t
  val setoid_symmetry : unit Proofview.tactic Hook.t
  val setoid_symmetry_in : (Names.Id.t -> unit Proofview.tactic) Hook.t
  val setoid_transitivity : (EConstr.constr option -> unit Proofview.tactic) Hook.t
  val unfold_in_concl :
    (Locus.occurrences * Names.evaluable_global_reference) list -> unit Proofview.tactic
  val intros_using : Names.Id.t list -> unit Proofview.tactic
  val simpl_in_concl : unit Proofview.tactic
  val reduct_option : ?check:bool -> tactic_reduction * Constr.cast_kind -> Locus.goal_location -> unit Proofview.tactic
  val simplest_split : unit Proofview.tactic
  val unfold_in_hyp :
    (Locus.occurrences * Names.evaluable_global_reference) list -> Locus.hyp_location -> unit Proofview.tactic
  val split : EConstr.constr Misctypes.bindings -> unit Proofview.tactic
  val red_in_concl : unit Proofview.tactic
  val change_in_concl   : (Locus.occurrences * Pattern.constr_pattern) option -> change_arg -> unit Proofview.tactic
  val eapply_with_bindings  : EConstr.constr Misctypes.with_bindings -> unit Proofview.tactic
  val assert_by  : Names.Name.t -> EConstr.types -> unit Proofview.tactic ->
                   unit Proofview.tactic
  val intro_avoiding : Names.Id.Set.t -> unit Proofview.tactic
  val pose_proof : Names.Name.t -> EConstr.constr -> unit Proofview.tactic
  val pattern_option :  (Locus.occurrences * EConstr.constr) list -> Locus.goal_location -> unit Proofview.tactic
  val compute_elim_sig : Evd.evar_map -> ?elimc:EConstr.constr Misctypes.with_bindings -> EConstr.types -> elim_scheme
  val try_intros_until :
    (Names.Id.t -> unit Proofview.tactic) -> Misctypes.quantified_hypothesis -> unit Proofview.tactic
  val cache_term_by_tactic_then :
    opaque:bool -> ?goal_type:(EConstr.constr option) -> Names.Id.t ->
    Decl_kinds.goal_kind -> unit Proofview.tactic -> (EConstr.constr -> EConstr.constr list -> unit Proofview.tactic) -> unit Proofview.tactic
  val apply_type : EConstr.constr -> EConstr.constr list -> unit Proofview.tactic
  val hnf_in_concl : unit Proofview.tactic
  val intro_mustbe_force : Names.Id.t -> unit Proofview.tactic

  module New :
  sig
    val refine : typecheck:bool -> (Evd.evar_map -> Evd.evar_map * EConstr.constr) -> unit Proofview.tactic
    val reduce_after_refine : unit Proofview.tactic
  end
  module Simple :
  sig
    val intro : Names.Id.t -> unit Proofview.tactic
    val apply  : EConstr.constr -> unit Proofview.tactic
    val case : EConstr.constr -> unit Proofview.tactic
  end
end

module Elim :
sig
  val h_decompose : Names.inductive list -> EConstr.constr -> unit Proofview.tactic
  val h_double_induction : Misctypes.quantified_hypothesis -> Misctypes.quantified_hypothesis-> unit Proofview.tactic
  val h_decompose_or : EConstr.constr -> unit Proofview.tactic
  val h_decompose_and : EConstr.constr -> unit Proofview.tactic
end

module Equality :
sig
  type orientation = bool
  type freeze_evars_flag = bool
  type dep_proof_flag = bool
  type conditions =
    | Naive
    | FirstSolved
    | AllMatches
  type inj_flags = {
    keep_proof_equalities : bool; (* One may want it or not *)
    injection_in_context : bool;  (* For regularity; one may want it from ML code but not interactively *)
    injection_pattern_l2r_order : bool; (* Compatibility option: no reason not to want it *)
  }

  val build_selector :
    Environ.env -> Evd.evar_map -> int -> EConstr.constr -> EConstr.types ->
    EConstr.constr -> EConstr.constr -> EConstr.constr
  val replace : EConstr.constr -> EConstr.constr -> unit Proofview.tactic
  val general_rewrite :
    orientation -> Locus.occurrences -> freeze_evars_flag -> dep_proof_flag ->
    ?tac:(unit Proofview.tactic * conditions) -> EConstr.constr -> unit Proofview.tactic
  val inj : inj_flags option -> Tactypes.intro_patterns option -> Misctypes.evars_flag ->
            Misctypes.clear_flag -> EConstr.constr Misctypes.with_bindings -> unit Proofview.tactic
  val general_multi_rewrite :
    Misctypes.evars_flag -> (bool * Misctypes.multi * Misctypes.clear_flag * Tactypes.delayed_open_constr_with_bindings) list ->
    Locus.clause -> (unit Proofview.tactic * conditions) option -> unit Proofview.tactic
  val replace_in_clause_maybe_by : EConstr.constr -> EConstr.constr -> Locus.clause -> unit Proofview.tactic option -> unit Proofview.tactic
  val replace_term : bool option -> EConstr.constr -> Locus.clause -> unit Proofview.tactic
  val dEq : keep_proofs:bool option -> Misctypes.evars_flag -> EConstr.constr Misctypes.with_bindings Misctypes.destruction_arg option -> unit Proofview.tactic
  val discr_tac : Misctypes.evars_flag ->
                  EConstr.constr Misctypes.with_bindings Misctypes.destruction_arg option -> unit Proofview.tactic
  val injClause    : inj_flags option -> Tactypes.intro_patterns option -> Misctypes.evars_flag ->
                     EConstr.constr Misctypes.with_bindings Misctypes.destruction_arg option -> unit Proofview.tactic

  val simpleInjClause : inj_flags option -> Misctypes.evars_flag ->
                        EConstr.constr Misctypes.with_bindings Misctypes.destruction_arg option ->
                        unit Proofview.tactic
  val rewriteInConcl : bool -> EConstr.constr -> unit Proofview.tactic
  val rewriteInHyp : bool -> EConstr.constr -> Names.Id.t -> unit Proofview.tactic
  val cutRewriteInConcl : bool -> EConstr.constr -> unit Proofview.tactic
  val cutRewriteInHyp : bool -> EConstr.types -> Names.Id.t -> unit Proofview.tactic
  val general_rewrite_ebindings_clause : Names.Id.t option ->
                                         orientation -> Locus.occurrences -> freeze_evars_flag -> dep_proof_flag ->
                                         ?tac:(unit Proofview.tactic * conditions) -> EConstr.constr Misctypes.with_bindings -> Misctypes.evars_flag -> unit Proofview.tactic
  val subst : Names.Id.t list -> unit Proofview.tactic

  type subst_tactic_flags = {
    only_leibniz : bool;
    rewrite_dependent_proof : bool
  }
  val subst_all : ?flags:subst_tactic_flags -> unit -> unit Proofview.tactic

  val general_rewrite_in :
    orientation -> Locus.occurrences -> freeze_evars_flag -> dep_proof_flag ->
    ?tac:(unit Proofview.tactic * conditions) -> Names.Id.t -> EConstr.constr -> Misctypes.evars_flag -> unit Proofview.tactic

  val general_setoid_rewrite_clause :
  (Names.Id.t option -> orientation -> Locus.occurrences -> EConstr.constr Misctypes.with_bindings ->
   new_goals:EConstr.constr list -> unit Proofview.tactic) Hook.t

  val discrConcl   : unit Proofview.tactic
  val rewriteLR : ?tac:(unit Proofview.tactic * conditions) -> EConstr.constr -> unit Proofview.tactic
  val rewriteRL : ?tac:(unit Proofview.tactic * conditions) -> EConstr.constr  -> unit Proofview.tactic
  val general_rewrite_bindings :
    orientation -> Locus.occurrences -> freeze_evars_flag -> dep_proof_flag ->
    ?tac:(unit Proofview.tactic * conditions) -> EConstr.constr Misctypes.with_bindings -> Misctypes.evars_flag -> unit Proofview.tactic
  val discriminable : Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr -> bool
  val discrHyp : Names.Id.t -> unit Proofview.tactic
  val injectable : Environ.env -> Evd.evar_map -> keep_proofs:(bool option) -> EConstr.constr -> EConstr.constr -> bool
  val injHyp : inj_flags option -> Misctypes.clear_flag -> Names.Id.t -> unit Proofview.tactic
  val subst_gen : bool -> Names.Id.t list -> unit Proofview.tactic
end

module Contradiction :
sig
  val contradiction : EConstr.constr Misctypes.with_bindings option -> unit Proofview.tactic
  val absurd : EConstr.constr -> unit Proofview.tactic
end

module Inv :
sig
  val dinv :
    Misctypes.inversion_kind -> EConstr.constr option ->
    Tactypes.or_and_intro_pattern option -> Misctypes.quantified_hypothesis -> unit Proofview.tactic
  val inv_clause :
    Misctypes.inversion_kind -> Tactypes.or_and_intro_pattern option -> Names.Id.t list ->
    Misctypes.quantified_hypothesis -> unit Proofview.tactic
  val inv_clear_tac : Names.Id.t -> unit Proofview.tactic
  val inv_tac : Names.Id.t -> unit Proofview.tactic
  val dinv_tac : Names.Id.t -> unit Proofview.tactic
  val dinv_clear_tac : Names.Id.t -> unit Proofview.tactic
  val inv : Misctypes.inversion_kind -> Tactypes.or_and_intro_pattern option ->
            Misctypes.quantified_hypothesis -> unit Proofview.tactic
end

module Leminv :
sig
  val lemInv_clause :
    Misctypes.quantified_hypothesis -> EConstr.constr -> Names.Id.t list -> unit Proofview.tactic
  val add_inversion_lemma_exn :
    Names.Id.t -> Constrexpr.constr_expr -> Sorts.family -> bool -> (Names.Id.t -> unit Proofview.tactic) ->
    unit
end

module Hints :
sig

  type raw_hint = EConstr.t * EConstr.types * Univ.ContextSet.t

  type 'a hint_ast =
    | Res_pf     of 'a (* Hint Apply *)
    | ERes_pf    of 'a (* Hint EApply *)
    | Give_exact of 'a
    | Res_pf_THEN_trivial_fail of 'a (* Hint Immediate *)
    | Unfold_nth of Names.evaluable_global_reference       (* Hint Unfold *)
    | Extern     of Genarg.glob_generic_argument (* Hint Extern *)

  type hint

  type debug =
    | Debug | Info | Off

  type 'a hints_path_atom_gen =
    | PathHints of 'a list
    | PathAny

  type hint_term =
    | IsGlobRef of Globnames.global_reference
    | IsConstr of EConstr.constr * Univ.ContextSet.t

  type hint_db_name = string
  type hint_info = (Names.Id.t list * Pattern.constr_pattern) Vernacexpr.hint_info_gen
  type hnf = bool
  type hints_path_atom = Globnames.global_reference hints_path_atom_gen

  type 'a hints_path_gen =
    | PathAtom of 'a hints_path_atom_gen
    | PathStar of 'a hints_path_gen
    | PathSeq of 'a hints_path_gen * 'a hints_path_gen
    | PathOr of 'a hints_path_gen * 'a hints_path_gen
    | PathEmpty
    | PathEpsilon

  type hints_path = Globnames.global_reference hints_path_gen

  type hints_entry =
    | HintsResolveEntry of (hint_info * Decl_kinds.polymorphic * hnf * hints_path_atom * hint_term) list
    | HintsImmediateEntry of (hints_path_atom * Decl_kinds.polymorphic * hint_term) list
    | HintsCutEntry of hints_path
    | HintsUnfoldEntry of Names.evaluable_global_reference list
    | HintsTransparencyEntry of Names.evaluable_global_reference list * bool
    | HintsModeEntry of Globnames.global_reference * Vernacexpr.hint_mode list
    | HintsExternEntry of hint_info * Genarg.glob_generic_argument

  type 'a with_metadata = private {
      pri     : int;
      poly    : Decl_kinds.polymorphic;
      pat     : Pattern.constr_pattern option;
      name    : hints_path_atom;
      db : string option;
      secvars : Names.Id.Pred.t;
      code    : 'a;
    }
  type full_hint = hint with_metadata

  module Hint_db :
  sig
    type t
    val empty : ?name:hint_db_name -> Names.transparent_state -> bool -> t
    val transparent_state : t -> Names.transparent_state
    val iter : (Globnames.global_reference option ->
                Vernacexpr.hint_mode array list -> full_hint list -> unit) -> t -> unit
  end
  type hint_db = Hint_db.t

  val add_hints : bool -> hint_db_name list -> hints_entry -> unit
  val searchtable_map : hint_db_name -> hint_db
  val pp_hints_path_atom : ('a -> Pp.t) -> 'a hints_path_atom_gen -> Pp.t
  val pp_hints_path_gen : ('a -> Pp.t) -> 'a hints_path_gen -> Pp.t
  val glob_hints_path_atom :
    Libnames.reference hints_path_atom_gen -> Globnames.global_reference hints_path_atom_gen
  val pp_hints_path : hints_path -> Pp.t
  val glob_hints_path :
    Libnames.reference hints_path_gen -> Globnames.global_reference hints_path_gen
  val run_hint : hint ->
    ((raw_hint * Clenv.clausenv) hint_ast -> 'r Proofview.tactic) -> 'r Proofview.tactic
  val typeclasses_db : hint_db_name
  val add_hints_init : (unit -> unit) -> unit
  val create_hint_db : bool -> hint_db_name -> Names.transparent_state -> bool -> unit
  val empty_hint_info : 'a Vernacexpr.hint_info_gen
  val repr_hint : hint -> (raw_hint * Clenv.clausenv) hint_ast
  val pr_hint_db_env : Environ.env -> Evd.evar_map -> Hint_db.t -> Pp.t
  val pr_hint_db : Hint_db.t -> Pp.t
  [@@ocaml.deprecated "please used pr_hint_db_env"]
end

module Auto :
sig
  val default_auto : unit Proofview.tactic
  val full_trivial : ?debug:Hints.debug ->
                     Tactypes.delayed_open_constr list -> unit Proofview.tactic
  val h_auto   : ?debug:Hints.debug ->
                 int option -> Tactypes.delayed_open_constr list -> Hints.hint_db_name list option -> unit Proofview.tactic
  val h_trivial : ?debug:Hints.debug ->
                  Tactypes.delayed_open_constr list -> Hints.hint_db_name list option -> unit Proofview.tactic
  val new_full_auto : ?debug:Hints.debug ->
                      int -> Tactypes.delayed_open_constr list -> unit Proofview.tactic
  val full_auto : ?debug:Hints.debug ->
                  int -> Tactypes.delayed_open_constr list -> unit Proofview.tactic
  val new_auto : ?debug:Hints.debug ->
                 int -> Tactypes.delayed_open_constr list -> Hints.hint_db_name list -> unit Proofview.tactic
  val default_full_auto : unit Proofview.tactic
end

module Eauto :
sig
  val e_assumption : unit Proofview.tactic
  val e_give_exact : ?flags:Unification.unify_flags -> EConstr.constr -> unit Proofview.tactic
  val prolog_tac : Tactypes.delayed_open_constr list -> int -> unit Proofview.tactic
  val make_dimension : int option -> int option -> bool * int
  val gen_eauto : ?debug:Hints.debug -> bool * int -> Tactypes.delayed_open_constr list ->
                  Hints.hint_db_name list option -> unit Proofview.tactic
  val autounfold_tac : Hints.hint_db_name list option -> Locus.clause -> unit Proofview.tactic
  val autounfold_one : Hints.hint_db_name list -> Locus.hyp_location option -> unit Proofview.tactic
  val eauto_with_bases :
    ?debug:Hints.debug -> bool * int -> Tactypes.delayed_open_constr list -> Hints.hint_db list -> Proof_type.tactic
end

module Class_tactics :
sig

  type search_strategy =
    | Dfs
    | Bfs

  val set_typeclasses_debug : bool -> unit
  val set_typeclasses_strategy : search_strategy -> unit
  val set_typeclasses_depth : int option -> unit
  val typeclasses_eauto : ?only_classes:bool -> ?st:Names.transparent_state -> ?strategy:search_strategy ->
                        depth:(Int.t option) ->
                        Hints.hint_db_name list -> unit Proofview.tactic
  val head_of_constr : Names.Id.t -> EConstr.constr -> unit Proofview.tactic
  val not_evar : EConstr.constr -> unit Proofview.tactic
  val is_ground : EConstr.constr -> unit Proofview.tactic
  val autoapply : EConstr.constr -> Hints.hint_db_name -> unit Proofview.tactic
  val catchable : exn -> bool
end

module Eqdecide :
sig
  val compare : EConstr.constr -> EConstr.constr -> unit Proofview.tactic
  val decideEqualityGoal : unit Proofview.tactic
end

module Autorewrite :
sig
  type rew_rule = { rew_lemma: Constr.t;
                    rew_type: Constr.types;
                    rew_pat: Constr.t;
                    rew_ctx: Univ.ContextSet.t;
                    rew_l2r: bool;
                    rew_tac: Genarg.glob_generic_argument option }
  type raw_rew_rule = (Constr.t Univ.in_universe_context_set * bool *
                         Genarg.raw_generic_argument option)
                        Loc.located
  val auto_multi_rewrite : ?conds:Equality.conditions -> string list -> Locus.clause -> unit Proofview.tactic
  val auto_multi_rewrite_with : ?conds:Equality.conditions -> unit Proofview.tactic -> string list -> Locus.clause -> unit Proofview.tactic
  val add_rew_rules : string -> raw_rew_rule list -> unit
  val find_rewrites : string -> rew_rule list
  val find_matches : string -> Constr.t -> rew_rule list
  val print_rewrite_hintdb : Environ.env -> Evd.evar_map -> string -> Pp.t
end

(************************************************************************)
(* End of modules from tactics/                                         *)
(************************************************************************)

(************************************************************************)
(* Modules from vernac/                                                 *)
(************************************************************************)

module Ppvernac :
sig
  val pr_vernac : Vernacexpr.vernac_expr -> Pp.t
  val pr_rec_definition : (Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) -> Pp.t
end

module Lemmas :
sig

  type 'a declaration_hook

  val mk_hook :
    (Decl_kinds.locality -> Globnames.global_reference -> 'a) -> 'a declaration_hook
  val start_proof : Names.Id.t -> ?pl:Univdecls.universe_decl -> Decl_kinds.goal_kind -> Evd.evar_map ->
    ?terminator:(Proof_global.lemma_possible_guards -> unit declaration_hook -> Proof_global.proof_terminator) ->
    ?sign:Environ.named_context_val -> EConstr.types ->
    ?init_tac:unit Proofview.tactic -> ?compute_guard:Proof_global.lemma_possible_guards ->
    unit declaration_hook -> unit
  val call_hook :
    Future.fix_exn -> 'a declaration_hook -> Decl_kinds.locality -> Globnames.global_reference -> 'a
  val save_proof : ?proof:Proof_global.closed_proof -> Vernacexpr.proof_end -> unit
  val get_current_context : unit -> Evd.evar_map * Environ.env
  [@@ocaml.deprecated "please use [Pfedit.get_current_context]"]
end

module Himsg :
sig
  val explain_refiner_error : Environ.env -> Evd.evar_map -> Logic.refiner_error -> Pp.t
  val explain_pretype_error : Environ.env -> Evd.evar_map -> Pretype_errors.pretype_error -> Pp.t
end

module ExplainErr :
sig
  val process_vernac_interp_error : ?allow_uncaught:bool -> Util.iexn -> Util.iexn
  val register_additional_error_info : (Util.iexn -> Pp.t option Loc.located option) -> unit
end

module Locality :
sig
  val make_section_locality : bool option -> bool
  val make_module_locality : bool option -> bool
end

module Metasyntax :
sig

  val add_token_obj : string -> unit

  type any_entry = AnyEntry : 'a Pcoq.Gram.entry -> any_entry
  val register_grammar : string -> any_entry list -> unit

end

module Search :
sig
  type glob_search_about_item =
                              | GlobSearchSubPattern of Pattern.constr_pattern
                              | GlobSearchString of string
  type filter_function = Globnames.global_reference -> Environ.env -> Constr.t -> bool
  type display_function = Globnames.global_reference -> Environ.env -> Constr.t -> unit
  val search_about_filter : glob_search_about_item -> filter_function
  val module_filter : Names.DirPath.t list * bool -> filter_function
  val generic_search : int option -> display_function -> unit
end

module Obligations :
sig
  val default_tactic : unit Proofview.tactic ref
  val obligation : int * Names.Id.t option * Constrexpr.constr_expr option ->
                   Genarg.glob_generic_argument option -> unit
  val next_obligation : Names.Id.t option -> Genarg.glob_generic_argument option -> unit
  val try_solve_obligation : int -> Names.Id.t option -> unit Proofview.tactic option -> unit
  val try_solve_obligations : Names.Id.t option -> unit Proofview.tactic option -> unit
  val solve_all_obligations : unit Proofview.tactic option -> unit
  val admit_obligations : Names.Id.t option -> unit
  val show_obligations : ?msg:bool -> Names.Id.t option -> unit
  val show_term : Names.Id.t option -> Pp.t
end

module Command :
sig
  open Names
  open Constrexpr
  open Vernacexpr

  type structured_fixpoint_expr = {
    fix_name : Id.t;
    fix_univs : universe_decl_expr option;
    fix_annot : Id.t Loc.located option;
    fix_binders : local_binder_expr list;
    fix_body : constr_expr option;
    fix_type : constr_expr
  }

  type structured_one_inductive_expr = {
    ind_name : Id.t;
    ind_univs : universe_decl_expr option;
    ind_arity : constr_expr;
    ind_lc : (Id.t * constr_expr) list
  }

  type structured_inductive_expr =
    local_binder_expr list * structured_one_inductive_expr list

  type recursive_preentry = Names.Id.t list * Constr.t option list * Constr.types list

  type one_inductive_impls

  val do_mutual_inductive :
    (Vernacexpr.one_inductive_expr * Vernacexpr.decl_notation list) list -> Decl_kinds.cumulative_inductive_flag -> Decl_kinds.polymorphic ->
    Decl_kinds.private_flag -> Declarations.recursivity_kind -> unit

  val do_definition : Names.Id.t -> Decl_kinds.definition_kind -> Vernacexpr.universe_decl_expr option ->
    Constrexpr.local_binder_expr list -> Redexpr.red_expr option -> Constrexpr.constr_expr ->
    Constrexpr.constr_expr option -> unit Lemmas.declaration_hook -> unit

  val do_fixpoint :
    Decl_kinds.locality -> Decl_kinds.polymorphic -> (Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) list -> unit

  val extract_fixpoint_components : bool ->
    (Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) list ->
    structured_fixpoint_expr list * Vernacexpr.decl_notation list

  val interp_fixpoint :
    structured_fixpoint_expr list -> Vernacexpr.decl_notation list ->
    recursive_preentry * Univdecls.universe_decl * UState.t *
      (EConstr.rel_context * Impargs.manual_implicits * int option) list

  val extract_mutual_inductive_declaration_components :
    (Vernacexpr.one_inductive_expr * Vernacexpr.decl_notation list) list ->
    structured_inductive_expr * Libnames.qualid list * Vernacexpr.decl_notation list

  val interp_mutual_inductive :
    structured_inductive_expr -> Vernacexpr.decl_notation list ->
    Decl_kinds.cumulative_inductive_flag ->
    Decl_kinds.polymorphic ->
    Decl_kinds.private_flag -> Declarations.recursivity_kind ->
    Entries.mutual_inductive_entry * Universes.universe_binders * one_inductive_impls list

  val declare_mutual_inductive_with_eliminations :
    Entries.mutual_inductive_entry -> Universes.universe_binders -> one_inductive_impls list ->
    Names.MutInd.t
end

module Classes :
sig
  val set_typeclass_transparency : Names.evaluable_global_reference -> bool -> bool -> unit
  val new_instance :
    ?abstract:bool ->
    ?global:bool ->
    ?refine:bool ->
    Decl_kinds.polymorphic ->
    Constrexpr.local_binder_expr list ->
    Vernacexpr.typeclass_constraint ->
    (bool * Constrexpr.constr_expr) option ->
    ?generalize:bool ->
    ?tac:unit Proofview.tactic  ->
    ?hook:(Globnames.global_reference -> unit) ->
    Vernacexpr.hint_info_expr ->
    Names.Id.t
end

module Vernacstate :
sig

  type t = {
    system  : States.state;        (* summary + libstack *)
    proof   : Proof_global.t;      (* proof state *)
    shallow : bool                 (* is the state trimmed down (libstack) *)
  }

  (* XXX: This should not be exported *)
  val freeze_interp_state : Summary.marshallable -> t
  val unfreeze_interp_state : t -> unit

end

module Vernacinterp :
sig

  type deprecation = bool

  type atts = {
    loc : Loc.t option;
    locality : bool option;
    polymorphic : bool;
  }

  type 'a vernac_command = 'a -> atts:atts -> st:Vernacstate.t -> Vernacstate.t

  type plugin_args = Genarg.raw_generic_argument list

  val vinterp_add : deprecation -> Vernacexpr.extend_name -> plugin_args vernac_command -> unit

end

module Mltop :
sig
  val declare_cache_obj : (unit -> unit) -> string -> unit
  val add_known_plugin : (unit -> unit) -> string -> unit
  val add_known_module : string -> unit
  val module_is_known : string -> bool
end

module Topfmt :
sig
  val std_ft : Format.formatter ref
  val with_output_to : out_channel -> Format.formatter
  val get_margin : unit -> int option
end

module Vernacentries :
sig

  val dump_global : Libnames.reference Misctypes.or_by_notation -> unit
  val interp_redexp_hook : (Environ.env -> Evd.evar_map -> Genredexpr.raw_red_expr ->
                            Evd.evar_map * Redexpr.red_expr) Hook.t
  val command_focus : unit Proof.focus_kind
end

(************************************************************************)
(* End of modules from vernac/                                          *)
(************************************************************************)

(************************************************************************)
(* Modules from stm/                                                    *)
(************************************************************************)

module Vernac_classifier :
sig
  val declare_vernac_classifier :
    Vernacexpr.extend_name -> (Genarg.raw_generic_argument list -> unit -> Vernacexpr.vernac_classification) -> unit
  val classify_as_proofstep : Vernacexpr.vernac_classification
  val classify_as_query : Vernacexpr.vernac_classification
  val classify_as_sideeff : Vernacexpr.vernac_classification
  val classify_vernac : Vernacexpr.vernac_expr -> Vernacexpr.vernac_classification
end

module Stm :
sig
  type doc

  val get_doc : Feedback.doc_id -> doc

  val state_of_id : doc:doc ->
    Stateid.t -> [ `Valid of Vernacstate.t option | `Expired | `Error of exn ]
end

(************************************************************************)
(* End of modules from stm/                                             *)
(************************************************************************)
