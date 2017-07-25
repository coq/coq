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

open Kernel_API
open Intf_API
open Library_API

(************************************************************************)
(* Modules from engine/                                                 *)
(************************************************************************)

module Universes :
sig
  type universe_binders
  type universe_opt_subst
  val fresh_inductive_instance : Environ.env -> Names.inductive -> Term.pinductive Univ.in_universe_context_set
  val new_Type : Names.DirPath.t -> Term.types
  val type_of_global : Globnames.global_reference -> Term.types Univ.in_universe_context_set
  val constr_of_global : Globnames.global_reference -> Constr.t
  val new_univ_level : Names.DirPath.t -> Univ.Level.t
  val new_sort_in_family : Sorts.family -> Sorts.t
  val pr_with_global_universes : Univ.Level.t -> Pp.std_ppcmds
  val pr_universe_opt_subst : universe_opt_subst -> Pp.std_ppcmds
  type universe_constraint

  module Constraints :
  sig
    type t
    val pr : t -> Pp.std_ppcmds
  end

  type universe_constraints = Constraints.t
end

module UState :
sig
  type t
  val context : t -> Univ.UContext.t
  val context_set : t -> Univ.ContextSet.t
  val of_context_set : Univ.ContextSet.t -> t

  type rigid =
    | UnivRigid
    | UnivFlexible of bool

end

(* XXX: Moved from intf *)
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
         | SubEvar of Constr.existential_key
end

module Evd :
sig

  type evar = Constr.existential_key

  val string_of_existential : Evar.t -> string
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
    val find_undefined : evar_map -> evar -> evar_info
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

    val meta_declare : Constr.metavariable -> Term.types -> ?name:Names.Name.t -> evar_map -> evar_map

    val clear_metas : evar_map -> evar_map

    (** Allocates a new evar that represents a {i sort}. *)
    val new_sort_variable : ?loc:Loc.t -> ?name:string -> rigid -> evar_map -> evar_map * Sorts.t

    val remove : evar_map -> Evar.t -> evar_map
    val fresh_global : ?loc:Loc.t -> ?rigid:rigid -> ?names:Univ.Instance.t -> Environ.env ->
                       evar_map -> Globnames.global_reference -> evar_map * Constr.t
    val evar_filtered_context : evar_info -> Context.Named.t
    val fresh_inductive_instance : ?loc:Loc.t -> Environ.env -> evar_map -> Names.inductive -> evar_map * Term.pinductive
    val fold_undefined : (Evar.t -> evar_info -> 'a -> 'a) -> evar_map -> 'a -> 'a

    val universe_context_set : evar_map -> Univ.ContextSet.t
    val evar_ident : evar -> evar_map -> Names.Id.t option
    val extract_all_conv_pbs : evar_map -> evar_map * evar_constraint list
    val universe_context : ?names:(Names.Id.t Loc.located) list -> evar_map ->
                           (Names.Id.t * Univ.Level.t) list * Univ.UContext.t
    val nf_constraints : evar_map -> evar_map
    val from_ctx : UState.t -> evar_map

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

  val existential_opt_value : evar_map -> Term.existential -> Constr.t option
  val existential_value : evar_map -> Term.existential -> Constr.t

  exception NotInstantiatedEvar

  val fresh_sort_in_family : ?loc:Loc.t -> ?rigid:rigid -> Environ.env -> evar_map -> Sorts.family -> evar_map * Sorts.t
end

(* XXX: moved from intf *)
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
     | CCases of Term.case_style
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

  type typeclass_constraint = (Names.Name.t Loc.located * Names.Id.t Loc.located list option) * Decl_kinds.binding_kind * constr_expr
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

(* XXX: end of moved from intf *)

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
  val eq_constr_universes : Evd.evar_map -> constr -> constr -> Universes.universe_constraints option
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

(* XXX: Located manually from intf *)
module Pattern :
sig

  type case_info_pattern =
    { cip_style : Misctypes.case_style;
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
    | PFix of Term.fixpoint
    | PCoFix of Term.cofixpoint

  type constr_under_binders = Names.Id.t list * EConstr.constr

  (** Types of substitutions with or w/o bound variables *)

  type patvar_map = EConstr.constr Names.Id.Map.t
  type extended_patvar_map = constr_under_binders Names.Id.Map.t

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
  val next_ident_away : Names.Id.t -> Names.Id.t list -> Names.Id.t

  val hdchar : Environ.env -> Evd.evar_map -> EConstr.types -> string
  val id_of_name_using_hdchar : Environ.env -> Evd.evar_map -> EConstr.types -> Names.Name.t -> Names.Id.t
  val next_ident_away_in_goal : Names.Id.t -> Names.Id.t list -> Names.Id.t
  val default_dependent_ident : Names.Id.t
  val next_global_ident_away : Names.Id.t -> Names.Id.t list -> Names.Id.t
  val rename_bound_vars_as_displayed :
    Evd.evar_map -> Names.Id.t list -> Names.Name.t list -> EConstr.types -> EConstr.types
end

module Termops :
sig
  val it_mkLambda_or_LetIn : Constr.t -> Context.Rel.t -> Constr.t
  val local_occur_var : Evd.evar_map -> Names.Id.t -> EConstr.constr -> bool
  val occur_var : Environ.env -> Evd.evar_map -> Names.Id.t -> EConstr.constr -> bool
  val pr_evar_info : Evd.evar_info -> Pp.std_ppcmds

  val print_constr : EConstr.constr -> Pp.std_ppcmds

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

  (** Remove the outer-most {!Term.kind_of_term.Cast} from a given term. *)
  val strip_outer_cast : Evd.evar_map -> EConstr.constr -> EConstr.constr

  (** [nb_lam] ⟦[fun (x1:t1)...(xn:tn) => c]⟧ where [c] is not an abstraction gives [n].
      Casts are ignored. *)
  val nb_lam : Evd.evar_map -> EConstr.constr -> int

  (** [push_rel_assum env_assumtion env] adds a given {i env assumption} to the {i env context} of a given {i environment}. *)
  val push_rel_assum : Names.Name.t * EConstr.types -> Environ.env -> Environ.env

  (** [push_rels_assum env_assumptions env] adds given {i env assumptions} to the {i env context} of a given {i environment}. *)
  val push_rels_assum : (Names.Name.t * Term.types) list -> Environ.env -> Environ.env

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
  val print_named_context : Environ.env -> Pp.std_ppcmds
  val print_constr_env : Environ.env -> Evd.evar_map -> EConstr.constr -> Pp.std_ppcmds
  val clear_named_body : Names.Id.t -> Environ.env -> Environ.env
  val is_Prop : Evd.evar_map -> EConstr.constr -> bool
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
  val pr_metaset : Evd.Metaset.t -> Pp.std_ppcmds
  val pr_evar_map : ?with_univs:bool -> int option -> Evd.evar_map -> Pp.std_ppcmds
  val pr_evar_universe_context : UState.t -> Pp.std_ppcmds
end

module Proofview_monad :
sig
  type lazy_msg = unit -> Pp.std_ppcmds
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
  val safe_evar_value : Evd.evar_map -> Term.existential -> Constr.t option
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
    val print_debug : Pp.std_ppcmds -> unit t
    val print_warning : Pp.std_ppcmds -> unit t
    val print_notice : Pp.std_ppcmds -> unit t
    val print_info : Pp.std_ppcmds -> unit t
    val run : 'a t -> 'a
    type 'a ref
    val ref : 'a -> 'a ref t
    val ( := ) : 'a ref -> 'a -> unit t
    val ( ! ) : 'a ref -> 'a t
    val raise : ?info:Exninfo.info -> exn -> 'a t
    val catch : 'a t -> (Exninfo.iexn -> 'a t) -> 'a t
    val read_line : string t
  end
  val proofview : proofview -> Evd.evar list * Evd.evar_map
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
                                                     * (bool * Evd.evar list * Evd.evar list)
                                                     * Proofview_monad.Info.tree
  val numgoals : int tactic
  val with_shelf : 'a tactic -> (Evd.evar list * 'a) tactic

  module Unsafe :
  sig
    val tclEVARS : Evd.evar_map -> unit tactic

    val tclGETGOALS : Evd.evar list tactic

    val tclSETGOALS : Evd.evar list -> unit tactic

    val tclNEWGOALS : Evd.evar list -> unit tactic
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
    val pr : 'a typ -> Pp.std_ppcmds
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

(* XXX: Located manually from intf *)
module Glob_term :
sig
  type cases_pattern_r =
    | PatVar  of Names.Name.t
    | PatCstr of Names.constructor * cases_pattern list * Names.Name.t
  and cases_pattern = cases_pattern_r CAst.t
  type existential_name = Names.Id.t
  type glob_constr_r =
    | GRef of Globnames.global_reference * Misctypes.glob_level list option
        (** An identifier that represents a reference to an object defined
            either in the (global) environment or in the (local) context. *)
    | GVar of Names.Id.t
        (** An identifier that cannot be regarded as "GRef".
            Bound variables are typically represented this way. *)
    | GEvar   of existential_name * (Names.Id.t * glob_constr) list
    | GPatVar of Evar_kinds.matching_var_kind
    | GApp    of glob_constr * glob_constr list
    | GLambda of Names.Name.t * Decl_kinds.binding_kind *  glob_constr * glob_constr
    | GProd   of Names.Name.t * Decl_kinds.binding_kind * glob_constr * glob_constr
    | GLetIn  of Names.Name.t * glob_constr * glob_constr option * glob_constr
    | GCases  of Term.case_style * glob_constr option * tomatch_tuples * cases_clauses
    | GLetTuple of Names.Name.t list * (Names.Name.t * glob_constr option) * glob_constr * glob_constr
    | GIf   of glob_constr * (Names.Name.t * glob_constr option) * glob_constr * glob_constr
    | GRec  of fix_kind * Names.Id.t array * glob_decl list array *
               glob_constr array * glob_constr array
    | GSort of Misctypes.glob_sort
    | GHole of Evar_kinds.t * Misctypes.intro_pattern_naming_expr * Genarg.glob_generic_argument option
    | GCast of glob_constr * glob_constr Misctypes.cast_type

   and glob_constr = glob_constr_r CAst.t

   and glob_decl = Names.Name.t * Decl_kinds.binding_kind * glob_constr option * glob_constr

   and fix_recursion_order =
     | GStructRec
     | GWfRec of glob_constr
     | GMeasureRec of glob_constr * glob_constr option

   and fix_kind =
     | GFix of ((int option * fix_recursion_order) array * int)
     | GCoFix of int

   and predicate_pattern =
     Names.Name.t * (Names.inductive * Names.Name.t list) Loc.located option

   and tomatch_tuple = (glob_constr * predicate_pattern)

   and tomatch_tuples = tomatch_tuple list

   and cases_clause = (Names.Id.t list * cases_pattern list * glob_constr) Loc.located
   and cases_clauses = cases_clause list

   (** A globalised term together with a closure representing the value
       of its free variables. Intended for use when these variables are taken
       from the Ltac environment. *)

   type closure = {
     idents : Names.Id.t Names.Id.Map.t;
     typed  : Pattern.constr_under_binders Names.Id.Map.t ;
     untyped: closed_glob_constr Names.Id.Map.t }
   and closed_glob_constr = {
     closure: closure;
     term: glob_constr }

   (** Ltac variable maps *)
   type var_map = Pattern.constr_under_binders Names.Id.Map.t
   type uconstr_var_map = closed_glob_constr Names.Id.Map.t
   type unbound_ltac_var_map = Geninterp.Val.t Names.Id.Map.t

   type ltac_var_map = {
     ltac_constrs : var_map;
     (** Ltac variables bound to constrs *)
     ltac_uconstrs : uconstr_var_map;
     (** Ltac variables bound to untyped constrs *)
     ltac_idents: Names.Id.t Names.Id.Map.t;
     (** Ltac variables bound to identifiers *)
     ltac_genargs : unbound_ltac_var_map;
     (** Ltac variables bound to other kinds of arguments *)
   }

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
                       | NCases of Term.case_style * notation_constr option *
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
end

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

(* XXX: end of moved from intf *)

(************************************************************************)
(* End of modules from engine/                                          *)
(************************************************************************)
