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
open Engine_API
open Library_API

(************************************************************************)
(* Modules from pretyping/                                              *)
(************************************************************************)

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
  val pr_state : state -> Pp.std_ppcmds
  module Stack :
  sig
    type 'a t
    val pr : ('a -> Pp.std_ppcmds) -> 'a t -> Pp.std_ppcmds
  end
  module Cst_stack :
  sig
    type t
    val pr : t -> Pp.std_ppcmds
  end
end

module Inductiveops :
sig
  type inductive_family
  type inductive_type =
    | IndType of inductive_family * EConstr.constr list
  type constructor_summary =
    {
      cs_cstr : Term.pconstructor;
      cs_params : Constr.t list;
      cs_nargs : int;
      cs_args : Context.Rel.t;
      cs_concl_realargs : Constr.t array;
    }

  val arities_of_constructors : Environ.env -> Term.pinductive -> Term.types array
  val constructors_nrealargs_env : Environ.env -> Names.inductive -> int array
  val constructor_nallargs_env : Environ.env -> Names.constructor -> int

  val inductive_nparams : Names.inductive -> int

  val inductive_nparamdecls : Names.inductive -> int

  val type_of_constructors : Environ.env -> Term.pinductive -> Term.types array
  val find_mrectype : Environ.env -> Evd.evar_map -> EConstr.types -> (Names.inductive * EConstr.EInstance.t) * EConstr.constr list
  val mis_is_recursive :
    Names.inductive * Declarations.mutual_inductive_body * Declarations.one_inductive_body -> bool
  val nconstructors : Names.inductive -> int
  val find_rectype : Environ.env -> Evd.evar_map -> EConstr.types -> inductive_type
  val get_constructors : Environ.env -> inductive_family -> constructor_summary array
  val dest_ind_family : inductive_family -> Names.inductive Term.puniverses * Constr.t list
  val find_inductive   : Environ.env -> Evd.evar_map -> EConstr.types -> (Names.inductive * EConstr.EInstance.t) * Constr.t list
  val type_of_inductive : Environ.env -> Term.pinductive -> Term.types
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
  val get_sort_family_of : ?polyprop:bool -> Environ.env -> Evd.evar_map -> EConstr.types -> Sorts.family
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

module Stm :
sig
  type state
  val state_of_id :
    Stateid.t -> [ `Valid of state option | `Expired | `Error of exn ]
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

  val empty_lvar : Glob_term.ltac_var_map

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
    Evd.evar_map -> Pattern.extended_patvar_map ->
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
    EConstr.constr -> bound_ident_map * Pattern.extended_patvar_map
  exception PatternMatchingFailure
  type matching_result =
    { m_sub : bound_ident_map * Pattern.patvar_map;
      m_ctx : EConstr.constr }
  val match_subterm_gen : Environ.env -> Evd.evar_map ->
                          bool ->
                          binding_bound_vars * Pattern.constr_pattern -> EConstr.constr ->
                          matching_result IStream.t
  val matches : Environ.env -> Evd.evar_map -> Pattern.constr_pattern -> EConstr.constr -> Pattern.patvar_map
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
  type inductive_flag = Decl_kinds.recursivity_kind
  type lname = Names.Name.t Loc.located
  type lident = Names.Id.t Loc.located
  type opacity_flag =
                    | Opaque of lident list option
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
                   | VtStm of vernac_control * vernac_part_of_script
                   | VtUnknown
   and vernac_qed_type =
     | VtKeep
     | VtKeepAsAxiom
     | VtDrop
   and vernac_start = string * opacity_guarantee * Names.Id.t list
   and vernac_sideff_type = Names.Id.t list
   and vernac_part_of_script = bool
   and vernac_control =
     | VtWait
     | VtJoinDocument
     | VtBack of Stateid.t
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

  type obsolete_locality = bool

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

  type plident = lident * lident list option

  type inductive_expr = plident with_coercion * Constrexpr.local_binder_expr list * Constrexpr.constr_expr option * inductive_kind * constructor_list_or_record_decl_expr

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

  type definition_expr =
    | ProveBody of local_binder_expr list * constr_expr
    | DefineBody of local_binder_expr list * Genredexpr.raw_red_expr option * constr_expr
                    * constr_expr option
  type proof_expr =
    plident option * (local_binder_expr list * constr_expr)

  type proof_end =
    | Admitted
    | Proved of opacity_flag * lident option

  type fixpoint_expr = plident * (Names.Id.t Loc.located option * Constrexpr.recursion_order_expr) * Constrexpr.local_binder_expr list * Constrexpr.constr_expr * Constrexpr.constr_expr option

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
  type stm_vernac
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

  type vernac_expr =
  | VernacLoad of verbose_flag * string
  | VernacTime of vernac_expr Loc.located
  | VernacRedirect of string * vernac_expr Loc.located
  | VernacTimeout of int * vernac_expr
  | VernacFail of vernac_expr
  | VernacSyntaxExtension of
      obsolete_locality * (lstring * syntax_modifier list)
  | VernacOpenCloseScope of obsolete_locality * (bool * scope_name)
  | VernacDelimiters of scope_name * string option
  | VernacBindScope of scope_name * class_rawexpr list
  | VernacInfix of obsolete_locality * (lstring * syntax_modifier list) *
      Constrexpr.constr_expr * scope_name option
  | VernacNotation of
      obsolete_locality * Constrexpr.constr_expr * (lstring * syntax_modifier list) *
      scope_name option
  | VernacNotationAddFormat of string * string * string
  | VernacDefinition of
      (Decl_kinds.locality option * Decl_kinds.definition_object_kind) * plident * definition_expr
  | VernacStartTheoremProof of Decl_kinds.theorem_kind * proof_expr list
  | VernacEndProof of proof_end
  | VernacExactProof of Constrexpr.constr_expr
  | VernacAssumption of (Decl_kinds.locality option * Decl_kinds.assumption_object_kind) *
      inline * (plident list * Constrexpr.constr_expr) with_coercion list
  | VernacInductive of Decl_kinds.cumulative_inductive_flag * Decl_kinds.private_flag * inductive_flag * (inductive_expr * decl_notation list) list
  | VernacFixpoint of
      Decl_kinds.locality option * (fixpoint_expr * decl_notation list) list
  | VernacCoFixpoint of
      Decl_kinds.locality option * (cofixpoint_expr * decl_notation list) list
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
  | VernacCoercion of obsolete_locality * Libnames.reference Misctypes.or_by_notation *
      class_rawexpr * class_rawexpr
  | VernacIdentityCoercion of obsolete_locality * lident *
      class_rawexpr * class_rawexpr
  | VernacNameSectionHypSet of lident * section_subset_expr
  | VernacInstance of
      bool *
      Constrexpr.local_binder_expr list *
        Constrexpr.typeclass_constraint *
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
  | VernacHints of obsolete_locality * string list * hints_expr
  | VernacSyntacticDefinition of Names.Id.t Loc.located * (Names.Id.t list * Constrexpr.constr_expr) *
      obsolete_locality * onlyparsing_flag
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
  | VernacStm of stm_vernac
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
    plident * Constrexpr.local_binder_expr list * Constrexpr.constr_expr option * constructor_expr list
end

(* XXX: end manual intf move *)

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
  val pr_cl_index : cl_index -> Pp.std_ppcmds
end

module Detyping :
sig
  val print_universes : bool ref
  val print_evar_arguments : bool ref
  val detype : ?lax:bool -> bool -> Names.Id.t list -> Environ.env -> Evd.evar_map -> EConstr.constr -> Glob_term.glob_constr
  val subst_glob_constr : Mod_subst.substitution -> Glob_term.glob_constr -> Glob_term.glob_constr
  val set_detype_anonymous : (?loc:Loc.t -> int -> Glob_term.glob_constr) -> unit
end

module Indrec :
sig
  type dep_flag = bool
  val lookup_eliminator : Names.inductive -> Sorts.family -> Globnames.global_reference
  val build_case_analysis_scheme : Environ.env -> Evd.evar_map -> Term.pinductive ->
                                   dep_flag -> Sorts.family -> Evd.evar_map * Constr.t
  val make_elimination_ident : Names.Id.t -> Sorts.family -> Names.Id.t
  val build_mutual_induction_scheme :
    Environ.env -> Evd.evar_map -> (Term.pinductive * dep_flag * Sorts.family) list -> Evd.evar_map * Constr.t list
  val build_case_analysis_scheme_default : Environ.env -> Evd.evar_map -> Term.pinductive ->
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

  type pure_open_constr = Evd.evar_map * EConstr.constr
  type glob_constr_ltac_closure = Glob_term.ltac_var_map * Glob_term.glob_constr

  val understand_ltac : inference_flags ->
                        Environ.env -> Evd.evar_map -> Glob_term.ltac_var_map ->
                        typing_constraint -> Glob_term.glob_constr -> pure_open_constr
  val understand_tcc : ?flags:inference_flags -> Environ.env -> Evd.evar_map ->
                       ?expected_type:typing_constraint -> Glob_term.glob_constr -> Evd.evar_map * EConstr.constr
  val type_uconstr :
    ?flags:inference_flags ->
    ?expected_type:typing_constraint ->
    Geninterp.interp_sign -> Glob_term.closed_glob_constr -> EConstr.constr Tactypes.delayed_open
  val understand : ?flags:inference_flags -> ?expected_type:typing_constraint ->
                   Environ.env -> Evd.evar_map -> Glob_term.glob_constr -> Constr.t Evd.in_evar_universe_context
  val check_evars : Environ.env -> Evd.evar_map -> Evd.evar_map -> EConstr.constr -> unit
  val interp_elimination_sort : Misctypes.glob_sort -> Sorts.family
  val register_constr_interp0 :
    ('r, 'g, 't) Genarg.genarg_type ->
    (Glob_term.unbound_ltac_var_map -> Environ.env -> Evd.evar_map -> EConstr.types -> 'g -> EConstr.constr * Evd.evar_map) -> unit
  val all_and_fail_flags : inference_flags
  val ise_pretype_gen :
    inference_flags -> Environ.env -> Evd.evar_map ->
    Glob_term.ltac_var_map -> typing_constraint -> Glob_term.glob_constr -> Evd.evar_map * EConstr.constr
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

(************************************************************************)
(* End of modules from pretyping/                                       *)
(************************************************************************)
