(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constrexpr
open Libnames

(** Vernac expressions, produced by the parser *)
type coercion_class = FunClass | SortClass | RefClass of qualid or_by_notation

type goal_identifier = string
type scope_name = string

type scope_delimiter = delimiter_depth * scope_name

type goal_reference =
  | OpenSubgoals
  | NthGoal of int
  | GoalId of Id.t

type debug_univ_name =
  | NamedUniv of qualid
  | RawUniv of lstring

type print_universes = {
  sort : bool;
  subgraph : debug_univ_name list option;
  with_sources : bool option;
  file : string option;
}

type printable =
  | PrintTypingFlags
  | PrintTables
  | PrintFullContext
  | PrintSectionContext of qualid
  | PrintInspect of int
  | PrintGrammar of string list
  | PrintCustomGrammar of string
  | PrintKeywords
  | PrintLoadPath of DirPath.t option
  | PrintLibraries
  | PrintModule of qualid
  | PrintModuleType of qualid
  | PrintNamespace of DirPath.t
  | PrintMLLoadPath
  | PrintMLModules
  | PrintDebugGC
  | PrintName of qualid or_by_notation * UnivNames.full_name_list option
  | PrintGraph
  | PrintClasses
  | PrintTypeclasses
  | PrintInstances of qualid or_by_notation
  | PrintCoercions
  | PrintCoercionPaths of coercion_class * coercion_class
  | PrintCanonicalConversions of qualid or_by_notation list
  | PrintUniverses of print_universes
  | PrintHint of qualid or_by_notation
  | PrintHintGoal
  | PrintHintDbName of string
  | PrintHintDb
  | PrintScopes
  | PrintScope of string
  | PrintVisibility of string option
  | PrintAbout of qualid or_by_notation * UnivNames.full_name_list option * Goal_select.t option
  | PrintImplicit of qualid or_by_notation
  | PrintAssumptions of bool * bool * qualid or_by_notation
  | PrintStrategy of qualid or_by_notation option
  | PrintRegistered
  | PrintRegisteredSchemes
  | PrintNotation of Constrexpr.notation_entry * string

type glob_search_where = InHyp | InConcl | Anywhere

type search_item =
  | SearchSubPattern of (glob_search_where * bool) * constr_pattern_expr
  | SearchString of (glob_search_where * bool) * string * scope_delimiter option
  | SearchKind of Decls.logical_kind

type search_request =
  | SearchLiteral of search_item
  | SearchDisjConj of (bool * search_request) list list

type searchable =
  | SearchPattern of constr_pattern_expr
  | SearchRewrite of constr_pattern_expr
  | Search of (bool * search_request) list

type locatable =
  | LocateAny of qualid or_by_notation
  | LocateTerm of qualid or_by_notation
  | LocateLibrary of qualid
  | LocateModule of qualid
  | LocateOther of string * qualid
  | LocateFile of string

type showable =
  | ShowGoal of goal_reference
  | ShowProof
  | ShowExistentials
  | ShowUniverses
  | ShowProofNames
  | ShowIntros of bool
  | ShowMatch of qualid

type comment =
  | CommentConstr of constr_expr
  | CommentString of string
  | CommentInt of int

type 'a search_restriction =
  | SearchInside of 'a
  | SearchOutside of 'a

type verbose_flag   = bool (* true = Verbose;       false = Silent         *)
type coercion_flag  = AddCoercion | NoCoercion
type instance_flag  = BackInstance | NoInstance

type export_flag = Lib.export_flag = Export | Import

type import_categories = {
  negative : bool;
  import_cats : string CAst.t list;
}

type export_with_cats = export_flag * import_categories option

type infix_flag     = bool (* true = Infix;         false = Notation       *)

type one_import_filter_name = qualid * bool (* import inductive components *)
type import_filter_expr =
  | ImportAll
  | ImportNames of one_import_filter_name list

type locality_flag  = bool (* true = Local *)

type option_setting =
  | OptionUnset
  | OptionSetTrue
  | OptionSetInt of int
  | OptionSetString of string

(** Identifier and optional list of bound universes and constraints. *)

type definition_expr =
  | ProveBody of local_binder_expr list * constr_expr
  | DefineBody of local_binder_expr list * Genredexpr.raw_red_expr option * constr_expr
      * constr_expr option

type notation_format =
  | TextFormat of lstring

type syntax_modifier =
  | SetItemLevel of string list * Notation_term.notation_binder_kind option * Extend.production_level
  | SetItemScope of string list * scope_name
  | SetLevel of int
  | SetCustomEntry of string * int option
  | SetAssoc of Gramlib.Gramext.g_assoc
  | SetEntryType of string * Extend.simple_constr_prod_entry_key
  | SetOnlyParsing
  | SetOnlyPrinting
  | SetFormat of notation_format

type notation_enable_modifier =
  | EnableNotationEntry of notation_entry CAst.t
  | EnableNotationOnly of Notationextern.notation_use
  | EnableNotationAll

type notation_declaration =
  { ntn_decl_string : lstring
  ; ntn_decl_interp : constr_expr
  ; ntn_decl_scope : scope_name option
  ; ntn_decl_modifiers : syntax_modifier CAst.t list
  }

type recursion_order_expr =
  | CFixRecOrder of fixpoint_order_expr option list
  | CCoFixRecOrder
  | CUnknownRecOrder

type recursive_expr_gen =
  { fname : lident
  ; univs : universe_decl_expr option
  ; binders : local_binder_expr list
  ; rtype : constr_expr
  ; body_def : constr_expr option
  ; notations : notation_declaration list
  }

type fixpoint_expr = fixpoint_order_expr option * recursive_expr_gen
type fixpoints_expr = fixpoint_order_expr option list * recursive_expr_gen list
type cofixpoints_expr = recursive_expr_gen list
type recursives_expr = recursion_order_expr * recursive_expr_gen list

type local_decl_expr =
  | AssumExpr of lname * local_binder_expr list * constr_expr
  | DefExpr of lname * local_binder_expr list * constr_expr * constr_expr option

type inductive_kind = Inductive_kw | CoInductive | Variant | Record | Structure | Class of bool (* true = definitional, false = inductive *)
type simple_binder = lident list  * constr_expr
type class_binder = lident * constr_expr list
type 'a with_coercion = coercion_flag * 'a
type 'a with_coercion_instance = (Attributes.vernac_flags * coercion_flag * instance_flag) * 'a
(* Attributes of a record field declaration *)
type record_field_attr = {
  rf_coercion: coercion_flag; (* the projection is an implicit coercion *)
  rf_reversible: bool option; (* coercion is reversible, if relevant *)
  rf_instance: instance_flag; (* the projection is an instance *)
  rf_priority: int option; (* priority of the instance, if relevant *)
  rf_locality: Goptions.option_locality; (* locality of coercion and instance *)
  rf_notation: notation_declaration list;
  rf_canonical: bool; (* use this projection in the search for canonical instances *)
  }
(* Same before parsing the attributes *)
type record_field_attr_unparsed = {
  rfu_attrs: Attributes.vernac_flags;
  rfu_coercion: coercion_flag;
  rfu_instance: instance_flag;
  rfu_priority: int option;
  rfu_notation: notation_declaration list;
  }
type constructor_expr = (lident * constr_expr) with_coercion_instance
type constructor_list_or_record_decl_expr =
  | Constructors of constructor_expr list
  | RecordDecl of lident option * (local_decl_expr * record_field_attr_unparsed) list * lident option
type inductive_params_expr = local_binder_expr list * local_binder_expr list option
(** If the option is nonempty the "|" marker was used *)

type inductive_expr =
  cumul_ident_decl with_coercion
  * inductive_params_expr * constr_expr option
  * constructor_list_or_record_decl_expr

type one_inductive_expr =
  lident * inductive_params_expr * constr_expr option * constructor_expr list

type typeclass_constraint = name_decl * Glob_term.binding_kind * constr_expr
and typeclass_context = typeclass_constraint list

type proof_expr =
  ident_decl * (local_binder_expr list * constr_expr)

type opacity_flag = Opaque | Transparent

type proof_end =
  | Admitted
  (*                         name in `Save ident` when closing goal *)
  | Proved of opacity_flag * lident option

type scheme_type =
  | SchemeInduction
  | SchemeMinimality
  | SchemeElimination
  | SchemeCase

type equality_scheme_type =
  | SchemeBooleanEquality
  | SchemeEquality

  (* The data of a Scheme decleration *)
type scheme = {
  sch_type : scheme_type ;
  sch_qualid : Libnames.qualid Constrexpr.or_by_notation ;
  sch_sort : Sorts.family ;
}

type section_subset_expr =
  | SsEmpty
  | SsType
  | SsSingl of lident
  | SsCompl of section_subset_expr
  | SsUnion of section_subset_expr * section_subset_expr
  | SsSubstr of section_subset_expr * section_subset_expr
  | SsFwdClose of section_subset_expr

(** Extension identifiers for the VERNAC EXTEND mechanism.

    {b ("Extraction", 0} indicates {b Extraction {i qualid}} command.

    {b ("Extraction", 1} indicates {b Recursive Extraction {i qualid}} command.

    {b ("Extraction", 2)} indicates {b Extraction "{i filename}" {i qualid{_ 1}} ... {i qualid{_ n}}} command.

    {b ("ExtractionLibrary", 0)} indicates {b Extraction Library {i ident}} command.

    {b ("RecursiveExtractionLibrary", 0)} indicates {b Recursive Extraction Library {i ident}} command.

    {b ("SeparateExtraction", 0)} indicates {b Separate Extraction {i qualid{_ 1}} ... {i qualid{_ n}}} command.

    {b ("ExtractionLanguage", 0)} indicates {b Extraction Language Ocaml} or {b Extraction Language Haskell} or {b Extraction Language Scheme} or {b Extraction Language JSON} commands.

    {b ("ExtractionImplicit", 0)} indicates {b Extraction Implicit {i qualid} \[ {i ident{_1}} ... {i ident{_n} } \] } command.

    {b ("ExtractionConstant", 0)} indicates {b Extract Constant {i qualid} => {i string}} command.

    {b ("ExtractionInlinedConstant", 0)} indicates {b Extract Inlined Constant {i qualid} => {i string}} command.

    {b ("ExtractionInductive", 0)} indicates {b Extract Inductive {i qualid} => {i string} [ {i string} ... {string} ] {i optstring}} command.

    {b ("ExtractionBlacklist", 0)} indicates {b Extraction Blacklist {i ident{_1}} ... {i ident{_n}}} command.
 *)

(* This type allows registering the inlining of constants in native compiler.
   It will be extended with primitive inductive types and operators *)
type register_kind =
  | RegisterInline
  | RegisterCoqlib of qualid
  | RegisterScheme of { inductive : qualid; scheme_kind : qualid }

(** {6 Types concerning the module layer} *)

type module_ast_inl = module_ast * Declaremods.inline
type module_binder = export_with_cats option * lident list * module_ast_inl

(** {6 The type of vernacular expressions} *)

type vernac_one_argument_status = {
  name : Name.t;
  recarg_like : bool;
  notation_scope : scope_delimiter CAst.t list;
  implicit_status : Glob_term.binding_kind;
}

type vernac_argument_status =
  | VolatileArg | BidiArg
  | RealArg of vernac_one_argument_status

type arguments_modifier =
  [  `Assert
  | `ClearBidiHint
  | `ClearImplicits
  | `ClearReduction
  | `ClearScopes
  | `DefaultImplicits
  | `ExtraScopes
  | `SimplDontExposeCase  (* simpl nomatch *)
  | `SimplNeverUnfold  (* simpl never *)
  | `Rename ]

type extend_name = {
  ext_plugin : string;
  (** Name of the plugin where the extension is defined as per DECLARE PLUGIN *)
  ext_entry : string;
  (** Name of the vernac entry where the tactic is defined, typically found
     after the VERNAC EXTEND statement in the source. *)
  ext_index : int;
  (* Index of the extension in the VERNAC EXTEND statement. Each parsing branch
     is given an offset, starting from zero. *)
}

type discharge = DoDischarge | NoDischarge

type hint_info_expr = Constrexpr.constr_pattern_expr Typeclasses.hint_info_gen

type reference_or_constr =
  | HintsReference of Libnames.qualid
  | HintsConstr of Constrexpr.constr_expr

type hints_expr =
  | HintsResolve of (hint_info_expr * bool * reference_or_constr) list
  | HintsResolveIFF of bool * Libnames.qualid list * int option
  | HintsImmediate of reference_or_constr list
  | HintsUnfold of Libnames.qualid list
  | HintsTransparency of Libnames.qualid Hints.hints_transparency_target * bool
  | HintsMode of Libnames.qualid * Hints.hint_mode list
  | HintsConstructors of Libnames.qualid list
  | HintsExtern of int * Constrexpr.constr_expr option * Genarg.raw_generic_argument

(** [synterp_vernac_expr] describes the AST of commands which have effects on
    parsing or parsing extensions *)
type synterp_vernac_expr =
  | VernacLoad of verbose_flag * string
  | VernacReservedNotation of infix_flag * (lstring * syntax_modifier CAst.t list)
  | VernacNotation of
      infix_flag * notation_declaration
  | VernacDeclareCustomEntry of string
  | VernacBeginSection of lident
  | VernacEndSegment of lident
  | VernacRequire of
      qualid option * export_with_cats option * (qualid * import_filter_expr) list
  | VernacImport of export_with_cats * (qualid * import_filter_expr) list
  (* Modules and Module Types *)
  | VernacDeclareModule of export_with_cats option * lident *
      module_binder list * module_ast_inl
  | VernacDefineModule of export_with_cats option * lident * module_binder list *
      module_ast_inl Declaremods.module_signature * module_ast_inl list
  | VernacDeclareModuleType of lident *
      module_binder list * module_ast_inl list * module_ast_inl list
  | VernacInclude of module_ast_inl list

  (* Auxiliary file and library management *)
  | VernacDeclareMLModule of string list
  | VernacChdir of string option
  | VernacExtraDependency of qualid * string * Id.t option

  | VernacSetOption of bool (* Export modifier? *) * Goptions.option_name * option_setting
  | VernacProofMode of string

  (* For extension *)
  | VernacExtend of extend_name * Genarg.raw_generic_argument list

(** [synpure_vernac_expr] describes the AST of commands which have no effect on
    parsing or parsing extensions. On these ASTs, the syntactic interpretation
    phase is the identity. *)
type nonrec synpure_vernac_expr =

  (* Syntax *)
  | VernacOpenCloseScope of bool * scope_name
  | VernacDeclareScope of scope_name
  | VernacDelimiters of scope_name * string option
  | VernacBindScope of scope_name * coercion_class list
  | VernacEnableNotation of bool * (string, Id.t list * qualid) Util.union option * constr_expr option * notation_enable_modifier list * notation_with_optional_scope option

  (* Gallina *)
  | VernacDefinition of (discharge * Decls.definition_object_kind) * name_decl * definition_expr
  | VernacStartTheoremProof of Decls.theorem_kind * proof_expr list
  | VernacEndProof of proof_end
  | VernacExactProof of constr_expr
  | VernacAssumption of (discharge * Decls.assumption_object_kind) *
      Declaremods.inline * (ident_decl list * constr_expr) with_coercion list
  | VernacSymbol of (ident_decl list * constr_expr) with_coercion list
  | VernacInductive of inductive_kind * (inductive_expr * notation_declaration list) list
  | VernacFixpoint of discharge * fixpoints_expr
  | VernacCoFixpoint of discharge * cofixpoints_expr
  | VernacScheme of (lident option * scheme) list
  | VernacSchemeEquality of equality_scheme_type * Libnames.qualid Constrexpr.or_by_notation
  | VernacCombinedScheme of lident * lident list
  | VernacUniverse of lident list
  | VernacConstraint of univ_constraint_expr list
  | VernacAddRewRule of lident * (universe_decl_expr option * constr_expr * constr_expr) list

  (* Gallina extensions *)
  | VernacCanonical of qualid or_by_notation
  | VernacCoercion of qualid or_by_notation *
      (coercion_class * coercion_class) option
  | VernacIdentityCoercion of lident * coercion_class * coercion_class
  | VernacNameSectionHypSet of lident * section_subset_expr

  (* Type classes *)
  | VernacInstance of
      name_decl * (* name *)
      local_binder_expr list * (* binders *)
      constr_expr * (* type *)
      (bool * constr_expr) option * (* body (bool=true when using {}) *)
      hint_info_expr

  | VernacDeclareInstance of
      ident_decl * (* name *)
      local_binder_expr list * (* binders *)
      constr_expr * (* type *)
      hint_info_expr

  | VernacContext of local_binder_expr list

  | VernacExistingInstance of
    (qualid * hint_info_expr) list (* instances names, priorities and patterns *)

  | VernacExistingClass of qualid (* inductive or definition name *)

  (* Resetting *)
  | VernacResetName of lident
  | VernacResetInitial
  | VernacBack of int

  (* Commands *)
  | VernacCreateHintDb of string * bool
  | VernacRemoveHints of string list * qualid list
  | VernacHints of string list * hints_expr
  | VernacSyntacticDefinition of
      lident * (Id.t list * constr_expr) * syntax_modifier CAst.t list
  | VernacArguments of
      qualid or_by_notation *
      vernac_argument_status list (* Main arguments status list *) *
      (Name.t * Glob_term.binding_kind) list list (* Extra implicit status lists *) *
      arguments_modifier list
  | VernacReserve of simple_binder list
  | VernacGeneralizable of (lident list) option
  | VernacSetOpacity of (Conv_oracle.level * qualid or_by_notation list) * bool
  | VernacSetStrategy of
      (Conv_oracle.level * qualid or_by_notation list) list
  | VernacMemOption of Goptions.option_name * Goptions.table_value list
  | VernacPrintOption of Goptions.option_name
  | VernacCheckMayEval of Genredexpr.raw_red_expr option * Goal_select.t option * constr_expr
  | VernacGlobalCheck of constr_expr
  | VernacDeclareReduction of string * Genredexpr.raw_red_expr
  | VernacPrint of printable
  | VernacSearch of searchable * Goal_select.t option * qualid list search_restriction
  | VernacLocate of locatable
  | VernacRegister of qualid * register_kind
  | VernacPrimitive of ident_decl * CPrimitives.op_or_type * constr_expr option
  | VernacComments of comment list
  | VernacAttributes of Attributes.vernac_flags

  (* Proof management *)
  | VernacAbort
  | VernacAbortAll
  | VernacRestart
  | VernacUndo of int
  | VernacUndoTo of int
  | VernacFocus of int option
  | VernacUnfocus
  | VernacUnfocused
  | VernacBullet of Proof_bullet.t
  | VernacSubproof of Goal_select.t option
  | VernacEndSubproof
  | VernacShow of showable
  | VernacCheckGuard
  | VernacValidateProof
  | VernacProof of Genarg.raw_generic_argument option * section_subset_expr option

  | VernacAddOption of Goptions.option_name * Goptions.table_value list
  | VernacRemoveOption of Goptions.option_name * Goptions.table_value list

(** We classify vernacular expressions in two categories. [VernacSynterp]
    represents commands which have an effect on parsing or on parsing extensions.
    [VernacSynPure] represents commands which have no such effects. *)
type 'a vernac_expr_gen =
  | VernacSynterp of 'a
  | VernacSynPure of synpure_vernac_expr

type vernac_expr = synterp_vernac_expr vernac_expr_gen

type control_flag =
  | ControlTime
  | ControlInstructions
  | ControlProfile of string option
  | ControlRedirect of string
  | ControlTimeout of int
  | ControlFail
  | ControlSucceed

type ('a, 'b) vernac_control_gen_r =
  { control : 'a list
  ; attrs : Attributes.vernac_flags
  ; expr : 'b vernac_expr_gen
  }
and 'a vernac_control_gen = (control_flag, 'a) vernac_control_gen_r CAst.t

type vernac_control = synterp_vernac_expr vernac_control_gen
