(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constrexpr
open Libnames

(** Vernac expressions, produced by the parser *)
type class_rawexpr = FunClass | SortClass | RefClass of qualid or_by_notation

type goal_identifier = string
type scope_name = string

type goal_reference =
  | OpenSubgoals
  | NthGoal of int
  | GoalId of Id.t

type printable =
  | PrintTables
  | PrintFullContext
  | PrintSectionContext of qualid
  | PrintInspect of int
  | PrintGrammar of string
  | PrintLoadPath of DirPath.t option
  | PrintModules
  | PrintModule of qualid
  | PrintModuleType of qualid
  | PrintNamespace of DirPath.t
  | PrintMLLoadPath
  | PrintMLModules
  | PrintDebugGC
  | PrintName of qualid or_by_notation * UnivNames.univ_name_list option
  | PrintGraph
  | PrintClasses
  | PrintTypeClasses
  | PrintInstances of qualid or_by_notation
  | PrintCoercions
  | PrintCoercionPaths of class_rawexpr * class_rawexpr
  | PrintCanonicalConversions
  | PrintUniverses of bool * qualid list option * string option
  | PrintHint of qualid or_by_notation
  | PrintHintGoal
  | PrintHintDbName of string
  | PrintHintDb
  | PrintScopes
  | PrintScope of string
  | PrintVisibility of string option
  | PrintAbout of qualid or_by_notation * UnivNames.univ_name_list option * Goal_select.t option
  | PrintImplicit of qualid or_by_notation
  | PrintAssumptions of bool * bool * qualid or_by_notation
  | PrintStrategy of qualid or_by_notation option
  | PrintRegistered

type search_about_item =
  | SearchSubPattern of constr_pattern_expr
  | SearchString of string * scope_name option

type searchable =
  | SearchPattern of constr_pattern_expr
  | SearchRewrite of constr_pattern_expr
  | SearchHead of constr_pattern_expr
  | SearchAbout of (bool * search_about_item) list

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
  | ShowScript
  | ShowExistentials
  | ShowUniverses
  | ShowProofNames
  | ShowIntros of bool
  | ShowMatch of qualid

type comment =
  | CommentConstr of constr_expr
  | CommentString of string
  | CommentInt of int

type search_restriction =
  | SearchInside of qualid list
  | SearchOutside of qualid list

type rec_flag       = bool (* true = Rec;           false = NoRec          *)
type verbose_flag   = bool (* true = Verbose;       false = Silent         *)
type coercion_flag  = bool (* true = AddCoercion    false = NoCoercion     *)
type instance_flag  = bool option
  (* Some true = Backward instance; Some false = Forward instance, None = NoInstance *)
type export_flag    = bool (* true = Export;        false = Import         *)
type inductive_flag = Declarations.recursivity_kind
type onlyparsing_flag = Flags.compat_version option
 (* Some v = Parse only;  None = Print also.
    If v<>Current, it contains the name of the coq version
    which this notation is trying to be compatible with *)
type locality_flag  = bool (* true = Local *)

type option_value = Goptions.option_value =
  | BoolValue of bool
  | IntValue of int option
  | StringValue of string
  | StringOptValue of string option

type option_ref_value =
  | StringRefValue of string
  | QualidRefValue of qualid

(** Identifier and optional list of bound universes and constraints. *)

type sort_expr = Sorts.family

type definition_expr =
  | ProveBody of local_binder_expr list * constr_expr
  | DefineBody of local_binder_expr list * Genredexpr.raw_red_expr option * constr_expr
      * constr_expr option

type fixpoint_expr =
    ident_decl * (lident option * recursion_order_expr) * local_binder_expr list * constr_expr * constr_expr option

type cofixpoint_expr =
    ident_decl * local_binder_expr list * constr_expr * constr_expr option

type local_decl_expr =
  | AssumExpr of lname * constr_expr
  | DefExpr of lname * constr_expr * constr_expr option

type inductive_kind = Inductive_kw | CoInductive | Variant | Record | Structure | Class of bool (* true = definitional, false = inductive *)
type decl_notation = lstring * constr_expr * scope_name option
type simple_binder = lident list  * constr_expr
type class_binder = lident * constr_expr list
type 'a with_coercion = coercion_flag * 'a
type 'a with_instance = instance_flag * 'a
type 'a with_notation = 'a * decl_notation list
type 'a with_priority = 'a * int option
type constructor_expr = (lident * constr_expr) with_coercion
type constructor_list_or_record_decl_expr =
  | Constructors of constructor_expr list
  | RecordDecl of lident option * local_decl_expr with_instance with_priority with_notation list
type inductive_expr =
  ident_decl with_coercion * local_binder_expr list * constr_expr option * inductive_kind *
    constructor_list_or_record_decl_expr

type one_inductive_expr =
  lident * local_binder_expr list * constr_expr option * constructor_expr list

type typeclass_constraint = name_decl * Decl_kinds.binding_kind * constr_expr
and typeclass_context = typeclass_constraint list

type proof_expr =
  ident_decl * (local_binder_expr list * constr_expr)

type syntax_modifier =
  | SetItemLevel of string list * Notation_term.constr_as_binder_kind option * Extend.production_level option
  | SetLevel of int
  | SetCustomEntry of string * int option
  | SetAssoc of Gramlib.Gramext.g_assoc
  | SetEntryType of string * Extend.simple_constr_prod_entry_key
  | SetOnlyParsing
  | SetOnlyPrinting
  | SetCompatVersion of Flags.compat_version
  | SetFormat of string * lstring

type proof_end =
  | Admitted
  (*                         name in `Save ident` when closing goal *)
  | Proved of Proof_global.opacity_flag * lident option

type scheme =
  | InductionScheme of bool * qualid or_by_notation * sort_expr
  | CaseScheme of bool * qualid or_by_notation * sort_expr
  | EqualityScheme of qualid or_by_notation

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

(** {6 Types concerning the module layer} *)

type module_ast_inl = module_ast * Declaremods.inline
type module_binder = bool option * lident list * module_ast_inl

(** [Some b] if locally enabled/disabled according to [b], [None] if
    we should use the global flag. *)
type vernac_cumulative = VernacCumulative | VernacNonCumulative

(** {6 The type of vernacular expressions} *)

type vernac_implicit_status = Implicit | MaximallyImplicit | NotImplicit

type vernac_argument_status = {
  name : Name.t;
  recarg_like : bool;
  notation_scope : string CAst.t option;
  implicit_status : vernac_implicit_status;
}

type extend_name =
  (* Name of the vernac entry where the tactic is defined, typically found
     after the VERNAC EXTEND statement in the source. *)
  string *
  (* Index of the extension in the VERNAC EXTEND statement. Each parsing branch
     is given an offset, starting from zero. *)
  int

type nonrec vernac_expr =

  | VernacLoad of verbose_flag * string
  (* Syntax *)
  | VernacSyntaxExtension of bool * (lstring * syntax_modifier list)
  | VernacOpenCloseScope of bool * scope_name
  | VernacDeclareScope of scope_name
  | VernacDelimiters of scope_name * string option
  | VernacBindScope of scope_name * class_rawexpr list
  | VernacInfix of (lstring * syntax_modifier list) *
      constr_expr * scope_name option
  | VernacNotation of
      constr_expr * (lstring * syntax_modifier list) *
      scope_name option
  | VernacNotationAddFormat of string * string * string
  | VernacDeclareCustomEntry of string

  (* Gallina *)
  | VernacDefinition of (Decl_kinds.discharge * Decl_kinds.definition_object_kind) * name_decl * definition_expr
  | VernacStartTheoremProof of Decl_kinds.theorem_kind * proof_expr list
  | VernacEndProof of proof_end
  | VernacExactProof of constr_expr
  | VernacAssumption of (Decl_kinds.discharge * Decl_kinds.assumption_object_kind) *
      Declaremods.inline * (ident_decl list * constr_expr) with_coercion list
  | VernacInductive of vernac_cumulative option * Decl_kinds.private_flag * inductive_flag * (inductive_expr * decl_notation list) list
  | VernacFixpoint of Decl_kinds.discharge * (fixpoint_expr * decl_notation list) list
  | VernacCoFixpoint of Decl_kinds.discharge * (cofixpoint_expr * decl_notation list) list
  | VernacScheme of (lident option * scheme) list
  | VernacCombinedScheme of lident * lident list
  | VernacUniverse of lident list
  | VernacConstraint of Glob_term.glob_constraint list

  (* Gallina extensions *)
  | VernacBeginSection of lident
  | VernacEndSegment of lident
  | VernacRequire of
      qualid option * export_flag option * qualid list
  | VernacImport of export_flag * qualid list
  | VernacCanonical of qualid or_by_notation
  | VernacCoercion of qualid or_by_notation *
      class_rawexpr * class_rawexpr
  | VernacIdentityCoercion of lident * class_rawexpr * class_rawexpr
  | VernacNameSectionHypSet of lident * section_subset_expr

  (* Type classes *)
  | VernacInstance of
      local_binder_expr list * (* super *)
        typeclass_constraint * (* instance name, class name, params *)
        (bool * constr_expr) option * (* props *)
        Hints.hint_info_expr

  | VernacDeclareInstance of
      local_binder_expr list * (* super *)
        (ident_decl * Decl_kinds.binding_kind * constr_expr) * (* instance name, class name, params *)
        Hints.hint_info_expr

  | VernacContext of local_binder_expr list

  | VernacExistingInstance of
    (qualid * Hints.hint_info_expr) list (* instances names, priorities and patterns *)

  | VernacExistingClass of qualid (* inductive or definition name *)

  (* Modules and Module Types *)
  | VernacDeclareModule of bool option * lident *
      module_binder list * module_ast_inl
  | VernacDefineModule of bool option * lident * module_binder list *
      module_ast_inl Declaremods.module_signature * module_ast_inl list
  | VernacDeclareModuleType of lident *
      module_binder list * module_ast_inl list * module_ast_inl list
  | VernacInclude of module_ast_inl list

  (* Solving *)

  | VernacSolveExistential of int * constr_expr

  (* Auxiliary file and library management *)
  | VernacAddLoadPath of rec_flag * string * DirPath.t option
  | VernacRemoveLoadPath of string
  | VernacAddMLPath of rec_flag * string
  | VernacDeclareMLModule of string list
  | VernacChdir of string option

  (* State management *)
  | VernacWriteState of string
  | VernacRestoreState of string

  (* Resetting *)
  | VernacResetName of lident
  | VernacResetInitial
  | VernacBack of int
  | VernacBackTo of int

  (* Commands *)
  | VernacCreateHintDb of string * bool
  | VernacRemoveHints of string list * qualid list
  | VernacHints of string list * Hints.hints_expr
  | VernacSyntacticDefinition of lident * (Id.t list * constr_expr) *
      onlyparsing_flag
  | VernacArguments of qualid or_by_notation *
      vernac_argument_status list (* Main arguments status list *) *
        (Name.t * vernac_implicit_status) list list (* Extra implicit status lists *) *
      int option (* Number of args to trigger reduction *) *
        [ `ReductionDontExposeCase | `ReductionNeverUnfold | `Rename |
          `ExtraScopes | `Assert | `ClearImplicits | `ClearScopes |
          `DefaultImplicits ] list
  | VernacReserve of simple_binder list
  | VernacGeneralizable of (lident list) option
  | VernacSetOpacity of (Conv_oracle.level * qualid or_by_notation list)
  | VernacSetStrategy of
      (Conv_oracle.level * qualid or_by_notation list) list
  | VernacUnsetOption of export_flag * Goptions.option_name
  | VernacSetOption of export_flag * Goptions.option_name * option_value
  | VernacAddOption of Goptions.option_name * option_ref_value list
  | VernacRemoveOption of Goptions.option_name * option_ref_value list
  | VernacMemOption of Goptions.option_name * option_ref_value list
  | VernacPrintOption of Goptions.option_name
  | VernacCheckMayEval of Genredexpr.raw_red_expr option * Goal_select.t option * constr_expr
  | VernacGlobalCheck of constr_expr
  | VernacDeclareReduction of string * Genredexpr.raw_red_expr
  | VernacPrint of printable
  | VernacSearch of searchable * Goal_select.t option * search_restriction
  | VernacLocate of locatable
  | VernacRegister of qualid * register_kind
  | VernacPrimitive of lident * CPrimitives.op_or_type * constr_expr option
  | VernacComments of comment list

  (* Proof management *)
  | VernacAbort of lident option
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
  | VernacProof of Genarg.raw_generic_argument option * section_subset_expr option
  | VernacProofMode of string

  (* For extension *)
  | VernacExtend of extend_name * Genarg.raw_generic_argument list

type vernac_control =
  | VernacExpr of Attributes.vernac_flags * vernac_expr
  (* boolean is true when the `-time` batch-mode command line flag was set.
     the flag is used to print differently in `-time` vs `Time foo` *)
  | VernacTime of bool * vernac_control CAst.t
  | VernacRedirect of string * vernac_control CAst.t
  | VernacTimeout of int * vernac_control
  | VernacFail of vernac_control
