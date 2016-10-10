(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open Misctypes
open Constrexpr
open Decl_kinds
open Libnames

(** Vernac expressions, produced by the parser *)

type lident = Id.t located
type lname = Name.t located
type lstring = string located

type class_rawexpr = FunClass | SortClass | RefClass of reference or_by_notation

(* spiwack: I'm choosing, for now, to have [goal_selector] be a
   different type than [goal_reference] mostly because if it makes sense
   to print a goal that is out of focus (or already solved) it doesn't
   make sense to apply a tactic to it. Hence it the types may look very
   similar, they do not seem to mean the same thing. *)
type goal_selector =
  | SelectNth of int
  | SelectList of (int * int) list
  | SelectId of Id.t
  | SelectAll

type goal_identifier = string
type scope_name = string

type goal_reference =
  | OpenSubgoals
  | NthGoal of int
  | GoalId of Id.t
  | GoalUid of goal_identifier

type printable =
  | PrintTables
  | PrintFullContext
  | PrintSectionContext of reference
  | PrintInspect of int
  | PrintGrammar of string
  | PrintLoadPath of DirPath.t option
  | PrintModules
  | PrintModule of reference
  | PrintModuleType of reference
  | PrintNamespace of DirPath.t
  | PrintMLLoadPath
  | PrintMLModules
  | PrintDebugGC
  | PrintName of reference or_by_notation
  | PrintGraph
  | PrintClasses
  | PrintTypeClasses
  | PrintInstances of reference or_by_notation
  | PrintCoercions
  | PrintCoercionPaths of class_rawexpr * class_rawexpr
  | PrintCanonicalConversions
  | PrintUniverses of bool * string option
  | PrintHint of reference or_by_notation
  | PrintHintGoal
  | PrintHintDbName of string
  | PrintHintDb
  | PrintScopes
  | PrintScope of string
  | PrintVisibility of string option
  | PrintAbout of reference or_by_notation * goal_selector option
  | PrintImplicit of reference or_by_notation
  | PrintAssumptions of bool * bool * reference or_by_notation
  | PrintStrategy of reference or_by_notation option

type search_about_item =
  | SearchSubPattern of constr_pattern_expr
  | SearchString of string * scope_name option

type searchable =
  | SearchPattern of constr_pattern_expr
  | SearchRewrite of constr_pattern_expr
  | SearchHead of constr_pattern_expr
  | SearchAbout of (bool * search_about_item) list

type locatable =
  | LocateAny of reference or_by_notation
  | LocateTerm of reference or_by_notation
  | LocateLibrary of reference
  | LocateModule of reference
  | LocateTactic of reference
  | LocateFile of string

type showable =
  | ShowGoal of goal_reference
  | ShowGoalImplicitly of int option
  | ShowProof
  | ShowNode
  | ShowScript
  | ShowExistentials
  | ShowUniverses
  | ShowTree
  | ShowProofNames
  | ShowIntros of bool
  | ShowMatch of reference
  | ShowThesis

type comment =
  | CommentConstr of constr_expr
  | CommentString of string
  | CommentInt of int

type reference_or_constr = 
  | HintsReference of reference
  | HintsConstr of constr_expr

type hint_mode =
  | ModeInput (* No evars *)
  | ModeNoHeadEvar (* No evar at the head *)
  | ModeOutput (* Anything *)

type 'a hint_info_gen =
    { hint_priority : int option;
      hint_pattern : 'a option }

type hint_info_expr = constr_pattern_expr hint_info_gen

type hints_expr =
  | HintsResolve of (hint_info_expr * bool * reference_or_constr) list
  | HintsImmediate of reference_or_constr list
  | HintsUnfold of reference list
  | HintsTransparency of reference list * bool
  | HintsMode of reference * hint_mode list
  | HintsConstructors of reference list
  | HintsExtern of int * constr_expr option * Genarg.raw_generic_argument

type search_restriction =
  | SearchInside of reference list
  | SearchOutside of reference list

type rec_flag       = bool (* true = Rec;           false = NoRec          *)
type verbose_flag   = bool (* true = Verbose;       false = Silent         *)
                           (*   list of idents for qed exporting           *)
type opacity_flag   = Opaque of lident list option | Transparent
type coercion_flag  = bool (* true = AddCoercion    false = NoCoercion     *)
type instance_flag  = bool option
  (* Some true = Backward instance; Some false = Forward instance, None = NoInstance *)
type export_flag    = bool (* true = Export;        false = Import         *)
type inductive_flag = Decl_kinds.recursivity_kind
type onlyparsing_flag = Flags.compat_version option
 (* Some v = Parse only;  None = Print also.
    If v<>Current, it contains the name of the coq version
    which this notation is trying to be compatible with *)
type locality_flag  = bool (* true = Local *)
type obsolete_locality = bool
(* Some grammar entries use obsolete_locality.  This bool is to be backward
 * compatible.  If the grammar is fixed removing deprecated syntax, this
 * bool should go away too *)

type option_value = Goptions.option_value =
  | BoolValue of bool
  | IntValue of int option
  | StringValue of string
  | StringOptValue of string option

type option_ref_value =
  | StringRefValue of string
  | QualidRefValue of reference

(** Identifier and optional list of bound universes. *)						 
type plident = lident * lident list option

type sort_expr = glob_sort

type definition_expr =
  | ProveBody of local_binder_expr list * constr_expr
  | DefineBody of local_binder_expr list * Genredexpr.raw_red_expr option * constr_expr
      * constr_expr option

type fixpoint_expr =
    plident * (Id.t located option * recursion_order_expr) * local_binder_expr list * constr_expr * constr_expr option

type cofixpoint_expr =
    plident * local_binder_expr list * constr_expr * constr_expr option

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
  plident with_coercion * local_binder_expr list * constr_expr option * inductive_kind *
    constructor_list_or_record_decl_expr

type one_inductive_expr =
  plident * local_binder_expr list * constr_expr option * constructor_expr list

type proof_expr =
  plident option * (local_binder_expr list * constr_expr)

type syntax_modifier =
  | SetItemLevel of string list * Extend.production_level
  | SetLevel of int
  | SetAssoc of Extend.gram_assoc
  | SetEntryType of string * Extend.simple_constr_prod_entry_key
  | SetOnlyParsing
  | SetOnlyPrinting
  | SetCompatVersion of Flags.compat_version
  | SetFormat of string * string located

type proof_end =
  | Admitted
  (*                         name in `Save ident` when closing goal *)
  | Proved of opacity_flag * lident option

type scheme =
  | InductionScheme of bool * reference or_by_notation * sort_expr
  | CaseScheme of bool * reference or_by_notation * sort_expr
  | EqualityScheme of reference or_by_notation

type section_subset_expr =
  | SsEmpty
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
type extend_name =
  (** Name of the vernac entry where the tactic is defined, typically found
      after the VERNAC EXTEND statement in the source. *)
  string *
  (** Index of the extension in the VERNAC EXTEND statement. Each parsing branch
      is given an offset, starting from zero. *)
  int

(* This type allows registering the inlining of constants in native compiler.
   It will be extended with primitive inductive types and operators *)
type register_kind = 
  | RegisterInline

type bullet =
    | Dash of int
    | Star of int
    | Plus of int

(** {6 Types concerning Stm} *)
type stm_vernac =
  | JoinDocument
  | Wait

(** {6 Types concerning the module layer} *)

(** Rigid / flexible module signature *)

type 'a module_signature =
  | Enforce of 'a (** ... : T *)
  | Check of 'a list (** ... <: T1 <: T2, possibly empty *)

(** Which module inline annotations should we honor,
    either None or the ones whose level is less or equal
    to the given integer *)

type inline =
  | NoInline
  | DefaultInline
  | InlineAt of int

type module_ast_inl = module_ast * inline
type module_binder = bool option * lident list * module_ast_inl

(** {6 The type of vernacular expressions} *)

type vernac_expr =
  (* Control *)
  | VernacLoad of verbose_flag * string
  | VernacTime of vernac_expr located
  | VernacRedirect of string * vernac_expr located
  | VernacTimeout of int * vernac_expr
  | VernacFail of vernac_expr

  (* Syntax *)
  | VernacSyntaxExtension of
      obsolete_locality * (lstring * syntax_modifier list)
  | VernacOpenCloseScope of obsolete_locality * (bool * scope_name)
  | VernacDelimiters of scope_name * string option
  | VernacBindScope of scope_name * class_rawexpr list
  | VernacInfix of obsolete_locality * (lstring * syntax_modifier list) *
      constr_expr * scope_name option
  | VernacNotation of
      obsolete_locality * constr_expr * (lstring * syntax_modifier list) *
      scope_name option
  | VernacNotationAddFormat of string * string * string

  (* Gallina *)
  | VernacDefinition of
      (locality option * definition_object_kind) * plident * definition_expr
  | VernacStartTheoremProof of theorem_kind * proof_expr list * bool
  | VernacEndProof of proof_end
  | VernacExactProof of constr_expr
  | VernacAssumption of (locality option * assumption_object_kind) *
      inline * (plident list * constr_expr) with_coercion list
  | VernacInductive of private_flag * inductive_flag * (inductive_expr * decl_notation list) list
  | VernacFixpoint of
      locality option * (fixpoint_expr * decl_notation list) list
  | VernacCoFixpoint of
      locality option * (cofixpoint_expr * decl_notation list) list
  | VernacScheme of (lident option * scheme) list
  | VernacCombinedScheme of lident * lident list
  | VernacUniverse of lident list
  | VernacConstraint of (glob_level * Univ.constraint_type * glob_level) list

  (* Gallina extensions *)
  | VernacBeginSection of lident
  | VernacEndSegment of lident
  | VernacRequire of
      reference option * export_flag option * reference list
  | VernacImport of export_flag * reference list
  | VernacCanonical of reference or_by_notation
  | VernacCoercion of obsolete_locality * reference or_by_notation *
      class_rawexpr * class_rawexpr
  | VernacIdentityCoercion of obsolete_locality * lident *
      class_rawexpr * class_rawexpr
  | VernacNameSectionHypSet of lident * section_subset_expr 

  (* Type classes *)
  | VernacInstance of
      bool * (* abstract instance *)
      local_binder_expr list * (* super *)
	typeclass_constraint * (* instance name, class name, params *)
	(bool * constr_expr) option * (* props *)
	hint_info_expr

  | VernacContext of local_binder_expr list

  | VernacDeclareInstances of
    (reference * hint_info_expr) list (* instances names, priorities and patterns *)

  | VernacDeclareClass of reference (* inductive or definition name *)

  (* Modules and Module Types *)
  | VernacDeclareModule of bool option * lident *
      module_binder list * module_ast_inl
  | VernacDefineModule of bool option * lident * module_binder list *
      module_ast_inl module_signature * module_ast_inl list
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
  | VernacRemoveHints of string list * reference list
  | VernacHints of obsolete_locality * string list * hints_expr
  | VernacSyntacticDefinition of Id.t located * (Id.t list * constr_expr) *
      obsolete_locality * onlyparsing_flag
  | VernacDeclareImplicits of reference or_by_notation *
      (explicitation * bool * bool) list list
  | VernacArguments of reference or_by_notation *
      vernac_argument_status list (* Main arguments status list *) *
        (Name.t * vernac_implicit_status) list list (* Extra implicit status lists *) *
      int option (* Number of args to trigger reduction *) *
        [ `ReductionDontExposeCase | `ReductionNeverUnfold | `Rename |
          `ExtraScopes | `Assert | `ClearImplicits | `ClearScopes |
          `DefaultImplicits ] list
  | VernacArgumentsScope of reference or_by_notation *
      scope_name option list
  | VernacReserve of simple_binder list
  | VernacGeneralizable of (lident list) option
  | VernacSetOpacity of (Conv_oracle.level * reference or_by_notation list)
  | VernacSetStrategy of
      (Conv_oracle.level * reference or_by_notation list) list
  | VernacUnsetOption of Goptions.option_name
  | VernacSetOption of Goptions.option_name * option_value
  | VernacSetAppendOption of Goptions.option_name * string
  | VernacAddOption of Goptions.option_name * option_ref_value list
  | VernacRemoveOption of Goptions.option_name * option_ref_value list
  | VernacMemOption of Goptions.option_name * option_ref_value list
  | VernacPrintOption of Goptions.option_name
  | VernacCheckMayEval of Genredexpr.raw_red_expr option * goal_selector option * constr_expr
  | VernacGlobalCheck of constr_expr
  | VernacDeclareReduction of string * Genredexpr.raw_red_expr
  | VernacPrint of printable
  | VernacSearch of searchable * goal_selector option * search_restriction
  | VernacLocate of locatable
  | VernacRegister of lident * register_kind
  | VernacComments of comment list

  (* Stm backdoor: used in fake_id, will be removed when fake_ide
     becomes aware of feedback about completed jobs. *)
  | VernacStm of stm_vernac

  (* Proof management *)
  | VernacGoal of constr_expr
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
  (* Toplevel control *)
  | VernacToplevelControl of exn

  (* For extension *)
  | VernacExtend of extend_name * Genarg.raw_generic_argument list

  (* Flags *)
  | VernacProgram of vernac_expr
  | VernacPolymorphic of bool * vernac_expr
  | VernacLocal of bool * vernac_expr

and vernac_implicit_status = Implicit | MaximallyImplicit | NotImplicit

and vernac_argument_status = {
  name : Name.t;
  recarg_like : bool;
  notation_scope : string Loc.located option;
  implicit_status : vernac_implicit_status;
}

(* A vernac classifier has to tell if a command:
   vernac_when: has to be executed now (alters the parser) or later
   vernac_type: if it is starts, ends, continues a proof or
     alters the global state or is a control command like BackTo or is
     a query like Check *)
type vernac_type =
  | VtStartProof of vernac_start
  | VtSideff of vernac_sideff_type
  | VtQed of vernac_qed_type
  | VtProofStep of proof_step
  | VtProofMode of string
  | VtQuery of vernac_part_of_script * report_with
  | VtStm of vernac_control * vernac_part_of_script
  | VtUnknown
and report_with = Stateid.t * Feedback.route_id (* feedback on id/route *)
and vernac_qed_type = VtKeep | VtKeepAsAxiom | VtDrop (* Qed/Admitted, Abort *)
and vernac_start = string * opacity_guarantee * Id.t list
and vernac_sideff_type = Id.t list
and vernac_part_of_script = bool
and vernac_control =
  | VtWait
  | VtJoinDocument
  | VtBack of Stateid.t
and opacity_guarantee =
  | GuaranteesOpacity (** Only generates opaque terms at [Qed] *)
  | Doesn'tGuaranteeOpacity (** May generate transparent terms even with [Qed].*)
and proof_step = { (* TODO: inline with OCaml 4.03 *)
  parallel : [ `Yes of solving_tac * anon_abstracting_tac | `No ];
  proof_block_detection : proof_block_name option
}
and solving_tac = bool (* a terminator *)
and anon_abstracting_tac = bool (* abstracting anonymously its result *)
and proof_block_name = string (* open type of delimiters *)
type vernac_when =
  | VtNow
  | VtLater
type vernac_classification = vernac_type * vernac_when
