(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open Tacexpr
open Misctypes
open Constrexpr
open Decl_kinds
open Libnames

(** Vernac expressions, produced by the parser *)

type lident = Id.t located
type lname = Name.t located
type lstring = string located
type lreference = reference

type class_rawexpr = FunClass | SortClass | RefClass of reference or_by_notation

(* spiwack: I'm choosing, for now, to have [goal_selector] be a
   different type than [goal_reference] mostly because if it makes sense
   to print a goal that is out of focus (or already solved) it doesn't
   make sense to apply a tactic to it. Hence it the types may look very
   similar, they do not seem to mean the same thing. *)
type goal_selector =
  | SelectNth of int
  | SelectId of Id.t
  | SelectAll
  | SelectAllParallel

type goal_identifier = string
type scope_name = string

type goal_reference =
  | OpenSubgoals
  | NthGoal of int
  | GoalId of goal_identifier

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
  | PrintLtac of reference
  | PrintCoercions
  | PrintCoercionPaths of class_rawexpr * class_rawexpr
  | PrintCanonicalConversions
  | PrintUniverses of bool * string option
  | PrintHint of reference or_by_notation
  | PrintHintGoal
  | PrintHintDbName of string
  | PrintRewriteHintDbName of string
  | PrintHintDb
  | PrintScopes
  | PrintScope of string
  | PrintVisibility of string option
  | PrintAbout of reference or_by_notation*int option
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
  | ShowMatch of lident
  | ShowThesis

type comment =
  | CommentConstr of constr_expr
  | CommentString of string
  | CommentInt of int

type reference_or_constr = 
  | HintsReference of reference
  | HintsConstr of constr_expr

type hints_expr =
  | HintsResolve of (int option * bool * reference_or_constr) list
  | HintsImmediate of reference_or_constr list
  | HintsUnfold of reference list
  | HintsTransparency of reference list * bool
  | HintsMode of reference * bool list
  | HintsConstructors of reference list
  | HintsExtern of int * constr_expr option * raw_tactic_expr

type search_restriction =
  | SearchInside of reference list
  | SearchOutside of reference list

type rec_flag       = bool (* true = Rec;           false = NoRec          *)
type verbose_flag   = bool (* true = Verbose;       false = Silent         *)
type opacity_flag   = bool (* true = Opaque;        false = Transparent    *)
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

type option_ref_value =
  | StringRefValue of string
  | QualidRefValue of reference

type sort_expr = glob_sort

type definition_expr =
  | ProveBody of local_binder list * constr_expr
  | DefineBody of local_binder list * raw_red_expr option * constr_expr
      * constr_expr option

type fixpoint_expr =
    Id.t located * (Id.t located option * recursion_order_expr) * local_binder list * constr_expr * constr_expr option

type cofixpoint_expr =
    Id.t located * local_binder list * constr_expr * constr_expr option

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
  lident with_coercion * local_binder list * constr_expr option * inductive_kind *
    constructor_list_or_record_decl_expr

type one_inductive_expr =
  lident * local_binder list * constr_expr option * constructor_expr list

type grammar_tactic_prod_item_expr =
  | TacTerm of string
  | TacNonTerm of Loc.t * string * (Names.Id.t * string) option

type syntax_modifier =
  | SetItemLevel of string list * Extend.production_level
  | SetLevel of int
  | SetAssoc of Extend.gram_assoc
  | SetEntryType of string * Extend.simple_constr_prod_entry_key
  | SetOnlyParsing of Flags.compat_version
  | SetFormat of string * string located

type proof_end =
  | Admitted
  | Proved of opacity_flag * (lident * theorem_kind option) option

type scheme =
  | InductionScheme of bool * reference or_by_notation * sort_expr
  | CaseScheme of bool * reference or_by_notation * sort_expr
  | EqualityScheme of reference or_by_notation

type section_subset_expr =
  | SsSet of lident list
  | SsCompl of section_subset_expr
  | SsUnion of section_subset_expr * section_subset_expr
  | SsSubstr of section_subset_expr * section_subset_expr

type section_subset_descr = SsAll | SsType | SsExpr of section_subset_expr

type extend_name = string * int

(* This type allows registering the inlining of constants in native compiler.
   It will be extended with primitive inductive types and operators *)
type register_kind = 
  | RegisterInline

type bullet =
    | Dash of int
    | Star of int
    | Plus of int

(** {6 Types concerning Stm} *)
type 'a stm_vernac =
  | JoinDocument
  | Finish
  | Wait
  | PrintDag
  | Observe of Stateid.t
  | Command of 'a (* An out of flow command not to be recorded by Stm *)
  | PGLast of 'a (* To ease the life of PG *)

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
  | VernacTime of vernac_list
  | VernacTimeout of int * vernac_expr
  | VernacFail of vernac_expr
  | VernacError of exn (* always fails *)

  (* Syntax *)
  | VernacTacticNotation of
      int * grammar_tactic_prod_item_expr list * raw_tactic_expr
  | VernacSyntaxExtension of
      obsolete_locality * (lstring * syntax_modifier list)
  | VernacOpenCloseScope of obsolete_locality * (bool * scope_name)
  | VernacDelimiters of scope_name * string
  | VernacBindScope of scope_name * reference or_by_notation list
  | VernacInfix of obsolete_locality * (lstring * syntax_modifier list) *
      constr_expr * scope_name option
  | VernacNotation of
      obsolete_locality * constr_expr * (lstring * syntax_modifier list) *
      scope_name option
  | VernacNotationAddFormat of string * string * string

  (* Gallina *)
  | VernacDefinition of
      (locality option * definition_object_kind) * lident * definition_expr
  | VernacStartTheoremProof of theorem_kind * 
      (lident option * (local_binder list * constr_expr * (lident option * recursion_order_expr) option)) list *
        bool
  | VernacEndProof of proof_end
  | VernacExactProof of constr_expr
  | VernacAssumption of (locality option * assumption_object_kind) *
      inline * simple_binder with_coercion list
  | VernacInductive of private_flag * inductive_flag * (inductive_expr * decl_notation list) list
  | VernacFixpoint of
      locality option * (fixpoint_expr * decl_notation list) list
  | VernacCoFixpoint of
      locality option * (cofixpoint_expr * decl_notation list) list
  | VernacScheme of (lident option * scheme) list
  | VernacCombinedScheme of lident * lident list
  | VernacUniverse of lident list
  | VernacConstraint of (lident * Univ.constraint_type * lident) list

  (* Gallina extensions *)
  | VernacBeginSection of lident
  | VernacEndSegment of lident
  | VernacRequire of
      export_flag option * lreference list
  | VernacImport of export_flag * lreference list
  | VernacCanonical of reference or_by_notation
  | VernacCoercion of obsolete_locality * reference or_by_notation *
      class_rawexpr * class_rawexpr
  | VernacIdentityCoercion of obsolete_locality * lident *
      class_rawexpr * class_rawexpr
  | VernacNameSectionHypSet of lident * section_subset_descr 

  (* Type classes *)
  | VernacInstance of
      bool * (* abstract instance *)
      local_binder list * (* super *)
	typeclass_constraint * (* instance name, class name, params *)
	(bool * constr_expr) option * (* props *)
	int option (* Priority *)

  | VernacContext of local_binder list

  | VernacDeclareInstances of
    reference list * int option (* instance names, priority *)

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

  | VernacSolve of goal_selector * int option * raw_tactic_expr * bool
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
  | VernacDeclareTacticDefinition of
      (rec_flag * (reference * bool * raw_tactic_expr) list)
  | VernacCreateHintDb of string * bool
  | VernacRemoveHints of string list * reference list
  | VernacHints of obsolete_locality * string list * hints_expr
  | VernacSyntacticDefinition of Id.t located * (Id.t list * constr_expr) *
      obsolete_locality * onlyparsing_flag
  | VernacDeclareImplicits of reference or_by_notation *
      (explicitation * bool * bool) list list
  | VernacArguments of reference or_by_notation *
      ((Name.t * bool * (Loc.t * string) option * bool * bool) list) list *
      int * [ `ReductionDontExposeCase | `ReductionNeverUnfold | `Rename |
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
  | VernacAddOption of Goptions.option_name * option_ref_value list
  | VernacRemoveOption of Goptions.option_name * option_ref_value list
  | VernacMemOption of Goptions.option_name * option_ref_value list
  | VernacPrintOption of Goptions.option_name
  | VernacCheckMayEval of raw_red_expr option * int option * constr_expr
  | VernacGlobalCheck of constr_expr
  | VernacDeclareReduction of string * raw_red_expr
  | VernacPrint of printable
  | VernacSearch of searchable * int option * search_restriction
  | VernacLocate of locatable
  | VernacRegister of lident * register_kind
  | VernacComments of comment list
  | VernacNop

  (* Stm backdoor *)
  | VernacStm of vernac_expr stm_vernac

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
  | VernacProof of raw_tactic_expr option * section_subset_descr option
  | VernacProofMode of string
  (* Toplevel control *)
  | VernacToplevelControl of exn

  (* For extension *)
  | VernacExtend of extend_name * Genarg.raw_generic_argument list

  (* Flags *)
  | VernacProgram of vernac_expr
  | VernacPolymorphic of bool * vernac_expr
  | VernacLocal of bool * vernac_expr

and vernac_list = located_vernac_expr list

and located_vernac_expr = Loc.t * vernac_expr

(* A vernac classifier has to tell if a command:
   vernac_when: has to be executed now (alters the parser) or later
   vernac_type: if it is starts, ends, continues a proof or
     alters the global state or is a control command like BackTo or is
     a query like Check *)
type vernac_type =
  | VtStartProof of vernac_start
  | VtSideff of vernac_sideff_type
  | VtQed of vernac_qed_type
  | VtProofStep of bool (* parallelize *)
  | VtProofMode of string
  | VtQuery of vernac_part_of_script * report_with
  | VtStm of vernac_control * vernac_part_of_script
  | VtUnknown
and report_with = Stateid.t * Feedback.route_id (* feedback on id/route *)
and vernac_qed_type = VtKeep | VtKeepAsAxiom | VtDrop (* Qed/Admitted, Abort *)
and vernac_start = string * opacity_guarantee * Id.t list
and vernac_sideff_type = Id.t list
and vernac_is_alias = bool
and vernac_part_of_script = bool
and vernac_control =
  | VtFinish
  | VtWait
  | VtJoinDocument
  | VtPrintDag
  | VtObserve of Stateid.t
  | VtBack of Stateid.t
  | VtPG
and opacity_guarantee =
  | GuaranteesOpacity (** Only generates opaque terms at [Qed] *)
  | Doesn'tGuaranteeOpacity (** May generate transparent terms even with [Qed].*)
type vernac_when =
  | VtNow
  | VtLater
type vernac_classification = vernac_type * vernac_when
