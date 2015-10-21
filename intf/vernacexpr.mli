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
  | ProveBody of local_binder list * constr_expr
  | DefineBody of local_binder list * raw_red_expr option * constr_expr
      * constr_expr option

type fixpoint_expr =
    plident * (Id.t located option * recursion_order_expr) * local_binder list * constr_expr * constr_expr option

type cofixpoint_expr =
    plident * local_binder list * constr_expr * constr_expr option

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
  plident with_coercion * local_binder list * constr_expr option * inductive_kind *
    constructor_list_or_record_decl_expr

type one_inductive_expr =
  plident * local_binder list * constr_expr option * constructor_expr list

type proof_expr =
  plident option * (local_binder list * constr_expr * (lident option * recursion_order_expr) option)

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
  | SsEmpty
  | SsSingl of lident
  | SsCompl of section_subset_expr
  | SsUnion of section_subset_expr * section_subset_expr
  | SsSubstr of section_subset_expr * section_subset_expr
  | SsFwdClose of section_subset_expr

(** Extension identifiers for the VERNAC EXTEND mechanism. *)
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

(* Reference manual defines the grammar for Vernacular commands in Chapter 6
 *
 * ------------------------------------------------------------
 *
 * These files:
 *
 *   parsing/*.ml4
 *
 * define mapping of concrete syntax into "vernac_expr" values.
 *
 * ------------------------------------------------------------
 *
 * One can explore this mapping in the following way:
 *
 *   $ make -j4 bin/coqtop.byte
 *   $ rlwrap bin/coqtop.byte
 *
 *   Coq < Drop.
 *
 *   # #use "dev/include";;
 *   open Vernacexpr;;
 *
 *   # Pcoq.Gram.entry_parse Pcoq.main_entry Coqloop.top_buffer.tokens;;
 *
 *   Coq < Time Load "foo".
 *     - : option (Loc.t * Vernacexpr.vernac_expr) =
 *     Some (_, VernacTime (_, VernacLoad False "foo"))
 *
 *   # Pcoq.Gram.entry_parse Pcoq.main_entry Coqloop.top_buffer.tokens;;
 *
 *   Coq < Definition foo := fun x => x = 3.
 *     - : option (Loc.t * Vernacexpr.vernac_expr) =
 *     Some
 *      (_,
 *      VernacDefinition (None, Decl_kinds.Definition) ((_, foo), None)
 *       (DefineBody [] None
 *         (CLambdaN _
 *           [([(_, Names.Name.Name x)], Default Decl_kinds.Explicit,
 *            CHole _ (Some (Evar_kinds.BinderType (Names.Name.Name x)))
 *             Misctypes.IntroAnonymous None)]
 *           (CNotation _ "_ = _"
 *             ([CRef (Ident (_, x)) None; CPrim _ (Numeral 3)], 
 *             [], [])))
 *         None))
 *)

(** Representation of Vernacular commands. *)
type vernac_expr =
  (* Control *)
  | VernacLoad of verbose_flag * string               (* Load ... *)
  | VernacTime of located_vernac_expr                 (* Time ... *)
  | VernacRedirect of string * located_vernac_expr    (* Redirect ... *)
  | VernacTimeout of int * vernac_expr                (* Timeout ... *)
  | VernacFail of vernac_expr                         (* Fail ... *)
  | VernacError of exn (* always fails *)

  (* Syntax *)
  | VernacTacticNotation of                                                    (* Tactic Notation ... *)
      int * grammar_tactic_prod_item_expr list * raw_tactic_expr
  | VernacSyntaxExtension of                                                   (* Reserved ... *)
      obsolete_locality * (lstring * syntax_modifier list)
  | VernacOpenCloseScope of obsolete_locality * (bool * scope_name)            (* Open Scope ... *)
                                                                               (* Close Scope ... *)
  | VernacDelimiters of scope_name * string option                             (* Delimit ... *)
  | VernacBindScope of scope_name * reference or_by_notation list              (* Bind Scope ... *)
  | VernacInfix of obsolete_locality * (lstring * syntax_modifier list) *      (* Infix ... *)
      constr_expr * scope_name option
  | VernacNotation of                                                          (* Notation ... *)
      obsolete_locality * constr_expr * (lstring * syntax_modifier list) *
      scope_name option
  | VernacNotationAddFormat of string * string * string                        (* Format ... *)

  (* Gallina *)
  | VernacDefinition of                                                        (* Definition ... *)
      (locality option * definition_object_kind) * plident * definition_expr
  | VernacStartTheoremProof of theorem_kind * proof_expr list * bool           (* Theorem ... *)
                                                                               (* Lemma ... *)
                                                                               (* Fact ... *)
                                                                               (* Remark ... *)
                                                                               (* Property ... *)
                                                                               (* Proposition ... *)
                                                                               (* Corollary ... *)
  | VernacEndProof of proof_end                                                (* Admitted ... *)
                                                                               (* Qed ... *)
                                                                               (* Save ... *)
                                                                               (* Defined ... *)
  | VernacExactProof of constr_expr                                            (* Proof <term>. *)
  | VernacAssumption of (locality option * assumption_object_kind) *           (* Hypothesis ... *)
      inline * (plident list * constr_expr) with_coercion list                 (* Hypotheses ... *)
                                                                               (* Variable ... *)
                                                                               (* Variables ... *)
                                                                               (* Axiom ... *)
                                                                               (* Axioms ... *)
                                                                               (* Parameter ... *)
                                                                               (* Parameters ... *)
  | VernacInductive of private_flag * inductive_flag * (inductive_expr * decl_notation list) list   (* ... Inductive ... *)
                                                                                                    (* ... CoInductive ... *)
                                                                                                    (* ... Variant ... *)
                                                                                                    (* ... Record ... *)
                                                                                                    (* ... Structure ... *)
                                                                                                    (* ... Class ... *)
  | VernacFixpoint of                                                          (* Fixpoint ... *)
      locality option * (fixpoint_expr * decl_notation list) list
  | VernacCoFixpoint of                                                        (* CoFixpoint ... *)
      locality option * (cofixpoint_expr * decl_notation list) list
  | VernacScheme of (lident option * scheme) list                              (* Scheme ... *)
  | VernacCombinedScheme of lident * lident list                               (* Combined Scheme ... *)
  | VernacUniverse of lident list                                              (* Universe ... *)
  | VernacConstraint of (lident * Univ.constraint_type * lident) list          (* Constraint ... *)

  (* Gallina extensions *)
  | VernacBeginSection of lident                                               (* Section *)
                                                                               (* Chapter *)
  | VernacEndSegment of lident                                                 (* End <ident>. *)
  | VernacRequire of                                                           (* Require ... *)
      lreference option * export_flag option * lreference list
  | VernacImport of export_flag * lreference list                              (* Import ... *)
  | VernacCanonical of reference or_by_notation                                (* Canonical Structure ... *)
  | VernacCoercion of obsolete_locality * reference or_by_notation *           (* Coercion ... *)
      class_rawexpr * class_rawexpr
  | VernacIdentityCoercion of obsolete_locality * lident *                     (* Identity Coercion ... *)
      class_rawexpr * class_rawexpr
  | VernacNameSectionHypSet of lident * section_subset_expr                    (* Collection ... *)

  (* Type classes *)
  | VernacInstance of                                                          (* Instance ... *)
      bool * (* abstract instance *)
      local_binder list * (* super *)
	typeclass_constraint * (* instance name, class name, params *)
	(bool * constr_expr) option * (* props *)
	int option (* Priority *)

  | VernacContext of local_binder list                                         (* Context *)

  | VernacDeclareInstances of                                                  (* Existing Instance ... *)
    reference list * int option (* instance names, priority *)

  | VernacDeclareClass of reference (* inductive or definition name *)         (* Existing Class ... *)

  (* Modules and Module Types *)
  | VernacDeclareModule of bool option * lident *                              (* Declare Module  [Import | Export | ] <ident> ... *)
      module_binder list * module_ast_inl
  | VernacDefineModule of bool option * lident * module_binder list *          (* Module [Import | Export | ] <ident> ... *)
      module_ast_inl module_signature * module_ast_inl list
  | VernacDeclareModuleType of lident *                                        (* Module Type <ident> ... *)
      module_binder list * module_ast_inl list * module_ast_inl list
  | VernacInclude of module_ast_inl list                                       (* Include ... *)

  (* Solving *)

  | VernacSolve of goal_selector * int option * raw_tactic_expr * bool
  | VernacSolveExistential of int * constr_expr

  (* Auxiliary file and library management *)
  | VernacAddLoadPath of rec_flag * string * DirPath.t option                  (* Add LoadPath ... *)
  | VernacRemoveLoadPath of string                                             (* Remove LoadPath ... *)
  | VernacAddMLPath of rec_flag * string                                       (* Add ML Path ... *)
  | VernacDeclareMLModule of string list                                       (* Declare Module ... *)
  | VernacChdir of string option                                               (* Pwd. *)
                                                                               (* Cd ... *)

  (* State management *)
  | VernacWriteState of string                                                 (* Write State ... *)
  | VernacRestoreState of string                                               (* Restore State ... *)

  (* Resetting *)
  | VernacResetName of lident                                                  (* Reset <ident>. *)
  | VernacResetInitial                                                         (* Reset Initial. *)
  | VernacBack of int                                                          (* Back ... *)
  | VernacBackTo of int                                                        (* BackTo ... *)

  (* Commands *)
  | VernacDeclareTacticDefinition of tacdef_body list                          (* Ltac ... *)
  | VernacCreateHintDb of string * bool                                        (* Create HintDb ... *)
  | VernacRemoveHints of string list * reference list                          (* Remove Hints ... *)
  | VernacHints of obsolete_locality * string list * hints_expr                (* Hint ... *)
  | VernacSyntacticDefinition of Id.t located * (Id.t list * constr_expr) *    (* Notation ... *)
      obsolete_locality * onlyparsing_flag
  | VernacDeclareImplicits of reference or_by_notation *                       (* Implicit Arguments ... *)
      (explicitation * bool * bool) list list
  | VernacArguments of reference or_by_notation *                              (* Arguments ... *)
      ((Name.t * bool * (Loc.t * string) option * bool * bool) list) list *
      int * [ `ReductionDontExposeCase | `ReductionNeverUnfold | `Rename |
              `ExtraScopes | `Assert | `ClearImplicits | `ClearScopes |
              `DefaultImplicits ] list
  | VernacArgumentsScope of reference or_by_notation *                         (* Arguments Scope ... *)
      scope_name option list
  | VernacReserve of simple_binder list                                        (* Implicit ... *)
  | VernacGeneralizable of (lident list) option
  | VernacSetOpacity of (Conv_oracle.level * reference or_by_notation list)    (* Opaque ... *)
  | VernacSetStrategy of                                                       (* Strategy ... *)
      (Conv_oracle.level * reference or_by_notation list) list
  | VernacUnsetOption of Goptions.option_name                                  (* Unset ... *)
  | VernacSetOption of Goptions.option_name * option_value                     (* Set ... *)
                                                                               (* Debug ... *)
  | VernacAddOption of Goptions.option_name * option_ref_value list            (* Add ... *)
  | VernacRemoveOption of Goptions.option_name * option_ref_value list         (* Remove ... *)
  | VernacMemOption of Goptions.option_name * option_ref_value list            (* Test ... for ... *)
  | VernacPrintOption of Goptions.option_name                                  (* Print Table ... *)
                                                                               (* Test ... *)
  | VernacCheckMayEval of raw_red_expr option * int option * constr_expr       (* Check ... *)
  | VernacGlobalCheck of constr_expr                                           (* Type ... *)
  | VernacDeclareReduction of string * raw_red_expr                            (* Declare Reduction ... *)
  | VernacPrint of printable                                                   (* Print ... *)
  | VernacSearch of searchable * int option * search_restriction               (* SearchHead ... *)
                                                                               (* SearchPattern ... *)
                                                                               (* SearchRewrite ... *)
                                                                               (* Search ... *)
                                                                               (* SearchAbout ... *)
  | VernacLocate of locatable                                                  (* Locate ... *)

  | VernacRegister of lident * register_kind                                   (* Register ... *)
  | VernacComments of comment list                                             (* Comments ... *)

  (* Stm backdoor *)
  | VernacStm of vernac_expr stm_vernac                                        (* Stm ... *)

  (* Proof management *)
  | VernacGoal of constr_expr                                                  (* Goal ... *)
  | VernacAbort of lident option                                               (* Abort. *)
  | VernacAbortAll                                                             (* Abort All. *)
  | VernacRestart                                                              (* Restart. *)
  | VernacUndo of int                                                          (* Undo. *)
  | VernacUndoTo of int                                                        (* Undo ... To ... *)
  | VernacBacktrack of int*int*int                                             (* Backtrack ... *)
  | VernacFocus of int option                                                  (* Focus ... *)
  | VernacUnfocus                                                              (* Unfocus ... *)
  | VernacUnfocused                                                            (* Unfocused ... *)
  | VernacBullet of bullet                                                     (* [ * | + | - ] *)
  | VernacSubproof of int option                                               (* { *)
  | VernacEndSubproof                                                          (* } *)
  | VernacShow of showable                                                     (* Show ... *)
  | VernacCheckGuard                                                           (* Guarded. *)
  | VernacProof of raw_tactic_expr option * section_subset_expr option         (* Proof. *)
                                                                               (* Proof using ... *)
  | VernacProofMode of string                                                  (* Proof with ... *)
  (* Toplevel control *)
  | VernacToplevelControl of exn                                               (* Drop. *)
                                                                               (* Quit. *)

  (* For extension *)
  | VernacExtend of extend_name * Genarg.raw_generic_argument list

  (* Flags *)
  | VernacProgram of vernac_expr                                               (* Program ... *)
  | VernacPolymorphic of bool * vernac_expr                                    (* Polymorphic ... *)
  | VernacLocal of bool * vernac_expr                                          (* Local ... *)
                                                                               (* Global ... *)

and tacdef_body =
  | TacticDefinition of Id.t Loc.located * raw_tactic_expr  (* indicates that user employed ':=' in Ltac body *)
  | TacticRedefinition of reference * raw_tactic_expr       (* indicates that user employed '::=' in Ltac body *)

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
