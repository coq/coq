(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Util
open Names
open Tacexpr
open Extend
open Genarg
open Topconstr
open Decl_kinds
open Ppextend

(* Toplevel control exceptions *)
exception ProtectedLoop
exception Drop
exception Quit

open Libnames
open Nametab

type lident = identifier located
type lname = name located
type lstring = string
type lreference = reference

type class_rawexpr = FunClass | SortClass | RefClass of reference
  
type printable =
  | PrintTables
  | PrintLocalContext
  | PrintFullContext
  | PrintSectionContext of reference
  | PrintInspect of int
  | PrintGrammar of string * string
  | PrintLoadPath
  | PrintModules
  | PrintModule of reference
  | PrintModuleType of reference
  | PrintMLLoadPath
  | PrintMLModules
  | PrintName of reference
  | PrintOpaqueName of reference
  | PrintGraph
  | PrintClasses
  | PrintCoercions
  | PrintCoercionPaths of class_rawexpr * class_rawexpr
  | PrintUniverses of string option
  | PrintHint of reference
  | PrintHintGoal
  | PrintHintDbName of string
  | PrintHintDb
  | PrintScopes
  | PrintScope of string
  | PrintVisibility of string option
  | PrintAbout of reference
  | PrintImplicit of reference

type search_about_item =
  | SearchRef of reference
  | SearchString of string

type searchable =
  | SearchPattern of pattern_expr
  | SearchRewrite of pattern_expr
  | SearchHead of reference
  | SearchAbout of search_about_item list

type locatable =
  | LocateTerm of reference
  | LocateLibrary of reference
  | LocateFile of string
  | LocateNotation of notation

type goable =
  | GoTo of int
  | GoTop
  | GoNext
  | GoPrev

type showable =
  | ShowGoal of int option
  | ShowGoalImplicitly of int option
  | ShowProof
  | ShowNode
  | ShowScript
  | ShowExistentials
  | ShowTree
  | ShowProofNames
  | ShowIntros of bool
  | ExplainProof of int list
  | ExplainTree of int list

type comment =
  | CommentConstr of constr_expr
  | CommentString of string
  | CommentInt of int

type hints =
  | HintsResolve of (identifier option * constr_expr) list
  | HintsImmediate of (identifier option * constr_expr) list
  | HintsUnfold of (identifier option * reference) list
  | HintsConstructors of identifier option * reference list
  | HintsExtern of identifier option * int * constr_expr * raw_tactic_expr
  | HintsDestruct of identifier *
      int * (bool,unit) location * constr_expr * raw_tactic_expr

type search_restriction =
  | SearchInside of reference list
  | SearchOutside of reference list

type option_value =
  | StringValue of string
  | IntValue of int
  | BoolValue of bool

type option_ref_value =
  | StringRefValue of string
  | QualidRefValue of reference

type rec_flag       = bool (* true = Rec;           false = NoRec          *)
type verbose_flag   = bool (* true = Verbose;       false = Silent         *)
type opacity_flag   = bool (* true = Opaque;        false = Transparent    *)
type locality_flag  = bool (* true = Local;         false = Global         *)
type coercion_flag  = bool (* true = AddCoercion;   false = NoCoercion     *)
type export_flag    = bool (* true = Export;        false = Import         *)
type specif_flag    = bool (* true = Specification; false = Implementation *)
type inductive_flag = bool (* true = Inductive;     false = CoInductive    *)
type onlyparsing_flag = bool (* true = Parse only;  false = Print also     *)

type sort_expr = Rawterm.rawsort

type decl_notation = (string * constr_expr * scope_name option) option
type simple_binder = lident list  * constr_expr
type 'a with_coercion = coercion_flag * 'a
type constructor_expr = (lident * constr_expr) with_coercion
type inductive_expr =
     lident * decl_notation * local_binder list * constr_expr
    * constructor_expr list
type definition_expr =
  | ProveBody of local_binder list * constr_expr
  | DefineBody of local_binder list * raw_red_expr option * constr_expr
      * constr_expr option

type local_decl_expr =
  | AssumExpr of lname * constr_expr
  | DefExpr of lname * constr_expr * constr_expr option

type module_binder = lident list * module_type_ast

type proof_end =
  | Admitted
  | Proved of opacity_flag * (lident * theorem_kind option) option

type vernac_expr =
  (* Control *)
  | VernacList of located_vernac_expr list
  | VernacLoad of verbose_flag * lstring
  | VernacTime of vernac_expr
  | VernacVar of lident

  (* Syntax *) 
  | VernacGrammar of lstring * raw_grammar_entry list
  | VernacTacticGrammar of
      (lstring * (lstring * grammar_production list) * raw_tactic_expr) list
  | VernacSyntax of lstring * raw_syntax_entry list
  | VernacSyntaxExtension of locality_flag *
      (lstring * syntax_modifier list) option 
      * (lstring * syntax_modifier list) option
  | VernacDistfix of locality_flag *
      grammar_associativity * precedence * lstring * lreference *
      scope_name option
  | VernacOpenCloseScope of (locality_flag * bool * scope_name)
  | VernacDelimiters of scope_name * lstring
  | VernacBindScope of scope_name * class_rawexpr list
  | VernacArgumentsScope of lreference * scope_name option list
  | VernacInfix of locality_flag * (lstring * syntax_modifier list) *
      lreference * (lstring * syntax_modifier list) option * scope_name option
  | VernacNotation of
      locality_flag * constr_expr * (lstring * syntax_modifier list) option *
      (lstring * syntax_modifier list) option * scope_name option

  (* Gallina *)
  | VernacDefinition of definition_kind * lident * definition_expr * 
      declaration_hook
  | VernacStartTheoremProof of theorem_kind * lident *
      (local_binder list * constr_expr) * bool * declaration_hook
  | VernacEndProof of proof_end
  | VernacExactProof of constr_expr
  | VernacAssumption of assumption_kind * simple_binder with_coercion list
  | VernacInductive of inductive_flag * inductive_expr list
  | VernacFixpoint of (fixpoint_expr * decl_notation) list
  | VernacCoFixpoint of cofixpoint_expr list
  | VernacScheme of (lident * bool * lreference * sort_expr) list

  (* Gallina extensions *)
  | VernacRecord of bool (* = Record or Structure *)
      * lident with_coercion * local_binder list
      * constr_expr * lident option * local_decl_expr with_coercion list
  | VernacBeginSection of lident
  | VernacEndSegment of lident
  | VernacRequire of
      export_flag option * specif_flag option * lreference list
  | VernacImport of export_flag * lreference list
  | VernacCanonical of lreference
  | VernacCoercion of strength * lreference * class_rawexpr * class_rawexpr
  | VernacIdentityCoercion of strength * lident * 
      class_rawexpr * class_rawexpr

  (* Modules and Module Types *)
  | VernacDeclareModule of lident * 
      module_binder list * (module_type_ast * bool) option * module_ast option
  | VernacDefineModule of lident * 
      module_binder list * (module_type_ast * bool) option * module_ast option
  | VernacDeclareModuleType of lident * 
      module_binder list * module_type_ast option

  (* Solving *)
  | VernacSolve of int * raw_tactic_expr * bool
  | VernacSolveExistential of int * constr_expr

  (* Auxiliary file and library management *)
  | VernacRequireFrom of export_flag option * specif_flag option * lstring
  | VernacAddLoadPath of rec_flag * lstring * dir_path option
  | VernacRemoveLoadPath of lstring
  | VernacAddMLPath of rec_flag * lstring
  | VernacDeclareMLModule of lstring list
  | VernacChdir of lstring option

  (* State management *)
  | VernacWriteState of lstring
  | VernacRestoreState of lstring

  (* Resetting *)
  | VernacResetName of lident
  | VernacResetInitial
  | VernacBack of int

  (* Commands *)
  | VernacDeclareTacticDefinition of
      rec_flag * (lident * raw_tactic_expr) list
  | VernacHints of locality_flag * lstring list * hints
  | VernacSyntacticDefinition of identifier * constr_expr * locality_flag *
      onlyparsing_flag
  | VernacDeclareImplicits of lreference * explicitation list option
  | VernacReserve of lident list * constr_expr
  | VernacSetOpacity of opacity_flag * lreference list
  | VernacUnsetOption of Goptions.option_name
  | VernacSetOption of Goptions.option_name * option_value
  | VernacAddOption of Goptions.option_name * option_ref_value list
  | VernacRemoveOption of Goptions.option_name * option_ref_value list
  | VernacMemOption of Goptions.option_name * option_ref_value list
  | VernacPrintOption of Goptions.option_name
  | VernacCheckMayEval of raw_red_expr option * int option * constr_expr
  | VernacGlobalCheck of constr_expr
  | VernacPrint of printable
  | VernacSearch of searchable * search_restriction
  | VernacLocate of locatable
  | VernacComments of comment list
  | VernacNop

  (* Proof management *)
  | VernacGoal of constr_expr
  | VernacAbort of lident option
  | VernacAbortAll
  | VernacRestart
  | VernacSuspend
  | VernacResume of lident option
  | VernacUndo of int
  | VernacFocus of int option
  | VernacUnfocus
  | VernacGo of goable
  | VernacShow of showable
  | VernacCheckGuard
  | VernacDebug of bool
  | VernacProof of raw_tactic_expr
  (* Toplevel control *)
  | VernacToplevelControl of exn

  (* For translation from V7 to V8 syntax *)
  | VernacV8only of vernac_expr
  | VernacV7only of vernac_expr

  (* For extension *)
  | VernacExtend of string * raw_generic_argument list

and located_vernac_expr = loc * vernac_expr
