(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

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

type def_kind = DEFINITION | LET | LOCAL | THEOREM | LETTOP | DECL | REMARK
  | FACT | LEMMA
  | COERCION | LCOERCION | OBJECT | LOBJECT | OBJCOERCION | LOBJCOERCION
  | SUBCLASS | LSUBCLASS

open Libnames
open Nametab

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
  | PrintScope of string

type searchable =
  | SearchPattern of pattern_expr
  | SearchRewrite of pattern_expr
  | SearchHead of reference
  | SearchAbout of reference

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

type raw_constr_expr = constr_expr

type hints =
  | HintsResolve of (identifier option * constr_expr) list
  | HintsImmediate of (identifier option * constr_expr) list
  | HintsUnfold of (identifier option * reference) list
  | HintsConstructors of identifier * reference
  | HintsExtern of identifier * int * raw_constr_expr * raw_tactic_expr

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

type sort_expr = Rawterm.rawsort

type simple_binder = identifier * constr_expr
type 'a with_coercion = coercion_flag * 'a
type constructor_expr = simple_binder with_coercion
type inductive_expr =
    identifier *  simple_binder list * constr_expr * constructor_expr list
type definition_expr =
  | ProveBody of local_binder list * constr_expr
  | DefineBody of local_binder list * raw_red_expr option * constr_expr
      * constr_expr option

type local_decl_expr =
  | AssumExpr of identifier * constr_expr
  | DefExpr of identifier * constr_expr * constr_expr option

type module_binder = identifier list * module_type_ast

type vernac_expr =
  (* Control *)
  | VernacList of located_vernac_expr list
  | VernacLoad of verbose_flag * string
  | VernacTime of vernac_expr
  | VernacVar of identifier

  (* Syntax *) 
  | VernacGrammar of string * raw_grammar_entry list
  | VernacTacticGrammar of
      (string * (string * grammar_production list) * raw_tactic_expr) list
  | VernacSyntax of string * raw_syntax_entry list
  | VernacSyntaxExtension of string * syntax_modifier list
  | VernacOpenScope of scope_name
  | VernacDelimiters of scope_name * string
  | VernacArgumentsScope of reference * scope_name option list
  | VernacInfix of
      grammar_associativity * precedence * string * reference * bool *
      scope_name option
  | VernacDistfix of
      grammar_associativity * precedence * string * reference *
      scope_name option
  | VernacNotation of
      string * constr_expr * syntax_modifier list * scope_name option

  (* Gallina *)
  | VernacDefinition of definition_kind * identifier * definition_expr *
      declaration_hook * definitionkind
  | VernacStartTheoremProof of theorem_kind * identifier *
      (local_binder list * constr_expr) * bool * declaration_hook
  | VernacEndProof of opacity_flag * (identifier * theorem_kind option) option
  | VernacExactProof of constr_expr
  | VernacAssumption of assumption_kind * simple_binder with_coercion list
  | VernacInductive of inductive_flag * inductive_expr list
  | VernacFixpoint of fixpoint_expr list
  | VernacCoFixpoint of cofixpoint_expr list
  | VernacScheme of (identifier * bool * reference * sort_expr) list
  | VernacRule of simple_binder list * constr_expr * constr_expr

  (* Gallina extensions *)
  | VernacRecord of identifier with_coercion * simple_binder list
      * constr_expr * identifier option * local_decl_expr with_coercion list
  | VernacBeginSection of identifier
  | VernacEndSegment of identifier
  | VernacRequire of
      export_flag option * specif_flag option * reference list
  | VernacImport of export_flag * reference list
  | VernacCanonical of reference
  | VernacCoercion of strength * reference * class_rawexpr * class_rawexpr
  | VernacIdentityCoercion of strength * identifier * 
      class_rawexpr * class_rawexpr

  (* Modules and Module Types *)
  | VernacDeclareModule of identifier * 
      module_binder list * (module_type_ast * bool) option * module_ast option
  | VernacDefineModule of identifier * 
      module_binder list * (module_type_ast * bool) option * module_ast option
  | VernacDeclareModuleType of identifier * 
      module_binder list * module_type_ast option

  (* Solving *)
  | VernacSolve of int * raw_tactic_expr * bool
  | VernacSolveExistential of int * constr_expr

  (* Auxiliary file and library management *)
  | VernacRequireFrom of export_flag * specif_flag option * string
  | VernacAddLoadPath of rec_flag * string * dir_path option
  | VernacRemoveLoadPath of string
  | VernacAddMLPath of rec_flag * string
  | VernacDeclareMLModule of string list
  | VernacChdir of string option

  (* State management *)
  | VernacWriteState of string
  | VernacRestoreState of string

  (* Resetting *)
  | VernacResetName of identifier located
  | VernacResetInitial
  | VernacBack of int

  (* Commands *)
  | VernacDeclareTacticDefinition of
      rec_flag * (identifier located * raw_tactic_expr) list
  | VernacHints of string list * hints
  | VernacHintDestruct of
      identifier * (bool,unit) location * constr_expr * int * raw_tactic_expr
  | VernacSyntacticDefinition of identifier * constr_expr * int option
  | VernacDeclareImplicits of reference * int list option
  | VernacSetOpacity of opacity_flag * reference list
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
  | VernacAbort of identifier located option
  | VernacAbortAll
  | VernacRestart
  | VernacSuspend
  | VernacResume of identifier located option
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
