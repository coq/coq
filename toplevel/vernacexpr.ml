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
open Coqast
open Tacexpr
open Extend
open Genarg

(* Toplevel control exceptions *)
exception ProtectedLoop
exception Drop
exception Quit

type def_kind = DEFINITION | LET | LOCAL | THEOREM | LETTOP | DECL | REMARK
  | FACT | LEMMA
  | COERCION | LCOERCION | OBJECT | LOBJECT | OBJCOERCION | LOBJCOERCION
  | SUBCLASS | LSUBCLASS

open Nametab

type class_rawexpr = FunClass | SortClass | RefClass of qualid located
  
type printable =
  | PrintTables
  | PrintLocalContext
  | PrintFullContext
  | PrintSectionContext of qualid located
  | PrintInspect of int
  | PrintGrammar of string * string
  | PrintLoadPath
  | PrintModules
  | PrintMLLoadPath
  | PrintMLModules
  | PrintName of qualid located
  | PrintOpaqueName of qualid located
  | PrintGraph
  | PrintClasses
  | PrintCoercions
  | PrintCoercionPaths of class_rawexpr * class_rawexpr
  | PrintUniverses of string option
  | PrintHint of qualid located
  | PrintHintGoal
  | PrintHintDbName of string
  | PrintHintDb

type searchable =
  | SearchPattern of pattern_ast
  | SearchRewrite of pattern_ast
  | SearchHead of qualid located

type locatable =
  | LocateTerm of qualid located
  | LocateLibrary of qualid located
  | LocateFile of string

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

type theorem_kind =
  | Theorem
  | Lemma
  | Decl
  | Fact
  | Remark

type definition_kind =
  | Definition
  | LocalDefinition

type goal_kind =
  | StartTheoremProof of theorem_kind
  | StartDefinitionBody of definition_kind

type assumption_kind =
  | AssumptionHypothesis
  | AssumptionVariable
  | AssumptionAxiom
  | AssumptionParameter

type comment =
  | CommentConstr of constr_ast
  | CommentString of string
  | CommentInt of int

type raw_constr_ast = t

type hints =
  | HintsResolve of (identifier option * constr_ast) list
  | HintsImmediate of (identifier option * constr_ast) list
  | HintsUnfold of (identifier option * qualid located) list
  | HintsConstructors of identifier * qualid located
  | HintsExtern of identifier * int * raw_constr_ast * raw_tactic_expr

type search_restriction =
  | SearchInside of qualid located list
  | SearchOutside of qualid located list

type option_value =
  | StringValue of string
  | IntValue of int
  | BoolValue of bool

type option_ref_value =
  | StringRefValue of string
  | QualidRefValue of qualid located

type rec_flag       = bool (* true = Rec;           false = NoRec          *)
type verbose_flag   = bool (* true = Verbose;       false = Silent         *)
type opacity_flag   = bool (* true = Opaque;        false = Transparent    *)
type locality_flag  = bool (* true = Local;         false = Global         *)
type coercion_flag  = bool (* true = AddCoercion;   false = NoCoercion     *)
type export_flag    = bool (* true = Export;        false = Import         *)
type specif_flag    = bool (* true = Specification; false = Implementation *)
type inductive_flag = bool (* true = Inductive;     false = CoInductive    *)

type sort_expr = t

type simple_binder = identifier * constr_ast
type 'a with_coercion = coercion_flag * 'a
type constructor_expr = simple_binder with_coercion
type inductive_expr =
    identifier *  simple_binder list * constr_ast * constructor_expr list
type fixpoint_expr =
    identifier * simple_binder list * constr_ast * constr_ast
type cofixpoint_expr =
    identifier * constr_ast * constr_ast

type local_decl_expr =
  | AssumExpr of identifier * constr_ast
  | DefExpr of identifier * constr_ast * constr_ast option

type grammar_entry_ast = 
  (loc * string) * Ast.entry_type option * 
    grammar_associativity * raw_grammar_rule list

type vernac_expr =
  (* Control *)
  | VernacList of located_vernac_expr list
  | VernacLoad of verbose_flag * string
  | VernacTime of vernac_expr
  | VernacVar of identifier

  (* Syntax *) 
  | VernacGrammar of string * grammar_entry_ast list
  | VernacTacticGrammar of
      (string * (string * grammar_production list) * raw_tactic_expr) list
  | VernacSyntax of string * syntax_entry_ast list
  | VernacInfix of grammar_associativity * int * string * qualid located
  | VernacDistfix of grammar_associativity * int * string * qualid located

  (* Gallina *)
  | VernacDefinition of definition_kind * identifier *
      raw_red_expr option * constr_ast * constr_ast option *
      Proof_type.declaration_hook
  | VernacStartProof of goal_kind * identifier option *
      constr_ast * bool * Proof_type.declaration_hook
  | VernacEndProof of opacity_flag * (identifier * theorem_kind option) option
  | VernacExactProof of constr_ast
  | VernacAssumption of assumption_kind * simple_binder with_coercion list
  | VernacInductive of inductive_flag * inductive_expr list
  | VernacFixpoint of fixpoint_expr list
  | VernacCoFixpoint of cofixpoint_expr list
  | VernacScheme of (identifier * bool * qualid located * sort_expr) list

  (* Gallina extensions *)
  | VernacRecord of identifier with_coercion * simple_binder list
      * sort_expr * identifier option * local_decl_expr with_coercion list
  | VernacBeginSection of identifier
  | VernacEndSection of identifier
  | VernacRequire of
      export_flag option * specif_flag option * qualid located list
  | VernacImport of export_flag * qualid located list
  | VernacCanonical of qualid located
  | VernacCoercion of strength * qualid located * class_rawexpr * class_rawexpr
  | VernacIdentityCoercion of strength * identifier * 
      class_rawexpr * class_rawexpr

  (* Solving *)
  | VernacSolve of int * raw_tactic_expr
  | VernacSolveExistential of int * constr_ast

  (* Auxiliary file and library management *)
  | VernacRequireFrom of export_flag * specif_flag option * identifier * string
  | VernacAddLoadPath of rec_flag * string * dir_path option
  | VernacRemoveLoadPath of string
  | VernacAddMLPath of rec_flag * string
  | VernacDeclareMLModule of string list
  | VernacChdir of string option

  (* State management *)
  | VernacWriteState of string
  | VernacRestoreState of string

  (* Resetting *)
  | VernacResetName of identifier
  | VernacResetInitial
  | VernacBack of int

  (* Commands *)
  | VernacDeclareTacticDefinition of
      loc * (identifier located * raw_tactic_expr) list
  | VernacHints of string list * hints
  | VernacHintDestruct of
      identifier * (bool,unit) location * constr_ast * int * raw_tactic_expr
  | VernacSyntacticDefinition of identifier * constr_ast * int option
  | VernacDeclareImplicits of qualid located * int list option
  | VernacSetOpacity of opacity_flag * qualid located list
  | VernacUnsetOption of Goptions.option_name
  | VernacSetOption of Goptions.option_name * option_value
  | VernacAddOption of Goptions.option_name * option_ref_value list
  | VernacRemoveOption of Goptions.option_name * option_ref_value list
  | VernacMemOption of Goptions.option_name * option_ref_value list
  | VernacPrintOption of Goptions.option_name
  | VernacCheckMayEval of raw_red_expr option * int option * constr_ast
  | VernacGlobalCheck of constr_ast
  | VernacPrint of printable
  | VernacSearch of searchable * search_restriction
  | VernacLocate of locatable
  | VernacComments of comment list
  | VernacNop

  (* Proof management *)
(*  | VernacGoal of constr_ast option*)
  | VernacAbort of identifier option
  | VernacAbortAll
  | VernacRestart
  | VernacSuspend
  | VernacResume of identifier option
  | VernacUndo of int
  | VernacFocus of int option
  | VernacUnfocus
  | VernacGo of goable
  | VernacShow of showable
  | VernacCheckGuard
  | VernacDebug of bool

  (* Toplevel control *)
  | VernacToplevelControl of exn

  (* For extension *)
  | VernacExtend of string * raw_generic_argument list

and located_vernac_expr = loc * vernac_expr
