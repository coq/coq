(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open Constrexpr
open Libnames
open Nametab
open Genredexpr
open Genarg
open Pattern
open Misctypes
open Locus

type direction_flag = bool (* true = Left-to-right    false = right-to-right *)
type lazy_flag =
  | General (* returns all possible successes *)
  | Select  (* returns all successes of the first matching branch *)
  | Once    (* returns the first success in a maching branch
               (not necessarily the first) *)
type global_flag = (* [gfail] or [fail] *)
  | TacGlobal
  | TacLocal
type evars_flag = bool     (* true = pose evars       false = fail on evars *)
type rec_flag = bool       (* true = recursive        false = not recursive *)
type advanced_flag = bool  (* true = advanced         false = basic *)
type letin_flag = bool     (* true = use local def    false = use Leibniz *)
type clear_flag = bool option (* true = clear hyp, false = keep hyp, None = use default *)

type debug = Debug | Info | Off (* for trivial / auto / eauto ... *)

type goal_selector =
  | SelectNth of int
  | SelectList of (int * int) list
  | SelectId of Id.t
  | SelectAll

type 'a core_destruction_arg =
  | ElimOnConstr of 'a
  | ElimOnIdent of Id.t located
  | ElimOnAnonHyp of int

type 'a destruction_arg =
  clear_flag * 'a core_destruction_arg

type inversion_kind =
  | SimpleInversion
  | FullInversion
  | FullInversionClear

type ('c,'d,'id) inversion_strength =
  | NonDepInversion of
      inversion_kind * 'id list * 'd or_and_intro_pattern_expr located or_var option
  | DepInversion of
      inversion_kind * 'c option * 'd or_and_intro_pattern_expr located or_var option
  | InversionUsing of 'c * 'id list

type ('a,'b) location = HypLocation of 'a | ConclLocation of 'b

type 'id message_token =
  | MsgString of string
  | MsgInt of int
  | MsgIdent of 'id

type ('dconstr,'id) induction_clause =
    'dconstr with_bindings destruction_arg *
    (intro_pattern_naming_expr located option (* eqn:... *)
    * 'dconstr or_and_intro_pattern_expr located or_var option) (* as ... *)
    * 'id clause_expr option (* in ... *)

type ('constr,'dconstr,'id) induction_clause_list =
    ('dconstr,'id) induction_clause list
    * 'constr with_bindings option (* using ... *)

type 'a with_bindings_arg = clear_flag * 'a with_bindings

type multi =
  | Precisely of int
  | UpTo of int
  | RepeatStar
  | RepeatPlus

(* Type of patterns *)
type 'a match_pattern =
  | Term of 'a
  | Subterm of bool * Id.t option * 'a

(* Type of hypotheses for a Match Context rule *)
type 'a match_context_hyps =
  | Hyp of Name.t located * 'a match_pattern
  | Def of Name.t located * 'a match_pattern * 'a match_pattern

(* Type of a Match rule for Match Context and Match *)
type ('a,'t) match_rule =
  | Pat of 'a match_context_hyps list * 'a match_pattern * 't
  | All of 't

(** Extension indentifiers for the TACTIC EXTEND mechanism. *)
type ml_tactic_name = {
  (** Name of the plugin where the tactic is defined, typically coming from a
      DECLARE PLUGIN statement in the source. *)
  mltac_plugin : string;
  (** Name of the tactic entry where the tactic is defined, typically found
      after the TACTIC EXTEND statement in the source. *)
  mltac_tactic : string;
}

type ml_tactic_entry = {
  mltac_name : ml_tactic_name;
  mltac_index : int;
}

(** Composite types *)

(** In globalize tactics, we need to keep the initial [constr_expr] to recompute
   in the environment by the effective calls to Intro, Inversion, etc 
   The [constr_expr] field is [None] in TacDef though *)
type glob_constr_and_expr = Glob_term.glob_constr * constr_expr option

type open_constr_expr = unit * constr_expr
type open_glob_constr = unit * glob_constr_and_expr

type binding_bound_vars = Id.Set.t
type glob_constr_pattern_and_expr = binding_bound_vars * glob_constr_and_expr * constr_pattern

type 'a delayed_open = 'a Pretyping.delayed_open =
  { delayed : 'r. Environ.env -> 'r Sigma.t -> ('a, 'r) Sigma.sigma }

type delayed_open_constr_with_bindings = Term.constr with_bindings delayed_open

type delayed_open_constr = Term.constr delayed_open

type intro_pattern = delayed_open_constr intro_pattern_expr located
type intro_patterns = delayed_open_constr intro_pattern_expr located list
type or_and_intro_pattern = delayed_open_constr or_and_intro_pattern_expr located
type intro_pattern_naming = intro_pattern_naming_expr located

(** Generic expressions for atomic tactics *)

type 'a gen_atomic_tactic_expr =
  (* Basic tactics *)
  | TacIntroPattern of evars_flag * 'dtrm intro_pattern_expr located list
  | TacApply of advanced_flag * evars_flag * 'trm with_bindings_arg list *
      ('nam * 'dtrm intro_pattern_expr located option) option
  | TacElim of evars_flag * 'trm with_bindings_arg * 'trm with_bindings option
  | TacCase of evars_flag * 'trm with_bindings_arg
  | TacMutualFix of Id.t * int * (Id.t * int * 'trm) list
  | TacMutualCofix of Id.t * (Id.t * 'trm) list
  | TacAssert of
      bool * 'tacexpr option option *
      'dtrm intro_pattern_expr located option * 'trm
  | TacGeneralize of ('trm with_occurrences * Name.t) list
  | TacLetTac of Name.t * 'trm * 'nam clause_expr * letin_flag *
      intro_pattern_naming_expr located option

  (* Derived basic tactics *)
  | TacInductionDestruct of
      rec_flag * evars_flag * ('trm,'dtrm,'nam) induction_clause_list

  (* Conversion *)
  | TacReduce of ('trm,'cst,'pat) red_expr_gen * 'nam clause_expr
  | TacChange of 'pat option * 'dtrm * 'nam clause_expr

  (* Equality and inversion *)
  | TacRewrite of evars_flag *
      (bool * multi * 'dtrm with_bindings_arg) list * 'nam clause_expr *
      (* spiwack: using ['dtrm] here is a small hack, may not be
         stable by a change in the representation of delayed
         terms. Because, in fact, it is the whole "with_bindings"
         which is delayed. But because the "t" level for ['dtrm] is
         uninterpreted, it works fine here too, and avoid more
         disruption of this file. *)
      'tacexpr option
  | TacInversion of ('trm,'dtrm,'nam) inversion_strength * quantified_hypothesis

constraint 'a = <
    term:'trm;
    dterm: 'dtrm;
    pattern:'pat;
    constant:'cst;
    reference:'ref;
    name:'nam;
    tacexpr:'tacexpr;
    level:'lev
>

(** Possible arguments of a tactic definition *)

type 'a gen_tactic_arg =
  | TacGeneric     of 'lev generic_argument
  | ConstrMayEval  of ('trm,'cst,'pat) may_eval
  | Reference      of 'ref
  | TacCall of Loc.t * 'ref *
      'a gen_tactic_arg list
  | TacFreshId of string or_var list
  | TacExactId of Id.t
  | Tacexp of 'tacexpr
  | TacPretype of 'trm
  | TacNumgoals

constraint 'a = <
    term:'trm;
    dterm: 'dtrm;
    pattern:'pat;
    constant:'cst;
    reference:'ref;
    name:'nam;
    tacexpr:'tacexpr;
    level:'lev
>

(** Generic ltac expressions.
    't : terms, 'p : patterns, 'c : constants, 'i : inductive,
    'r : ltac refs, 'n : idents, 'l : levels *)

and 'a gen_tactic_expr =
  | TacAtom of Loc.t * 'a gen_atomic_tactic_expr
  | TacThen of
      'a gen_tactic_expr *
      'a gen_tactic_expr
  | TacDispatch of
      'a gen_tactic_expr list
  | TacExtendTac of
      'a gen_tactic_expr array *
      'a gen_tactic_expr *
      'a gen_tactic_expr array
  | TacThens of
      'a gen_tactic_expr *
      'a gen_tactic_expr list
  | TacThens3parts of
      'a gen_tactic_expr *
      'a gen_tactic_expr array *
      'a gen_tactic_expr *
      'a gen_tactic_expr array
  | TacFirst of 'a gen_tactic_expr list
  | TacComplete of 'a gen_tactic_expr
  | TacSolve of 'a gen_tactic_expr list
  | TacTry of 'a gen_tactic_expr
  | TacOr of
      'a gen_tactic_expr *
      'a gen_tactic_expr
  | TacOnce of
      'a gen_tactic_expr
  | TacExactlyOnce of
      'a gen_tactic_expr
  | TacIfThenCatch of
      'a gen_tactic_expr *
      'a gen_tactic_expr *
      'a gen_tactic_expr
  | TacOrelse of
      'a gen_tactic_expr *
      'a gen_tactic_expr
  | TacDo of int or_var * 'a gen_tactic_expr
  | TacTimeout of int or_var * 'a gen_tactic_expr
  | TacTime of string option * 'a gen_tactic_expr
  | TacRepeat of 'a gen_tactic_expr
  | TacProgress of 'a gen_tactic_expr
  | TacShowHyps of 'a gen_tactic_expr
  | TacAbstract of
      'a gen_tactic_expr * Id.t option
  | TacId of 'n message_token list
  | TacFail of global_flag * int or_var * 'n message_token list
  | TacInfo of 'a gen_tactic_expr
  | TacLetIn of rec_flag *
      (Id.t located * 'a gen_tactic_arg) list *
      'a gen_tactic_expr
  | TacMatch of lazy_flag *
      'a gen_tactic_expr *
      ('p,'a gen_tactic_expr) match_rule list
  | TacMatchGoal of lazy_flag * direction_flag *
      ('p,'a gen_tactic_expr) match_rule list
  | TacFun of 'a gen_tactic_fun_ast
  | TacArg of 'a gen_tactic_arg located
  | TacSelect of goal_selector * 'a gen_tactic_expr
  (* For ML extensions *)
  | TacML of Loc.t * ml_tactic_entry * 'a gen_tactic_arg list
  (* For syntax extensions *)
  | TacAlias of Loc.t * KerName.t * 'a gen_tactic_arg list

constraint 'a = <
    term:'t;
    dterm: 'dtrm;
    pattern:'p;
    constant:'c;
    reference:'r;
    name:'n;
    tacexpr:'tacexpr;
    level:'l
>

and 'a gen_tactic_fun_ast =
    Id.t option list * 'a gen_tactic_expr

constraint 'a = <
    term:'t;
    dterm: 'dtrm;
    pattern:'p;
    constant:'c;
    reference:'r;
    name:'n;
    tacexpr:'te;
    level:'l
>

(** Globalized tactics *)

type g_trm = glob_constr_and_expr
type g_pat = glob_constr_pattern_and_expr
type g_cst = evaluable_global_reference and_short_name or_var
type g_ref = ltac_constant located or_var
type g_nam  = Id.t located

type g_dispatch =  <
    term:g_trm;
    dterm:g_trm;
    pattern:g_pat;
    constant:g_cst;
    reference:g_ref;
    name:g_nam;
    tacexpr:glob_tactic_expr;
    level:glevel
>

and glob_tactic_expr =
    g_dispatch gen_tactic_expr

type glob_atomic_tactic_expr =
    g_dispatch gen_atomic_tactic_expr

type glob_tactic_arg =
    g_dispatch gen_tactic_arg

(** Raw tactics *)

type r_trm = constr_expr
type r_pat = constr_pattern_expr
type r_cst = reference or_by_notation
type r_ref = reference
type r_nam  = Id.t located
type r_lev = rlevel

type r_dispatch =  <
    term:r_trm;
    dterm:r_trm;
    pattern:r_pat;
    constant:r_cst;
    reference:r_ref;
    name:r_nam;
    tacexpr:raw_tactic_expr;
    level:rlevel
>

and raw_tactic_expr =
    r_dispatch gen_tactic_expr

type raw_atomic_tactic_expr =
    r_dispatch gen_atomic_tactic_expr

type raw_tactic_arg =
    r_dispatch gen_tactic_arg

(** Interpreted tactics *)

type t_trm = Term.constr
type t_pat = constr_pattern
type t_cst = evaluable_global_reference
type t_ref = ltac_constant located
type t_nam  = Id.t

type t_dispatch =  <
    term:t_trm;
    dterm:g_trm;
    pattern:t_pat;
    constant:t_cst;
    reference:t_ref;
    name:t_nam;
    tacexpr:unit;
    level:tlevel
>

type atomic_tactic_expr =
    t_dispatch gen_atomic_tactic_expr

(** Misc *)

type raw_red_expr = (r_trm, r_cst, r_pat) red_expr_gen
type glob_red_expr = (g_trm, g_cst, g_pat) red_expr_gen

(** Traces *)

type ltac_call_kind =
  | LtacMLCall of glob_tactic_expr
  | LtacNotationCall of KerName.t
  | LtacNameCall of ltac_constant
  | LtacAtomCall of glob_atomic_tactic_expr
  | LtacVarCall of Id.t * glob_tactic_expr
  | LtacConstrInterp of Glob_term.glob_constr * Pretyping.ltac_var_map

type ltac_trace = (Loc.t * ltac_call_kind) list
