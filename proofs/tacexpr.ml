(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Names
open Topconstr
open Libnames
open Nametab
open Rawterm
open Util
open Genarg
open Pattern

type 'a or_metaid = AI of 'a | MetaId of loc * string

type direction_flag = bool (* true = Left-to-right    false = right-to-right *)

type raw_red_flag =
  | FBeta
  | FIota
  | FZeta
  | FConst of reference list
  | FDeltaBut of reference list

let make_red_flag =
  let rec add_flag red = function
    | [] -> red
    | FBeta :: lf -> add_flag { red with rBeta = true } lf
    | FIota :: lf -> add_flag { red with rIota = true } lf
    | FZeta :: lf -> add_flag { red with rZeta = true } lf
    | FConst l :: lf ->
	if red.rDelta then
	  error
	    "Cannot set both constants to unfold and constants not to unfold";
        add_flag { red with rConst = list_union red.rConst l } lf
    | FDeltaBut l :: lf ->
	if red.rConst <> [] & not red.rDelta then
	  error
	    "Cannot set both constants to unfold and constants not to unfold";
        add_flag 
	  { red with rConst = list_union red.rConst l; rDelta = true }
	  lf
  in
  add_flag
    {rBeta = false; rIota = false; rZeta = false; rDelta = false; rConst = []} 

type hyp_location_flag = (* To distinguish body and type of local defs *)
  | InHyp
  | InHypTypeOnly
  | InHypValueOnly

type 'a raw_hyp_location = 
    'a * int list * (hyp_location_flag * hyp_location_flag option ref)

type 'a induction_arg =
  | ElimOnConstr of 'a
  | ElimOnIdent of identifier located
  | ElimOnAnonHyp of int

type inversion_kind =
  | SimpleInversion
  | FullInversion
  | FullInversionClear

type ('c,'id) inversion_strength =
  | NonDepInversion of inversion_kind * 'id list * intro_pattern_expr option
  | DepInversion of inversion_kind * 'c option * intro_pattern_expr option
  | InversionUsing of 'c * 'id list

type ('a,'b) location = HypLocation of 'a | ConclLocation of 'b

type 'id gsimple_clause = ('id raw_hyp_location) option
(* onhyps:
     [None] means *on every hypothesis*
     [Some l] means on hypothesis belonging to l *)
type 'id gclause =
  { onhyps : 'id raw_hyp_location list option;
    onconcl : bool;
    concl_occs :int list }

let simple_clause_of = function
    { onhyps = Some[scl]; onconcl = false } -> Some scl
  | { onhyps = Some []; onconcl = true; concl_occs=[] } -> None
  | _ -> error "not a simple clause (one hypothesis or conclusion)"

type pattern_expr = constr_expr

(* Type of patterns *)
type 'a match_pattern =
  | Term of 'a
  | Subterm of identifier option * 'a

(* Type of hypotheses for a Match Context rule *)
type 'a match_context_hyps =
  | Hyp of name located * 'a match_pattern

(* Type of a Match rule for Match Context and Match *)
type ('a,'t) match_rule =
  | Pat of 'a match_context_hyps list * 'a match_pattern * 't
  | All of 't

type ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_atomic_tactic_expr =
  (* Basic tactics *)
  | TacIntroPattern of intro_pattern_expr list
  | TacIntrosUntil of quantified_hypothesis
  | TacIntroMove of identifier option * identifier located option
  | TacAssumption
  | TacExact of 'constr
  | TacApply of 'constr with_bindings
  | TacElim of 'constr with_bindings * 'constr with_bindings option
  | TacElimType of 'constr
  | TacCase of 'constr with_bindings
  | TacCaseType of 'constr
  | TacFix of identifier option * int
  | TacMutualFix of identifier * int * (identifier * int * 'constr) list
  | TacCofix of identifier option
  | TacMutualCofix of identifier * (identifier * 'constr) list
  | TacCut of 'constr
  | TacTrueCut of name * 'constr 
  | TacForward of bool * name * 'constr
  | TacGeneralize of 'constr list
  | TacGeneralizeDep of 'constr
  | TacLetTac of name * 'constr * 'id gclause
  | TacInstantiate of int * 'constr * 'id gclause

  (* Derived basic tactics *)
  | TacSimpleInduction of (quantified_hypothesis * (bool ref * intro_pattern_expr list ref list) list ref)
  | TacNewInduction of 'constr induction_arg * 'constr with_bindings option
      * (intro_pattern_expr option * (bool ref * intro_pattern_expr list ref list) list ref)
  | TacSimpleDestruct of quantified_hypothesis
  | TacNewDestruct of 'constr induction_arg * 'constr with_bindings option
      * (intro_pattern_expr option * (bool ref * intro_pattern_expr list ref list) list ref)

  | TacDoubleInduction of quantified_hypothesis * quantified_hypothesis
  | TacDecomposeAnd of 'constr
  | TacDecomposeOr of 'constr
  | TacDecompose of 'ind list * 'constr
  | TacSpecialize of int option * 'constr with_bindings
  | TacLApply of 'constr

  (* Automation tactics *)
  | TacTrivial of string list option
  | TacAuto of int or_var option * string list option
  | TacAutoTDB of int option
  | TacDestructHyp of (bool * identifier located)
  | TacDestructConcl
  | TacSuperAuto of (int option * reference list * bool * bool)
  | TacDAuto of int or_var option * int option

  (* Context management *)
  | TacClear of 'id list
  | TacClearBody of 'id list
  | TacMove of bool * 'id * 'id
  | TacRename of 'id * 'id

  (* Constructors *)
  | TacLeft of 'constr bindings
  | TacRight of 'constr bindings
  | TacSplit of bool * 'constr bindings
  | TacAnyConstructor of 'tac option
  | TacConstructor of int or_metaid * 'constr bindings

  (* Conversion *)
  | TacReduce of ('constr,'cst) red_expr_gen * 'id gclause
  | TacChange of
      'constr occurrences option * 'constr * 'id gclause

  (* Equivalence relations *)
  | TacReflexivity
  | TacSymmetry of 'id gclause
  | TacTransitivity of 'constr 

  (* Equality and inversion *)
  | TacInversion of ('constr,'id) inversion_strength * quantified_hypothesis
      
  (* For ML extensions *)
  | TacExtend of loc * string * ('constr,'tac) generic_argument list

  (* For syntax extensions *)
  | TacAlias of loc * string *
      (identifier * ('constr,'tac) generic_argument) list
      * (dir_path * 'tac)

and ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr =
  | TacAtom of loc * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_atomic_tactic_expr
  | TacThen of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacThens of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr list
  | TacFirst of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr list
  | TacSolve of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr list
  | TacTry of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacOrelse of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacDo of int or_var * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacRepeat of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacProgress of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacAbstract of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr * identifier option
  | TacId of string
  | TacFail of int or_var * string
  | TacInfo of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr

  | TacLetRecIn of (identifier located * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_fun_ast) list * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacLetIn of (identifier located * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr option * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_arg) list * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacMatch of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr * ('pat,('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr) match_rule list
  | TacMatchContext of direction_flag * ('pat,('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr) match_rule list
  | TacFun of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_fun_ast
  | TacArg of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_arg

and ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_fun_ast =
  identifier option list * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr

  (* These are possible arguments of a tactic definition *)
and ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_arg =
  | TacDynamic     of loc * Dyn.t
  | TacVoid
  | MetaIdArg      of loc * string
  | ConstrMayEval  of ('constr,'cst) may_eval
  | IntroPattern   of intro_pattern_expr
  | Reference      of 'ref
  | Integer        of int
  | TacCall        of loc *
      'ref * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_arg list
  | TacFreshId     of string option
  | Tacexp of 'tac

type raw_tactic_expr =
    (constr_expr,
     pattern_expr,
     reference,
     reference,
     reference,
     identifier located or_metaid,
     raw_tactic_expr) gen_tactic_expr

type raw_atomic_tactic_expr =
    (constr_expr,                  (* constr *)
     pattern_expr,                 (* pattern *)
     reference,                    (* evaluable reference *)
     reference,                    (* inductive *)
     reference,                    (* ltac reference *)
     identifier located or_metaid, (* identifier *)
     raw_tactic_expr) gen_atomic_tactic_expr

type raw_tactic_arg =
    (constr_expr,
     pattern_expr,
     reference,
     reference,
     reference,
     identifier located or_metaid,
     raw_tactic_expr) gen_tactic_arg

type raw_generic_argument =
    (constr_expr,raw_tactic_expr) generic_argument

type raw_red_expr = (constr_expr, reference) red_expr_gen

(* Globalized tactics *)
type glob_tactic_expr =
    (rawconstr_and_expr,
     constr_pattern,
     evaluable_global_reference and_short_name or_var,
     inductive or_var,
     ltac_constant located or_var,
     identifier located,
     glob_tactic_expr) gen_tactic_expr

type glob_atomic_tactic_expr =
    (rawconstr_and_expr,
     constr_pattern,
     evaluable_global_reference and_short_name or_var,
     inductive or_var,
     ltac_constant located or_var,
     identifier located,
     glob_tactic_expr) gen_atomic_tactic_expr

type glob_tactic_arg =
    (rawconstr_and_expr,
     constr_pattern,
     evaluable_global_reference and_short_name or_var,
     inductive or_var,
     ltac_constant located,
     identifier located or_var,
     glob_tactic_expr) gen_tactic_arg

type glob_generic_argument =
    (rawconstr_and_expr,glob_tactic_expr) generic_argument

type glob_red_expr =
    (rawconstr_and_expr, evaluable_global_reference or_var) red_expr_gen

type closed_raw_generic_argument =
    (constr_expr,raw_tactic_expr) generic_argument

type 'a raw_abstract_argument_type =
    ('a,constr_expr,raw_tactic_expr) abstract_argument_type

type 'a glob_abstract_argument_type =
    ('a,rawconstr_and_expr,glob_tactic_expr) abstract_argument_type

type open_generic_argument =
    (Term.constr,glob_tactic_expr) generic_argument

type closed_generic_argument =
    (Term.constr,glob_tactic_expr) generic_argument

type 'a closed_abstract_argument_type =
    ('a,Term.constr,glob_tactic_expr) abstract_argument_type

type declaration_hook = Decl_kinds.strength -> global_reference -> unit
