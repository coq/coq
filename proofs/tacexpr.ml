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
open Decl_kinds

type 'a or_metaid = AI of 'a | MetaId of loc * string

type direction_flag = bool (* true = Left-to-right    false = right-to-right *)
type lazy_flag = bool      (* true = lazy             false = eager *)
type evars_flag = bool     (* true = pose evars       false = fail on evars *)
type rec_flag = bool       (* true = recursive        false = not recursive *)
type advanced_flag = bool  (* true = advanced         false = basic *)
type split_flag = bool     (* true = exists           false = split *)
type hidden_flag = bool    (* true = internal use     false = user-level *)
type letin_flag = bool     (* true = use local def    false = use Leibniz *)

type raw_red_flag =
  | FBeta
  | FIota
  | FZeta
  | FConst of reference or_by_notation list
  | FDeltaBut of reference or_by_notation list

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

type 'a raw_hyp_location = 'a with_occurrences * Termops.hyp_location_flag

type 'id move_location =
  | MoveAfter of 'id
  | MoveBefore of 'id
  | MoveToEnd of bool

let no_move = MoveToEnd true

open Pp

let pr_move_location pr_id = function
  | MoveAfter id -> brk(1,1) ++ str "after " ++ pr_id id
  | MoveBefore id -> brk(1,1) ++ str "before " ++ pr_id id
  | MoveToEnd toleft -> str (if toleft then " at bottom" else " at top")

type 'a induction_arg =
  | ElimOnConstr of 'a
  | ElimOnIdent of identifier located
  | ElimOnAnonHyp of int

type inversion_kind =
  | SimpleInversion
  | FullInversion
  | FullInversionClear

type ('c,'id) inversion_strength =
  | NonDepInversion of 
      inversion_kind * 'id list * intro_pattern_expr located option
  | DepInversion of
      inversion_kind * 'c option * intro_pattern_expr located option
  | InversionUsing of 'c * 'id list

type ('a,'b) location = HypLocation of 'a | ConclLocation of 'b

type 'id message_token =
  | MsgString of string
  | MsgInt of int
  | MsgIdent of 'id


type 'id gsimple_clause = ('id raw_hyp_location) option
(* onhyps:
     [None] means *on every hypothesis*
     [Some l] means on hypothesis belonging to l *)
type 'id gclause =
  { onhyps : 'id raw_hyp_location list option;
    concl_occs : bool * int or_var list }

let nowhere = {onhyps=Some[]; concl_occs=no_occurrences_expr}

let simple_clause_of = function
| { onhyps = Some [scl]; concl_occs = occs } when occs = no_occurrences_expr ->
      Some scl
| { onhyps = Some []; concl_occs = occs } when occs = all_occurrences_expr ->
    None
| _ ->
    error "not a simple clause (one hypothesis or conclusion)"

type ('constr,'id) induction_clause = 
    ('constr with_bindings induction_arg list * 'constr with_bindings option * 
     (intro_pattern_expr located option * intro_pattern_expr located option) *
     'id gclause option)

type multi = 
  | Precisely of int
  | UpTo of int
  | RepeatStar
  | RepeatPlus

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
  | TacIntroPattern of intro_pattern_expr located list
  | TacIntrosUntil of quantified_hypothesis
  | TacIntroMove of identifier option * 'id move_location
  | TacAssumption
  | TacExact of 'constr
  | TacExactNoCheck of 'constr
  | TacVmCastNoCheck of 'constr
  | TacApply of advanced_flag * evars_flag * 'constr with_bindings list
  | TacElim of evars_flag * 'constr with_bindings * 
      'constr with_bindings option
  | TacElimType of 'constr
  | TacCase of evars_flag * 'constr with_bindings
  | TacCaseType of 'constr
  | TacFix of identifier option * int
  | TacMutualFix of hidden_flag * identifier * int * (identifier * int * 
      'constr) list
  | TacCofix of identifier option
  | TacMutualCofix of hidden_flag * identifier * (identifier * 'constr) list
  | TacCut of 'constr
  | TacAssert of 'tac option * intro_pattern_expr located * 'constr
  | TacGeneralize of ('constr with_occurrences * name) list
  | TacGeneralizeDep of 'constr
  | TacLetTac of name * 'constr * 'id gclause * letin_flag

  (* Derived basic tactics *)
  | TacSimpleInductionDestruct of rec_flag * quantified_hypothesis
  | TacInductionDestruct of rec_flag * evars_flag * ('constr,'id) induction_clause list
  | TacDoubleInduction of quantified_hypothesis * quantified_hypothesis
  | TacDecomposeAnd of 'constr
  | TacDecomposeOr of 'constr
  | TacDecompose of 'ind list * 'constr
  | TacSpecialize of int option * 'constr with_bindings
  | TacLApply of 'constr

  (* Automation tactics *)
  | TacTrivial of 'constr list * string list option
  | TacAuto of int or_var option * 'constr list * string list option
  | TacAutoTDB of int option
  | TacDestructHyp of (bool * identifier located)
  | TacDestructConcl
  | TacSuperAuto of (int option * reference list * bool * bool)
  | TacDAuto of int or_var option * int option * 'constr list

  (* Context management *)
  | TacClear of bool * 'id list
  | TacClearBody of 'id list
  | TacMove of bool * 'id * 'id move_location
  | TacRename of ('id *'id) list
  | TacRevert of 'id list

  (* Constructors *)
  | TacLeft of evars_flag * 'constr bindings
  | TacRight of evars_flag * 'constr bindings
  | TacSplit of evars_flag * split_flag * 'constr bindings
  | TacAnyConstructor of evars_flag * 'tac option
  | TacConstructor of evars_flag * int or_metaid * 'constr bindings

  (* Conversion *)
  | TacReduce of ('constr,'cst) red_expr_gen * 'id gclause
  | TacChange of 'constr with_occurrences option * 'constr * 'id gclause

  (* Equivalence relations *)
  | TacReflexivity
  | TacSymmetry of 'id gclause
  | TacTransitivity of 'constr 

  (* Equality and inversion *)
  | TacRewrite of 
      evars_flag * (bool * multi * 'constr with_bindings) list * 'id gclause * 'tac option
  | TacInversion of ('constr,'id) inversion_strength * quantified_hypothesis
      
  (* For ML extensions *)
  | TacExtend of loc * string * 'constr generic_argument list

  (* For syntax extensions *)
  | TacAlias of loc * string *
      (identifier * 'constr generic_argument) list
      * (dir_path * glob_tactic_expr)

and ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr =
  | TacAtom of loc * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_atomic_tactic_expr
  | TacThen of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr * 
	('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr array *
	('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr *
	('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr array
  | TacThens of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr * 
	('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr list
  | TacFirst of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr list
  | TacComplete of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacSolve of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr list
  | TacTry of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacOrelse of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacDo of int or_var * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacRepeat of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacProgress of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacAbstract of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr * identifier option
  | TacId of 'id message_token list
  | TacFail of int or_var * 'id message_token list
  | TacInfo of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacLetIn of rec_flag * (identifier located * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_arg) list * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr
  | TacMatch of lazy_flag * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr * ('pat,('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr) match_rule list
  | TacMatchGoal of lazy_flag * direction_flag * ('pat,('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr) match_rule list
  | TacFun of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_fun_ast
  | TacArg of ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_arg

and ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_fun_ast =
  identifier option list * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_expr

  (* These are the possible arguments of a tactic definition *)
and ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_arg =
  | TacDynamic     of loc * Dyn.t
  | TacVoid
  | MetaIdArg      of loc * bool * string
  | ConstrMayEval  of ('constr,'cst) may_eval
  | IntroPattern   of intro_pattern_expr located
  | Reference      of 'ref
  | Integer        of int
  | TacCall        of loc *
      'ref * ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_arg list
  | TacExternal of loc * string * string * 
      ('constr,'pat,'cst,'ind,'ref,'id,'tac) gen_tactic_arg list
  | TacFreshId     of string or_var list
  | Tacexp of 'tac

(* Globalized tactics *)
and glob_tactic_expr =
    (rawconstr_and_expr,
     constr_pattern,
     evaluable_global_reference and_short_name or_var,
     inductive or_var,
     ltac_constant located or_var,
     identifier located,
     glob_tactic_expr) gen_tactic_expr

type raw_tactic_expr =
    (constr_expr,
     pattern_expr,
     reference or_by_notation,
     reference or_by_notation,
     reference,
     identifier located or_metaid,
     raw_tactic_expr) gen_tactic_expr

type raw_atomic_tactic_expr =
    (constr_expr,                  (* constr *)
     pattern_expr,                 (* pattern *)
     reference or_by_notation,     (* evaluable reference *)
     reference or_by_notation,     (* inductive *)
     reference,                    (* ltac reference *)
     identifier located or_metaid, (* identifier *)
     raw_tactic_expr) gen_atomic_tactic_expr

type raw_tactic_arg =
    (constr_expr,
     pattern_expr,
     reference or_by_notation,
     reference or_by_notation,
     reference,
     identifier located or_metaid,
     raw_tactic_expr) gen_tactic_arg

type raw_generic_argument = constr_expr generic_argument

type raw_red_expr = (constr_expr, reference or_by_notation) red_expr_gen

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
     ltac_constant located or_var,
     identifier located,
     glob_tactic_expr) gen_tactic_arg

type glob_generic_argument = rawconstr_and_expr generic_argument

type glob_red_expr =
    (rawconstr_and_expr, evaluable_global_reference or_var) red_expr_gen

type typed_generic_argument = Evd.open_constr generic_argument

type 'a raw_abstract_argument_type = ('a,rlevel) abstract_argument_type

type 'a glob_abstract_argument_type = ('a,glevel) abstract_argument_type

type 'a typed_abstract_argument_type = ('a,tlevel) abstract_argument_type

type declaration_hook = locality -> global_reference -> unit
