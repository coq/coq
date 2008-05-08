(************************************************************************)
(*  v      *   The Coq Proof Assistant                                  *)
(* <O___,, *                                                            *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *      GNU Lesser General Public License Version 2.1,        *)
(*         *      or (at your option) any later version.                *)
(************************************************************************)

(* Copyright © 2007, Lionel Elie Mamane <lionel@mamane.lu> *)

(* This is distributed in the hope that it will be useful,           *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of    *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details.                   *)

(* You should have received a copy of the GNU Lesser General Public    *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,          *)
(* MA  02110-1301, USA                                                 *)


(* LEM TODO: a .mli file *)

open Refiner
open Proof_type
open Rawterm
open Term
open Libnames
open Util
open Tacexpr
open Entries

(* DBG utilities, to be removed *)
let print_bool b = print_string (string_of_bool b)
let string_of_ppcmds p = Pp.pp_with Format.str_formatter p; Format.flush_str_formatter()
let acc_str f = List.fold_left (fun a b -> a ^ (f b) ^ "+") "O"
(* End utilities, to be removed *)

let explore_tree pfs =
  print_string "explore_tree called\n";
  print_string "pfs is a top: ";
  (* We expect yes. *)
  print_string (if (is_top_pftreestate pfs) then "yes" else "no");
  print_newline();
  let rec explain_tree (pt:proof_tree) =
    match pt.ref with
      | None -> "none"
      | Some (Prim p, l) -> "<Prim (" ^ (explain_prim p) ^ ") | " ^ (acc_str explain_tree l) ^ ">"
      | Some (Nested (t,p), l) -> "<Nested (" ^ explain_compound t ^ ", " ^ (explain_tree p) ^ ") | " ^ (acc_str explain_tree l) ^ ">"
      | Some (Decl_proof _, _) -> "Decl_proof"
      | Some (Daimon, _) -> "Daimon"
  and explain_compound cr =
    match cr with
      | Tactic (texp, b) -> "Tactic (" ^ (string_of_ppcmds (Tactic_printer.pr_tactic texp)) ^ ", " ^ (string_of_bool b) ^ ")"
      | Proof_instr (b, instr) -> "Proof_instr (" ^ (string_of_bool b) ^ (string_of_ppcmds (Tactic_printer.pr_proof_instr instr)) ^ ")"
  and explain_prim = function
    | Refine c -> "Refine " ^ (string_of_ppcmds (Printer.prterm c))
    | Intro identifier -> "Intro"
    | Intro_replacing identifier -> "Intro_replacing"
    | Cut (bool, identifier, types) -> "Cut"
    | FixRule (identifier, int, l) -> "FixRule"
    | Cofix (identifier, l) -> "Cofix"
    | Convert_concl (types, cast_kind) -> "Convert_concl"
    | Convert_hyp named_declaration -> "Convert_hyp"
    | Thin identifier_list -> "Thin"
    | ThinBody identifier_list -> "ThinBody"
    | Move (bool, identifier, identifier') -> "Move"
    | Rename (identifier, identifier') -> "Rename"
    | Change_evars -> "Change_evars"
  in
  let pt = proof_of_pftreestate pfs in
    (* We expect 0 *)
    print_string "Number of open subgoals: ";
    print_int pt.open_subgoals;
    print_newline();
    print_string "First rule is a ";
    print_string (explain_tree pt);
    print_newline()


let o f g x = f (g x)
let fst_of_3 (x, _, _) = x
let snd_of_3 (_, x, _) = x
let trd_of_3 (_, _, x) = x

(* TODO: These for now return a Libnames.global_reference, but a
   prooftree will also depend on things like tactic declarations, etc
   so we may need a new type for that. *)
let rec depends_of_hole_kind hk acc = match hk with
  | Evd.ImplicitArg (gr,_)            -> gr::acc
  | Evd.TomatchTypeParameter (ind, _) -> (IndRef ind)::acc
  | Evd.BinderType _
  | Evd.QuestionMark _
  | Evd.CasesType
  | Evd.InternalHole
  | Evd.GoalEvar
  | Evd.ImpossibleCase  -> acc

let depends_of_'a_cast_type depends_of_'a act acc = match act with
  | CastConv (ck, a) -> depends_of_'a a acc
  | CastCoerce       -> acc

let depends_of_'a_bindings depends_of_'a ab acc = match ab with
  | ImplicitBindings al  -> list_union_map depends_of_'a al acc
  | ExplicitBindings apl -> list_union_map (fun x y -> depends_of_'a (trd_of_3 x) y) apl acc
  | NoBindings -> acc

let depends_of_'a_with_bindings depends_of_'a (a, ab) acc =
  depends_of_'a a (depends_of_'a_bindings depends_of_'a ab acc)

(* let depends_of_constr_with_bindings = depends_of_'a_with_bindings depends_of_constr *)
(* and depends_of_open_constr_with_bindings = depends_of_'a_with_bindings depends_of_open_let *)

let depends_of_'a_induction_arg depends_of_'a aia acc = match aia with
  | ElimOnConstr a -> depends_of_'a a acc
  | ElimOnIdent _ ->
      (* TODO: Check that this really refers only to an hypothesis (not a section variable, etc.)
       * It *seems* thaat section variables are seen as hypotheses, so we have a problem :-(

       * Plan: Load all section variables before anything in that
       * section and call the user's proof script "brittle" and refuse
       * to handle if it breaks because of that
       *)
      acc
  | ElimOnAnonHyp _ -> acc

let depends_of_'a_or_var depends_of_'a aov acc = match aov with
  | ArgArg a -> depends_of_'a a acc
  | ArgVar _ -> acc

let depends_of_'a_with_occurences depends_of_'a (_,a) acc =
  depends_of_'a a acc

let depends_of_'a_'b_red_expr_gen depends_of_'a reg acc = match reg with
  (* TODO: dirty assumption that the 'b doesn't make any dependency *)
  | Red _
  | Hnf
  | Cbv _
  | Lazy _
  | Unfold _
  | ExtraRedExpr _
  | CbvVm           -> acc
  | Simpl awoo ->
      Option.fold_right
	(depends_of_'a_with_occurences depends_of_'a)
	awoo
	acc
  | Fold al -> list_union_map depends_of_'a al acc
  | Pattern awol ->
      list_union_map
	(depends_of_'a_with_occurences depends_of_'a)
	awol
	acc

let depends_of_'a_'b_inversion_strength depends_of_'a is acc = match is with
  (* TODO: dirty assumption that the 'b doesn't make any dependency *)
  | NonDepInversion _       -> acc
  | DepInversion (_, ao, _) -> Option.fold_right depends_of_'a ao acc
  | InversionUsing (a, _)   -> depends_of_'a a acc

let depends_of_'a_pexistential depends_of_'a (_, aa) acc = array_union_map depends_of_'a aa acc

let depends_of_named_vals nvs acc =
  (* TODO: I'm stopping here because I have noooo idea what to do with values... *)
  acc

let depends_of_inductive ind acc = (IndRef ind)::acc

let rec depends_of_constr c acc = match kind_of_term c with
  | Rel       _                -> acc
  | Var       id               -> (VarRef id)::acc
  | Meta      _                -> acc
  | Evar      ev               -> depends_of_'a_pexistential depends_of_constr ev acc
  | Sort      _                -> acc
  | Cast      (c, _, t)        -> depends_of_constr c (depends_of_constr t acc)
  | Prod      (_, t, t')       -> depends_of_constr t (depends_of_constr t' acc)
  | Lambda    (_, t, c)        -> depends_of_constr t (depends_of_constr c acc)
  | LetIn     (_, c, t, c')    -> depends_of_constr c (depends_of_constr t (depends_of_constr c' acc))
  | App       (c, ca)          -> depends_of_constr c (array_union_map depends_of_constr ca acc)
  | Const     cnst             -> (ConstRef cnst)::acc
  | Ind       ind              -> (IndRef ind)::acc
  | Construct cons             -> (ConstructRef cons)::acc
  | Case      (_, c, c', ca)   -> depends_of_constr c (depends_of_constr c' (array_union_map depends_of_constr ca acc))
  | Fix       (_, (_, ta, ca))
  | CoFix     (_, (_, ta, ca)) -> array_union_map depends_of_constr ca (array_union_map depends_of_constr ta acc)
and depends_of_evar_map evm acc =
  Evd.fold (fun ev evi -> depends_of_evar_info evi) evm acc
and depends_of_evar_info evi acc =
  (* TODO: evi.evar_extra contains a dynamic... Figure out what to do with it. *)
  depends_of_constr evi.Evd.evar_concl (depends_of_evar_body evi.Evd.evar_body (depends_of_named_context_val evi.Evd.evar_hyps acc))
and depends_of_evar_body evb acc = match evb with
  | Evd.Evar_empty -> acc
  | Evd.Evar_defined c -> depends_of_constr c acc
and depends_of_named_context nc acc = list_union_map depends_of_named_declaration nc acc
and depends_of_named_context_val ncv acc =
  depends_of_named_context (Environ.named_context_of_val ncv) (depends_of_named_vals (Environ.named_vals_of_val ncv) acc)
and depends_of_named_declaration (_,co,t) acc = depends_of_constr t (Option.fold_right depends_of_constr co acc)



let depends_of_open_constr (evm,c) acc =
  depends_of_constr c (depends_of_evar_map evm acc)

let rec depends_of_rawconstr rc acc = match rc with
  | RRef (_,r)         -> r::acc
  | RVar (_, id)       -> (VarRef id)::acc
  | REvar (_, _, rclo) -> Option.fold_right depends_of_rawconstr_list rclo acc
  | RPatVar _          -> acc
  | RApp (_, rc, rcl)  -> depends_of_rawconstr rc (depends_of_rawconstr_list rcl acc)
  | RLambda (_, _, _, rct, rcb)
  | RProd   (_, _, _, rct, rcb)
  | RLetIn  (_, _, rct, rcb) -> depends_of_rawconstr rcb (depends_of_rawconstr rct acc)
  | RCases  (_, _, rco, tmt, cc) ->
      (* LEM TODO: handle the cc *)
      (Option.fold_right depends_of_rawconstr rco
         (list_union_map
	    (fun (rc, pp) acc ->
	       Option.fold_right (fun (_,ind,_,_) acc -> (IndRef ind)::acc) (snd pp)
	       (depends_of_rawconstr rc acc))
	    tmt
	    acc))
  | RLetTuple (_,_,(_,rco),rc0,rc1) ->
     depends_of_rawconstr rc1 (depends_of_rawconstr rc0 (Option.fold_right depends_of_rawconstr rco acc))
  | RIf (_, rcC, (_, rco), rcT, rcF) -> let dorc = depends_of_rawconstr in
      dorc rcF (dorc rcT (dorc rcF (dorc rcC (Option.fold_right dorc rco acc))))
  | RRec (_, _, _, rdla, rca0, rca1) -> let dorca = array_union_map depends_of_rawconstr in
      dorca rca0 (dorca rca1 (array_union_map
				(list_union_map (fun (_,_,rco,rc) acc -> depends_of_rawconstr rc (Option.fold_right depends_of_rawconstr rco acc)))
				rdla
				acc))
  | RSort _ -> acc
  | RHole (_, hk) -> depends_of_hole_kind hk acc
  | RCast (_, rc, rcct) -> depends_of_rawconstr rc (depends_of_'a_cast_type depends_of_rawconstr rcct acc)
  | RDynamic (_, dyn) -> failwith "Depends of a dyn not implemented yet" (* TODO: figure out how these dyns are used*)
and depends_of_rawconstr_list l = list_union_map depends_of_rawconstr l

let depends_of_rawconstr_and_expr (rc, _) acc =
  (* TODO Le constr_expr représente le même terme que le rawconstr. Vérifier ça. *)
  depends_of_rawconstr rc acc

let rec depends_of_gen_tactic_expr depends_of_'constr depends_of_'ind depends_of_'tac =
  (* TODO:
   * Dirty assumptions that the 'id, 'cst, 'ref don't generate dependencies
   *)
  let rec depends_of_tacexpr texp acc = match texp with
    | TacAtom (_, atexpr) -> depends_of_atomic_tacexpr atexpr acc
    | TacThen (tac0, taca0, tac1, taca1) ->
	depends_of_tacexpr tac0 (array_union_map depends_of_tacexpr taca0 (depends_of_tacexpr tac1 (array_union_map depends_of_tacexpr taca1 acc)))
    | TacThens (tac, tacl) ->
	depends_of_tacexpr tac (list_union_map depends_of_tacexpr tacl acc)
    | TacFirst tacl -> list_union_map depends_of_tacexpr tacl acc
    | TacComplete tac -> depends_of_tacexpr tac acc
    | TacSolve tacl -> list_union_map depends_of_tacexpr tacl acc
    | TacTry tac -> depends_of_tacexpr tac acc
    | TacOrelse (tac0, tac1) -> depends_of_tacexpr tac0 (depends_of_tacexpr tac1 acc)
    | TacDo (_, tac) -> depends_of_tacexpr tac acc
    | TacRepeat tac -> depends_of_tacexpr tac acc
    | TacProgress tac -> depends_of_tacexpr tac acc
    | TacAbstract (tac, _) -> depends_of_tacexpr tac acc
    | TacId _
    | TacFail _ -> acc
    | TacInfo tac -> depends_of_tacexpr tac acc
    | TacLetIn (_, igtal, tac) ->
	depends_of_tacexpr
	  tac
	  (list_union_map
	     (fun x y -> depends_of_tac_arg (snd x) y)
	     igtal
	     acc)
    | TacMatch (_, tac, tacexpr_mrl) -> failwith "depends_of_tacexpr of a Match not implemented yet"
    | TacMatchContext (_, _, tacexpr_mrl) -> failwith "depends_of_tacexpr of a Match Context not implemented yet"
    | TacFun tacfa -> depends_of_tac_fun_ast tacfa acc
    | TacArg tacarg -> depends_of_tac_arg tacarg acc
  and depends_of_atomic_tacexpr atexpr acc = let depends_of_'constr_with_bindings = depends_of_'a_with_bindings depends_of_'constr in match atexpr with
      (* Basic tactics *)
    | TacIntroPattern _
    | TacIntrosUntil _
    | TacIntroMove _
    | TacAssumption  -> acc
    | TacExact          c
    | TacExactNoCheck   c
    | TacVmCastNoCheck  c  -> depends_of_'constr c acc
    | TacApply (_, _, cb) -> depends_of_'constr_with_bindings cb acc
    | TacElim (_, cwb, cwbo) ->
	depends_of_'constr_with_bindings cwb
	  (Option.fold_right depends_of_'constr_with_bindings cwbo acc)
    | TacElimType c -> depends_of_'constr c acc
    | TacCase (_, cb) -> depends_of_'constr_with_bindings cb acc
    | TacCaseType c -> depends_of_'constr c acc
    | TacFix _
    | TacMutualFix _
    | TacCofix _
    | TacMutualCofix _ -> failwith "depends_of_atomic_tacexpr of a Tac(Mutual)(Co)Fix not implemented yet"
    | TacCut c -> depends_of_'constr c acc
    | TacAssert (taco, _, c) ->
	Option.fold_right depends_of_'tac taco (depends_of_'constr c acc)
    | TacGeneralize cl -> list_union_map depends_of_'constr cl acc
    | TacGeneralizeDep c -> depends_of_'constr c acc
    | TacLetTac (_,c,_) -> depends_of_'constr c acc

    (* Derived basic tactics *)
    | TacSimpleInduction _
    | TacSimpleDestruct  _
    | TacDoubleInduction _ -> acc
    | TacNewInduction (_, cwbial, cwbo, _)
    | TacNewDestruct (_, cwbial, cwbo, _) ->
	list_union_map (depends_of_'a_induction_arg depends_of_'constr_with_bindings)
	  cwbial
	  (Option.fold_right depends_of_'constr_with_bindings cwbo acc)
    | TacDecomposeAnd c
    | TacDecomposeOr  c -> depends_of_'constr c acc
    | TacDecompose (il, c) -> depends_of_'constr c (list_union_map depends_of_'ind il acc)
    | TacSpecialize (_,cwb) -> depends_of_'constr_with_bindings cwb acc
    | TacLApply c -> depends_of_'constr c acc

    (* Automation tactics *)
    | TacTrivial (cl, bs) -> 
	(* TODO: Maybe make use of bs: list of hint bases to be used. *)
	list_union_map depends_of_'constr cl acc
    | TacAuto (_, cs, bs) ->
	(* TODO: Maybe make use of bs: list of hint bases to be used.
           None -> all ("with *")
           Some list -> a list, "core" added implicitly *)
	list_union_map depends_of_'constr cs acc
    | TacAutoTDB _     -> acc
    | TacDestructHyp _ -> acc
    | TacDestructConcl -> acc
    | TacSuperAuto _ -> (* TODO: this reference thing is scary*)
	acc
    | TacDAuto     _ -> acc

    (* Context management *)
    | TacClear     _
    | TacClearBody _
    | TacMove      _
    | TacRename    _ 
    | TacRevert    _ -> acc

    (* Constructors *)
    | TacLeft        (_,cb)
    | TacRight       (_,cb)
    | TacSplit       (_, _, cb)
    | TacConstructor (_, _, cb) -> depends_of_'a_bindings depends_of_'constr cb acc
    | TacAnyConstructor (_,taco) -> Option.fold_right depends_of_'tac taco acc

    (* Conversion *)
    | TacReduce  (reg,_) ->
	depends_of_'a_'b_red_expr_gen depends_of_'constr reg acc
    | TacChange (cwoo, c, _) ->
	depends_of_'constr
	  c
	  (Option.fold_right (depends_of_'a_with_occurences depends_of_'constr) cwoo acc)

    (* Equivalence relations *)
    | TacReflexivity
    | TacSymmetry     _ -> acc
    | TacTransitivity c -> depends_of_'constr c acc

    (* Equality and inversion *)
    | TacRewrite (_,cbl,_,_) -> list_union_map (o depends_of_'constr_with_bindings (fun (_,_,x)->x)) cbl acc
    | TacInversion (is, _)  -> depends_of_'a_'b_inversion_strength depends_of_'constr is acc

    (* For ML extensions *)
    | TacExtend (_, _, cgal) -> failwith "depends of TacExtend not implemented because depends of a generic_argument not implemented"

    (* For syntax extensions *)
    | TacAlias (_,_,gal,(_,gte)) -> failwith "depends of a TacAlias not implemented because depends of a generic_argument not implemented"
  and depends_of_tac_fun_ast tfa acc = failwith "depend_of_tac_fun_ast not implemented yet"
  and depends_of_tac_arg ta acc = match ta with
    | TacDynamic (_,d)  -> failwith "Don't know what to do with a Dyn in tac_arg"
    | TacVoid           -> acc
    | MetaIdArg  _      -> failwith "Don't know what to do with a MetaIdArg in tac_arg"
    | ConstrMayEval  me -> failwith "TODO: depends_of_tac_arg of a ConstrMayEval"
    | IntroPattern   _  -> acc
    | Reference     ltc -> acc (* TODO: This assumes the "ltac constant" cannot somehow refer to a named object... *)
    | Integer       _   -> acc
    | TacCall (_,ltc,l) -> (* TODO: This assumes the "ltac constant" cannot somehow refer to a named object... *)
	list_union_map depends_of_tac_arg l acc
    | TacExternal (_,_,_,l) -> list_union_map depends_of_tac_arg l acc
    | TacFreshId     _  -> acc
    | Tacexp       tac  ->
	depends_of_'tac tac acc
  in
    depends_of_tacexpr

let rec depends_of_glob_tactic_expr (gte:glob_tactic_expr) acc =
  depends_of_gen_tactic_expr
    depends_of_rawconstr_and_expr
    (depends_of_'a_or_var depends_of_inductive)
    depends_of_glob_tactic_expr
    gte
    acc

let rec depends_of_tacexpr te acc =
  depends_of_gen_tactic_expr
    depends_of_open_constr
    depends_of_inductive
    depends_of_glob_tactic_expr
    te
    acc

let depends_of_compound_rule cr acc = match cr with
  | Tactic (texp, _) -> depends_of_tacexpr texp acc
  | Proof_instr (b, instr) ->
      (* TODO: What is the boolean b? Should check. *)
      failwith "Dependency calculation of Proof_instr not implemented yet"
and depends_of_prim_rule pr acc = match pr with
  | Refine c                     -> depends_of_constr c acc
  | Intro id                     -> acc
  | Intro_replacing id           -> acc
  | Cut (_, _, t)                -> depends_of_constr t acc (* TODO: check what 2nd argument contains *)
  | FixRule (_, _, l)            -> list_union_map (o depends_of_constr trd_of_3) l acc (* TODO: check what the arguments contain *)
  | Cofix (_, l)                 -> list_union_map (o depends_of_constr snd) l acc (* TODO: check what the arguments contain *)
  | Convert_concl (t, _)         -> depends_of_constr t acc
  | Convert_hyp (_, None, t)     -> depends_of_constr t acc
  | Convert_hyp (_, (Some c), t) -> depends_of_constr c (depends_of_constr t acc)
  | Thin _                       -> acc
  | ThinBody _                   -> acc
  | Move _                       -> acc
  | Rename _                     -> acc
  | Change_evars                 -> acc

let rec depends_of_pftree pt acc =
  match pt.ref with
    | None -> acc
    | Some (Prim   pr    , l) -> depends_of_prim_rule pr (list_union_map depends_of_pftree l  acc)
    | Some (Nested (t, p), l) -> depends_of_compound_rule t (depends_of_pftree p (list_union_map depends_of_pftree l acc))
    | Some (Decl_proof _ , l) -> list_union_map depends_of_pftree l acc
    | Some (Daimon,        l) -> list_union_map depends_of_pftree l acc

let rec depends_of_pftree_head pt acc =
  match pt.ref with
    | None -> acc
    | Some (Prim   pr    , l) -> depends_of_prim_rule pr acc
    | Some (Nested (t, p), l) -> depends_of_compound_rule t (depends_of_pftree p acc)
    | Some (Decl_proof _ , l) -> acc
    | Some (Daimon,        l) -> acc

let depends_of_pftreestate depends_of_pftree pfs =
(*   print_string "depends_of_pftreestate called\n"; *)
(*   explore_tree pfs; *)
  let pt = proof_of_pftreestate pfs in
    assert (is_top_pftreestate pfs);
    assert (pt.open_subgoals = 0);
    depends_of_pftree pt []

let depends_of_definition_entry de ~acc =
  Option.fold_right
    depends_of_constr
    de.const_entry_type
    (depends_of_constr de.const_entry_body acc)
