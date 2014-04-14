(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Tacexpr
open Mod_subst
open Genarg
open Constrarg
open Misctypes
open Globnames
open Term
open Genredexpr
open Inductiveops
open Patternops
open Pretyping

(** Substitution of tactics at module closing time *)

(** For generic arguments, we declare and store substitutions
    in a table *)

let subst_quantified_hypothesis _ x = x

let subst_declared_or_quantified_hypothesis _ x = x

let subst_glob_constr_and_expr subst (c,e) =
  assert (Option.is_empty e); (* e<>None only for toplevel tactics *)
  (Detyping.subst_glob_constr subst c,None)

let subst_glob_constr = subst_glob_constr_and_expr (* shortening *)

let subst_binding subst (loc,b,c) =
  (loc,subst_quantified_hypothesis subst b,subst_glob_constr subst c)

let subst_bindings subst = function
  | NoBindings -> NoBindings
  | ImplicitBindings l -> ImplicitBindings (List.map (subst_glob_constr subst) l)
  | ExplicitBindings l -> ExplicitBindings (List.map (subst_binding subst) l)

let subst_glob_with_bindings subst (c,bl) =
  (subst_glob_constr subst c, subst_bindings subst bl)

let subst_induction_arg subst = function
  | ElimOnConstr c -> ElimOnConstr (subst_glob_with_bindings subst c)
  | ElimOnAnonHyp n as x -> x
  | ElimOnIdent id as x -> x

let subst_and_short_name f (c,n) =
(*  assert (n=None); *)(* since tacdef are strictly globalized *)
  (f c,None)

let subst_or_var f =  function
  | ArgVar _ as x -> x
  | ArgArg x -> ArgArg (f x)

let dloc = Loc.ghost

let subst_located f (_loc,id) = (dloc,f id)

let subst_reference subst =
  subst_or_var (subst_located (subst_kn subst))

(*CSC: subst_global_reference is used "only" for RefArgType, that propagates
  to the syntactic non-terminals "global", used in commands such as
  Print. It is also used for non-evaluable references. *)
open Pp
open Printer

let subst_global_reference subst =
 let subst_global ref =
  let ref',t' = subst_global subst ref in
   if not (eq_constr (constr_of_global ref') t') then
    msg_warning (strbrk "The reference " ++ pr_global ref ++ str " is not " ++
          str " expanded to \"" ++ pr_lconstr t' ++ str "\", but to " ++
          pr_global ref') ;
   ref'
 in
  subst_or_var (subst_located subst_global)

let subst_evaluable subst =
  let subst_eval_ref = subst_evaluable_reference subst in
    subst_or_var (subst_and_short_name subst_eval_ref)

let subst_unfold subst (l,e) =
  (l,subst_evaluable subst e)

let subst_flag subst red =
  { red with rConst = List.map (subst_evaluable subst) red.rConst }

let subst_constr_with_occurrences subst (l,c) = (l,subst_glob_constr subst c)

let subst_glob_constr_or_pattern subst (c,p) =
  (subst_glob_constr subst c,subst_pattern subst p)

let subst_pattern_with_occurrences subst (l,p) =
  (l,subst_glob_constr_or_pattern subst p)

let subst_redexp subst = function
  | Unfold l -> Unfold (List.map (subst_unfold subst) l)
  | Fold l -> Fold (List.map (subst_glob_constr subst) l)
  | Cbv f -> Cbv (subst_flag subst f)
  | Cbn f -> Cbn (subst_flag subst f)
  | Lazy f -> Lazy (subst_flag subst f)
  | Pattern l -> Pattern (List.map (subst_constr_with_occurrences subst) l)
  | Simpl o -> Simpl (Option.map (subst_pattern_with_occurrences subst) o)
  | CbvVm o -> CbvVm (Option.map (subst_pattern_with_occurrences subst) o)
  | CbvNative o -> CbvNative (Option.map (subst_pattern_with_occurrences subst) o)
  | (Red _ | Hnf | ExtraRedExpr _ as r) -> r

let subst_raw_may_eval subst = function
  | ConstrEval (r,c) -> ConstrEval (subst_redexp subst r,subst_glob_constr subst c)
  | ConstrContext (locid,c) -> ConstrContext (locid,subst_glob_constr subst c)
  | ConstrTypeOf c -> ConstrTypeOf (subst_glob_constr subst c)
  | ConstrTerm c -> ConstrTerm (subst_glob_constr subst c)

let subst_match_pattern subst = function
  | Subterm (b,ido,pc) -> Subterm (b,ido,(subst_glob_constr_or_pattern subst pc))
  | Term pc -> Term (subst_glob_constr_or_pattern subst pc)

let rec subst_match_goal_hyps subst = function
  | Hyp (locs,mp) :: tl ->
      Hyp (locs,subst_match_pattern subst mp)
      :: subst_match_goal_hyps subst tl
  | Def (locs,mv,mp) :: tl ->
      Def (locs,subst_match_pattern subst mv, subst_match_pattern subst mp)
      :: subst_match_goal_hyps subst tl
  | [] -> []

let rec subst_atomic subst (t:glob_atomic_tactic_expr) = match t with
  (* Basic tactics *)
  | TacIntroPattern _ | TacIntrosUntil _ | TacIntroMove _ as x -> x
  | TacAssumption as x -> x
  | TacExact c -> TacExact (subst_glob_constr subst c)
  | TacExactNoCheck c -> TacExactNoCheck (subst_glob_constr subst c)
  | TacVmCastNoCheck c -> TacVmCastNoCheck (subst_glob_constr subst c)
  | TacApply (a,ev,cb,cl) ->
      TacApply (a,ev,List.map (subst_glob_with_bindings subst) cb,cl)
  | TacElim (ev,cb,cbo) ->
      TacElim (ev,subst_glob_with_bindings subst cb,
               Option.map (subst_glob_with_bindings subst) cbo)
  | TacElimType c -> TacElimType (subst_glob_constr subst c)
  | TacCase (ev,cb) -> TacCase (ev,subst_glob_with_bindings subst cb)
  | TacCaseType c -> TacCaseType (subst_glob_constr subst c)
  | TacFix (idopt,n) as x -> x
  | TacMutualFix (id,n,l) ->
      TacMutualFix(id,n,List.map (fun (id,n,c) -> (id,n,subst_glob_constr subst c)) l)
  | TacCofix idopt as x -> x
  | TacMutualCofix (id,l) ->
      TacMutualCofix (id, List.map (fun (id,c) -> (id,subst_glob_constr subst c)) l)
  | TacCut c -> TacCut (subst_glob_constr subst c)
  | TacAssert (b,na,c) ->
      TacAssert (Option.map (subst_tactic subst) b,na,subst_glob_constr subst c)
  | TacGeneralize cl ->
      TacGeneralize (List.map (on_fst (subst_constr_with_occurrences subst))cl)
  | TacGeneralizeDep c -> TacGeneralizeDep (subst_glob_constr subst c)
  | TacLetTac (id,c,clp,b,eqpat) ->
    TacLetTac (id,subst_glob_constr subst c,clp,b,eqpat)

  (* Automation tactics *)
  | TacTrivial (d,lems,l) -> TacTrivial (d,List.map (subst_glob_constr subst) lems,l)
  | TacAuto (d,n,lems,l) -> TacAuto (d,n,List.map (subst_glob_constr subst) lems,l)

  (* Derived basic tactics *)
  | TacSimpleInductionDestruct (isrec,h) as x -> x
  | TacInductionDestruct (isrec,ev,(l,el,cls)) ->
      let l' = List.map (fun (c,ids) -> subst_induction_arg subst c, ids) l in
      let el' = Option.map (subst_glob_with_bindings subst) el in
      TacInductionDestruct (isrec,ev,(l',el',cls))
  | TacDoubleInduction (h1,h2) as x -> x
  | TacDecomposeAnd c -> TacDecomposeAnd (subst_glob_constr subst c)
  | TacDecomposeOr c -> TacDecomposeOr (subst_glob_constr subst c)
  | TacDecompose (l,c) ->
      let l = List.map (subst_or_var (subst_inductive subst)) l in
      TacDecompose (l,subst_glob_constr subst c)
  | TacSpecialize (n,l) -> TacSpecialize (n,subst_glob_with_bindings subst l)
  | TacLApply c -> TacLApply (subst_glob_constr subst c)

  (* Context management *)
  | TacClear _ as x -> x
  | TacClearBody l as x -> x
  | TacMove (dep,id1,id2) as x -> x
  | TacRename l as x -> x
  | TacRevert _ as x -> x

  (* Constructors *)
  | TacLeft (ev,bl) -> TacLeft (ev,subst_bindings subst bl)
  | TacRight (ev,bl) -> TacRight (ev,subst_bindings subst bl)
  | TacSplit (ev,b,bll) -> TacSplit (ev,b,List.map (subst_bindings subst) bll)
  | TacAnyConstructor (ev,t) -> TacAnyConstructor (ev,Option.map (subst_tactic subst) t)
  | TacConstructor (ev,n,bl) -> TacConstructor (ev,n,subst_bindings subst bl)

  (* Conversion *)
  | TacReduce (r,cl) -> TacReduce (subst_redexp subst r, cl)
  | TacChange (op,c,cl) ->
      TacChange (Option.map (subst_glob_constr_or_pattern subst) op,
        subst_glob_constr subst c, cl)

  (* Equivalence relations *)
  | TacReflexivity | TacSymmetry _ as x -> x
  | TacTransitivity c -> TacTransitivity (Option.map (subst_glob_constr subst) c)

  (* Equality and inversion *)
  | TacRewrite (ev,l,cl,by) ->
      TacRewrite (ev,
		  List.map (fun (b,m,c) ->
			      b,m,subst_glob_with_bindings subst c) l,
		 cl,Option.map (subst_tactic subst) by)
  | TacInversion (DepInversion (k,c,l),hyp) ->
     TacInversion (DepInversion (k,Option.map (subst_glob_constr subst) c,l),hyp)
  | TacInversion (NonDepInversion _,_) as x -> x
  | TacInversion (InversionUsing (c,cl),hyp) ->
      TacInversion (InversionUsing (subst_glob_constr subst c,cl),hyp)

  (* For extensions *)
  | TacExtend (_loc,opn,l) ->
      TacExtend (dloc,opn,List.map (subst_genarg subst) l)
  | TacAlias (_,s,l) ->
      let s = subst_kn subst s in
      TacAlias (dloc,s,List.map (fun (id,a) -> (id,subst_genarg subst a)) l)

and subst_tactic subst (t:glob_tactic_expr) = match t with
  | TacAtom (_loc,t) -> TacAtom (dloc, subst_atomic subst t)
  | TacFun tacfun -> TacFun (subst_tactic_fun subst tacfun)
  | TacLetIn (r,l,u) ->
      let l = List.map (fun (n,b) -> (n,subst_tacarg subst b)) l in
      TacLetIn (r,l,subst_tactic subst u)
  | TacMatchGoal (lz,lr,lmr) ->
      TacMatchGoal(lz,lr, subst_match_rule subst lmr)
  | TacMatch (lz,c,lmr) ->
      TacMatch (lz,subst_tactic subst c,subst_match_rule subst lmr)
  | TacId _ | TacFail _ as x -> x
  | TacProgress tac -> TacProgress (subst_tactic subst tac:glob_tactic_expr)
  | TacShowHyps tac -> TacShowHyps (subst_tactic subst tac:glob_tactic_expr)
  | TacAbstract (tac,s) -> TacAbstract (subst_tactic subst tac,s)
  | TacThen (t1,tf,t2,tl) ->
      TacThen (subst_tactic subst t1,Array.map (subst_tactic subst) tf,
	       subst_tactic subst t2,Array.map (subst_tactic subst) tl)
  | TacThens (t,tl) ->
      TacThens (subst_tactic subst t, List.map (subst_tactic subst) tl)
  | TacDo (n,tac) -> TacDo (n,subst_tactic subst tac)
  | TacTimeout (n,tac) -> TacTimeout (n,subst_tactic subst tac)
  | TacTry tac -> TacTry (subst_tactic subst tac)
  | TacInfo tac -> TacInfo (subst_tactic subst tac)
  | TacRepeat tac -> TacRepeat (subst_tactic subst tac)
  | TacOr (tac1,tac2) ->
      TacOr (subst_tactic subst tac1,subst_tactic subst tac2)
  | TacOnce tac ->
      TacOnce (subst_tactic subst tac)
  | TacExactlyOnce tac ->
      TacExactlyOnce (subst_tactic subst tac)
  | TacOrelse (tac1,tac2) ->
      TacOrelse (subst_tactic subst tac1,subst_tactic subst tac2)
  | TacFirst l -> TacFirst (List.map (subst_tactic subst) l)
  | TacSolve l -> TacSolve (List.map (subst_tactic subst) l)
  | TacComplete tac -> TacComplete (subst_tactic subst tac)
  | TacArg (_,a) -> TacArg (dloc,subst_tacarg subst a)

and subst_tactic_fun subst (var,body) = (var,subst_tactic subst body)

and subst_tacarg subst = function
  | Reference r -> Reference (subst_reference subst r)
  | ConstrMayEval c -> ConstrMayEval (subst_raw_may_eval subst c)
  | MetaIdArg (_loc,_,_) -> assert false
  | TacCall (_loc,f,l) ->
      TacCall (_loc, subst_reference subst f, List.map (subst_tacarg subst) l)
  | TacExternal (_loc,com,req,la) ->
      TacExternal (_loc,com,req,List.map (subst_tacarg subst) la)
  | TacFreshId _ as x -> x
  | Tacexp t -> Tacexp (subst_tactic subst t)
  | TacGeneric arg -> TacGeneric (Genintern.generic_substitute subst arg)
  | TacDynamic(the_loc,t) as x ->
      (match Dyn.tag t with
	| "tactic" | "value" -> x
        | "constr" ->
          TacDynamic(the_loc, constr_in (subst_mps subst (constr_out t)))
	| s -> Errors.anomaly ~loc:dloc ~label:"Tacinterp.val_interp"
                 (str "Unknown dynamic: <" ++ str s ++ str ">"))

(* Reads the rules of a Match Context or a Match *)
and subst_match_rule subst = function
  | (All tc)::tl ->
      (All (subst_tactic subst tc))::(subst_match_rule subst tl)
  | (Pat (rl,mp,tc))::tl ->
      let hyps = subst_match_goal_hyps subst rl in
      let pat = subst_match_pattern subst mp in
      Pat (hyps,pat,subst_tactic subst tc)
      ::(subst_match_rule subst tl)
  | [] -> []

and subst_genarg subst (x:glob_generic_argument) =
  match genarg_tag x with
  | IntOrVarArgType -> in_gen (glbwit wit_int_or_var) (out_gen (glbwit wit_int_or_var) x)
  | IdentArgType ->
      in_gen (glbwit wit_ident) (out_gen (glbwit wit_ident) x)
  | VarArgType -> in_gen (glbwit wit_var) (out_gen (glbwit wit_var) x)
  | GenArgType -> in_gen (glbwit wit_genarg) (subst_genarg subst (out_gen (glbwit wit_genarg) x))
  | ConstrArgType ->
      in_gen (glbwit wit_constr) (subst_glob_constr subst (out_gen (glbwit wit_constr) x))
  | ConstrMayEvalArgType ->
      in_gen (glbwit wit_constr_may_eval) (subst_raw_may_eval subst (out_gen (glbwit wit_constr_may_eval) x))
  | QuantHypArgType ->
      in_gen (glbwit wit_quant_hyp)
        (subst_declared_or_quantified_hypothesis subst
          (out_gen (glbwit wit_quant_hyp) x))
  | RedExprArgType ->
      in_gen (glbwit wit_red_expr) (subst_redexp subst (out_gen (glbwit wit_red_expr) x))
  | OpenConstrArgType ->
      in_gen (glbwit wit_open_constr)
        ((),subst_glob_constr subst (snd (out_gen (glbwit wit_open_constr) x)))
  | ConstrWithBindingsArgType ->
      in_gen (glbwit wit_constr_with_bindings)
        (subst_glob_with_bindings subst (out_gen (glbwit wit_constr_with_bindings) x))
  | BindingsArgType ->
      in_gen (glbwit wit_bindings)
        (subst_bindings subst (out_gen (glbwit wit_bindings) x))
  | ListArgType _ -> app_list (subst_genarg subst) x
  | OptArgType _ -> app_opt (subst_genarg subst) x
  | PairArgType _ -> app_pair (subst_genarg subst) (subst_genarg subst) x
  | ExtraArgType s ->
      Genintern.generic_substitute subst x

(** Registering *)

let () =
  Genintern.register_subst0 wit_ref subst_global_reference;
  Genintern.register_subst0 wit_intro_pattern (fun _ v -> v);
  Genintern.register_subst0 wit_tactic subst_tactic;
  Genintern.register_subst0 wit_sort (fun _ v -> v);
  Genintern.register_subst0 wit_clause_dft_concl (fun _ v -> v)

let _ = Hook.set Auto.extern_subst_tactic subst_tactic
