(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Tacexpr
open Mod_subst
open Genarg
open Stdarg
open Tacarg
open Tactypes
open Tactics
open Globnames
open Genredexpr
open Patternops

(** Substitution of tactics at module closing time *)

(** For generic arguments, we declare and store substitutions
    in a table *)

let subst_quantified_hypothesis _ x = x

let subst_declared_or_quantified_hypothesis _ x = x

let subst_glob_constr_and_expr subst (c, e) =
  (Detyping.subst_glob_constr subst c, e)

let subst_glob_constr = subst_glob_constr_and_expr (* shortening *)

let subst_binding subst =
  CAst.map (fun (b,c) ->
      subst_quantified_hypothesis subst b,subst_glob_constr subst c)

let subst_bindings subst = function
  | NoBindings -> NoBindings
  | ImplicitBindings l -> ImplicitBindings (List.map (subst_glob_constr subst) l)
  | ExplicitBindings l -> ExplicitBindings (List.map (subst_binding subst) l)

let subst_glob_with_bindings subst (c,bl) =
  (subst_glob_constr subst c, subst_bindings subst bl)

let subst_glob_with_bindings_arg subst (clear,c) =
  (clear,subst_glob_with_bindings subst c)

let rec subst_intro_pattern subst = CAst.map (function
  | IntroAction p -> IntroAction (subst_intro_pattern_action subst p)
  | IntroNaming _ | IntroForthcoming _ as x -> x)

and subst_intro_pattern_action subst = let open CAst in function
  | IntroApplyOn ({loc;v=t},pat) ->
    IntroApplyOn (make ?loc @@ subst_glob_constr subst t,subst_intro_pattern subst pat)
  | IntroOrAndPattern l ->
      IntroOrAndPattern (subst_intro_or_and_pattern subst l)
  | IntroInjection l -> IntroInjection (List.map (subst_intro_pattern subst) l)
  | IntroWildcard | IntroRewrite _ as x -> x

and subst_intro_or_and_pattern subst = function
  | IntroAndPattern l ->
      IntroAndPattern (List.map (subst_intro_pattern subst) l)
  | IntroOrPattern ll ->
      IntroOrPattern (List.map (List.map (subst_intro_pattern subst)) ll)

let subst_destruction_arg subst = function
  | clear,ElimOnConstr c -> clear,ElimOnConstr (subst_glob_with_bindings subst c)
  | clear,ElimOnAnonHyp n as x -> x
  | clear,ElimOnIdent id as x -> x

let subst_and_short_name f (c,n) =
(*  assert (n=None); *)(* since tacdef are strictly globalized *)
  (f c,None)

let subst_or_var f =  let open Locus in function
  | ArgVar _ as x -> x
  | ArgArg x -> ArgArg (f x)

let subst_located f = Loc.map f

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
   if not (is_global ref' t') then
    (let sigma, env = Pfedit.get_current_context () in
     Feedback.msg_warning (strbrk "The reference " ++ pr_global ref ++ str " is not " ++
          str " expanded to \"" ++ pr_lconstr_env env sigma t' ++ str "\", but to " ++
          pr_global ref'));
   ref'
 in
  subst_or_var (subst_located subst_global)

let subst_evaluable subst =
  let subst_eval_ref = subst_evaluable_reference subst in
    subst_or_var (subst_and_short_name subst_eval_ref)

let subst_constr_with_occurrences subst (l,c) = (l,subst_glob_constr subst c)

let subst_glob_constr_or_pattern subst (bvars,c,p) =
  (bvars,subst_glob_constr subst c,subst_pattern subst p)

let subst_redexp subst =
  Redops.map_red_expr_gen
    (subst_glob_constr subst)
    (subst_evaluable subst)
    (subst_glob_constr_or_pattern subst)

let subst_raw_may_eval subst = function
  | ConstrEval (r,c) -> ConstrEval (subst_redexp subst r,subst_glob_constr subst c)
  | ConstrContext (locid,c) -> ConstrContext (locid,subst_glob_constr subst c)
  | ConstrTypeOf c -> ConstrTypeOf (subst_glob_constr subst c)
  | ConstrTerm c -> ConstrTerm (subst_glob_constr subst c)

let subst_match_pattern subst = function
  | Subterm (ido,pc) -> Subterm (ido,(subst_glob_constr_or_pattern subst pc))
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
  | TacIntroPattern (ev,l) -> TacIntroPattern (ev,List.map (subst_intro_pattern subst) l)
  | TacApply (a,ev,cb,cl) ->
      TacApply (a,ev,List.map (subst_glob_with_bindings_arg subst) cb,cl)
  | TacElim (ev,cb,cbo) ->
      TacElim (ev,subst_glob_with_bindings_arg subst cb,
               Option.map (subst_glob_with_bindings subst) cbo)
  | TacCase (ev,cb) -> TacCase (ev,subst_glob_with_bindings_arg subst cb)
  | TacMutualFix (id,n,l) ->
      TacMutualFix(id,n,List.map (fun (id,n,c) -> (id,n,subst_glob_constr subst c)) l)
  | TacMutualCofix (id,l) ->
      TacMutualCofix (id, List.map (fun (id,c) -> (id,subst_glob_constr subst c)) l)
  | TacAssert (ev,b,otac,na,c) ->
      TacAssert (ev,b,Option.map (Option.map (subst_tactic subst)) otac,na,
                 subst_glob_constr subst c)
  | TacGeneralize cl ->
      TacGeneralize (List.map (on_fst (subst_constr_with_occurrences subst))cl)
  | TacLetTac (ev,id,c,clp,b,eqpat) ->
    TacLetTac (ev,id,subst_glob_constr subst c,clp,b,eqpat)

  (* Derived basic tactics *)
  | TacInductionDestruct (isrec,ev,(l,el)) ->
      let l' = List.map (fun (c,ids,cls) ->
        subst_destruction_arg subst c, ids, cls) l in
      let el' = Option.map (subst_glob_with_bindings subst) el in
      TacInductionDestruct (isrec,ev,(l',el'))

  (* Conversion *)
  | TacReduce (r,cl) -> TacReduce (subst_redexp subst r, cl)
  | TacChange (op,c,cl) ->
      TacChange (Option.map (subst_glob_constr_or_pattern subst) op,
        subst_glob_constr subst c, cl)

  (* Equality and inversion *)
  | TacRewrite (ev,l,cl,by) ->
      TacRewrite (ev,
		  List.map (fun (b,m,c) ->
			      b,m,subst_glob_with_bindings_arg subst c) l,
		 cl,Option.map (subst_tactic subst) by)
  | TacInversion (DepInversion (k,c,l),hyp) ->
     TacInversion (DepInversion (k,Option.map (subst_glob_constr subst) c,l),hyp)
  | TacInversion (NonDepInversion _,_) as x -> x
  | TacInversion (InversionUsing (c,cl),hyp) ->
      TacInversion (InversionUsing (subst_glob_constr subst c,cl),hyp)

and subst_tactic subst (t:glob_tactic_expr) = match t with
  | TacAtom (_loc,t) -> TacAtom (Loc.tag @@ subst_atomic subst t)
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
  | TacThen (t1,t2) ->
      TacThen (subst_tactic subst t1, subst_tactic subst t2)
  | TacDispatch tl -> TacDispatch (List.map (subst_tactic subst) tl)
  | TacExtendTac (tf,t,tl) ->
      TacExtendTac (Array.map (subst_tactic subst) tf,
	            subst_tactic subst t,
                    Array.map (subst_tactic subst) tl)
  | TacThens (t,tl) ->
      TacThens (subst_tactic subst t, List.map (subst_tactic subst) tl)
  | TacThens3parts (t1,tf,t2,tl) ->
      TacThens3parts (subst_tactic subst t1,Array.map (subst_tactic subst) tf,
	       subst_tactic subst t2,Array.map (subst_tactic subst) tl)
  | TacDo (n,tac) -> TacDo (n,subst_tactic subst tac)
  | TacTimeout (n,tac) -> TacTimeout (n,subst_tactic subst tac)
  | TacTime (s,tac) -> TacTime (s,subst_tactic subst tac)
  | TacTry tac -> TacTry (subst_tactic subst tac)
  | TacInfo tac -> TacInfo (subst_tactic subst tac)
  | TacRepeat tac -> TacRepeat (subst_tactic subst tac)
  | TacOr (tac1,tac2) ->
      TacOr (subst_tactic subst tac1,subst_tactic subst tac2)
  | TacOnce tac ->
      TacOnce (subst_tactic subst tac)
  | TacExactlyOnce tac ->
      TacExactlyOnce (subst_tactic subst tac)
  | TacIfThenCatch (tac,tact,tace) ->
      TacIfThenCatch (
        subst_tactic subst tac,
        subst_tactic subst tact,
        subst_tactic subst tace)
  | TacOrelse (tac1,tac2) ->
      TacOrelse (subst_tactic subst tac1,subst_tactic subst tac2)
  | TacFirst l -> TacFirst (List.map (subst_tactic subst) l)
  | TacSolve l -> TacSolve (List.map (subst_tactic subst) l)
  | TacComplete tac -> TacComplete (subst_tactic subst tac)
  | TacArg (_,a) -> TacArg (Loc.tag @@ subst_tacarg subst a)
  | TacSelect (s, tac) -> TacSelect (s, subst_tactic subst tac)

  (* For extensions *)
  | TacAlias (_,(s,l)) ->
      let s = subst_kn subst s in
      TacAlias (Loc.tag (s,List.map (subst_tacarg subst) l))
  | TacML (loc,(opn,l)) -> TacML (loc, (opn,List.map (subst_tacarg subst) l))

and subst_tactic_fun subst (var,body) = (var,subst_tactic subst body)

and subst_tacarg subst = function
  | Reference r -> Reference (subst_reference subst r)
  | ConstrMayEval c -> ConstrMayEval (subst_raw_may_eval subst c)
  | TacCall (loc,(f,l)) ->
      TacCall (Loc.tag ?loc (subst_reference subst f, List.map (subst_tacarg subst) l))
  | TacFreshId _ as x -> x
  | TacPretype c -> TacPretype (subst_glob_constr subst c)
  | TacNumgoals -> TacNumgoals
  | Tacexp t -> Tacexp (subst_tactic subst t)
  | TacGeneric arg -> TacGeneric (subst_genarg subst arg)

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

and subst_genarg subst (GenArg (Glbwit wit, x)) =
  match wit with
  | ListArg wit ->
    let map x =
      let ans = subst_genarg subst (in_gen (glbwit wit) x) in
      out_gen (glbwit wit) ans
    in
    in_gen (glbwit (wit_list wit)) (List.map map x)
  | OptArg wit ->
    let ans = match x with
    | None -> in_gen (glbwit (wit_opt wit)) None
    | Some x ->
      let s = out_gen (glbwit wit) (subst_genarg subst (in_gen (glbwit wit) x)) in
      in_gen (glbwit (wit_opt wit)) (Some s)
    in
    ans
  | PairArg (wit1, wit2) ->
    let p, q = x in
    let p = out_gen (glbwit wit1) (subst_genarg subst (in_gen (glbwit wit1) p)) in
    let q = out_gen (glbwit wit2) (subst_genarg subst (in_gen (glbwit wit2) q)) in
    in_gen (glbwit (wit_pair wit1 wit2)) (p, q)
  | ExtraArg s ->
      Genintern.generic_substitute subst (in_gen (glbwit wit) x)

(** Registering *)

let () =
  Genintern.register_subst0 wit_int_or_var (fun _ v -> v);
  Genintern.register_subst0 wit_ref subst_global_reference;
  Genintern.register_subst0 wit_pre_ident (fun _ v -> v);
  Genintern.register_subst0 wit_ident (fun _ v -> v);
  Genintern.register_subst0 wit_var (fun _ v -> v);
  Genintern.register_subst0 wit_intro_pattern (fun _ v -> v);
  Genintern.register_subst0 wit_tactic subst_tactic;
  Genintern.register_subst0 wit_ltac subst_tactic;
  Genintern.register_subst0 wit_constr subst_glob_constr;
  Genintern.register_subst0 wit_clause_dft_concl (fun _ v -> v);
  Genintern.register_subst0 wit_uconstr (fun subst c -> subst_glob_constr subst c);
  Genintern.register_subst0 wit_open_constr (fun subst c -> subst_glob_constr subst c);
  Genintern.register_subst0 wit_red_expr subst_redexp;
  Genintern.register_subst0 wit_quant_hyp subst_declared_or_quantified_hypothesis;
  Genintern.register_subst0 wit_bindings subst_bindings;
  Genintern.register_subst0 wit_constr_with_bindings subst_glob_with_bindings;
  Genintern.register_subst0 wit_destruction_arg subst_destruction_arg;
  ()
