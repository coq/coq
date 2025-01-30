(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Constr
open Context
open Termops
open Environ
open EConstr
open Reductionops

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

(* Errors *)

type reduction_tactic_error =
    InvalidAbstraction of env * Evd.evar_map * EConstr.constr * (env * Type_errors.type_error)

type 'a change = NoChange | Changed of 'a
type change_function = env -> Evd.evar_map -> constr -> (Evd.evar_map * constr) change

exception ReductionTacticError of reduction_tactic_error

(* Evaluable reference *)

exception Elimconst

(* Here the semantics is completely unclear.
   What does "Hint Unfold t" means when "t" is a parameter?
   Does the user mean "Unfold X.t" or does she mean "Unfold y"
   where X.t is later on instantiated with y? I choose the first
   interpretation (i.e. an evaluable reference is never expanded). *)
let subst_evaluable_reference subst =
  Evaluable.map (fun id -> id) (Mod_subst.subst_constant subst)
    (Mod_subst.subst_proj_repr subst)

exception NotEvaluableRef of GlobRef.t

let () = CErrors.register_handler (function
    | NotEvaluableRef r ->
      Some Pp.(str "Cannot coerce" ++ spc () ++ Nametab.pr_global_env Id.Set.empty r ++
               spc () ++ str "to an evaluable reference.")
    | _ -> None)

let error_not_evaluable ?loc r = Loc.raise ?loc (NotEvaluableRef r)

let is_evaluable_const env cst =
  is_transparent env (Evaluable.EvalConstRef cst) && evaluable_constant cst env

let is_evaluable_var env id =
  is_transparent env (Evaluable.EvalVarRef id) && evaluable_named id env

let is_evaluable_projection env p =
  is_transparent env (Evaluable.EvalProjectionRef p)

let is_evaluable env = function
  | Evaluable.EvalConstRef cst -> is_evaluable_const env cst
  | Evaluable.EvalVarRef id -> is_evaluable_var env id
  | Evaluable.EvalProjectionRef p -> is_evaluable_projection env p

let value_of_evaluable_ref env evref u =
  match evref with
  | Evaluable.EvalConstRef con ->
    let u = Unsafe.to_instance u in
    EConstr.of_constr (constant_value_in env (con, u))
  | Evaluable.EvalVarRef id ->
    env |> lookup_named id |> NamedDecl.get_value |> Option.get
  | Evaluable.EvalProjectionRef _ ->
    assert false (* TODO *)

let soft_evaluable_of_global_reference ?loc = function
  | GlobRef.ConstRef cst ->
    begin
      match Structures.PrimitiveProjections.find_opt cst with
      | None -> Evaluable.EvalConstRef cst
      | Some p -> Evaluable.EvalProjectionRef p
    end
  | GlobRef.VarRef id -> Evaluable.EvalVarRef id
  | r -> error_not_evaluable ?loc r

let evaluable_of_global_reference env = function
  | GlobRef.ConstRef cst when is_evaluable_const env cst ->
      begin
        match Structures.PrimitiveProjections.find_opt cst with
        | None -> Evaluable.EvalConstRef cst
        | Some p -> Evaluable.EvalProjectionRef p
      end
  | GlobRef.VarRef id when is_evaluable_var env id -> Evaluable.EvalVarRef id
  | r -> error_not_evaluable r

let global_of_evaluable_reference = function
  | Evaluable.EvalConstRef cst -> GlobRef.ConstRef cst
  | Evaluable.EvalVarRef id -> GlobRef.VarRef id
  | Evaluable.EvalProjectionRef p -> GlobRef.ConstRef (Projection.Repr.constant p)

type evaluable_reference =
  | EvalConst of Constant.t
  | EvalVar of Id.t
  | EvalRel of int
  | EvalEvar of EConstr.existential

let evaluable_reference_eq env sigma r1 r2 = match r1, r2 with
| EvalConst c1, EvalConst c2 -> QConstant.equal env c1 c2
| EvalVar id1, EvalVar id2 -> Id.equal id1 id2
| EvalRel i1, EvalRel i2 -> Int.equal i1 i2
| EvalEvar (e1, ctx1), EvalEvar (e2, ctx2) ->
  EConstr.eq_constr sigma (mkEvar (e1, ctx1)) (mkEvar (e2, ctx2))
| (EvalConst _ | EvalVar _ | EvalRel _ | EvalEvar _), _ -> false

let mkEvalRef ref u =
  match ref with
  | EvalConst cst -> mkConstU (cst,u)
  | EvalVar id -> mkVar id
  | EvalRel n -> mkRel n
  | EvalEvar ev -> EConstr.mkEvar ev

let isEvalRef env sigma c = match EConstr.kind sigma c with
  | Const (sp,_) -> is_evaluable env (EvalConstRef sp)
  | Var id -> is_evaluable env (EvalVarRef id)
  | Rel _ | Evar _ -> true
  | _ -> false

let isTransparentEvalRef env sigma ts c = match EConstr.kind sigma c with
  | Const (cst,_) -> is_evaluable env (EvalConstRef cst) && Structures.PrimitiveProjections.is_transparent_constant ts cst
  | Var id -> is_evaluable env (EvalVarRef id) && TransparentState.is_transparent_variable ts id
  | Rel _ -> true
  | Evar _ -> false (* undefined *)
  | _ -> false

let destEvalRefU sigma c = match EConstr.kind sigma c with
  | Const (cst,u) ->  EvalConst cst, u
  | Var id  -> (EvalVar id, EInstance.empty)
  | Rel n -> (EvalRel n, EInstance.empty)
  | Evar ev -> (EvalEvar ev, EInstance.empty)
  | _ -> anomaly (Pp.str "Not an unfoldable reference.")

module CacheTable = Hashtbl.Make(struct
    type t = Constant.t * UVars.Instance.t

    (* WARNING if we use CanOrd and we have [M.x := N.x] unfolding M.x
       first will put [M.x -> N.x] in the cache, then trying to unfold
       N.x will return N.x ie loop. *)
    let equal (c,u) (c',u') =
      Constant.UserOrd.equal c c' && UVars.Instance.equal u u'

    let hash (c,u) =
      Hashset.Combine.combine (Constant.UserOrd.hash c) (UVars.Instance.hash u)
  end)

let reference_opt_value cache env sigma eval u =
  match eval with
  | EvalConst cst ->
    let u = EInstance.kind sigma u in
    let cu = (cst, u) in
    begin match CacheTable.find_opt cache cu with
    | Some v -> v
    | None ->
      let v = Option.map EConstr.of_constr (constant_opt_value_in env cu) in
      CacheTable.add cache cu v;
      v
    end
  | EvalVar id ->
      env |> lookup_named id |> NamedDecl.get_value
  | EvalRel n ->
      env |> lookup_rel n |> RelDecl.get_value |> Option.map (Vars.lift n)
  | EvalEvar ev ->
    match EConstr.kind sigma (mkEvar ev) with
    | Evar _ -> None
    | c -> Some (EConstr.of_kind c)

exception NotEvaluable
let reference_value cache env sigma c u =
  match reference_opt_value cache env sigma c u with
    | None -> raise NotEvaluable
    | Some d -> d

(************************************************************************)
(* Reduction of constants hiding a fixpoint (e.g. for "simpl" tactic).  *)
(* One reuses the name of the function after reduction of the fixpoint  *)

type fix_refolding = {
  refolding_names : (evaluable_reference * EInstance.t) option array;
  refolding_wrapper_data : (int * constr) list;
  expected_args : int;
}

type fix_evaluation_data = {
  trigger_min_args : int;
  refolding_target : evaluable_reference;
  refolding_data : fix_refolding;
}

type constant_elimination =
  | EliminationFix of fix_evaluation_data
  | EliminationCases of constr * int
  | EliminationProj of constr * int
  | NotAnElimination of constr
  | NotAnEliminationConstant

type constant_coelimination =
  | CoEliminationCoFix of fix_evaluation_data
  | CoEliminationConstruct of constr
  | CoEliminationPrimitive of constr
  | NotACoElimination of constr
  | NotACoEliminationConstant

(************************************************************************)

type simpl_infos = {
  constant_body_cache : EConstr.t option CacheTable.t;
  elim_cache : constant_elimination CacheTable.t;
  coelim_cache : constant_coelimination CacheTable.t;
  red_behavior : ReductionBehaviour.Db.t;
  main_reds : RedFlags.reds;
  construct_reds : RedFlags.reds;
}

let make_simpl_infos (red_behavior, main_reds, construct_reds) = {
  constant_body_cache = CacheTable.create 12;
  elim_cache = CacheTable.create 12;
  coelim_cache = CacheTable.create 12;
  red_behavior;
  main_reds;
  construct_reds;
}

(* [compute_constant_elimination] determines whether f is an "elimination constant"

   either [yn:Tn]..[y1:T1](match yi with f1..fk end g1 ..gp)

   or     [yn:Tn]..[y1:T1](Fix(m0,..) yi1..yip)
          with yi1..yip distinct variables among the yi, not occurring in t

   In the second case, [check_fix_reversibility [T1;...;Tn] args fix]
   checks that [args] is a subset of disjoint variables in y1..yn (a necessary
   condition for reversibility). Assuming a constant f_m naming
   Fix(m,..), with f := f_m0, it also returns for each m the relevant
   information ([i1,Ti1;..;ip,Tip],n) in order to compute an
   equivalent g_m of Fix(m,..) such that

   g_m := [xp:Tip']..[x1:Ti1'](f_m a1..an)
       == [xp:Tip']..[x1:Ti1'](Fix(f|t) yi1..yip)

   with a_k:=y_k if k<>i_j and (but only in the case m_0), a_k:=args_k
   otherwise, as well as Tij':=Tij[x1..xi(j-1) <- a1..ai(j-1)]

   Note that the types Tk, when no i_j=k, must not be dependent on
   the xp..x1.
*)

let compute_constant_reversibility sigma labs args fix =
  let nlam = List.length labs in
  let nargs = List.length args in
  if nargs > nlam then
    (* Necessary non-linear, thus not reversible *)
    raise Elimconst;
  (* Check that arguments are bound by the lambdas, up to a
     substitution, and that they do not occur elsewhere *)
  let typed_reversible_args =
    List.map
      (function d -> match EConstr.kind sigma d with
         | Rel k ->
             if Vars.noccurn sigma k fix && k <= nlam then
               (* Bound in labs and occurring only in args *)
               (k, snd (List.nth labs (k-1)))
             else
               raise Elimconst
         | _ ->
             raise Elimconst) args in
  let reversible_rels = List.map fst typed_reversible_args in
  if not (List.distinct_f Int.compare reversible_rels) then
    raise Elimconst;
  (* Lambda's that are not used should not depend on those that are
     used and that will thus be different in the recursive calls *)
  List.iteri (fun i (_,t_i) ->
    if not (Int.List.mem (i+1) reversible_rels) then
      let fvs = List.map ((+) (i+1)) (Int.Set.elements (free_rels sigma t_i)) in
      match List.intersect Int.equal fvs reversible_rels with
      | [] -> ()
      | _ -> raise Elimconst)
    labs;
  typed_reversible_args, nlam, nargs

let check_fix_reversibility env sigma ref u labs args minarg refs ((lv,i),_ as fix) =
  let li, nlam, nargs = compute_constant_reversibility sigma labs args (mkFix fix) in
  let k = lv.(i) in
  let refolding_data = {
    refolding_names = refs;
    refolding_wrapper_data = li;
    expected_args = nlam;
  } in
  if k < nargs then
(*  Such an optimisation would need eta-expansion
      let p = destRel (List.nth args k) in
      EliminationFix (n-p+1,(li,n))
*)
      {
        trigger_min_args = max minarg nlam;
        refolding_target = ref;
        refolding_data;
        }
  else
      {
        trigger_min_args = max minarg (nlam - nargs + k + 1);
        refolding_target = ref;
        refolding_data;
        }

let check_cofix_reversibility env sigma ref u labs args minarg refs (i,_ as cofix) =
  let li, nlam, nargs = compute_constant_reversibility sigma labs args (mkCoFix cofix) in
  let refolding_data = {
    refolding_names = refs;
    refolding_wrapper_data = li;
    expected_args = nlam;
  } in
  {
    trigger_min_args = max minarg nlam; (* Does not matter; will be maximally applied anyway *)
    refolding_target = ref;
    refolding_data;
  }

let compute_recursive_wrapper infos env sigma ref u =
  try match reference_opt_value infos.constant_body_cache env sigma ref u with
    | None -> None
    | Some c ->
      let labs, ccl = whd_decompose_lambda env sigma c in
      let c, l = whd_stack_gen infos.main_reds env sigma ccl in
      Some (labs, l)
  with Not_found (* Undefined ref *) -> None

(* Heuristic to look if global names are associated to other
   components of a mutual fixpoint *)

let invert_recursive_names infos env sigma ref u names i =
  let labs, l =
    match compute_recursive_wrapper infos env sigma ref u with
    | None -> assert false
    | Some (labs, l) -> labs, l in
  let make_name j =
    if Int.equal i j then Some (ref, u) else
    match names.(j).binder_name with
      | Anonymous -> None (* should not happen *)
      | Name id ->
        let refi = match ref with
          | EvalRel _ | EvalEvar _ -> None
          | EvalVar id' -> Some (EvalVar id)
          | EvalConst kn ->
            let kn = Constant.change_label kn (Label.of_id id) in
            if Environ.mem_constant kn env then Some (EvalConst kn) else None
        in
        match refi with
        | None -> None
        | Some ref ->
          match compute_recursive_wrapper infos env sigma ref u with
          | None -> None
          | Some (labs', l') ->
              let eq_constr c1 c2 = EConstr.eq_constr sigma c1 c2 in
              if List.equal (fun (_,t) (_,t') -> eq_constr t t') labs' labs &&
                 List.equal eq_constr l l' then Some (ref, u)
              else None in
  labs, l, Array.init (Array.length names) make_name

let deactivate_delta allowed_reds =
  (* Act both on Delta and transparent state as not all reduction functions work the same *)
  RedFlags.(red_add_transparent (red_sub allowed_reds fDELTA) TransparentState.empty)

(* [compute_constant_elimination] stepwise expands an arbitrary long sequence of
    reversible constants, eventually refolding to the initial constant
    for unary fixpoints and to the last constant encapsulating the Fix
    for mutual fixpoints *)

let compute_constant_elimination infos env sigma ref u =
  let allowed_reds_no_delta = deactivate_delta infos.main_reds in
  let rec srec env all_abs lastref lastu onlyproj c stk =
    let c', args = whd_stack_gen allowed_reds_no_delta env sigma c in
    (* We now know that the initial [ref] evaluates to [fun all_abs => c' args] *)
    (* and that the last visited name in the evaluation is [lastref] *)
    match EConstr.kind sigma c' with
      | Lambda (id,t,g) ->
          assert (List.is_empty args && Stack.is_empty stk);
          let open Context.Rel.Declaration in
          srec (push_rel (LocalAssum (id,t)) env) ((id,t)::all_abs) lastref lastu onlyproj g Stack.empty
      | Fix ((lv,i),(names,_,_) as fix) when not onlyproj ->
          let n_all_abs = List.length all_abs in
          let nbfix = Array.length lv in
          (if nbfix = 1 then
            (* Try to refold to [ref] *)
            let refs = [|Some (ref,u)|] in
            try EliminationFix (check_fix_reversibility env sigma ref u all_abs args n_all_abs refs fix)
            with Elimconst -> NotAnEliminationConstant
          else
            (* Try to refold to [lastref] *)
            let last_labs, last_args, names = invert_recursive_names infos env sigma lastref lastu names i in
            try EliminationFix (check_fix_reversibility env sigma lastref lastu last_labs last_args n_all_abs names fix)
            with Elimconst -> NotAnEliminationConstant)
      | Case (_,_,_,_,_,d,_) when isRel sigma d && not onlyproj ->
          EliminationCases (it_mkLambda (Stack.zip sigma (c',Stack.append_app_list args stk)) all_abs, List.length all_abs)
      | Case (ci,u,pms,p,iv,d,lf) -> srec env all_abs lastref lastu true d Stack.(Case (mkCaseStk (ci,u,pms,p,iv,lf)) :: append_app_list args stk)
      | Proj (p, _, d) when isRel sigma d ->
          EliminationProj (it_mkLambda (Stack.zip sigma (c',Stack.append_app_list args stk)) all_abs, List.length all_abs)
      | _ when isTransparentEvalRef env sigma (RedFlags.red_transparent infos.main_reds) c' ->
          (* Continue stepwise unfolding from [c' args] *)
          let ref, u = destEvalRefU sigma c' in
          (match reference_opt_value infos.constant_body_cache env sigma ref u with
            | None -> NotAnEliminationConstant (* e.g. if a rel *)
            | Some c -> srec env all_abs ref u onlyproj (applist (c, args)) stk)
      | _ -> NotAnEliminationConstant
  in
  match reference_opt_value infos.constant_body_cache env sigma ref u with
    | None -> NotAnEliminationConstant
    | Some c -> match srec env [] ref u false c Stack.empty with NotAnEliminationConstant -> NotAnElimination c | e -> e

(* [compute_constant_coelimination] stepwise expands an arbitrary long sequence of
    reversible constants, eventually refolding to the initial constant
    for unary cofixpoints and to the last constant encapsulating the CoFix
    for mutual cofixpoints *)

let compute_constant_coelimination infos env sigma ref u =
  let allowed_reds_no_delta = deactivate_delta infos.construct_reds in
  let rec srec env all_abs lastref lastu c =
    let c', args = whd_stack_gen allowed_reds_no_delta env sigma c in
    (* We now know that the initial [ref] evaluates to [fun all_abs => c' args] *)
    (* and that the last visited name in the evaluation is [lastref] *)
    match EConstr.kind sigma c' with
      | Lambda (id,t,g) ->
          assert (List.is_empty args);
          let open Context.Rel.Declaration in
          srec (push_rel (LocalAssum (id,t)) env) ((id,t)::all_abs) lastref lastu g
      | Construct _ ->
          let c = it_mkLambda (applist (c', args)) all_abs in
          CoEliminationConstruct c
      | Int _ | Float _ | String _ | Array _ (* reduced by primitives *) ->
          let c = it_mkLambda (applist (c', args)) all_abs in
          CoEliminationPrimitive c
      | CoFix (i,(names,_,_) as cofix) ->
          let n_all_abs = List.length all_abs in
          let nbfix = Array.length names in
          (if nbfix = 1 then
            (* Try to refold to [ref] *)
            let refs = [|Some (ref,u)|] in
            try CoEliminationCoFix (check_cofix_reversibility env sigma ref u all_abs args n_all_abs refs cofix)
            with Elimconst -> NotACoEliminationConstant
          else
            (* Try to refold to [lastref] *)
            let last_labs, last_args, names = invert_recursive_names infos env sigma lastref lastu names i in
            try CoEliminationCoFix (check_cofix_reversibility env sigma lastref lastu last_labs last_args n_all_abs names cofix)
            with Elimconst -> NotACoEliminationConstant)
      | _ when isTransparentEvalRef env sigma (RedFlags.red_transparent infos.construct_reds) c' ->
          (* Continue stepwise unfolding from [c' args] *)
          let ref, u = destEvalRefU sigma c' in
          (match reference_opt_value infos.constant_body_cache env sigma ref u with
            | None -> NotACoEliminationConstant (* e.g. if a rel *)
            | Some c -> srec env all_abs ref u (applist (c, args)))
      | _ -> NotACoEliminationConstant
  in
  match reference_opt_value infos.constant_body_cache env sigma ref u with
    | None -> NotACoEliminationConstant
    | Some c -> match srec env [] ref u c with NotACoEliminationConstant -> NotACoElimination c | e -> e

let compute_reference_elimination infos env sigma ref u =
  match ref with
  | EvalConst cst as ref ->
    let cu = cst, EInstance.kind sigma u in
    (match CacheTable.find_opt infos.elim_cache cu with
     | Some v -> v
     | None ->
       let v = compute_constant_elimination infos env sigma ref u in
       CacheTable.add infos.elim_cache cu v;
       v)
  | ref -> compute_constant_elimination infos env sigma ref u

let compute_reference_coelimination infos env sigma ref u =
  match ref with
  | EvalConst cst as ref ->
    let cu = cst, EInstance.kind sigma u in
    (match CacheTable.find_opt infos.coelim_cache cu with
     | Some v -> v
     | None ->
       let v = compute_constant_coelimination infos env sigma ref u in
       CacheTable.add infos.coelim_cache cu v;
       v)
  | ref -> compute_constant_coelimination infos env sigma ref u

(* If f is bound to EliminationFix (n',refs,infos), then n' is the minimal
   number of args for triggering the reduction and infos is
   ([(yi1,Ti1);...;(yip,Tip)],n) indicating that f converts
   to some [y1:T1,...,yn:Tn](Fix(..) yip .. yi1) where the y_{i_j} consist in a
   disjoint subset of the yi, i.e. 1 <= ij <= n and the ij are disjoint (in
   particular, p <= n).

   f is applied to largs := arg1 .. argn and we need for recursive
   calls to build the function

      g := [xp:Tip',...,x1:Ti1'](f a1 ... an)

   s.t. any (Fix(..) u1 ... up) can be re-expanded to (g u1 ... up)

   This is made possible by setting
      a_k:=x_j    if k=i_j for some j
      a_k:=arg_k  otherwise

   The type Tij' is Tij[yi(j-1)..y1 <- ai(j-1)..a1]

   In the case of a mutual fix and f is the m-th component, this is
   the same for the components different from m except that for the
   f_l associated to component l, and f_l is convertible to
   [y1:U1,...,yn:Un](Fix(..,l,..) yip .. yi1), we need i_j to be a
   bijection (since we have no more arg_k at our disposal to fill a
   position k not in the image of i_j).
*)

let xname = Name Namegen.default_dependent_ident

(* [f] is convertible to [Fix(recindices,bodynum),bodyvect)]:
   do so that the reduction uses this extra information *)

let substl_with_function subst sigma constr =
  let v = Array.of_list subst in
  let rec subst_total k c = match EConstr.kind sigma c with
  | Rel i when k < i ->
    if i <= k + Array.length v then
      (* A recursive call *)
      Vars.lift k v.(i-k-1)
    else
      (* A variable bound beyond the scope of the fix *)
      mkRel (i - Array.length v)
  | _ ->
    map_with_binders sigma succ subst_total k c in
  subst_total 0 constr

type 'a fix_reduction_result = NotReducible | Reduced of 'a

let[@ocaml.inline] (let*) m f = match m with
| NotReducible -> NotReducible
| Reduced x -> f x

let mkLambda_with_eta sigma x t c =
  let f, args = decompose_app_list sigma c in
  if List.is_empty args then mkLambda (x, t, c)
  else
    let b, args = List.sep_last args in
    if isRelN sigma 1 b then applist (f, List.map (Vars.lift (-1)) args)
    else mkLambda (x, t, c)

let contract_rec env sigma f nbodies mk_rec contract body =
  match f with
  | None -> contract ()
  | Some f ->
    let {refolding_names; refolding_wrapper_data = lv; expected_args = n}, largs = f in
    let lu = List.firstn n largs in
    let p = List.length lv in
    let lyi = List.map fst lv in
    let la =
      List.map_i (fun q aq ->
          (* k from the comment is q+1 *)
          try mkRel (p+1-(List.index Int.equal (n-q) lyi))
          with Not_found -> Vars.lift p aq)
        0 lu
    in
    let make_Fi i = match refolding_names.(i) with
      | None -> mk_rec i
      | Some (ref, u) ->
        let body = applist (mkEvalRef ref u, la) in
        List.fold_left_i (fun q (* j = n+1-q *) c (ij,tij) ->
            let subst = List.map (Vars.lift (-q)) (List.firstn (n-ij) la) in
            let tij' = Vars.substl (List.rev subst) tij in
            let x = make_annot xname ERelevance.relevant in  (* TODO relevance *)
            mkLambda_with_eta sigma x tij' c)
          1 body (List.rev lv)
    in
    let lbodies = List.init nbodies make_Fi in
    let c = substl_with_function (List.rev lbodies) sigma (nf_beta env sigma body) in
    nf_beta env sigma c

let contract_fix env sigma f ((recindices,bodynum),(_names,_types,bodies as typedbodies) as fixp) =
  contract_rec env sigma f
    (Array.length bodies)
    (fun i -> mkFix((recindices,i),typedbodies))
    (fun () -> contract_fix sigma fixp)
    bodies.(bodynum)

let contract_cofix env sigma f (bodynum,(_names,_types,bodies as typedbodies) as cofixp) =
  contract_rec env sigma f
    (Array.length bodies)
    (fun i -> mkCoFix(i,typedbodies))
    (fun () -> contract_cofix sigma cofixp)
    bodies.(bodynum)

let reducible_construct sigma c = match EConstr.kind sigma c with
| Construct _ | CoFix _ (* reduced by case *)
| Int _ | Float _ | String _ | Array _ (* reduced by primitives *) -> true
| _ -> false

let match_eval_ref env sigma constr stack =
  match EConstr.kind sigma constr with
  | Const (sp, u) ->
     reduction_effect_hook env sigma sp
        (lazy (EConstr.to_constr sigma (applist (constr,stack))));
     if is_evaluable env (EvalConstRef sp) then Some (EvalConst sp, u) else None
  | Var id when is_evaluable env (EvalVarRef id) -> Some (EvalVar id, EInstance.empty)
  | Rel i -> Some (EvalRel i, EInstance.empty)
  | Evar ev -> Some (EvalEvar ev, EInstance.empty)
  | _ -> None

let match_eval_ref_value env sigma constr stack =
  match EConstr.kind sigma constr with
  | Const (sp, u) ->
     reduction_effect_hook env sigma sp
        (lazy (EConstr.to_constr sigma (applist (constr,stack))));
    if is_evaluable env (EvalConstRef sp) then
      let u = EInstance.kind sigma u in
      Some (EConstr.of_constr (constant_value_in env (sp, u)))
    else
      None
  | Proj (p, r, c) when not (Projection.unfolded p) ->
     if is_evaluable env (EvalProjectionRef (Projection.repr p)) then
       Some (mkProj (Projection.unfold p, r, c))
     else None
  | Var id when is_evaluable env (EvalVarRef id) ->
     env |> lookup_named id |> NamedDecl.get_value
  | Rel n ->
     env |> lookup_rel n |> RelDecl.get_value |> Option.map (Vars.lift n)
  | _ -> None

let push_app sigma (hd, stk as p) = match EConstr.kind sigma hd with
| App (hd, args) ->
  (hd, Array.fold_right (fun x accu -> x :: accu) args stk)
| _ -> p

let recargs behavior = function
  | EvalVar _ | EvalRel _ | EvalEvar _ -> None
  | EvalConst c -> ReductionBehaviour.get_from_db behavior c

let fix_recarg ((recindices,bodynum),_) stack =
  assert (0 <= bodynum && bodynum < Array.length recindices);
  let recargnum = Array.get recindices bodynum in
  try
    Some (recargnum, List.nth stack recargnum)
  with Failure _ ->
    None

let contract_projection env sigma f (p,r) ~npars (hd, args) =
  match EConstr.kind sigma hd with
  | Construct _ ->
    let proj_narg = npars + Projection.arg p in
    Reduced (List.nth args proj_narg)
  | CoFix cofix ->
    let cofix_def = contract_cofix env sigma f cofix in
    (* If the cofix_def does not reduce to a constructor, do we
       really want to say it is Reduced? Consider e.g.:
       CoInductive stream := cons { hd : bool; tl : stream }.
       CoFixpoint const (x : bool) := if x then cons x (const x) else cons x (const x).
       Eval simpl in fun x => (const x).(tl) *)
    Reduced (mkProj (p, r, applist(cofix_def, args)))
  | _ -> NotReducible

let rec beta_applist sigma accu c stk = match EConstr.kind sigma c, stk with
| Lambda (_, _, c), arg :: stk -> beta_applist sigma (arg :: accu) c stk
| _ -> Vars.substl accu c, stk

let whd_nothing_for_iota env sigma s =
  let rec whrec (x, stack as s) =
    match EConstr.kind sigma x with
      | Rel n ->
          let open Context.Rel.Declaration in
          (match lookup_rel n env with
             | LocalDef (_,body,_) -> whrec (Vars.lift n body, stack)
             | _ -> s)
      | Var id ->
          let open Context.Named.Declaration in
          (match lookup_named id env with
             | LocalDef (_,body,_) -> whrec (body, stack)
             | _ -> s)
      | Evar _ | Meta _ -> s
      | Const (const, u) ->
          let u = EInstance.kind sigma u in
          (match constant_opt_value_in env (const, u) with
             | Some  body -> whrec (EConstr.of_constr body, stack)
             | None -> s)
      | LetIn (_,b,_,c) -> whrec (beta_applist sigma [b] c stack)
      | Cast (c,_,_) -> whrec (c, stack)
      | App (f,cl)  -> whrec (f, Array.fold_right (fun c accu -> c :: accu) cl stack)
      | Lambda (na,t,c) ->
          (match stack with
             | a :: stack -> whrec (beta_applist sigma [a] c stack)
             | _ -> s)

      | x -> s
  in
  whrec s

(* The reductions that should be performed as part of the simpl and hnf tactic *)
let make_reds env behavior =
  let open RedFlags in
  let open ReductionBehaviour.Db in
  let simpl_never = all_never_unfold behavior in
  let transparent_state = Conv_oracle.get_transp_state (Environ.oracle env) in
  let transparent_state_never =
    { transparent_state with
      tr_cst = Cpred.diff transparent_state.tr_cst simpl_never
    }
  in
  let reds = no_red in
  let reds = red_add reds fDELTA in
  let reds = red_add reds fZETA in
  let reds = red_add reds fBETA in
  let reds = red_add_transparent reds transparent_state in
  let reds_never = red_add_transparent reds transparent_state_never in
  behavior, reds_never, reds

let rec descend cache env sigma target (ref,u) args =
  let c = reference_value cache env sigma ref u in
  if evaluable_reference_eq env sigma ref target then
    (c,args)
  else
    let c', lrest = whd_betalet_stack env sigma (applist (c, args)) in
    descend cache env sigma target (destEvalRefU sigma c') lrest

(* The reductions that should be performed as part of the simpl tactic,
  excluding symbols that have the NeverUnfold flag. *)
let make_simpl_reds env =
  make_reds env (ReductionBehaviour.Db.get ())

(* The reductions that should be performed as part of the hnf tactic *)
let make_hnf_reds env =
  make_reds env ReductionBehaviour.Db.empty

(* [red_elim_const] contracts iota/fix/cofix redexes hidden behind
   constants by keeping the name of the constants in the recursive calls;
   it fails if no redex is around *)

let rec red_elim_const infos env sigma ref u largs =
  let open ReductionBehaviour in
  let nargs = List.length largs in
  let* largs, unfold_anyway, unfold_nonelim, nocase =
    match recargs infos.red_behavior ref with
    | None -> Reduced (largs, false, false, false)
    | Some NeverUnfold -> NotReducible
    | Some (UnfoldWhen { nargs = Some n } | UnfoldWhenNoMatch { nargs = Some n })
      when nargs < n -> NotReducible
    | Some (UnfoldWhen { recargs = x::l } | UnfoldWhenNoMatch { recargs = x::l })
      when nargs <= List.fold_left max x l -> NotReducible
    | Some (UnfoldWhen { recargs; nargs = None }) ->
      let* params = reduce_params infos env sigma largs recargs in
      Reduced (params,
      false,
      false,
      false)
    | Some (UnfoldWhenNoMatch { recargs; nargs = None }) ->
      let* params = reduce_params infos env sigma largs recargs in
      Reduced (params,
      false,
      false,
      true)
    | Some (UnfoldWhen { recargs; nargs = Some n }) ->
      let is_empty = List.is_empty recargs in
      let* params = reduce_params infos env sigma largs recargs in
      Reduced (params,
      is_empty && nargs >= n,
      not is_empty && nargs >= n,
      false)
    | Some (UnfoldWhenNoMatch { recargs; nargs = Some n }) ->
      let is_empty = List.is_empty recargs in
      let* params = reduce_params infos env sigma largs recargs in
      Reduced (params,
      is_empty && nargs >= n,
      not is_empty && nargs >= n,
      true)
  in
  let ans = match compute_reference_elimination infos env sigma ref u with
    | EliminationCases (c,n) when nargs >= n ->
        let c', stack = whd_nothing_for_iota env sigma (c, largs) in
        let* ans = reduce_case infos env sigma (EConstr.destCase sigma c') in
        Reduced ((ans, stack), nocase)
    | EliminationProj (c,n) when nargs >= n ->
        let c', stack = whd_nothing_for_iota env sigma (c, largs) in
        let* ans = reduce_nested_projection infos env sigma c' in
        Reduced ((ans, stack), nocase)
    | EliminationFix {trigger_min_args; refolding_target; refolding_data}
      when nargs >= trigger_min_args ->
        let (_, midargs as s) = descend infos.constant_body_cache env sigma refolding_target (ref,u) largs in
        let d, stack = whd_nothing_for_iota env sigma s in
        let f = refolding_data, midargs in
        let* c = reduce_fix infos env sigma (Some f) (destFix sigma d) stack in
        Reduced (c, nocase)
    | NotAnElimination c when unfold_nonelim ->
        Reduced ((whd_betaiotazeta env sigma (applist (c, largs)), []), nocase)
    | _ -> NotReducible
  in
  match ans with
  | NotReducible when unfold_anyway ->
    let c = reference_value infos.constant_body_cache env sigma ref u in
    Reduced ((whd_betaiotazeta env sigma (applist (c, largs)), []), nocase)
  | _ -> ans

and reduce_params infos env sigma stack l =
  let len = List.length stack in
  let rec redp stack l = match l with
  | [] -> Reduced stack
  | i :: l ->
    if len <= i then NotReducible
    else
      let arg = List.nth stack i in
      let* rarg = whd_construct_stack infos env sigma arg in
      match EConstr.kind sigma (fst rarg) with
      | Construct _ | Int _ | Float _ | String _ | Array _ ->
        redp (List.assign stack i (applist rarg)) l
      | _ -> NotReducible
  in
  redp stack l

(* reduce to whd normal form or to an applied constant that does not hide
   a reducible iota/fix/cofix redex (the "simpl" tactic) *)

and whd_simpl_stack infos env sigma =
  let rec redrec s =
    let s' = push_app sigma s in
    let (x, stack) = s' in
    match EConstr.kind sigma x with
      | Lambda (na,t,c) ->
          (match stack with
             | [] -> s'
             | a :: rest -> redrec (beta_applist sigma [a] c rest))
      | LetIn (n,b,t,c) -> redrec (Vars.substl [b] c, stack)
      | App (f,cl) -> assert false (* see push_app above *)
      | Cast (c,_,_) -> redrec (c, stack)
      | Case (ci,u,pms,p,iv,c,lf) ->
        begin match reduce_case infos env sigma (ci,u,pms,p,iv,c,lf) with
        | Reduced c -> redrec (c, stack)
        | NotReducible -> s'
        end
      | Fix fix ->
        begin match reduce_fix infos env sigma None fix stack with
        | Reduced s' -> redrec s'
        | NotReducible -> s'
        end
      | Proj (p, r, c) ->
        let ans =
           let unf = Projection.unfolded p in
           if unf || is_evaluable env (EvalProjectionRef (Projection.repr p)) then
             let npars = Projection.npars p in
             match unf, ReductionBehaviour.get_from_db infos.red_behavior (Projection.constant p) with
              | false, Some NeverUnfold -> NotReducible
              | false, Some (UnfoldWhen { recargs } | UnfoldWhenNoMatch { recargs })
                when not (List.is_empty recargs) ->
                let l' = List.map_filter (fun i ->
                    let idx = (i - (npars + 1)) in
                    if idx < 0 then None else Some idx) recargs in
                let* stack = reduce_params infos env sigma stack l' in
                let* c = reduce_projection infos env sigma (p,r) ~npars c in
                Reduced (c, stack)
              | _ ->
                let* c = reduce_projection infos env sigma (p,r) ~npars c in
                Reduced (c, stack)
            else NotReducible
          in
          begin match ans with
          | Reduced s' -> redrec s'
          | NotReducible -> s'
          end

      | Const (cst, _) when is_primitive env cst ->
        let ans =
            let args =
              List.map_filter_i (fun i a ->
                  match a with CPrimitives.Kwhnf -> Some i | _ -> None)
                (CPrimitives.kind (Option.get (get_primitive env cst))) in
            let* stack = reduce_params infos env sigma stack args in
            Reduced (whd_const cst env sigma (applist (x, stack)), [])
        in
        begin match ans with
        | Reduced s' -> s'
        | NotReducible -> s'
        end

      | Const (cst, _) when is_symbol env cst ->
          whd_all env sigma (applist s'), []

      | _ ->
        match match_eval_ref env sigma x stack with
        | Some (ref, u) ->
          let ans =
             let* sapp, nocase = red_elim_const infos env sigma ref u stack in
             let hd, _ as s'' = redrec sapp in
             let rec is_case x = match EConstr.kind sigma x with
               | Lambda (_,_, x) | LetIn (_,_,_, x) | Cast (x, _,_) -> is_case x
               | App (hd, _) -> is_case hd
               | Case _ -> true
               | _ -> false in
               if nocase && is_case hd then NotReducible else Reduced s''
          in
          begin match ans with
          | Reduced s' -> s'
          | NotReducible -> s'
          end
        | None -> s'
  in
  redrec

and reduce_fix infos env sigma f fix stack =
  match fix_recarg fix stack with
  | None -> NotReducible
  | Some (recargnum,recarg) ->
    let* (recarg'hd,_ as recarg') = whd_construct_stack infos env sigma recarg in
    match EConstr.kind sigma recarg'hd with
    | Construct _ ->
      let stack' = List.assign stack recargnum (applist recarg') in
      Reduced (contract_fix env sigma f fix, stack')
    | _ -> NotReducible

and reduce_nested_projection infos env sigma c =
  let rec redrec c =
    match EConstr.kind sigma c with
    | Proj (p, r, c) ->
      let c' = match redrec c with NotReducible -> c | Reduced c -> c in
      let npars = Projection.npars p in
      reduce_projection infos env sigma (p,r) ~npars c'
    | Case (n,u,pms,p,iv,c,brs) ->
      let* c' = redrec c in
      let p = (n,u,pms,p,iv,c',brs) in
      begin match reduce_case infos env sigma p with
      | Reduced c -> Reduced c
      | NotReducible -> Reduced (mkCase p) (* Why not NotReducible *)
      end
    | _ -> NotReducible
  in redrec c

and reduce_projection infos env sigma p ~npars c =
  let* f, s = whd_construct infos env sigma (c, []) in
  contract_projection env sigma f p ~npars s

and reduce_case infos env sigma (ci, u, pms, p, iv, c, lf) =
  let* f, (hd, args) = whd_construct infos env sigma (c, []) in
  match EConstr.kind sigma hd with
  | Construct ((_, i as cstr),u) ->
    let real_cargs = List.skipn ci.ci_npar args in
    let br = lf.(i - 1) in
    let ctx = EConstr.expand_branch env sigma u pms cstr br in
    let br = it_mkLambda_or_LetIn (snd br) ctx in
    Reduced (applist (br, real_cargs))
  | CoFix (bodynum,(names,_,_) as cofix) ->
    let cofix_def = contract_cofix env sigma f cofix in
    (* If the cofix_def does not reduce to a constructor, do we
       really want to say it is Reduced? Consider e.g.:
       CoInductive stream := cons { hd : bool; tl : stream }.
       CoFixpoint const (x : bool) := if x then cons x (const x) else cons x (const x).
       Eval simpl in fun x => (const x).(tl) *)
    Reduced (mkCase (ci, u, pms, p, iv, applist(cofix_def, args), lf))
  | Int _ | Float _ | String _ | Array _ -> NotReducible (* TODO: assert false? *)
  | _ -> assert false

and whd_construct_stack infos env sigma s =
  let* _, s = whd_construct infos env sigma (s, []) in
  Reduced s

(* reduce until finding an applied constructor (or primitive value) or fail *)

and whd_construct infos env sigma c =
  let (constr, cargs) =
    let construct_infos = { infos with red_behavior = ReductionBehaviour.Db.empty; main_reds = infos.construct_reds } in
    whd_simpl_stack construct_infos env sigma c in
  match match_eval_ref env sigma constr cargs with
  | Some (ref, u) ->
    (match compute_reference_coelimination infos env sigma ref u with
     | CoEliminationConstruct c -> Reduced (None, whd_stack_gen infos.main_reds env sigma (applist (c, cargs)))
     | CoEliminationPrimitive c -> Reduced (None, whd_stack_gen infos.main_reds env sigma (applist (c, cargs)))
     | CoEliminationCoFix {refolding_target; refolding_data} ->
        let (_, midargs as s) = descend infos.constant_body_cache env sigma refolding_target (ref,u) cargs in
        let s = whd_nothing_for_iota env sigma s in
        let f = refolding_data, midargs in
        Reduced (Some f, s)
     | NotACoElimination c ->
       (* Now try to get a construct/cofix/prim using the arguments of the constant
          so that possible internal iota-redexes are triggered *)
       whd_construct infos env sigma (c, cargs)
     | NotACoEliminationConstant -> NotReducible)
  | None ->
    if reducible_construct sigma constr then Reduced (None, (constr, cargs))
    else NotReducible

(************************************************************************)
(*            Special Purpose Reduction Strategies                     *)

(* Red reduction tactic: one step of delta reduction + full
   beta-iota-fix-cofix-zeta-cast at the head of the conclusion of a
   sequence of products; fails if no delta redex is around
*)

let try_red_product env sigma c =
  let simpfun c = clos_norm_flags RedFlags.betaiotazeta env sigma c in
  let cache = CacheTable.create 12 in
  let rec redrec env x =
    let x = whd_betaiota env sigma x in
    match EConstr.kind sigma x with
      | App (f,l) ->
          (match EConstr.kind sigma f with
             | Fix fix ->
                 (match fix_recarg fix (Array.to_list l) with
                    | None -> NotReducible
                    | Some (recargnum,recarg) ->
                        let* recarg' = redrec env recarg in
                        let l = Array.copy l in
                        let () = Array.set l recargnum recarg' in
                        Reduced (simpfun (mkApp (f, l))))
             | _ ->
              let* r = redrec env f in
              Reduced (simpfun (mkApp (r, l))))
      | Cast (c,_,_) -> redrec env c
      | Prod (x,a,b) ->
          let open Context.Rel.Declaration in
          let* b = redrec (push_rel (LocalAssum (x, a)) env) b in
          Reduced (mkProd (x, a, b))
      | LetIn (x,a,b,t) -> redrec env (Vars.subst1 a t)
      | Case (ci,u,pms,p,iv,d,lf) ->
        let* d = redrec env d in
        Reduced (simpfun (mkCase (ci,u,pms,p,iv,d,lf)))
      | Proj (p, r, c) ->
        let* c' =
          match EConstr.kind sigma c with
          | Construct _ | CoFix _ -> Reduced c
          | _ -> redrec env c
        in
        let npars = Projection.npars p in
        let* c = contract_projection env sigma None (p,r) ~npars (whd_betaiotazeta_stack env sigma c') in
        Reduced (simpfun c)
      | _ ->
        (match match_eval_ref env sigma x [] with
        | Some (ref, u) ->
          (* TO DO: re-fold fixpoints after expansion *)
          (* to get true one-step reductions *)
          (match reference_opt_value cache env sigma ref u with
             | None -> NotReducible
             | Some c -> Reduced c)
        | _ -> NotReducible)
  in redrec env c

let red_product env sigma c = match try_red_product env sigma c with
| Reduced c -> Some c
| NotReducible -> None

(*
(* This old version of hnf uses betadeltaiota instead of itself (resp
   whd_construct_state) to reduce the argument of Case (resp Fix);
   The new version uses the "simpl" strategy instead. For instance,

   Variable n:nat.
   Eval hnf in match (plus (S n) O) with S n => n | _ => O end.

   returned

   (fix plus (n m : nat) {struct n} : nat :=
        match n with
        | O => m
        | S p => S (plus p m)
        end) n 0

   while the new version returns (plus n O)
 *)

let whd_simpl_orelse_delta_but_fix_old env sigma c =
  let whd_all = whd_all_state env sigma in
  let rec redrec (x, stack as s) =
    match kind_of_term x with
      | Lambda (na,t,c) ->
          (match decomp_stack stack with
             | None      -> s
             | Some (a,rest) -> stacklam redrec [a] c rest)
      | LetIn (n,b,t,c) -> stacklam redrec [b] c stack
      | App (f,cl)   -> redrec (f, append_stack cl stack)
      | Cast (c,_,_) -> redrec (c, stack)
      | Case (ci,p,d,lf) ->
          (try
             redrec (reduce_case env sigma whd_all (ci,p,d,lf), stack)
           with Redelimination ->
             s)
      | Fix fix ->
          (match reduce_fix whd_all fix stack with
             | Reduced s' -> redrec s'
             | NotReducible -> s)
      | _ when isEvalRef env x ->
          let ref = destEvalRef x in
          (try
            redrec (red_elim_const env sigma ref stack)
           with Redelimination ->
             match reference_opt_value env sigma ref with
               | Some c ->
                   (match kind_of_term (strip_lam c) with
                     | CoFix _ | Fix _ -> s
                     | _ -> redrec (c, stack))
               | None -> s)
      | _ -> s
  in app_stack (redrec (c, empty_stack))
*)

(* Same as [whd_simpl] but also reduces constants that do not hide a
   reducible fix, but does this reduction of constants only until it
   immediately hides a non reducible fix or a cofix *)

let whd_simpl_orelse_delta_but_fix env sigma c =
  let infos = make_simpl_infos (make_hnf_reds env) in
  let rec redrec s =
    let (constr, stack as s') = whd_simpl_stack infos env sigma s in
    match match_eval_ref_value env sigma constr stack with
    | Some c ->
      (match EConstr.kind sigma (snd (decompose_lambda sigma c)) with
      | CoFix _ | Fix _ -> s'
      | Proj (p,_,t) when
          (match EConstr.kind sigma constr with
          | Const (c', _) -> QConstant.equal env (Projection.constant p) c'
          | _ -> false) ->
        let npars = Projection.npars p in
          if List.length stack <= npars then
            (* Do not show the eta-expanded form *)
            s'
          else redrec (c, stack)
      | _ -> redrec (c, stack))
    | None -> s'
  in
  applist (redrec c)

let hnf_constr0 env sigma c =
  whd_simpl_orelse_delta_but_fix env sigma (c, [])

let hnf_constr env sigma c =
  let c = whd_simpl_orelse_delta_but_fix env sigma (c, []) in
  clos_norm_flags RedFlags.betaiota env sigma c

(* The "simpl" reduction tactic *)

let whd_simpl_with_reds infos env sigma c =
  applist (whd_simpl_stack infos env sigma (c, []))

let whd_simpl env sigma x =
  let infos = make_simpl_infos (make_simpl_reds env) in
  whd_simpl_with_reds infos env sigma x

let simpl env sigma c =
  let infos = make_simpl_infos (make_simpl_reds env) in
  let rec strongrec env t =
    map_constr_with_full_binders env sigma push_rel strongrec env
      (whd_simpl_with_reds infos env sigma t) in
  strongrec env c

(* Reduction at specific subterms *)

let matches_head env sigma c t =
  let t, l = decompose_app sigma t in
  match EConstr.kind sigma t, Array.is_empty l with
    | Proj (p, _, _), _ -> Constr_matching.matches env sigma c (mkConstU (Projection.constant p, EInstance.empty))
    | _, false -> Constr_matching.matches env sigma c t
    | _ -> raise Constr_matching.PatternMatchingFailure

(** FIXME: Specific function to handle projections: it ignores what happens on the
    parameters. This is a temporary fix while rewrite etc... are not up to equivalence
    of the projection and its eta expanded form.
*)
let change_map_constr_with_binders_left_to_right changed g f (env, l as acc) sigma c =
  match EConstr.kind sigma c with
  | Proj (p, r, v) -> (* Treat specially for partial applications *)
    let t = Retyping.expand_projection env sigma p v [] in
    let hdf, al = destApp sigma t in
    let a = al.(Array.length al - 1) in
    let app = (mkApp (hdf, Array.sub al 0 (Array.length al - 1))) in
    let app' = f acc app in
    let a' = f acc a in
    let hdf', _ = decompose_app sigma app' in
    if hdf' == hdf then
      (* Still the same projection, we ignore the change in parameters *)
      mkProj (p, r, a')
    else
      let () = changed := true in
      mkApp (app', [| a' |])
  | _ -> map_constr_with_binders_left_to_right env sigma g f acc c

let e_contextually byhead (occs,c) f = begin fun env sigma t ->
  let count = ref (Locusops.initialize_occurrence_counter occs) in
  (* FIXME: we do suspicious things with this evarmap *)
  let evd = ref sigma in
  let changed = ref false in
  let rec traverse nested (env,c as envc) t =
    if Locusops.occurrences_done !count then (* Shortcut *) t
    else
    try
      let subst =
        if byhead then matches_head env sigma c t
        else Constr_matching.matches env sigma c t in
      let ok, count' = Locusops.update_occurrence_counter !count in count := count';
      if ok then begin
        if Option.has_some nested then
          user_err Pp.(str "The subterm at occurrence " ++ int (Option.get nested) ++ str " overlaps with the subterm at occurrence " ++ int (Locusops.current_occurrence !count) ++ str ".");
        (* Skip inner occurrences for stable counting of occurrences *)
        let () = if Locusops.more_specific_occurrences !count then
          ignore (traverse_below (Some (Locusops.current_occurrence !count)) envc t)
        in
        match (f subst) env !evd t with
        | NoChange -> t
        | Changed (evm, t) ->
          let () = changed := true in
          let () = evd := evm in
          t
      end
      else
        traverse_below nested envc t
    with Constr_matching.PatternMatchingFailure ->
      traverse_below nested envc t
  and traverse_below nested envc t =
    (* when byhead, find other occurrences without matching again partial
       application with same head *)
    match EConstr.kind !evd t with
    | App (f,l) when byhead -> mkApp (f, Array.map_left (traverse nested envc) l)
    | Proj (p,r,c) when byhead -> mkProj (p,r,traverse nested envc c)
    | _ ->
        change_map_constr_with_binders_left_to_right changed
          (fun d (env,c) -> (push_rel d env, Patternops.lift_pattern 1 c))
          (traverse nested) envc sigma t
  in
  let t' = traverse None (env,c) t in
  let () = Locusops.check_used_occurrences !count in
  if !changed then Changed (!evd, t') else NoChange
  end

let contextually byhead occs f env sigma t =
  let f' subst env sigma t = Changed (sigma, f subst env sigma t) in
  match e_contextually byhead occs f' env sigma t with
  | Changed (_, t) -> t
  | NoChange -> t

(* linear bindings (following pretty-printer) of the value of name in c.
 * n is the number of the next occurrence of name.
 * ol is the occurrence list to find. *)

let match_constr_evaluable_ref env sigma c evref =
  match EConstr.kind sigma c, evref with
  | Const (c,u), Evaluable.EvalConstRef c' when QConstant.equal env c c' -> Some u
  | Proj (p,_,_), Evaluable.EvalProjectionRef p' when QProjection.Repr.equal env (Projection.repr p) p' -> Some EInstance.empty
  | Var id, Evaluable.EvalVarRef id' when Id.equal id id' -> Some EInstance.empty
  | _, _ -> None

let substlin env sigma evalref occs c =
  let count = ref (Locusops.initialize_occurrence_counter occs) in
  let value u = value_of_evaluable_ref env evalref u in
  let rec substrec () c =
    if Locusops.occurrences_done !count then c
    else
      match match_constr_evaluable_ref env sigma c evalref with
      | Some u ->
        let ok, count' = Locusops.update_occurrence_counter !count in
        count := count';
        if ok then value u else c
      | None ->
        map_constr_with_binders_left_to_right env sigma
          (fun _ () -> ())
          substrec () c
  in
  let t' = substrec () c in
  Locusops.check_used_occurrences !count;
  (Locusops.current_occurrence !count, t')

let string_of_evaluable_ref env = function
  | Evaluable.EvalVarRef id -> Id.to_string id
  | Evaluable.EvalConstRef kn ->
      Libnames.string_of_qualid
        (Nametab.shortest_qualid_of_global (vars_of_env env) (GlobRef.ConstRef kn))
  | Evaluable.EvalProjectionRef p ->
      Projection.Repr.to_string p

(* Removing fZETA for finer behaviour would break many developments *)
let unfold_side_flags = RedFlags.[fBETA;fMATCH;fFIX;fCOFIX;fZETA]
let unfold_side_red = RedFlags.(mkflags [fBETA;fMATCH;fFIX;fCOFIX;fZETA])
let unfold_red kn =
  let open RedFlags in
  let flags = fDELTA :: unfold_side_flags in
  let flags = match kn with
    | Evaluable.EvalVarRef id -> fVAR id :: flags
    | Evaluable.EvalConstRef sp ->
      begin
        match Structures.PrimitiveProjections.find_opt sp with
        | None -> fCONST sp :: flags
        | Some p -> fCONST sp :: fPROJ p :: flags
      end
    | Evaluable.EvalProjectionRef p ->
      fPROJ p :: fCONST (Projection.Repr.constant p) :: flags
  in
  mkflags flags

let unfold env sigma name c =
  if is_evaluable env name then
    clos_norm_flags (unfold_red name) env sigma c
  else
    user_err Pp.(str (string_of_evaluable_ref env name^" is opaque."))

(* [unfoldoccs : (readable_constraints -> (int list * full_path) -> constr -> constr)]
 * Unfolds the constant name in a term c following a list of occurrences occl.
 * at the occurrences of occ_list. If occ_list is empty, unfold all occurrences.
 * Performs a betaiota reduction after unfolding. *)
let unfoldoccs env sigma (occs,name) c =
  let open Locus in
  match occs with
  | NoOccurrences -> c
  | AllOccurrences -> unfold env sigma name c
  | OnlyOccurrences _ | AllOccurrencesBut _ | AtLeastOneOccurrence ->
    let (occ,uc) = substlin env sigma name occs c in
    if Int.equal occ 0 then
      user_err Pp.(str ((string_of_evaluable_ref env name)^" does not occur."));
    nf_betaiotazeta env sigma uc

(* Unfold reduction tactic: *)
let unfoldn loccname env sigma c =
  List.fold_left (fun c occname -> unfoldoccs env sigma occname c) c loccname

(* Re-folding constants tactics: refold com in term c *)
let fold_one_com com env sigma c =
  let rcom = match red_product env sigma com with
  | None -> user_err Pp.(str "No head constant to reduce.")
  | Some c -> c
  in
  (* Reason first on the beta-iota-zeta normal form of the constant as
     unfold produces it, so that the "unfold f; fold f" configuration works
     to refold fix expressions *)
  let a = subst_term sigma (clos_norm_flags unfold_side_red env sigma rcom) c in
  if not (EConstr.eq_constr sigma a c) then
    Vars.subst1 com a
  else
    (* Then reason on the non beta-iota-zeta form for compatibility -
       even if it is probably a useless configuration *)
    let a = subst_term sigma rcom c in
    Vars.subst1 com a

let fold_commands cl env sigma c =
  List.fold_right (fun com c -> fold_one_com com env sigma c) (List.rev cl) c


(* call by value reduction functions *)
let cbv_norm_flags flags ~strong env sigma t =
  Cbv.(cbv_norm (create_cbv_infos flags ~strong env sigma) t)

let cbv_beta = cbv_norm_flags RedFlags.beta ~strong:true
let cbv_betaiota = cbv_norm_flags RedFlags.betaiota ~strong:true
let cbv_betadeltaiota env sigma = cbv_norm_flags RedFlags.all env sigma ~strong:true
let whd_cbv_betadeltaiota env sigma = cbv_norm_flags RedFlags.all env sigma ~strong:false

let whd_compute = whd_cbv_betadeltaiota
let compute = cbv_betadeltaiota

(* Pattern *)

(* gives [na:ta]c' such that c converts to ([na:ta]c' a), abstracting only
 * the specified occurrences. *)

let abstract_scheme env (locc,a) (c, sigma) =
  let ta = Retyping.get_type_of env sigma a in
  let r = Retyping.relevance_of_term env sigma a in
  let sigma, ta = Evarsolve.refresh_universes ~onlyalg:true (Some false) env sigma ta in
  let na = Namegen.named_hd env sigma ta Anonymous in
  let na = make_annot na r in
  if occur_meta sigma ta then user_err Pp.(str "Cannot find a type for the generalisation.");
  if occur_meta sigma a then
    mkLambda (na,ta,c), sigma
  else
    let c', sigma = Find_subterm.subst_closed_term_occ env sigma (Locus.AtOccs locc) a c in
      mkLambda (na,ta,c'), sigma

let pattern_occs loccs_trm = begin fun env sigma c ->
  let abstr_trm, sigma = List.fold_right (abstract_scheme env) loccs_trm (c,sigma) in
  try
    let sigma, _ = Typing.type_of env sigma abstr_trm in
    Changed (sigma, applist(abstr_trm, List.map snd loccs_trm)) (* TODO: fast path *)
  with Type_errors.TypeError (env',t) ->
    raise (ReductionTacticError (InvalidAbstraction (env,sigma,abstr_trm,(env',t))))
  end

(* Used in several tactics. *)

let check_privacy env ind =
  let spec = Inductive.lookup_mind_specif env ind in
  if Inductive.is_private spec then
    user_err Pp.(str "case analysis on a private type.")

(* put t as t'=(x1:A1)..(xn:An)B with B an inductive definition of name name
   return name, B and t' *)

let reduce_to_ind_gen allow_product env sigma t =
  let rec elimrec env t l =
    let t = hnf_constr0 env sigma t in
    match EConstr.kind sigma (fst (decompose_app sigma t)) with
      | Ind (ind, _ as indu) ->
        let t = nf_betaiota env sigma t in
        check_privacy env ind; (Some indu, it_mkProd_or_LetIn t l)
      | Prod (n,ty,t') ->
          let open Context.Rel.Declaration in
          if allow_product then
            let ty = nf_betaiota env sigma ty in
            elimrec (push_rel (LocalAssum (n,ty)) env) t' ((LocalAssum (n,ty))::l)
          else
            None, it_mkProd_or_LetIn t l
      | _ ->
          (* Last chance: we allow to bypass the Opaque flag (as it
             was partially the case between V5.10 and V8.1 *)
          let t' = whd_all env sigma t in
          match EConstr.kind sigma (fst (decompose_app sigma t')) with
            | Ind (ind, _ as indu) -> check_privacy env ind; (Some indu, it_mkProd_or_LetIn t' l)
            | _ -> None, it_mkProd_or_LetIn t l

  in
  elimrec env t []

let reduce_to_quantified_ind env sigma c =
  match reduce_to_ind_gen true env sigma c with
  | None, _ -> user_err Pp.(str"Not an inductive definition.")
  | Some i, t -> i, t
let reduce_to_atomic_ind env sigma c =
  match reduce_to_ind_gen false env sigma c with
  | None, _ -> user_err Pp.(str"Not an inductive definition.")
  | Some i, t -> i, t

let eval_to_quantified_ind env sigma t =
  let rec elimrec env t =
    let t = hnf_constr0 env sigma t in
    match EConstr.kind sigma (fst (decompose_app sigma t)) with
      | Ind (ind, _ as indu) ->
        let () = check_privacy env ind in
        indu
      | Prod (n,ty,t') ->
        elimrec (push_rel (Context.Rel.Declaration.LocalAssum (n,ty)) env) t'
      | _ ->
          (* Last chance: we allow to bypass the Opaque flag (as it
             was partially the case between V5.10 and V8.1 *)
          let t' = whd_all env sigma t in
          match EConstr.kind sigma (fst (decompose_app sigma t')) with
            | Ind (ind, _ as indu) -> check_privacy env ind; indu
            | _ -> user_err Pp.(str"Not an inductive product.")
  in
  elimrec env t

let find_hnf_rectype env sigma t =
  let ind,t = reduce_to_atomic_ind env sigma t in
  ind, snd (decompose_app_list sigma t)

(* Reduce the weak-head redex [beta,iota/fix/cofix[all],cast,zeta,simpl/delta]
   or raise [NotStepReducible] if not a weak-head redex *)

exception NotStepReducible

let one_step_reduce env sigma c =
  let infos = make_simpl_infos (ReductionBehaviour.Db.empty, RedFlags.betadeltazeta, RedFlags.betadeltazeta) in
  let rec redrec (x, stack) =
    match EConstr.kind sigma x with
      | Lambda (n,t,c)  ->
          (match stack with
             | []        -> raise NotStepReducible
             | a :: rest -> (Vars.subst1 a c, rest))
      | App (f,cl) -> redrec (f, (Array.to_list cl)@stack)
      | LetIn (_,f,_,cl) -> (Vars.subst1 f cl,stack)
      | Cast (c,_,_) -> redrec (c,stack)
      | Case (ci,u,pms,p,iv,c,lf) ->
        begin match reduce_case infos env sigma (ci,u,pms,p,iv,c,lf) with
        | Reduced c -> (c, stack)
        | NotReducible -> raise NotStepReducible
        end
      | Fix fix ->
        begin match reduce_fix infos env sigma None fix stack with
        | Reduced s' -> s'
        | NotReducible -> raise NotStepReducible
        end
      (* Why not treating Proj? *)
      | _ when isEvalRef env sigma x ->
          let ref,u = destEvalRefU sigma x in
          begin match red_elim_const infos env sigma ref u stack with
          | Reduced (c, _) -> c
          | NotReducible ->
             match reference_opt_value infos.constant_body_cache env sigma ref u with
               | Some d -> (d, stack)
               | None -> raise NotStepReducible
          end

      | _ -> raise NotStepReducible
  in
  applist (redrec (c,[]))

let error_cannot_recognize ref =
  user_err
    Pp.(str "Cannot recognize a statement based on " ++
        Nametab.pr_global_env Id.Set.empty ref ++ str".")

let reduce_to_ref_gen allow_failure allow_product env sigma ref t =
  match ref with
  | GlobRef.IndRef mind' ->
    let (i,t) = reduce_to_ind_gen allow_product env sigma t in
    if allow_failure then t else
      (match i with
       | Some (mind,u) when QInd.equal env mind mind' -> t
       | _ -> error_cannot_recognize ref)
  | _ -> (* lazily reduces to match the head of [t] with the expected [ref] *)
    let rec elimrec env t l =
      let c, _ = decompose_app sigma t in
      match EConstr.kind sigma c with
      | Prod (n,ty,t') ->
        if allow_product then
          let open Context.Rel.Declaration in
          elimrec (push_rel (LocalAssum (n,ty)) env) t' ((LocalAssum (n,ty))::l)
        else if allow_failure then
          it_mkProd_or_LetIn t l
        else
          error_cannot_recognize ref
      | _ ->
        if isRefX env sigma ref c
        then it_mkProd_or_LetIn t l
        else
          try
            let t' = nf_betaiota env sigma (one_step_reduce env sigma t) in
            elimrec env t' l
          with NotStepReducible ->
            if allow_failure then
              it_mkProd_or_LetIn t l
            else
              error_cannot_recognize ref
    in
    elimrec env t []

let reduce_to_quantified_ref ?(allow_failure=false) = reduce_to_ref_gen allow_failure true
let reduce_to_atomic_ref ?(allow_failure=false) = reduce_to_ref_gen allow_failure false
