(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

let error_not_evaluable r = raise (NotEvaluableRef r)

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

let evaluable_reference_eq sigma r1 r2 = match r1, r2 with
| EvalConst c1, EvalConst c2 -> Constant.CanOrd.equal c1 c2
| EvalVar id1, EvalVar id2 -> Id.equal id1 id2
| EvalRel i1, EvalRel i2 -> Int.equal i1 i2
| EvalEvar (e1, ctx1), EvalEvar (e2, ctx2) ->
  EConstr.eq_constr sigma (mkEvar (e1, ctx1)) (mkEvar (e2, ctx2))
| _ -> false

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
  | Const (cst,_) -> is_evaluable env (EvalConstRef cst) && TransparentState.is_transparent_constant ts cst
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

let reference_opt_value env sigma eval u =
  match eval with
  | EvalConst cst ->
    let u = EInstance.kind sigma u in
    Option.map EConstr.of_constr (constant_opt_value_in env (cst,u))
  | EvalVar id ->
      env |> lookup_named id |> NamedDecl.get_value
  | EvalRel n ->
      env |> lookup_rel n |> RelDecl.get_value |> Option.map (Vars.lift n)
  | EvalEvar ev ->
    match EConstr.kind sigma (mkEvar ev) with
    | Evar _ -> None
    | c -> Some (EConstr.of_kind c)

exception NotEvaluable
let reference_value env sigma c u =
  match reference_opt_value env sigma c u with
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

type constant_evaluation =
  | EliminationFix of fix_evaluation_data
  | EliminationCases of int
  | EliminationProj of int
  | NotAnElimination

(* We use a cache registered as a global table *)

type frozen = constant_evaluation Cmap.t

let eval_table = Summary.ref (Cmap.empty : frozen) ~name:"evaluation"

(* [compute_consteval] determines whether f is an "elimination constant"

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

let compute_fix_reversibility sigma labs args fix =
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
               (k, List.nth labs (k-1))
             else
               raise Elimconst
         | _ ->
             raise Elimconst) args in
  let reversible_rels = List.map fst typed_reversible_args in
  if not (List.distinct_f Int.compare reversible_rels) then
    raise Elimconst;
  (* Lambda's that are not used should not depend on those that are
     used and that will thus be different in the recursive calls *)
  List.iteri (fun i t_i ->
    if not (Int.List.mem (i+1) reversible_rels) then
      let fvs = List.map ((+) (i+1)) (Int.Set.elements (free_rels sigma t_i)) in
      match List.intersect Int.equal fvs reversible_rels with
      | [] -> ()
      | _ -> raise Elimconst)
    labs;
  typed_reversible_args, nlam, nargs

let check_fix_reversibility env sigma ref u labs args minarg refs ((lv,i),_ as fix) =
  let li, nlam, nargs = compute_fix_reversibility sigma labs args (mkFix fix) in
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
      EliminationFix {
        trigger_min_args = max minarg nlam;
        refolding_target = ref;
        refolding_data;
        }
  else
    EliminationFix {
        trigger_min_args = max minarg (nlam - nargs + k + 1);
        refolding_target = ref;
        refolding_data;
        }

let compute_fix_wrapper allowed_reds env sigma ref u =
  try match reference_opt_value env sigma ref u with
    | None -> None
    | Some c ->
      let labs, ccl = whd_decompose_lambda env sigma c in
      let c, l = whd_stack_gen allowed_reds env sigma ccl in
      let labs = List.map snd labs in
      assert (isFix sigma c);
      Some (labs, l)
  with Not_found (* Undefined ref *) -> None

(* Heuristic to look if global names are associated to other
   components of a mutual fixpoint *)

let invert_names allowed_reds env sigma ref u names i =
  let labs, l =
    match compute_fix_wrapper allowed_reds env sigma ref u with
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
          match compute_fix_wrapper allowed_reds env sigma ref u with
          | None -> None
          | Some (labs', l') ->
              let eq_constr c1 c2 = EConstr.eq_constr sigma c1 c2 in
              if List.equal eq_constr labs' labs &&
                 List.equal eq_constr l l' then Some (ref, u)
              else None in
  labs, l, Array.init (Array.length names) make_name

let deactivate_delta allowed_reds =
  (* Act both on Delta and transparent state as not all reduction functions work the same *)
  RedFlags.(red_add_transparent (red_sub allowed_reds fDELTA) TransparentState.empty)

(* [compute_consteval] stepwise expands an arbitrary long sequence of
    reversible constants, eventually refolding to the initial constant
    for unary fixpoints and to the last constant encapsulating the Fix
    for mutual fixpoints *)

let compute_consteval allowed_reds env sigma ref u =
  let allowed_reds_no_delta = deactivate_delta allowed_reds in
  let rec srec env all_abs lastref lastu onlyproj c =
    let c', args = whd_stack_gen allowed_reds_no_delta env sigma c in
    (* We now know that the initial [ref] evaluates to [fun all_abs => c' args] *)
    (* and that the last visited name in the evaluation is [lastref] *)
    match EConstr.kind sigma c' with
      | Lambda (id,t,g) when not onlyproj ->
          assert (List.is_empty args);
          let open Context.Rel.Declaration in
          srec (push_rel (LocalAssum (id,t)) env) (t::all_abs) lastref lastu onlyproj g
      | Fix ((lv,i),(names,_,_) as fix) when not onlyproj ->
          let n_all_abs = List.length all_abs in
          let nbfix = Array.length lv in
          (if nbfix = 1 then
            (* Try to refold to [ref] *)
            let names = [|Some (ref,u)|] in
            try check_fix_reversibility env sigma ref u all_abs args n_all_abs names fix
            with Elimconst -> NotAnElimination
          else
            (* Try to refold to [lastref] *)
            let last_labs, last_args, names = invert_names allowed_reds env sigma lastref lastu names i in
            try check_fix_reversibility env sigma lastref lastu last_labs last_args n_all_abs names fix
            with Elimconst -> NotAnElimination)
      | Case (_,_,_,_,_,d,_) when isRel sigma d && not onlyproj -> EliminationCases (List.length all_abs)
      | Case (_,_,_,_,_,d,_) -> srec env all_abs lastref lastu true d
      | Proj (p, _, d) when isRel sigma d -> EliminationProj (List.length all_abs)
      | _ when isTransparentEvalRef env sigma (RedFlags.red_transparent allowed_reds) c' ->
          (* Continue stepwise unfolding from [c' args] *)
          let ref, u = destEvalRefU sigma c' in
          (match reference_opt_value env sigma ref u with
            | None -> NotAnElimination (* e.g. if a rel *)
            | Some c -> srec env all_abs ref u onlyproj (applist (c, args)))
      | _ -> NotAnElimination
  in
  match reference_opt_value env sigma ref u with
    | None -> NotAnElimination
    | Some c -> srec env [] ref u false c

let reference_eval allowed_reds env sigma ref u =
  match ref with
  | EvalConst cst as ref when EInstance.is_empty u ->
      (try
         Cmap.find cst !eval_table
       with Not_found -> begin
         let v = compute_consteval allowed_reds env sigma ref u in
         eval_table := Cmap.add cst v !eval_table;
         v
       end)
  | ref -> compute_consteval allowed_reds env sigma ref u

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

let contract_fix env sigma f
  ((recindices,bodynum),(_names,_types,bodies as typedbodies) as fixp) = match f with
| None -> contract_fix sigma fixp
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
  | None -> mkFix((recindices,i),typedbodies)
  | Some (ref, u) ->
      let body = applist (mkEvalRef ref u, la) in
      List.fold_left_i (fun q (* j = n+1-q *) c (ij,tij) ->
          let subst = List.map (Vars.lift (-q)) (List.firstn (n-ij) la) in
          let tij' = Vars.substl (List.rev subst) tij in
          let x = make_annot xname Sorts.Relevant in  (* TODO relevance *)
          mkLambda_with_eta sigma x tij' c)
          1 body (List.rev lv)
  in
  let nbodies = Array.length recindices in
  let lbodies = List.init nbodies make_Fi in
  let c = substl_with_function (List.rev lbodies) sigma (nf_beta env sigma bodies.(bodynum)) in
  nf_beta env sigma c

let contract_cofix env sigma f
  (bodynum,(names,_,bodies as typedbodies) as fixp) args = match f with
| None -> contract_cofix sigma fixp
| Some f ->
  let make_Fi i =
    let cofix = mkCoFix (i,typedbodies) in
    match f with
    | EvalConst kn, u ->
      begin
        if Int.equal i bodynum then mkConstU (kn, u)
        else match names.(i).binder_name with
          | Anonymous -> cofix
          | Name id ->
              (* In case of a call to another component of a block of
                  mutual inductive, try to reuse the global name if
                  the block was indeed initially built as a global
                  definition *)
              let kn = Constant.change_label kn (Label.of_id id) in
              let cst = (kn, EInstance.kind sigma u) in
              try match constant_opt_value_in env cst with
                | None -> cofix
                    (* TODO: check kn is correct *)
                | Some _ -> mkConstU (kn, u)
              with Not_found -> cofix
      end
    | _ ->
      cofix in
  let nbodies = Array.length bodies in
  let subbodies = List.init nbodies make_Fi in
  substl_with_function (List.rev subbodies)
    sigma (nf_beta env sigma bodies.(bodynum))

let reducible_construct sigma c = match EConstr.kind sigma c with
| Construct _ | CoFix _ (* reduced by case *)
| Int _ | Float _ | Array _ (* reduced by primitives *) -> true
| _ -> false

let reduce_mind_case env sigma f (ci, u, pms, p, iv, (hd, args), lf) =
  match EConstr.kind sigma hd with
    | Construct ((_, i as cstr),u) ->
        let real_cargs = List.skipn ci.ci_npar args in
        let br = lf.(i - 1) in
        let ctx = EConstr.expand_branch env sigma u pms cstr br in
        let br = it_mkLambda_or_LetIn (snd br) ctx in
        Reduced (applist (br, real_cargs))
    (* TODO, consider the case of lambdas in front of the CoFix ?? *)
    | CoFix (bodynum,(names,_,_) as cofix) ->
        let cofix_def = contract_cofix env sigma f cofix args in
        Reduced (mkCase (ci, u, pms, p, iv, applist(cofix_def, args), lf))
    | Int _ | Float _ | Array _ -> NotReducible
    | _ -> assert false


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
     if is_evaluable env (EvalConstRef (Projection.constant p)) then
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

let recargs = function
  | EvalVar _ | EvalRel _ | EvalEvar _ -> None
  | EvalConst c -> ReductionBehaviour.get c

let fix_recarg ((recindices,bodynum),_) stack =
  assert (0 <= bodynum && bodynum < Array.length recindices);
  let recargnum = Array.get recindices bodynum in
  try
    Some (recargnum, List.nth stack recargnum)
  with Failure _ ->
    None

let reduce_projection env sigma p ~npars (recarg'hd,stack') stack =
  (match EConstr.kind sigma recarg'hd with
  | Construct _ ->
    let proj_narg = npars + Projection.arg p in
    Reduced (List.nth stack' proj_narg, stack)
  | _ -> NotReducible)

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
      | Evar ev -> s
      | Meta ev ->
        (try whrec (Evd.meta_value sigma ev, stack)
        with Not_found -> s)
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

(* The reductions that should be performed as part of the simpl tactic,
  excluding symbols that have the NeverUnfold flag. *)
let make_simpl_reds env =
  let open RedFlags in
  let open ReductionBehaviour in
  let simpl_never = all_never_unfold () in
  let transparent_state = Conv_oracle.get_transp_state (Environ.oracle env) in
  let transparent_state =
    { transparent_state with
      tr_cst = Cpred.diff transparent_state.tr_cst simpl_never
    }
  in
  let reds = no_red in
  let reds = red_add_transparent reds transparent_state in
  let reds = red_add reds fDELTA in
  let reds = red_add reds fZETA in
  let reds = red_add reds fBETA in
  reds

(* [red_elim_const] contracts iota/fix/cofix redexes hidden behind
   constants by keeping the name of the constants in the recursive calls;
   it fails if no redex is around *)

let rec red_elim_const allowed_reds env sigma ref u largs =
  let open ReductionBehaviour in
  let nargs = List.length largs in
  let* largs, unfold_anyway, unfold_nonelim, nocase =
    match recargs ref with
    | None -> Reduced (largs, false, false, false)
    | Some NeverUnfold -> NotReducible
    | Some (UnfoldWhen { nargs = Some n } | UnfoldWhenNoMatch { nargs = Some n })
      when nargs < n -> NotReducible
    | Some (UnfoldWhen { recargs = x::l } | UnfoldWhenNoMatch { recargs = x::l })
      when nargs <= List.fold_left max x l -> NotReducible
    | Some (UnfoldWhen { recargs; nargs = None }) ->
      let* params = reduce_params allowed_reds env sigma largs recargs in
      Reduced (params,
      false,
      false,
      false)
    | Some (UnfoldWhenNoMatch { recargs; nargs = None }) ->
      let* params = reduce_params allowed_reds env sigma largs recargs in
      Reduced (params,
      false,
      false,
      true)
    | Some (UnfoldWhen { recargs; nargs = Some n }) ->
      let is_empty = List.is_empty recargs in
      let* params = reduce_params allowed_reds env sigma largs recargs in
      Reduced (params,
      is_empty && nargs >= n,
      not is_empty && nargs >= n,
      false)
    | Some (UnfoldWhenNoMatch { recargs; nargs = Some n }) ->
      let is_empty = List.is_empty recargs in
      let* params = reduce_params allowed_reds env sigma largs recargs in
      Reduced (params,
      is_empty && nargs >= n,
      not is_empty && nargs >= n,
      true)
  in
  let ans = match reference_eval allowed_reds env sigma ref u with
    | EliminationCases n when nargs >= n ->
        let c = reference_value env sigma ref u in
        let c', lrest = whd_nothing_for_iota env sigma (c, largs) in
        let* ans = special_red_case allowed_reds env sigma (EConstr.destCase sigma c') in
        Reduced ((ans, lrest), nocase)
    | EliminationProj n when nargs >= n ->
        let c = reference_value env sigma ref u in
        let c', lrest = whd_nothing_for_iota env sigma (c, largs) in
        let* ans = reduce_proj allowed_reds env sigma c' in
        Reduced ((ans, lrest), nocase)
    | EliminationFix {trigger_min_args; refolding_target; refolding_data}
      when nargs >= trigger_min_args ->
        let rec descend (ref,u) args =
          let c = reference_value env sigma ref u in
          if evaluable_reference_eq sigma ref refolding_target then
            (c,args)
          else
            let c', lrest = whd_betalet_stack env sigma (applist(c,args)) in
            descend (destEvalRefU sigma c') lrest in
        let (_, midargs as s) = descend (ref,u) largs in
        let d, lrest = whd_nothing_for_iota env sigma s in
        let f = refolding_data, midargs in
        let* (c, rest) = reduce_fix allowed_reds env sigma (Some f) (destFix sigma d) lrest in
        Reduced ((c, rest), nocase)
    | NotAnElimination when unfold_nonelim ->
        let c = reference_value env sigma ref u in
        Reduced ((whd_betaiotazeta env sigma (applist (c, largs)), []), nocase)
    | _ -> NotReducible
  in
  match ans with
  | NotReducible when unfold_anyway ->
    let c = reference_value env sigma ref u in
    Reduced ((whd_betaiotazeta env sigma (applist (c, largs)), []), nocase)
  | _ -> ans

and reduce_params allowed_reds env sigma stack l =
  let len = List.length stack in
  let rec redp stack l = match l with
  | [] -> Reduced stack
  | i :: l ->
    if len <= i then NotReducible
    else
      let arg = List.nth stack i in
      let* rarg = whd_construct_stack allowed_reds env sigma arg in
      match EConstr.kind sigma (fst rarg) with
      | Construct _ | Int _ | Float _ | Array _ ->
        redp (List.assign stack i (applist rarg)) l
      | _ -> NotReducible
  in
  redp stack l

(* reduce to whd normal form or to an applied constant that does not hide
   a reducible iota/fix/cofix redex (the "simpl" tactic) *)

and whd_simpl_stack allowed_reds env sigma =
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
        begin match special_red_case allowed_reds env sigma (ci,u,pms,p,iv,c,lf) with
        | Reduced c -> redrec (c, stack)
        | NotReducible -> s'
        end
      | Fix fix ->
        begin match reduce_fix allowed_reds env sigma None fix stack with
        | Reduced s' -> redrec s'
        | NotReducible -> s'
        end
      | Proj (p, _, c) ->
        let ans =
           let unf = Projection.unfolded p in
           if unf || is_evaluable env (EvalConstRef (Projection.constant p)) then
             let npars = Projection.npars p in
             match unf, ReductionBehaviour.get (Projection.constant p) with
              | false, Some NeverUnfold -> NotReducible
              | false, Some (UnfoldWhen { recargs } | UnfoldWhenNoMatch { recargs })
                when not (List.is_empty recargs) ->
                let l' = List.map_filter (fun i ->
                    let idx = (i - (npars + 1)) in
                    if idx < 0 then None else Some idx) recargs in
                let* stack = reduce_params allowed_reds env sigma stack l' in
                let* r = whd_construct_stack allowed_reds env sigma c in
                reduce_projection env sigma p ~npars r stack
              | _ ->
                let* r = whd_construct_stack allowed_reds env sigma c in
                reduce_projection env sigma p ~npars r stack
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
            let* stack = reduce_params allowed_reds env sigma stack args in
            Reduced (whd_const cst env sigma (applist (x, stack)), [])
        in
        begin match ans with
        | Reduced s' -> s'
        | NotReducible -> s'
        end

      | _ ->
        match match_eval_ref env sigma x stack with
        | Some (ref, u) ->
          let ans =
             let* sapp, nocase = red_elim_const allowed_reds env sigma ref u stack in
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

and reduce_fix allowed_reds env sigma f fix stack =
  match fix_recarg fix stack with
    | None -> NotReducible
    | Some (recargnum,recarg) ->
       let* (recarg'hd,_ as recarg') =
         whd_construct_stack allowed_reds env sigma recarg in
        let stack' = List.assign stack recargnum (applist recarg') in
        (match EConstr.kind sigma recarg'hd with
           | Construct _ -> Reduced (contract_fix env sigma f fix, stack')
           | _ -> NotReducible)

and reduce_proj allowed_reds env sigma c =
  let rec redrec s =
    match EConstr.kind sigma s with
    | Proj (proj, _, c) ->
      let c' = match redrec c with NotReducible -> c | Reduced c -> c in
      let* (constr, cargs) = whd_construct_stack allowed_reds env sigma c' in
        (match EConstr.kind sigma constr with
        | Construct _ ->
          let proj_narg = Projection.npars proj + Projection.arg proj in
          Reduced (List.nth cargs proj_narg)
        | _ -> NotReducible)
    | Case (n,u,pms,p,iv,c,brs) ->
      let* c' = redrec c in
      let p = (n,u,pms,p,iv,c',brs) in
      begin match special_red_case allowed_reds env sigma p with
      | Reduced c -> Reduced c
      | NotReducible -> Reduced (mkCase p)
      end
    | _ -> NotReducible
  in redrec c

and special_red_case allowed_reds env sigma (ci, u, pms, p, iv, c, lf) =
  let* f, head, args = whd_construct allowed_reds env sigma (c, []) in
  reduce_mind_case env sigma f (ci, u, pms, p, iv, (head, args), lf)

and whd_construct_stack allowed_reds env sigma s =
  let* _, head, args = whd_construct allowed_reds env sigma (s, []) in
  Reduced (head, args)

(* reduce until finding an applied constructor (or primitive value) or fail *)

and whd_construct allowed_reds env sigma s =
  let (constr, cargs) = whd_simpl_stack allowed_reds env sigma s in
  match match_eval_ref env sigma constr cargs with
  | Some (ref, u) ->
    (match reference_opt_value env sigma ref u with
    | None -> NotReducible
    | Some gvalue ->
      if reducible_construct sigma gvalue then Reduced (Some (ref, u), gvalue, cargs)
      else whd_construct allowed_reds env sigma (gvalue, cargs))
  | None ->
    if reducible_construct sigma constr then Reduced (None, constr, cargs)
    else NotReducible

(************************************************************************)
(*            Special Purpose Reduction Strategies                     *)

(* Red reduction tactic: one step of delta reduction + full
   beta-iota-fix-cofix-zeta-cast at the head of the conclusion of a
   sequence of products; fails if no delta redex is around
*)

let try_red_product env sigma c =
  let simpfun c = clos_norm_flags RedFlags.betaiotazeta env sigma c in
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
      | Proj (p, _, c) ->
        let* c' =
          match EConstr.kind sigma c with
          | Construct _ -> Reduced c
          | _ -> redrec env c
        in
        let npars = Projection.npars p in
        let* s = reduce_projection env sigma p ~npars (whd_betaiotazeta_stack env sigma c') [] in
        Reduced (simpfun (applist s))
      | _ ->
        (match match_eval_ref env sigma x [] with
        | Some (ref, u) ->
          (* TO DO: re-fold fixpoints after expansion *)
          (* to get true one-step reductions *)
          (match reference_opt_value env sigma ref u with
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
             redrec (special_red_case env sigma whd_all (ci,p,d,lf), stack)
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
  let reds = make_simpl_reds env in
  let rec redrec s =
    let (constr, stack as s') = whd_simpl_stack reds env sigma s in
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

let whd_simpl_with_reds allowed_reds env sigma c =
  applist (whd_simpl_stack allowed_reds env sigma (c, []))

let whd_simpl env sigma x = whd_simpl_with_reds (make_simpl_reds env) env sigma x

let simpl env sigma c =
  let allowed_reds = make_simpl_reds env in
  let rec strongrec env t =
    map_constr_with_full_binders env sigma push_rel strongrec env
        (whd_simpl_with_reds allowed_reds env sigma t) in
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
let change_map_constr_with_binders_left_to_right g f (env, l as acc) sigma c =
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
    else mkApp (app', [| a' |])
  | _ -> map_constr_with_binders_left_to_right env sigma g f acc c

let e_contextually byhead (occs,c) f = begin fun env sigma t ->
  let count = ref (Locusops.initialize_occurrence_counter occs) in
  (* FIXME: we do suspicious things with this evarmap *)
  let evd = ref sigma in
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
        if Locusops.more_specific_occurrences !count then
          ignore (traverse_below (Some (Locusops.current_occurrence !count)) envc t);
        let (evm, t) = (f subst) env !evd t in
        (evd := evm; t)
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
        change_map_constr_with_binders_left_to_right
          (fun d (env,c) -> (push_rel d env, Patternops.lift_pattern 1 c))
          (traverse nested) envc sigma t
  in
  let t' = traverse None (env,c) t in
  Locusops.check_used_occurrences !count;
  (!evd, t')
  end

let contextually byhead occs f env sigma t =
  let f' subst env sigma t = sigma, f subst env sigma t in
  snd (e_contextually byhead occs f' env sigma t)

(* linear bindings (following pretty-printer) of the value of name in c.
 * n is the number of the next occurrence of name.
 * ol is the occurrence list to find. *)

let match_constr_evaluable_ref sigma c evref =
  match EConstr.kind sigma c, evref with
  | Const (c,u), Evaluable.EvalConstRef c' when Constant.CanOrd.equal c c' -> Some u
  | Proj (p,_,_), Evaluable.EvalProjectionRef p' when Projection.Repr.CanOrd.equal (Projection.repr p) p' -> Some EInstance.empty
  | Var id, Evaluable.EvalVarRef id' when Id.equal id id' -> Some EInstance.empty
  | _, _ -> None

let substlin env sigma evalref occs c =
  let count = ref (Locusops.initialize_occurrence_counter occs) in
  let value u = value_of_evaluable_ref env evalref u in
  let rec substrec () c =
    if Locusops.occurrences_done !count then c
    else
      match match_constr_evaluable_ref sigma c evalref with
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
  let flag = match kn with
    | Evaluable.EvalVarRef id -> RedFlags.fVAR id
    | Evaluable.EvalConstRef kn -> RedFlags.fCONST kn
    | Evaluable.EvalProjectionRef p -> RedFlags.fPROJ p in
  RedFlags.mkflags (flag::RedFlags.fDELTA::unfold_side_flags)

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
    (sigma, applist(abstr_trm, List.map snd loccs_trm))
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
        begin match special_red_case RedFlags.betadeltazeta env sigma (ci,u,pms,p,iv,c,lf) with
        | Reduced c -> (c, stack)
        | NotReducible -> raise NotStepReducible
        end
      | Fix fix ->
        begin match reduce_fix RedFlags.betadeltazeta env sigma None fix stack with
        | Reduced s' -> s'
        | NotReducible -> raise NotStepReducible
        end
      | _ when isEvalRef env sigma x ->
          let ref,u = destEvalRefU sigma x in
          begin match red_elim_const RedFlags.betadeltazeta env sigma ref u stack with
          | Reduced (c, _) -> c
          | NotReducible ->
             match reference_opt_value env sigma ref u with
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
