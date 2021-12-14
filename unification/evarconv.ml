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
open Termops
open Environ
open EConstr
open Context
open Vars
open Reduction
open Reductionops
open Structures
open Evarutil
open Evardefine
open Evarsolve
open Evd
open Pretype_errors

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

type unify_flags = Evarsolve.unify_flags

type unify_fun = unify_flags ->
  env -> evar_map -> conv_pb -> EConstr.constr -> EConstr.constr -> Evarsolve.unification_result

let default_transparent_state env = TransparentState.full
(* Conv_oracle.get_transp_state (Environ.oracle env) *)

let default_flags_of ?(subterm_ts=TransparentState.empty) ts =
  { modulo_betaiota = true;
    open_ts = ts; closed_ts = ts; subterm_ts;
    allowed_evars = AllowedEvars.all; with_cs = true;
    allow_K_at_toplevel = true }

let default_flags env =
  let ts = default_transparent_state env in
  default_flags_of ts

let debug_unification = CDebug.create ~name:"unification" ()

let debug_ho_unification = CDebug.create ~name:"ho-unification" ()

(*******************************************)
(* Functions to deal with impossible cases *)
(*******************************************)

(* In case the constants id/ID are not defined *)
let unit_judge_fallback =
  let na1 = make_annot (Name (Id.of_string "A")) Sorts.Relevant in
  let na2 = make_annot (Name (Id.of_string "H")) Sorts.Relevant in
  make_judge
    (mkLambda (na1,mkProp,mkLambda(na2,mkRel 1,mkRel 1)))
    (mkProd (na1,mkProp,mkArrow (mkRel 1) Sorts.Relevant (mkRel 2)))

let coq_unit_judge env sigma =
  match Coqlib.lib_ref "core.IDProp.idProp" with
  | c ->
    let sigma, c = Evd.fresh_global env sigma c in
    let t = Retyping.get_type_of env sigma c in
    sigma, make_judge c t
  | exception _ -> sigma, unit_judge_fallback

let unfold_projection env evd ts p c =
  let cst = Projection.constant p in
    if TransparentState.is_transparent_constant ts cst then
      Some (mkProj (Projection.unfold p, c))
    else None

let eval_flexible_term ts env evd c =
  match EConstr.kind evd c with
  | Const (c, u) ->
      if TransparentState.is_transparent_constant ts c
      then Option.map EConstr.of_constr (constant_opt_value_in env (c, EInstance.kind evd u))
      else None
  | Rel n ->
      (try match lookup_rel n env with
           | RelDecl.LocalAssum _ -> None
           | RelDecl.LocalDef (_,v,_) -> Some (lift n v)
       with Not_found -> None)
  | Var id ->
      (try
         if TransparentState.is_transparent_variable ts id then
           env |> lookup_named id |> NamedDecl.get_value
         else None
       with Not_found -> None)
  | LetIn (_,b,_,c) -> Some (subst1 b c)
  | Lambda _ -> Some c
  | Proj (p, c) ->
    if Projection.unfolded p then assert false
    else unfold_projection env evd ts p c
  | _ -> assert false

type flex_kind_of_term =
  | Rigid
  | MaybeFlexible of EConstr.t (* reducible but not necessarily reduced *)
  | Flexible of EConstr.existential

let has_arg s = Option.has_some (Stack.strip_n_app 0 s)

let flex_kind_of_term flags env evd c sk =
  match EConstr.kind evd c with
    | LetIn _ | Rel _ | Const _ | Var _ | Proj _ ->
      Option.cata (fun x -> MaybeFlexible x) Rigid (eval_flexible_term flags.open_ts env evd c)
    | Lambda _ when has_arg sk ->
       if flags.modulo_betaiota then MaybeFlexible c
       else Rigid
    | Evar ev ->
       if is_evar_allowed flags (fst ev) then Flexible ev else Rigid
    | Lambda _ | Prod _ | Sort _ | Ind _ | Int _ | Float _ | Array _ -> Rigid
    | Construct _ | CoFix _ (* Incorrect: should check only app in sk *) -> Rigid
    | Meta _ -> Rigid
    | Fix _ -> Rigid (* happens when the fixpoint is partially applied (should check it?) *)
    | Cast _ | App _ | Case _ -> assert false

let apprec_nohdbeta flags env evd c =
  let (t,sk as appr) = Reductionops.whd_nored_state env evd (c, []) in
  if flags.modulo_betaiota && Stack.not_purely_applicative sk
  then Stack.zip evd (whd_betaiota_deltazeta_for_iota_state
                   flags.open_ts env evd appr)
  else c

let position_problem l2r = function
  | CONV -> None
  | CUMUL -> Some l2r

(* [occur_rigidly ev evd t] tests if the evar ev occurs in a rigid
   context in t. Precondition: t has a rigid head and is not reducible.

   That function is an under approximation of occur-check, it can return
   false even if the occur-check would succeed on the normal form.  This
   means we might postpone unsolvable constraints which will ultimately
   result in an occur-check after reductions. If it returns true, we
   know that the occur-check would also return true on the normal form.

   [t] is assumed to have a rigid head, which can
   appear under a elimination context (e.g. application, match or projection).

   In the inner recursive function, the result indicates if the term is
   rigid (irreducible), normal (succession of constructors) or
   potentially reducible. For applications, this means than an
   occurrence of the evar in arguments should be looked at to find an
   occur-check if the head is rigid or normal. For inductive
   eliminations, only an occurrence in a rigid context of the
   discriminee counts as a rigid occurrence overall, not a normal
   occurrence which might disappear after reduction. *)

type result = Rigid of bool | Normal of bool | Reducible

let rigid_normal_occ = function Rigid b -> b | Normal b -> b | _ -> false

let occur_rigidly flags env evd (evk,_) t =
  let rec aux t =
    match EConstr.kind evd t with
    | App (f, c) ->
      (match aux f with
      | Rigid b -> Rigid (b || Array.exists (fun x -> rigid_normal_occ (aux x)) c)
      | Normal b -> Normal (b || Array.exists (fun x -> rigid_normal_occ (aux x)) c)
      | Reducible -> Reducible)
    | Construct _ -> Normal false
    | Ind _ | Sort _ -> Rigid false
    | Proj (p, c) ->
      let cst = Projection.constant p in
      let rigid = not (TransparentState.is_transparent_constant flags.open_ts cst) in
        if rigid then aux c
        else (* if the evar appears rigidly in c then this elimination
                cannot reduce and we have a rigid occurrence, otherwise
                we don't know. *)
          (match aux c with
          | Rigid _ as res -> res
          | Normal b -> Reducible
          | Reducible -> Reducible)
    | Evar (evk',l) ->
      if Evar.equal evk evk' then Rigid true
      else if is_evar_allowed flags evk' then
        Reducible
        else Rigid (List.exists (fun x -> rigid_normal_occ (aux x)) l)
    | Cast (p, _, _) -> aux p
    | Lambda (na, t, b) -> aux b
    | LetIn (na, _, _, b) -> aux b
    | Const (c,_) ->
      if TransparentState.is_transparent_constant flags.open_ts c then Reducible
      else Rigid false
    | Prod (_, b, t) ->
      let b' = aux b and t' = aux t in
      if rigid_normal_occ b' || rigid_normal_occ t' then Rigid true
      else Reducible
    | Rel _ | Var _ -> Reducible
    | Case (_,_,_,_,_,c,_) ->
      (match aux c with
      | Rigid b -> Rigid b
      | _ -> Reducible)
    | Meta _ | Fix _ | CoFix _ | Int _ | Float _ | Array _ -> Reducible
  in
    match aux t with
    | Rigid b -> b
    | Normal b -> b
    | Reducible -> false

(* [check_conv_record env sigma (t1,stack1) (t2,stack2)] tries to decompose
   the problem (t1 stack1) = (t2 stack2) into a problem

     stack1 = params1@[c1]@extra_args1
     stack2 = us2@extra_args2
     t1 params1 c1 = proji params (c xs)
     t2 us2 = head us
     extra_args1 = extra_args2

   by finding a record R and an object c := [xs:bs](Build_R params v1..vn)
   with vi = (head us), for which we know that the i-th projection proji
   satisfies

      proji params (c xs) = head us

   Rem: such objects, usable for conversion, are defined in the objdef
   table; practically, it amounts to "canonically" equip t2 into a
   object c in structure R (since, if c1 were not an evar, the
   projection would have been reduced) *)

let check_conv_record env sigma (t1,sk1) (t2,sk2) =
  let open ValuePattern in
  let (proji, u), arg = Termops.global_app_of_constr sigma t1 in
  let t2, sk2' = decompose_app_vect sigma (shrink_eta sigma t2) in
  let sk2 = Stack.append_app sk2' sk2 in
  let (sigma, solution), sk2_effective =
    let t2 =
      let rec remove_lambda t2 =
        match EConstr.kind sigma t2 with
        | Lambda (_,_,t2) -> remove_lambda t2
        | Cast (t2,_,_) -> remove_lambda t2
        | App (t2,_) -> t2
        | _ -> t2 in
      if Stack.is_empty sk2 then remove_lambda t2 else t2 in
    try
      match EConstr.kind sigma t2 with
        Prod (_,_,_) -> (* assert (l2=[]); *)
            CanonicalSolution.find env sigma (proji, Prod_cs),
            (Stack.append_app [|t2|] Stack.empty)
      | Sort s ->
        let s = ESorts.kind sigma s in
        CanonicalSolution.find env sigma
          (proji, Sort_cs (Sorts.family s)),[]
      | Proj (p, c) ->
        CanonicalSolution.find env sigma(proji, Proj_cs (Names.Projection.repr p)), Stack.append_app [|c|] sk2
      | _ ->
        let (c2, _) = try destRef sigma t2 with DestKO -> raise Not_found in
          CanonicalSolution.find env sigma (proji, Const_cs c2),sk2
    with Not_found ->
      CanonicalSolution.find env sigma (proji,Default_cs), []
  in
  let open CanonicalSolution in
  let params1, c1, extra_args1 =
    match arg with
    | Some c -> (* A primitive projection applied to c *)
      let ty = Retyping.get_type_of ~lax:true env sigma c in
      let (i,u), ind_args =
        (* Are we sure that ty is not an evar? *)
        try Inductiveops.find_mrectype env sigma ty
        with _ -> raise Not_found
      in ind_args, c, sk1
    | None ->
      match Stack.strip_n_app solution.nparams sk1 with
      | Some (params1, c1, extra_args1) -> (Option.get @@ Stack.list_of_app_stack params1), c1, extra_args1
      | _ -> raise Not_found in
  let us2,extra_args2 =
    let l_us = List.length solution.cvalue_arguments in
      if Int.equal l_us 0 then [], sk2_effective
      else match (Stack.strip_n_app (l_us-1) sk2_effective) with
      | None -> raise Not_found
      | Some (l',el,s') -> ((Option.get @@ Stack.list_of_app_stack l') @ [el],s') in
  let h, _ = decompose_app_vect sigma solution.body in
    sigma,(h, t2),solution.constant,solution.abstractions_ty,(solution.params,params1),
    (solution.cvalue_arguments,us2),(extra_args1,extra_args2),c1,
    (solution.cvalue_abstraction, Stack.zip sigma (t2,sk2))

(* Precondition: one of the terms of the pb is an uninstantiated evar,
 * possibly applied to arguments. *)

let join_failures evd1 evd2 e1 e2 =
  match e1, e2 with
  | _, CannotSolveConstraint (_,ProblemBeyondCapabilities) -> (evd1,e1)
  | _ -> (evd2,e2)

let rec ise_try evd = function
    [] -> assert false
  | [f] -> f evd
  | f1::l ->
      match f1 evd with
      | Success _ as x -> x
      | UnifFailure (evd1,e1) ->
          match ise_try evd l with
          | Success _ as x -> x
          | UnifFailure (evd2,e2) ->
              let evd,e = join_failures evd1 evd2 e1 e2 in
              UnifFailure (evd,e)

let ise_and evd l =
  let rec ise_and i = function
      [] -> assert false
    | [f] -> f i
    | f1::l ->
        match f1 i with
        | Success i' -> ise_and i' l
        | UnifFailure _ as x -> x in
  ise_and evd l

let ise_list2 evd f l1 l2 =
  let rec allrec k l1 l2 = match l1, l2 with
  | [], [] -> k evd
  | x1 :: l1, x2 :: l2 ->
    let k evd = match k evd with
    | Success evd -> f evd x1 x2
    | UnifFailure _ as x -> x
    in
    allrec k l1 l2
  | ([], _ :: _) | (_ :: _, []) -> UnifFailure (evd, NotSameArgSize)
  in
  allrec (fun i -> Success i) l1 l2

let ise_array2 evd f v1 v2 =
  let rec allrec i = function
    | -1 -> Success i
    | n ->
        match f i v1.(n) v2.(n) with
        | Success i' -> allrec i' (n-1)
        | UnifFailure _ as x -> x in
  let lv1 = Array.length v1 in
  if Int.equal lv1 (Array.length v2) then allrec evd (pred lv1)
  else UnifFailure (evd,NotSameArgSize)

let rec ise_inst2 evd f l1 l2 = match l1, l2 with
| [], [] -> Success evd
| [], (_ :: _) | (_ :: _), [] -> assert false
| c1 :: l1, c2 :: l2 ->
  match ise_inst2 evd f l1 l2 with
  | Success evd' -> f evd' c1 c2
  | UnifFailure _ as x -> x

(* Applicative node of stack are read from the outermost to the innermost
   but are unified the other way. *)
let rec ise_app_rev_stack2 env f evd revsk1 revsk2 =
  match Stack.decomp_rev revsk1, Stack.decomp_rev revsk2 with
  | Some (t1,revsk1), Some (t2,revsk2) ->
     begin
       match ise_app_rev_stack2 env f evd revsk1 revsk2 with
       | (_, UnifFailure _) as x -> x
       | x, Success i' -> x, f env i' CONV t1 t2
     end
  | _, _ -> (revsk1,revsk2), Success evd

(* This function tries to unify 2 stacks element by element. It works
   from the end to the beginning. If it unifies a non empty suffix of
   stacks but not the entire stacks, the first part of the answer is
   Some(the remaining prefixes to tackle)
   If [no_app] is set, situations like [match head u1 u2 with ... end]
   will not try to match [u1] and [u2] (why?); but situations like
   [match head u1 u2 with ... end v] will try to match [v] (??) *)
(* Input: E1[] =? E2[] where the E1, E2 are concatenations of
     n-ary-app/case/fix/proj elimination rules
   Output:
   - either None if E1 = E2 is solved,
   - or Some (E1'',E2'') such that there is a decomposition of
     E1[] = E1'[E1''[]] and E2[] = E2'[E2''[]] s.t.  E1' = E2' and
     E1'' cannot be unified with E2''
   - UnifFailure if no such non-empty E1' = E2' exists *)
let rec ise_stack2 no_app env evd f sk1 sk2 =
  let rec ise_rev_stack2 deep i revsk1 revsk2 =
    let fail x = if deep then Some (List.rev revsk1, List.rev revsk2), Success i
      else None, x in
    match revsk1, revsk2 with
    | [], [] -> None, Success i
    | Stack.Case cse1 :: q1, Stack.Case cse2 :: q2 ->
      let (t1, c1) = Stack.expand_case env evd cse1 in
      let (t2, c2) = Stack.expand_case env evd cse2 in
      begin
        match ise_and i [
          (fun i -> f env i CONV t1 t2);
          (fun i -> ise_array2 i (fun ii -> f env ii CONV) c1 c2)]
        with
        | Success i' -> ise_rev_stack2 true i' q1 q2
        | UnifFailure _ as x -> fail x
      end
    | Stack.Proj (p1)::q1, Stack.Proj (p2)::q2 ->
       if QProjection.Repr.equal env (Projection.repr p1) (Projection.repr p2)
       then ise_rev_stack2 true i q1 q2
       else fail (UnifFailure (i, NotSameHead))
    | Stack.Fix (((li1, i1),(_,tys1,bds1 as recdef1)),a1)::q1,
      Stack.Fix (((li2, i2),(_,tys2,bds2)),a2)::q2 ->
      if Int.equal i1 i2 && Array.equal Int.equal li1 li2 then
        match ise_and i [
          (fun i -> ise_array2 i (fun ii -> f env ii CONV) tys1 tys2);
          (fun i -> ise_array2 i (fun ii -> f (push_rec_types recdef1 env) ii CONV) bds1 bds2);
          (fun i -> snd (ise_stack2 no_app env i f a1 a2))] with
        | Success i' -> ise_rev_stack2 true i' q1 q2
        | UnifFailure _ as x -> fail x
      else fail (UnifFailure (i,NotSameHead))
    | Stack.App _ :: _, Stack.App _ :: _ ->
       if no_app && deep then fail ((*dummy*)UnifFailure(i,NotSameHead)) else
         begin match ise_app_rev_stack2 env f i revsk1 revsk2 with
               |_,(UnifFailure _ as x) -> fail x
               |(l1, l2), Success i' -> ise_rev_stack2 true i' l1 l2
         end
    |_, _ -> fail (UnifFailure (i,(* Maybe improve: *) NotSameHead))
  in ise_rev_stack2 false evd (List.rev sk1) (List.rev sk2)

(* Make sure that the matching suffix is the all stack *)
let rec exact_ise_stack2 env evd f sk1 sk2 =
  let rec ise_rev_stack2 i revsk1 revsk2 =
    match revsk1, revsk2 with
    | [], [] -> Success i
    | Stack.Case cse1 :: q1, Stack.Case cse2 :: q2 ->
      let (t1, c1) = Stack.expand_case env evd cse1 in
      let (t2, c2) = Stack.expand_case env evd cse2 in
      ise_and i [
      (fun i -> ise_rev_stack2 i q1 q2);
      (fun i -> ise_array2 i (fun ii -> f env ii CONV) c1 c2);
      (fun i -> f env i CONV t1 t2)]
    | Stack.Fix (((li1, i1),(_,tys1,bds1 as recdef1)),a1)::q1,
      Stack.Fix (((li2, i2),(_,tys2,bds2)),a2)::q2 ->
      if Int.equal i1 i2 && Array.equal Int.equal li1 li2 then
        ise_and i [
          (fun i -> ise_rev_stack2 i q1 q2);
          (fun i -> ise_array2 i (fun ii -> f env ii CONV) tys1 tys2);
          (fun i -> ise_array2 i (fun ii -> f (push_rec_types recdef1 env) ii CONV) bds1 bds2);
          (fun i -> exact_ise_stack2 env i f a1 a2)]
      else UnifFailure (i,NotSameHead)
    | Stack.Proj (p1)::q1, Stack.Proj (p2)::q2 ->
       if QProjection.Repr.equal env (Projection.repr p1) (Projection.repr p2)
       then ise_rev_stack2 i q1 q2
       else (UnifFailure (i, NotSameHead))
    | Stack.App _ :: _, Stack.App _ :: _ ->
         begin match ise_app_rev_stack2 env f i revsk1 revsk2 with
               |_,(UnifFailure _ as x) -> x
               |(l1, l2), Success i' -> ise_rev_stack2 i' l1 l2
         end
    |_, _ -> UnifFailure (i,(* Maybe improve: *) NotSameHead)
  in
  if Reductionops.Stack.compare_shape sk1 sk2 then
    ise_rev_stack2 evd (List.rev sk1) (List.rev sk2)
  else UnifFailure (evd, (* Dummy *) NotSameHead)

(* Add equality constraints for covariant/invariant positions. For
   irrelevant positions, unify universes when flexible. *)
let compare_cumulative_instances evd variances u u' =
  match Evarutil.compare_cumulative_instances CONV variances u u' evd with
  | Inl evd ->
    Success evd
  | Inr p -> UnifFailure (evd, UnifUnivInconsistency p)

let compare_heads env evd ~nargs term term' =
    let check_strict evd u u' =
      let cstrs = Univ.enforce_eq_instances u u' Univ.Constraints.empty in
      try Success (Evd.add_constraints evd cstrs)
      with Univ.UniverseInconsistency p -> UnifFailure (evd, UnifUnivInconsistency p)
    in
      match EConstr.kind evd term, EConstr.kind evd term' with
      | Const (c, u), Const (c', u') when QConstant.equal env c c' ->
        if Int.equal nargs 1 && Environ.is_array_type env c
        then
          let u = EInstance.kind evd u and u' = EInstance.kind evd u' in
          compare_cumulative_instances evd [|Univ.Variance.Irrelevant|] u u'
        else
          let u = EInstance.kind evd u and u' = EInstance.kind evd u' in
          check_strict evd u u'
      | Const _, Const _ -> UnifFailure (evd, NotSameHead)
      | Ind ((mi,i) as ind , u), Ind (ind', u') when Names.Ind.CanOrd.equal ind ind' ->
        if EInstance.is_empty u && EInstance.is_empty u' then Success evd
        else
          let u = EInstance.kind evd u and u' = EInstance.kind evd u' in
          let mind = Environ.lookup_mind mi env in
          let open Declarations in
          begin match mind.mind_variance with
            | None -> check_strict evd u u'
            | Some variances ->
              let needed = Reduction.inductive_cumulativity_arguments (mind,i) in
              if not (Int.equal nargs needed)
              then check_strict evd u u'
              else
                compare_cumulative_instances evd variances u u'
          end
      | Ind _, Ind _ -> UnifFailure (evd, NotSameHead)
      | Construct (((mi,ind),ctor as cons), u), Construct (cons', u')
        when Names.Construct.CanOrd.equal cons cons' ->
        if EInstance.is_empty u && EInstance.is_empty u' then Success evd
        else
          let u = EInstance.kind evd u and u' = EInstance.kind evd u' in
          let mind = Environ.lookup_mind mi env in
          let open Declarations in
          begin match mind.mind_variance with
            | None -> check_strict evd u u'
            | Some variances ->
              let needed = Reduction.constructor_cumulativity_arguments (mind,ind,ctor) in
              if not (Int.equal nargs needed)
              then check_strict evd u u'
              else
                Success (compare_constructor_instances evd u u')
          end
      | Construct _, Construct _ -> UnifFailure (evd, NotSameHead)
      | _, _ -> anomaly (Pp.str "")


let conv_fun f flags on_types =
  let typefn env evd pbty term1 term2 =
    let flags = { (default_flags env) with
      with_cs = flags.with_cs;
      allowed_evars = flags.allowed_evars }
    in f flags env evd pbty term1 term2
  in
  let termfn env evd pbty term1 term2 =
    f flags env evd pbty term1 term2
  in
    match on_types with
    | TypeUnification -> typefn
    | TermUnification -> termfn

let rec evar_conv_x flags env evd pbty term1 term2 =
  let term1 = whd_head_evar evd term1 in
  let term2 = whd_head_evar evd term2 in
  (* Maybe convertible but since reducing can erase evars which [evar_apprec]
     could have found, we do it only if the terms are free of evar.
     Note: incomplete heuristic... *)
  let ground_test =
    if is_ground_term evd term1 && is_ground_term evd term2 then (
      let e =
          match infer_conv ~catch_incon:false ~pb:pbty ~ts:flags.closed_ts env evd term1 term2 with
          | Some evd -> Success evd
          | None -> UnifFailure (evd, ConversionFailed (env,term1,term2))
          | exception Univ.UniverseInconsistency e -> UnifFailure (evd, UnifUnivInconsistency e)
      in
        match e with
        | UnifFailure (evd, e) when not (is_ground_env evd env) -> None
        | _ -> Some e)
    else None
  in
  match ground_test with
    | Some result -> result
    | None ->
      (* Until pattern-unification is used consistently, use nohdbeta to not
           destroy beta-redexes that can be used for 1st-order unification *)
        let term1 = apprec_nohdbeta flags env evd term1 in
        let term2 = apprec_nohdbeta flags env evd term2 in
        let default () =
        match
          evar_eqappr_x flags env evd pbty
            (whd_nored_state env evd (term1,Stack.empty))
            (whd_nored_state env evd (term2,Stack.empty))
        with
        | UnifFailure _ as x ->
           if Retyping.relevance_of_term env evd term1 == Sorts.Irrelevant ||
              Retyping.relevance_of_term env evd term2 == Sorts.Irrelevant
           then Success evd
           else x
        | Success _ as x -> x
        in
          begin match EConstr.kind evd term1, EConstr.kind evd term2 with
          | Evar ev, _ when Evd.is_undefined evd (fst ev) && is_evar_allowed flags (fst ev) ->
            (match solve_simple_eqn (conv_fun evar_conv_x) flags env evd
              (position_problem true pbty,ev,term2) with
              | UnifFailure (_,(OccurCheck _ | NotClean _)) ->
                (* Eta-expansion might apply *)
                (* OccurCheck: eta-expansion could solve
                     ?X = {| foo := ?X.(foo) |}
                   NotClean: pruning in solve_simple_eqn is incomplete wrt
                     Miller patterns *)
                default ()
              | x -> x)
          | _, Evar ev when Evd.is_undefined evd (fst ev) && is_evar_allowed flags (fst ev) ->
            (match solve_simple_eqn (conv_fun evar_conv_x) flags env evd
              (position_problem false pbty,ev,term1) with
              | UnifFailure (_, (OccurCheck _ | NotClean _)) ->
                (* OccurCheck: eta-expansion could solve
                     ?X = {| foo := ?X.(foo) |}
                   NotClean: pruning in solve_simple_eqn is incomplete wrt
                     Miller patterns *)
                default ()
              | x -> x)
          | _ -> default ()
        end

and evar_eqappr_x ?(rhs_is_already_stuck = false) flags env evd pbty
    (term1, sk1 as appr1) (term2, sk2 as appr2) =
  let quick_fail i = (* not costly, loses info *)
    UnifFailure (i, NotSameHead)
  in
  let miller_pfenning l2r fallback ev lF tM evd =
    match is_unification_pattern_evar env evd ev lF tM with
      | None -> fallback ()
      | Some l1' -> (* Miller-Pfenning's patterns unification *)
        let t2 = tM in
        let t2 = solve_pattern_eqn env evd l1' t2 in
          solve_simple_eqn (conv_fun evar_conv_x) flags env evd
            (position_problem l2r pbty,ev,t2)
  in
  let consume_stack l2r (termF,skF) (termO,skO) evd =
    let switch f a b = if l2r then f a b else f b a in
    let not_only_app = Stack.not_purely_applicative skO in
    match switch (ise_stack2 not_only_app env evd (evar_conv_x flags)) skF skO with
    | Some (l,r), Success i' when l2r && (not_only_app || List.is_empty l) ->
        (* E[?n]=E'[redex] reduces to either l[?n]=r[redex] with
           case/fix/proj in E' (why?) or ?n=r[redex] *)
        switch (evar_conv_x flags env i' pbty) (Stack.zip evd (termF,l)) (Stack.zip evd (termO,r))
    | Some (r,l), Success i' when not l2r && (not_only_app || List.is_empty l) ->
        (* E'[redex]=E[?n] reduces to either r[redex]=l[?n] with
           case/fix/proj in E' (why?) or r[redex]=?n *)
        switch (evar_conv_x flags env i' pbty) (Stack.zip evd (termF,l)) (Stack.zip evd (termO,r))
    | None, Success i' -> switch (evar_conv_x flags env i' pbty) termF termO
    | _, (UnifFailure _ as x) -> x
    | Some _, _ -> UnifFailure (evd,NotSameArgSize) in
  let eta_lambda env evd onleft term (term',sk') =
    (* Reduces an equation [env |- <(fun na:c1 => c'1)|empty> = <term'|sk'>] to
       [env, na:c1 |- c'1 = sk'[term'] (with some additional reduction) *)
    let (na,c1,c'1) = destLambda evd term in
    let env' = push_rel (RelDecl.LocalAssum (na,c1)) env in
    let out1 = whd_betaiota_deltazeta_for_iota_state
      flags.open_ts env' evd (c'1, Stack.empty) in
    let out2 = whd_nored_state env' evd
      (lift 1 (Stack.zip evd (term', sk')), Stack.append_app [|EConstr.mkRel 1|] Stack.empty) in
    if onleft then evar_eqappr_x flags env' evd CONV out1 out2
    else evar_eqappr_x flags env' evd CONV out2 out1
  in
  let rigids env evd sk term sk' term' =
    let nargs = Stack.args_size sk in
    let nargs' = Stack.args_size sk' in
    if not (Int.equal nargs nargs') then UnifFailure (evd, NotSameArgSize)
    else
      ise_and evd [(fun i ->
          try compare_heads env i ~nargs term term'
          with Univ.UniverseInconsistency p -> UnifFailure (i, UnifUnivInconsistency p));
         (fun i -> exact_ise_stack2 env i (evar_conv_x flags) sk sk')]
  in
  let consume l2r (_, skF as apprF) (_,skM as apprM) i =
    if not (Stack.is_empty skF && Stack.is_empty skM) then
      consume_stack l2r apprF apprM i
    else quick_fail i
  in
  let miller l2r ev (termF,skF as apprF) (termM, skM as apprM) i =
    let switch f a b = if l2r then f a b else f b a in
    let not_only_app = Stack.not_purely_applicative skM in
      match Stack.list_of_app_stack skF with
      | None -> quick_fail evd
      | Some lF ->
        let tM = Stack.zip evd apprM in
          miller_pfenning l2r
            (fun () -> if not_only_app then (* Postpone the use of an heuristic *)
              switch (fun x y -> Success (Evarutil.add_unification_pb (pbty,env,x,y) i)) (Stack.zip evd apprF) tM
            else quick_fail i)
            ev lF tM i
  in
  let flex_maybeflex l2r ev (termF,skF as apprF) (termM, skM as apprM) vM =
    (* Problem: E[?n[inst]] = E'[redex]
       Strategy, as far as I understand:
       1.  if E[]=[]u1..un and ?n[inst] u1..un = E'[redex] is a Miller pattern: solve it now
       2a. if E'=E'1[E'2] and E=E'1 unifiable, recursively solve ?n[inst] = E'2[redex]
       2b. if E'=E'1[E'2] and E=E1[E2] and E=E'1 unifiable and E' contient app/fix/proj,
           recursively solve E2[?n[inst]] = E'2[redex]
       3.  reduce the redex into M and recursively solve E[?n[inst]] =? E'[M] *)
    let switch f a b = if l2r then f a b else f b a in
    let delta i =
      switch (evar_eqappr_x flags env i pbty) apprF
        (whd_betaiota_deltazeta_for_iota_state flags.open_ts env i (vM,skM))
    in
    let default i = ise_try i [miller l2r ev apprF apprM;
                               consume l2r apprF apprM;
                               delta]
    in
      match EConstr.kind evd termM with
      | Proj (p, c) when not (Stack.is_empty skF) ->
        (* Might be ?X args = p.c args', and we have to eta-expand the
           primitive projection if |args| >= |args'|+1. *)
        let nargsF = Stack.args_size skF and nargsM = Stack.args_size skM in
          begin
            (* ?X argsF' ~= (p.c ..) argsM' -> ?X ~= (p.c ..), no need to expand *)
            if nargsF <= nargsM then default evd
            else
              let f =
                try
                  let termM' = Retyping.expand_projection env evd p c [] in
                  let apprM' =
                    whd_betaiota_deltazeta_for_iota_state flags.open_ts env evd (termM',skM)
                  in
                  let delta' i =
                    switch (evar_eqappr_x flags env i pbty) apprF apprM'
                  in
                  fun i -> ise_try i [miller l2r ev apprF apprM';
                                   consume l2r apprF apprM'; delta']
                with Retyping.RetypeError _ ->
                (* Happens thanks to w_unify building ill-typed terms *)
                  default
              in f evd
          end
      | _ -> default evd
  in
  let flex_rigid l2r ev (termF, skF as apprF) (termR, skR as apprR) =
    (* Problem: E[?n[inst]] = E'[M] with M blocking computation (in theory)
       Strategy, as far as I understand:
       1.  if E[]=[]u1..un and ?n[inst] u1..un = E'[M] is a Miller pattern: solve it now
       2a. if E'=E'1[E'2] and E=E'1 unifiable and E' contient app/fix/proj,
           recursively solve ?n[inst] = E'2[M]
       2b. if E'=E'1[E'2] and E=E1[E2] and E=E'1 unifiable and E' contient app/fix/proj,
           recursively solve E2[?n[inst]] = E'2[M]
       3a. if M a lambda or a constructor: eta-expand and recursively solve
       3b. if M a constructor C ..ui..: eta-expand and recursively solve proji[E[?n[inst]]]=ui
       4.  fail if E purely applicative and ?n occurs rigidly in E'[M]
       5.  absorb arguments if purely applicative and postpone *)
    let switch f a b = if l2r then f a b else f b a in
    let eta evd =
      match EConstr.kind evd termR with
      | Lambda _ when (* if ever problem is ill-typed: *) List.is_empty skR ->
         eta_lambda env evd false termR apprF
      | Construct u -> eta_constructor flags env evd u skR apprF
      | _ -> UnifFailure (evd,NotSameHead)
    in
    match Stack.list_of_app_stack skF with
    | None ->
        ise_try evd [consume_stack l2r apprF apprR; eta]
    | Some lF ->
        let tR = Stack.zip evd apprR in
          miller_pfenning l2r
            (fun () ->
              ise_try evd
                [eta;(* Postpone the use of an heuristic *)
                 (fun i ->
                   if not (occur_rigidly flags env i ev tR) then
                     let i,tF =
                       if isRel i tR || isVar i tR then
                         (* Optimization so as to generate candidates *)
                         let i,ev = evar_absorb_arguments env i ev lF in
                         i,mkEvar ev
                       else
                         i,Stack.zip evd apprF in
                     switch (fun x y -> Success (Evarutil.add_unification_pb (pbty,env,x,y) i))
                       tF tR
                   else
                     UnifFailure (evd,OccurCheck (fst ev,tR)))])
            ev lF tR evd
  in
  let first_order env i t1 t2 sk1 sk2 =
    (* Try first-order unification *)
    match ise_stack2 false env i (evar_conv_x flags) sk1 sk2 with
    | None, Success i' ->
       (* We do have sk1[] = sk2[]: we now unify ?ev1 and ?ev2 *)
       (* Note that ?ev1 and ?ev2, may have been instantiated in the meantime *)
       let ev1' = whd_evar i' t1 in
       if isEvar i' ev1' then
         solve_simple_eqn (conv_fun evar_conv_x) flags env i'
                          (position_problem true pbty,destEvar i' ev1',term2)
       else
         (* HH: Why not to drop sk1 and sk2 since they unified *)
         evar_eqappr_x flags env evd pbty
                       (ev1', sk1) (term2, sk2)
    | Some (r,[]), Success i' ->
       (* We have sk1'[] = sk2[] for some sk1' s.t. sk1[]=sk1'[r[]] *)
       (* we now unify r[?ev1] and ?ev2 *)
       let ev2' = whd_evar i' t2 in
       if isEvar i' ev2' then
         solve_simple_eqn (conv_fun evar_conv_x) flags env i'
                          (position_problem false pbty,destEvar i' ev2',Stack.zip i' (term1,r))
       else
         evar_eqappr_x flags env evd pbty
                       (ev2', sk1) (term2, sk2)
    | Some ([],r), Success i' ->
       (* Symmetrically *)
       (* We have sk1[] = sk2'[] for some sk2' s.t. sk2[]=sk2'[r[]] *)
       (* we now unify ?ev1 and r[?ev2] *)
       let ev1' = whd_evar i' t1 in
       if isEvar i' ev1' then
         solve_simple_eqn (conv_fun evar_conv_x) flags env i'
                          (position_problem true pbty,destEvar i' ev1',Stack.zip i' (term2,r))
       else
         (* HH: Why not to drop sk1 and sk2 since they unified *)
         evar_eqappr_x flags env evd pbty
                          (ev1', sk1) (term2, sk2)
    | None, (UnifFailure _ as x) ->
       (* sk1 and sk2 have no common outer part *)
       if Stack.not_purely_applicative sk2 then
         (* Ad hoc compatibility with 8.4 which treated non-app as rigid *)
         flex_rigid true (destEvar evd t1) appr1 appr2
       else
         if Stack.not_purely_applicative sk1 then
           (* Ad hoc compatibility with 8.4 which treated non-app as rigid *)
           flex_rigid false (destEvar evd t2) appr2 appr1
         else
           (* We could instead try Miller unification, then
              postpone to see if other equations help, as in:
              [Check fun a b : unit => (eqᵣefl : _ a = _ a b)] *)
           x
    | Some _, Success _ ->
       (* sk1 and sk2 have a common outer part *)
       if Stack.not_purely_applicative sk2 then
         (* Ad hoc compatibility with 8.4 which treated non-app as rigid *)
         flex_rigid true (destEvar evd t1) appr1 appr2
       else
         if Stack.not_purely_applicative sk1 then
           (* Ad hoc compatibility with 8.4 which treated non-app as rigid *)
           flex_rigid false (destEvar evd t2) appr2 appr1
         else
           (* We could instead try Miller unification, then
              postpone to see if other equations help, as in:
              [Check fun a b c : unit => (eq_refl : _ a b = _ c a b)] *)
           UnifFailure (i,NotSameArgSize)
    | _, _ -> anomaly (Pp.str "Unexpected result from ise_stack2.")
  in
  let app_empty = match sk1, sk2 with [], [] -> true | _ -> false in
  (* Evar must be undefined since we have flushed evars *)
  let () = debug_unification (fun () -> Pp.(v 0 (pr_state env evd appr1 ++ cut () ++ pr_state env evd appr2 ++ cut ()))) in
  match (flex_kind_of_term flags env evd term1 sk1,
         flex_kind_of_term flags env evd term2 sk2) with
    | Flexible (sp1,al1), Flexible (sp2,al2) ->
      (* Notations:
         - "sk" is a stack (or, more abstractly, an evaluation context, written E)
         - "ev" is an evar "?ev", more precisely an evar ?n with an instance inst
         - "al" is an evar instance
         Problem: E₁[?n₁[inst₁]] = E₂[?n₂[inst₂]] (i.e. sk1[?ev1] =? sk2[?ev2]
         Strategy is first-order unification
           1a. if E₁=E₂ unifiable, solve ?n₁[inst₁] = ?n₂[inst₂]
           1b. if E₂=E₂'[E₂''] and E₁=E₂' unifiable, recursively solve ?n₁[inst₁] = E₂''[?n₂[inst₂]]
           1b'. if E₁=E₁'[E₁''] and E₁'=E₂ unifiable, recursively solve E₁''[?n₁[inst₁]] = ?n₂[inst₂]
             recursively solve E2[?n[inst]] = E'2[redex]
           2. fails if neither E₁ nor E₂ is a prefix of the other *)
        let f1 i = first_order env i term1 term2 sk1 sk2
        and f2 i =
          if Evar.equal sp1 sp2 then
            match ise_stack2 false env i (evar_conv_x flags) sk1 sk2 with
            |None, Success i' ->
              Success (solve_refl (fun flags p env i pbty a1 a2 ->
                let flags =
                  match p with
                  | TypeUnification -> default_flags env
                  | TermUnification -> flags
                in
                is_success (evar_conv_x flags env i pbty a1 a2)) flags
                env i' (position_problem true pbty) sp1 al1 al2)
            |_, (UnifFailure _ as x) -> x
            |Some _, _ -> UnifFailure (i,NotSameArgSize)
          else UnifFailure (i,NotSameHead)
        and f3 i = miller true (sp1,al1) appr1 appr2 i
        and f4 i = miller false (sp2,al2) appr2 appr1 i
        and f5 i =
          (* We ensure failure of consuming the stacks does not
             propagate an error about unification of the stacks while
             the heads themselves cannot be unified, so we return
             NotSameHead. *)
          match consume true appr1 appr2 i with
          | Success _ as x -> x
          | UnifFailure _ -> quick_fail i
        in
        ise_try evd [f1; f2; f3; f4; f5]

    | Flexible ev1, MaybeFlexible v2 ->
      flex_maybeflex true ev1 appr1 appr2 v2

    | MaybeFlexible v1, Flexible ev2 ->
      flex_maybeflex false ev2 appr2 appr1 v1

    | MaybeFlexible v1, MaybeFlexible v2 -> begin
        match EConstr.kind evd term1, EConstr.kind evd term2 with
        | LetIn (na1,b1,t1,c'1), LetIn (na2,b2,t2,c'2) ->
        let f1 i = (* FO *)
          ise_and i
            [(fun i -> ise_try i
               [(fun i -> evar_conv_x flags env i CUMUL t1 t2);
                (fun i -> evar_conv_x flags env i CUMUL t2 t1)]);
             (fun i -> evar_conv_x flags env i CONV b1 b2);
             (fun i ->
               let b = nf_evar i b1 in
               let t = nf_evar i t1 in
               let na = Nameops.Name.pick_annot na1 na2 in
               evar_conv_x flags (push_rel (RelDecl.LocalDef (na,b,t)) env) i pbty c'1 c'2);
             (fun i -> exact_ise_stack2 env i (evar_conv_x flags) sk1 sk2)]
        and f2 i =
          let out1 = whd_betaiota_deltazeta_for_iota_state flags.open_ts env i (v1,sk1)
          and out2 = whd_betaiota_deltazeta_for_iota_state flags.open_ts env i (v2,sk2)
          in evar_eqappr_x flags env i pbty out1 out2
        in
        ise_try evd [f1; f2]

        | Proj (p, c), Proj (p', c') when QProjection.Repr.equal env (Projection.repr p) (Projection.repr p') ->
          let f1 i =
            ise_and i
            [(fun i -> evar_conv_x flags env i CONV c c');
             (fun i -> exact_ise_stack2 env i (evar_conv_x flags) sk1 sk2)]
          and f2 i =
            let out1 = whd_betaiota_deltazeta_for_iota_state flags.open_ts env i (v1,sk1)
            and out2 = whd_betaiota_deltazeta_for_iota_state flags.open_ts env i (v2,sk2)
            in evar_eqappr_x flags env i pbty out1 out2
          in
            ise_try evd [f1; f2]

        (* Catch the p.c ~= p c' cases *)
        | Proj (p,c), Const (p',u) when QConstant.equal env (Projection.constant p) p' ->
          let res =
            try Some (destApp evd (Retyping.expand_projection env evd p c []))
            with Retyping.RetypeError _ -> None
          in
            (match res with
            | Some (f1,args1) ->
              evar_eqappr_x flags env evd pbty (f1,Stack.append_app args1 sk1)
                appr2
            | None -> UnifFailure (evd,NotSameHead))

        | Const (p,u), Proj (p',c') when QConstant.equal env p (Projection.constant p') ->
          let res =
            try Some (destApp evd (Retyping.expand_projection env evd p' c' []))
            with Retyping.RetypeError _ -> None
          in
            (match res with
            | Some (f2,args2) ->
              evar_eqappr_x flags env evd pbty appr1 (f2,Stack.append_app args2 sk2)
            | None -> UnifFailure (evd,NotSameHead))

        | _, _ ->
        let f1 i =
          (* Gather the universe constraints that would make term1 and term2 equal.
             If these only involve unifications of flexible universes to other universes,
             allow this identification (first-order unification of universes). Otherwise
             fallback to unfolding.
          *)
          let univs = EConstr.eq_constr_universes env evd term1 term2 in
          match univs with
          | Some univs ->
              ise_and i [(fun i ->
                try Success (Evd.add_universe_constraints i univs)
                with UniversesDiffer -> UnifFailure (i,NotSameHead)
                | Univ.UniverseInconsistency p -> UnifFailure (i, UnifUnivInconsistency p));
                         (fun i -> exact_ise_stack2 env i (evar_conv_x flags) sk1 sk2)]
          | None ->
            UnifFailure (i,NotSameHead)
        and f2 i =
          (try
             if not flags.with_cs then raise Not_found
             else conv_record flags env
               (try check_conv_record env i appr1 appr2
                with Not_found -> check_conv_record env i appr2 appr1)
           with Not_found -> UnifFailure (i,NoCanonicalStructure))
        and f3 i =
          (* heuristic: unfold second argument first, exception made
             if the first argument is a beta-redex (expand a constant
             only if necessary) or the second argument is potentially
             usable as a canonical projection or canonical value *)
          let rec is_unnamed (hd, args) = match EConstr.kind i hd with
            | (Var _|Construct _|Ind _|Const _|Prod _|Sort _|Int _ |Float _|Array _) ->
              Stack.not_purely_applicative args
            | (CoFix _|Meta _|Rel _)-> true
            | Evar _ -> Stack.not_purely_applicative args
            (* false (* immediate solution without Canon Struct *)*)
            | Lambda _ -> assert (match args with [] -> true | _ -> false); true
            | LetIn (_,b,_,c) -> is_unnamed
             (whd_betaiota_deltazeta_for_iota_state
                      flags.open_ts env i (subst1 b c, args))
            | Fix _ -> true (* Partially applied fix can be the result of a whd call *)
            | Proj (p, _) -> Projection.unfolded p || Stack.not_purely_applicative args
            | Case _ | App _| Cast _ -> assert false in
          let rhs_is_stuck_and_unnamed () =
            let applicative_stack = fst (Stack.strip_app sk2) in
            is_unnamed
              (whd_betaiota_deltazeta_for_iota_state
                      flags.open_ts env i (v2, applicative_stack)) in
          let rhs_is_already_stuck =
            rhs_is_already_stuck || rhs_is_stuck_and_unnamed () in

          if (EConstr.isLambda i term1 || rhs_is_already_stuck)
            && (not (Stack.not_purely_applicative sk1)) then
            evar_eqappr_x ~rhs_is_already_stuck flags env i pbty
              (whd_betaiota_deltazeta_for_iota_state
                 flags.open_ts env i(v1,sk1))
              appr2
          else
            evar_eqappr_x flags env i pbty appr1
              (whd_betaiota_deltazeta_for_iota_state
                 flags.open_ts env i (v2,sk2))
        in
        ise_try evd [f1; f2; f3]
    end

    | Rigid, Rigid when EConstr.isLambda evd term1 && EConstr.isLambda evd term2 ->
        let (na1,c1,c'1) = EConstr.destLambda evd term1 in
        let (na2,c2,c'2) = EConstr.destLambda evd term2 in
        ise_and evd
          [(fun i -> evar_conv_x flags env i CONV c1 c2);
           (fun i ->
             let c = nf_evar i c1 in
             let na = Nameops.Name.pick_annot na1 na2 in
             evar_conv_x flags (push_rel (RelDecl.LocalAssum (na,c)) env) i CONV c'1 c'2);
           (* When in modulo_betaiota = false case, lambda's are not reduced *)
           (fun i -> exact_ise_stack2 env i (evar_conv_x flags) sk1 sk2)]

    | Flexible ev1, Rigid -> flex_rigid true ev1 appr1 appr2
    | Rigid, Flexible ev2 -> flex_rigid false ev2 appr2 appr1

    | MaybeFlexible v1, Rigid ->
        let f3 i =
          (try
             if not flags.with_cs then raise Not_found
             else conv_record flags env (check_conv_record env i appr1 appr2)
           with Not_found -> UnifFailure (i,NoCanonicalStructure))
        and f4 i =
          evar_eqappr_x flags env i pbty
            (whd_betaiota_deltazeta_for_iota_state
               flags.open_ts env i (v1,sk1))
            appr2
        in
          ise_try evd [f3; f4]

    | Rigid, MaybeFlexible v2 ->
        let f3 i =
          (try
             if not flags.with_cs then raise Not_found
             else conv_record flags env (check_conv_record env i appr2 appr1)
           with Not_found -> UnifFailure (i,NoCanonicalStructure))
        and f4 i =
          evar_eqappr_x flags env i pbty appr1
            (whd_betaiota_deltazeta_for_iota_state
               flags.open_ts env i (v2,sk2))
        in
          ise_try evd [f3; f4]

    (* Eta-expansion *)
    | Rigid, _ when isLambda evd term1 && (* if ever ill-typed: *) List.is_empty sk1 ->
        eta_lambda env evd true term1 (term2,sk2)

    | _, Rigid when isLambda evd term2 && (* if ever ill-typed: *) List.is_empty sk2 ->
        eta_lambda env evd false term2 (term1,sk1)

    | Rigid, Rigid -> begin
        match EConstr.kind evd term1, EConstr.kind evd term2 with

        | Sort s1, Sort s2 when app_empty ->
            (try
              let s1 = ESorts.kind evd s1 in
              let s2 = ESorts.kind evd s2 in
               let evd' =
                 if pbty == CONV
                 then Evd.set_eq_sort env evd s1 s2
                 else Evd.set_leq_sort env evd s1 s2
               in Success evd'
             with Univ.UniverseInconsistency p ->
               UnifFailure (evd,UnifUnivInconsistency p)
             | e when CErrors.noncritical e -> UnifFailure (evd,NotSameHead))

        | Prod (n1,c1,c'1), Prod (n2,c2,c'2) when app_empty ->
            ise_and evd
              [(fun i -> evar_conv_x flags env i CONV c1 c2);
               (fun i ->
                 let c = nf_evar i c1 in
                 let na = Nameops.Name.pick_annot n1 n2 in
                 evar_conv_x flags (push_rel (RelDecl.LocalAssum (na,c)) env) i pbty c'1 c'2)]

        | Rel x1, Rel x2 ->
            if Int.equal x1 x2 then
              exact_ise_stack2 env evd (evar_conv_x flags) sk1 sk2
            else UnifFailure (evd,NotSameHead)

        | Var var1, Var var2 ->
            if Id.equal var1 var2 then
              exact_ise_stack2 env evd (evar_conv_x flags) sk1 sk2
            else UnifFailure (evd,NotSameHead)

        | Const _, Const _
        | Ind _, Ind _
        | Construct _, Construct _
        | Int _, Int _
        | Float _, Float _
        | Array _, Array _ ->
          rigids env evd sk1 term1 sk2 term2

        | Evar (sp1,al1), Evar (sp2,al2) -> (* Frozen evars *)
          if Evar.equal sp1 sp2 then
            match ise_stack2 false env evd (evar_conv_x flags) sk1 sk2 with
            |None, Success i' ->
              ise_inst2 i' (fun i' -> evar_conv_x flags env i' CONV) al1 al2
            |_, (UnifFailure _ as x) -> x
            |Some _, _ -> UnifFailure (evd,NotSameArgSize)
          else UnifFailure (evd,NotSameHead)

        | Construct u, _ ->
          eta_constructor flags env evd u sk1 (term2,sk2)

        | _, Construct u ->
          eta_constructor flags env evd u sk2 (term1,sk1)

        | Fix ((li1, i1),(_,tys1,bds1 as recdef1)), Fix ((li2, i2),(_,tys2,bds2)) -> (* Partially applied fixs *)
          if Int.equal i1 i2 && Array.equal Int.equal li1 li2 then
            ise_and evd [
              (fun i -> ise_array2 i (fun i' -> evar_conv_x flags env i' CONV) tys1 tys2);
              (fun i -> ise_array2 i (fun i' -> evar_conv_x flags (push_rec_types recdef1 env) i' CONV) bds1 bds2);
              (fun i -> exact_ise_stack2 env i (evar_conv_x flags) sk1 sk2)]
          else UnifFailure (evd, NotSameHead)

        | CoFix (i1,(_,tys1,bds1 as recdef1)), CoFix (i2,(_,tys2,bds2)) ->
            if Int.equal i1 i2  then
              ise_and evd
                [(fun i -> ise_array2 i
                    (fun i -> evar_conv_x flags env i CONV) tys1 tys2);
                 (fun i -> ise_array2 i
                     (fun i -> evar_conv_x flags (push_rec_types recdef1 env) i CONV)
                     bds1 bds2);
                 (fun i -> exact_ise_stack2 env i
                     (evar_conv_x flags) sk1 sk2)]
            else UnifFailure (evd,NotSameHead)

        | (Meta _, _) | (_, Meta _) ->
          begin match ise_stack2 true env evd (evar_conv_x flags) sk1 sk2 with
          |_, (UnifFailure _ as x) -> x
          |None, Success i' -> evar_conv_x flags env i' CONV term1 term2
          |Some (sk1',sk2'), Success i' -> evar_conv_x flags env i' CONV (Stack.zip i' (term1,sk1')) (Stack.zip i' (term2,sk2'))
          end

        | (Ind _ | Sort _ | Prod _ | CoFix _ | Fix _ | Rel _ | Var _ | Const _ | Int _ | Float _ | Array _ | Evar _ | Lambda _), _ ->
          UnifFailure (evd,NotSameHead)
        | _, (Ind _ | Sort _ | Prod _ | CoFix _ | Fix _ | Rel _ | Var _ | Const _ | Int _ | Array _ | Evar _ | Lambda _) ->
          UnifFailure (evd,NotSameHead)
        | Case _, _ -> UnifFailure (evd,NotSameHead)
        | Proj _, _ -> UnifFailure (evd,NotSameHead)
        | (App _ | Cast _), _ -> assert false
        | LetIn _, _ -> assert false
      end

and conv_record flags env (evd,(h,h2),c,bs,(params,params1),(us,us2),(sk1,sk2),c1,(n,t2)) =
  (* Tries to unify the states

        (proji params1 c1 | sk1)   =   (proji params2 (c (?xs:bs)) | sk2)

     and the terms

        h us  =  h2 us2

     where

     c = the constant for the canonical structure (i.e. some term of the form
         fun (xs:bs) => Build_R params v1 .. vi-1 (h us) vi+1 .. vn)
     bs = the types of the parameters of the canonical structure
     c1 = the main argument of the canonical projection
     sk1, sk2 = the surrounding stacks of the conversion problem
     params1, params2 = the params of the projection (empty if a primitive proj)

     knowing that

       (proji params1 c1 | sk1)   =   (h2 us2 | sk2)

     had to be initially resolved
  *)
  if Reductionops.Stack.compare_shape sk1 sk2 then
    let (evd',ks,_,test) =
      List.fold_left
        (fun (i,ks,m,test) b ->
          if match n with Some n -> Int.equal m n | None -> false then
            let ty = Retyping.get_type_of env i t2 in
            let test i = evar_conv_x flags env i CUMUL ty (substl ks b) in
              (i,t2::ks, m-1, test)
          else
            let dloc = Loc.tag Evar_kinds.InternalHole in
            let (i', ev) = Evarutil.new_evar env i ~src:dloc (substl ks b) in
            (i', ev :: ks, m - 1,test))
        (evd,[],List.length bs,fun i -> Success i) bs
    in
    let app = mkApp (c, Array.rev_of_list ks) in
    ise_and evd'
      [(fun i ->
        ise_list2 i
          (fun i' x1 x -> evar_conv_x flags env i' CONV x1 (substl ks x))
          params1 params);
       (fun i ->
         ise_list2 i
           (fun i' u1 u -> evar_conv_x flags env i' CONV u1 (substl ks u))
           us2 us);
       (fun i -> evar_conv_x flags env i CONV c1 app);
       (fun i -> exact_ise_stack2 env i (evar_conv_x flags) sk1 sk2);
       test;
       (fun i -> evar_conv_x flags env i CONV h2
         (fst (decompose_app_vect i (substl ks h))))]
  else UnifFailure(evd,(*dummy*)NotSameHead)

and eta_constructor flags env evd ((ind, i), u) sk1 (term2,sk2) =
  (* reduces an equation <Construct(ind,i)|sk1> == <term2|sk2> to the
     equations [arg_i = Proj_i (sk2[term2])] where [sk1] is [params args] *)
  let open Declarations in
  let mib = lookup_mind (fst ind) env in
    match get_projections env ind with
    | Some projs when mib.mind_finite == BiFinite ->
      let pars = mib.mind_nparams in
      begin match Stack.list_of_app_stack sk1 with
      | None -> UnifFailure (evd,NotSameHead)
      | Some l1 ->
        (try
           let l1' = List.skipn pars l1 in
           let l2' =
             let term = Stack.zip evd (term2,sk2) in
               List.map (fun p -> EConstr.mkProj (Projection.make p false, term)) (Array.to_list projs)
           in
          let f i t1 t2 = evar_conv_x { flags with with_cs = false } env i CONV t1 t2 in
          ise_list2 evd f l1' l2'
         with
         | Failure _ ->
           (* List.skipn: partially applied constructor *)
           UnifFailure(evd,NotSameHead))
      end
    | _ -> UnifFailure (evd,NotSameHead)

let evar_conv_x flags = evar_conv_x flags

let evar_unify = conv_fun evar_conv_x

let evar_conv_hook_get, evar_conv_hook_set = Hook.make ~default:evar_conv_x ()

let evar_conv_x flags = Hook.get evar_conv_hook_get flags

let set_evar_conv f = Hook.set evar_conv_hook_set f


(* We assume here |l1| <= |l2| *)

let first_order_unification flags env evd (ev1,l1) (term2,l2) =
  let (deb2,rest2) = Array.chop (Array.length l2-Array.length l1) l2 in
  ise_and evd
    (* First compare extra args for better failure message *)
    [(fun i -> ise_array2 i (fun i -> evar_conv_x flags env i CONV) rest2 l1);
    (fun i ->
      (* Then instantiate evar unless already done by unifying args *)
      let t2 = mkApp(term2,deb2) in
      if is_defined i (fst ev1) then
        evar_conv_x flags env i CONV t2 (mkEvar ev1)
      else
        solve_simple_eqn ~choose:true ~imitate_defs:false
          evar_unify flags env i (None,ev1,t2))]

let choose_less_dependent_instance evk evd term args =
  let evi = Evd.find_undefined evd evk in
  let subst = make_pure_subst evi args in
  let subst' = List.filter (fun (id,c) -> EConstr.eq_constr evd c term) subst in
  match subst' with
  | [] -> None
  | (id, _) :: _ -> Some (Evd.define evk (mkVar id) evd)

type occurrence_match_test =
  env -> evar_map -> constr ->
  env -> evar_map -> int -> constr -> constr -> bool * evar_map

type occurrence_selection =
  | AtOccurrences of Locus.occurrences
  | Unspecified of Abstraction.abstraction

type occurrences_selection =
  occurrence_match_test * occurrence_selection list

let default_occurrence_selection = Unspecified Abstraction.Imitate

let default_occurrence_test ~allowed_evars ts _ origsigma _ env sigma _ c pat =
  let flags = { (default_flags_of ~subterm_ts:ts ts) with allowed_evars } in
  match evar_conv_x flags env sigma CONV c pat with
  | Success sigma -> true, sigma
  | UnifFailure _ -> false, sigma

let default_occurrences_selection ?(allowed_evars=AllowedEvars.all) ts n =
  (default_occurrence_test ~allowed_evars ts,
   List.init n (fun _ -> default_occurrence_selection))

let occur_evars sigma evs c =
  if Evar.Set.is_empty evs then false
  else
    let rec occur_rec c = match EConstr.kind sigma c with
      | Evar (sp,_) when Evar.Set.mem sp evs -> raise Occur
      | _ -> EConstr.iter sigma occur_rec c
    in
    try occur_rec c; false with Occur -> true

let apply_on_subterm env evd fixed f test c t =
  let test = test env evd c in
  let prc env evd = Termops.Internal.print_constr_env env evd in
  let evdref = ref evd in
  let fixedref = ref fixed in
  let rec applyrec (env,(k,c) as acc) t =
    if occur_evars !evdref !fixedref t then
      match EConstr.kind !evdref t with
      | Evar (ev, args) when Evar.Set.mem ev !fixedref -> t
      | _ -> map_constr_with_binders_left_to_right env !evdref
              (fun d (env,(k,c)) -> (push_rel d env, (k+1,lift 1 c)))
              applyrec acc t
    else
    (debug_ho_unification (fun () ->
     Pp.(str"Testing " ++ prc env !evdref c ++ str" against " ++ prc env !evdref t));
     let b, evd =
        try test env !evdref k c t
        with e when CErrors.noncritical e -> assert false in
     if b then (debug_ho_unification (fun () -> Pp.str "succeeded");
                let evd', fixed, t' = f !evdref !fixedref k t in
                fixedref := fixed;
                evdref := evd'; t')
     else (
       debug_ho_unification (fun () -> Pp.str "failed");
       map_constr_with_binders_left_to_right env !evdref
        (fun d (env,(k,c)) -> (push_rel d env, (k+1,lift 1 c)))
        applyrec acc t))
  in
  let t' = applyrec (env,(0,c)) t in
  !evdref, !fixedref, t'

let filter_possible_projections evd c ty ctxt args =
  (* Since args in the types will be replaced by holes, we count the
     fv of args to have a well-typed filter; don't know how necessary
    it is however to have a well-typed filter here *)
  let args = Array.of_list args in
  let fv1 = free_rels evd (mkApp (c,args)) (* Hack: locally untyped *) in
  let fv2 = collect_vars evd (mkApp (c,args)) in
  let len = Array.length args in
  let tyvars = collect_vars evd ty in
  List.map_i (fun i decl ->
    let () = assert (i < len) in
    let a = Array.unsafe_get args i in
    (match decl with
     | NamedDecl.LocalAssum _ -> false
     | NamedDecl.LocalDef (_,c,_) -> not (isRel evd c || isVar evd c)) ||
    a == c ||
    (* Here we make an approximation, for instance, we could also be *)
    (* interested in finding a term u convertible to c such that a occurs *)
    (* in u *)
    isRel evd a && Int.Set.mem (destRel evd a) fv1 ||
    isVar evd a && Id.Set.mem (destVar evd a) fv2 ||
    Id.Set.mem (NamedDecl.get_id decl) tyvars)
    0 ctxt

let solve_evars = ref (fun _ -> failwith "solve_evars not installed")
let set_solve_evars f = solve_evars := f

(* We solve the problem env_rhs |- ?e[u1..un] = rhs knowing
 * x1:T1 .. xn:Tn |- ev : ty
 * by looking for a maximal well-typed abtraction over u1..un in rhs
 *
 * We first build C[e11..e1p1,..,en1..enpn] obtained from rhs by replacing
 * all occurrences of u1..un by evars eij of type Ti' where itself Ti' has
 * been obtained from the type of ui by also replacing all occurrences of
 * u1..ui-1 by evars.
 *
 * Then, we use typing to infer the relations between the different
 * occurrences. If some occurrence is still unconstrained after typing,
 * we instantiate successively the unresolved occurrences of un by xn,
 * of un-1 by xn-1, etc [the idea comes from Chung-Kil Hur, that he
 * used for his Heq plugin; extensions to several arguments based on a
 * proposition from Dan Grayson]
 *)

let check_selected_occs env sigma c occ occs =
  let notfound =
    match occs with
    | AtOccurrences occs ->
       (match occs with
       | Locus.AtLeastOneOccurrence -> occ == 1
       | Locus.AllOccurrences -> false
       | Locus.AllOccurrencesBut l -> List.last l > occ
       | Locus.OnlyOccurrences l -> List.last l > occ
       | Locus.NoOccurrences -> false)
    | Unspecified abstract -> false
  in if notfound then
     raise (PretypeError (env,sigma,NoOccurrenceFound (c,None)))
     else ()

(* Error local to the module *)
exception TypingFailed of evar_map

let set_of_evctx l =
  List.fold_left (fun s decl -> Id.Set.add (NamedDecl.get_id decl) s) Id.Set.empty l

(** Weaken the existentials so that they can be typed in sign and raise
    an error if the term otherwise mentions variables not bound in sign. *)
let thin_evars env sigma sign c =
  let sigma = ref sigma in
  let ctx = set_of_evctx sign in
  let rec applyrec (env,acc) t =
    match kind !sigma t with
    | Evar (ev, args) ->
       let evi = Evd.find_undefined !sigma ev in
       let filter = List.map (fun c -> Id.Set.subset (collect_vars !sigma c) ctx) args in
       let filter = Filter.make filter in
       let candidates = Option.map (List.map EConstr.of_constr) (evar_candidates evi) in
       let evd, ev = restrict_evar !sigma ev filter candidates in
       sigma := evd; whd_evar !sigma t
    | Var id ->
       if not (Id.Set.mem id ctx) then raise (TypingFailed !sigma)
       else t
    | _ ->
       map_constr_with_binders_left_to_right env !sigma
        (fun d (env,acc) -> (push_rel d env, acc+1))
        applyrec (env,acc) t
  in
  let c' = applyrec (env,0) c in
  (!sigma, c')

let second_order_matching flags env_rhs evd (evk,args) (test,argoccs) rhs =
  try
  let evi = Evd.find_undefined evd evk in
  let evi = nf_evar_info evd evi in
  let env_evar_unf = evar_env env_rhs evi in
  let env_evar = evar_filtered_env env_rhs evi in
  let sign = named_context_val env_evar in
  let ctxt = evar_filtered_context evi in
  debug_ho_unification (fun () ->
     Pp.(str"env rhs: " ++ Termops.Internal.print_env env_rhs ++ fnl () ++
         str"env evars: " ++ Termops.Internal.print_env env_evar));
  let args = List.map (nf_evar evd) args in
  let argsubst = List.map2 (fun decl c -> (NamedDecl.get_id decl, c)) ctxt args in
  let instance = evar_identity_subst evi in
  let rhs = nf_evar evd rhs in
  if not (noccur_evar env_rhs evd evk rhs) then raise (TypingFailed evd);
  (* Ensure that any progress made by Typing.e_solve_evars will not contradict
      the solution we are trying to build here by adding the problem as a constraint. *)
  let evd = Evarutil.add_unification_pb (CONV,env_rhs,mkEvar (evk,args),rhs) evd in
  let prc env evd c = Termops.Internal.print_constr_env env evd c in
  let rec make_subst = function
    | decl'::ctxt', c::l, occs::occsl when isVarId evd (NamedDecl.get_id decl') c ->
      begin match occs with
        | AtOccurrences loc when not (Locusops.is_all_occurrences loc) ->
          user_err Pp.(str "Cannot force abstraction on identity instance.")
        | _ ->
          make_subst (ctxt',l,occsl)
      end
    | decl'::ctxt', c::l, occs::occsl ->
      let id = NamedDecl.get_annot decl' in
      let t = NamedDecl.get_type decl' in
      let evs = ref [] in
      let c = nf_evar evd c in
      (* ty is in env_rhs now *)
      let ty = replace_vars argsubst t in
      let filter' = filter_possible_projections evd c (nf_evar evd ty) ctxt args in
      (id,t,c,ty,evs,Filter.make filter',occs) :: make_subst (ctxt',l,occsl)
    | _, _, [] -> []
    | _ -> anomaly (Pp.str "Signature or instance are shorter than the occurrences list.")
  in
  let rec set_holes env_rhs evd fixed rhs = function
  | (id,idty,c,cty,evsref,filter,occs)::subst ->
     let c = nf_evar evd c in
     debug_ho_unification (fun () ->
       Pp.(str"set holes for: " ++
                                prc env_rhs evd (mkVar id.binder_name) ++ spc () ++
                                prc env_rhs evd c ++ str" in " ++
                                prc env_rhs evd rhs));
     let occ = ref 1 in
     let set_var evd fixed k inst =
       let oc = !occ in
       debug_ho_unification (fun () ->
       Pp.(str"Found one occurrence" ++ fnl () ++
           str"cty: " ++ prc env_rhs evd c));
       incr occ;
       match occs with
       | AtOccurrences occs ->
          if Locusops.is_selected oc occs then evd, fixed, mkVar id.binder_name
          else evd, fixed, inst
       | Unspecified prefer_abstraction ->
          let evd, fixed, evty = set_holes env_rhs evd fixed cty subst in
          let evty = nf_evar evd evty in
          debug_ho_unification (fun () ->
            Pp.(str"abstracting one occurrence " ++ prc env_rhs evd inst ++
                str" of type: " ++ prc env_evar evd evty ++
                str " for " ++ prc env_rhs evd c));
          let instance = Filter.filter_list filter instance in
          (* Allow any type lower than the variable's type as the
             abstracted subterm might have a smaller type, which could be
             crucial to make the surrounding context typecheck. *)
          let evd, evty =
            if isArity evd evty then
              refresh_universes ~status:Evd.univ_flexible (Some true)
                env_evar_unf evd evty
            else evd, evty in
          let (evd, evk) = new_pure_evar sign evd evty ~filter in
          let fixed = Evar.Set.add evk fixed in
          evsref := (evk,evty,inst,prefer_abstraction)::!evsref;
          evd, fixed, mkEvar (evk, instance)
     in
     let evd, fixed, rhs' = apply_on_subterm env_rhs evd fixed set_var test c rhs in
     debug_ho_unification (fun () ->
       Pp.(str"abstracted: " ++ prc env_rhs evd rhs'));
     let () = check_selected_occs env_rhs evd c !occ occs in
     let env_rhs' = push_named (NamedDecl.LocalAssum (id,idty)) env_rhs in
     set_holes env_rhs' evd fixed rhs' subst
  | [] -> evd, fixed, rhs in

  let subst = make_subst (ctxt,args,argoccs) in

  let evd, _, rhs' = set_holes env_rhs evd Evar.Set.empty rhs subst in
  let rhs' = nf_evar evd rhs' in
  (* Thin evars making the term typable in env_evar *)
  let evd, rhs' = thin_evars env_evar evd ctxt rhs' in
  (* We instantiate the evars of which the value is forced by typing *)
  debug_ho_unification (fun () ->
    Pp.(str"solve_evars on: " ++ prc env_evar evd rhs' ++ fnl () ++
        str"evars: " ++ pr_evar_map (Some 0) env_evar evd));
  let evd,rhs' =
    try !solve_evars env_evar evd rhs'
    with e when Pretype_errors.precatchable_exception e ->
      (* Could not revert all subterms *)
      raise (TypingFailed evd) in
  let rhs' = nf_evar evd rhs' in
  (* We instantiate the evars of which the value is forced by typing *)
  debug_ho_unification (fun () ->
    Pp.(str"after solve_evars: " ++ prc env_evar evd rhs' ++ fnl () ++
    str"evars: " ++ pr_evar_map (Some 0) env_evar evd));

  let rec abstract_free_holes evd = function
   | (id,idty,c,cty,evsref,_,_)::l ->
     let id = id.binder_name in
     let c = nf_evar evd c in
     debug_ho_unification (fun () ->
       Pp.(str"abstracting: " ++
             prc env_rhs evd (mkVar id) ++ spc () ++
             prc env_rhs evd c));
     let rec force_instantiation evd = function
     | (evk,evty,inst,abstract)::evs ->
       let evk = Option.default evk (Evarutil.advance evd evk) in
       let evd =
         if is_undefined evd evk then
         (* We try abstraction or concretisation for *)
         (* this unconstrained occurrence *)
         (* and we use typing to propagate this instantiation *)
         (* We avoid making an arbitrary choice by leaving candidates *)
         (* if both can work *)
         let evi = Evd.find_undefined evd evk in
         let vid = mkVar id in
         let candidates = [inst; vid] in
           try
             let evd, ev = Evarutil.restrict_evar evd evk (Evd.evar_filter evi) (Some candidates) in
             let evi = Evd.find evd ev in
               (match evar_candidates evi with
               | Some [t] ->
                 if not (noccur_evar env_rhs evd ev (EConstr.of_constr t)) then
                   raise (TypingFailed evd);
                 instantiate_evar evar_unify flags env_rhs evd ev (EConstr.of_constr t)
               | Some l when abstract = Abstraction.Abstract &&
                          List.exists (fun c -> isVarId evd id (EConstr.of_constr c)) l ->
                 instantiate_evar evar_unify flags env_rhs evd ev vid
               | _ -> evd)
           with IllTypedInstance _ (* from instantiate_evar *) | TypingFailed _ ->
              user_err (Pp.str "Cannot find an instance.")
         else
           ((debug_ho_unification (fun () ->
               let evi = Evd.find evd evk in
               let env = Evd.evar_env env_rhs evi in
               Pp.(str"evar is defined: " ++
                 int (Evar.repr evk) ++ spc () ++
                 prc env evd (match evar_body evi with Evar_defined c -> c
                   | Evar_empty -> assert false)));
            evd))
       in force_instantiation evd evs
     | [] -> abstract_free_holes evd l
     in force_instantiation evd !evsref
   | [] ->
     if Evd.is_defined evd evk then
       (* Can happen due to dependencies: instantiating evars in the arguments of evk might
           instantiate evk itself. *)
       (debug_ho_unification (fun () ->
          begin
            let evi = Evd.find evd evk in
            let evenv = evar_env env_rhs evi in
            let body = match evar_body evi with Evar_empty -> assert false | Evar_defined c -> c in
            Pp.(str"evar was defined already as: " ++ prc evenv evd body)
          end);
        evd)
     else
       try
         let evi = Evd.find_undefined evd evk in
         let evenv = evar_env env_rhs evi in
         let rhs' = nf_evar evd rhs' in
           debug_ho_unification (fun () ->
             Pp.(str"abstracted type before second solve_evars: " ++
                   prc evenv evd rhs'));
         (* solve_evars is not commuting with nf_evar, because restricting
             an evar might provide a more specific type. *)
          let evd, _ = !solve_evars evenv evd rhs' in
          debug_ho_unification (fun () ->
            Pp.(str"abstracted type: " ++ prc evenv evd (nf_evar evd rhs')));
          let flags = default_flags_of TransparentState.full in
            Evarsolve.instantiate_evar evar_unify flags env_rhs evd evk rhs'
         with IllTypedInstance _ -> raise (TypingFailed evd)
  in
  let evd = abstract_free_holes evd subst in
  evd, true
  with TypingFailed evd -> evd, false

let default_evar_selection flags evd (ev,args) =
  let evi = Evd.find_undefined evd ev in
  let rec aux args abs =
    match args, abs with
    | _ :: args, a :: abs ->
      let spec =
        if not flags.allow_K_at_toplevel then
          (* [evar_absorb_arguments] puts an Abstract flag for the
             toplevel binders that were absorbed. *)
          let occs =
            if a == Abstraction.Abstract then Locus.AtLeastOneOccurrence
            else Locus.AllOccurrences
          in AtOccurrences occs
        else Unspecified a
      in spec :: aux args abs
    | l, [] -> List.map (fun _ -> default_occurrence_selection) l
    | [], _ :: _ -> assert false
  in aux args evi.evar_abstract_arguments

let second_order_matching_with_args flags env evd with_ho pbty ev l t =
  if with_ho then
    let evd,ev = evar_absorb_arguments env evd ev (Array.to_list l) in
    let argoccs = default_evar_selection flags evd ev in
    let test = default_occurrence_test ~allowed_evars:flags.allowed_evars flags.subterm_ts in
    let evd, b =
      try second_order_matching flags env evd ev (test,argoccs) t
      with PretypeError (_, _, NoOccurrenceFound _) -> evd, false
    in
    if b then Success evd
    else
      UnifFailure (evd, ConversionFailed (env,mkApp(mkEvar ev,l),t))
  else
    let pb = (pbty,env,mkApp(mkEvar ev,l),t) in
    UnifFailure (evd, CannotSolveConstraint (pb,ProblemBeyondCapabilities))

let is_beyond_capabilities = function
  | CannotSolveConstraint (pb,ProblemBeyondCapabilities) -> true
  | _ -> false

let apply_conversion_problem_heuristic flags env evd with_ho pbty t1 t2 =
  let t1 = apprec_nohdbeta flags env evd (whd_head_evar evd t1) in
  let t2 = apprec_nohdbeta flags env evd (whd_head_evar evd t2) in
  let (term1,l1 as appr1) = try destApp evd t1 with DestKO -> (t1, [||]) in
  let (term2,l2 as appr2) = try destApp evd t2 with DestKO -> (t2, [||]) in
  let () = debug_unification (fun () ->
             Pp.(v 0 (str "Heuristic:" ++ spc () ++
                                Termops.Internal.print_constr_env env evd t1 ++ cut () ++
                                Termops.Internal.print_constr_env env evd t2 ++ cut ()))) in
  let app_empty = Array.is_empty l1 && Array.is_empty l2 in
  match EConstr.kind evd term1, EConstr.kind evd term2 with
  | Evar (evk1,args1), (Rel _|Var _) when app_empty
      && is_evar_allowed flags evk1
      && List.for_all (fun a -> EConstr.eq_constr evd a term2 || isEvar evd a)
        (remove_instance_local_defs evd evk1 args1) ->
      (* The typical kind of constraint coming from pattern-matching return
         type inference *)
      (match choose_less_dependent_instance evk1 evd term2 args1 with
      | Some evd -> Success evd
      | None ->
         let reason = ProblemBeyondCapabilities in
         UnifFailure (evd, CannotSolveConstraint ((pbty,env,t1,t2),reason)))
  | (Rel _|Var _), Evar (evk2,args2) when app_empty
    && is_evar_allowed flags evk2
    && List.for_all (fun a -> EConstr.eq_constr evd a term1 || isEvar evd a)
        (remove_instance_local_defs evd evk2 args2) ->
      (* The typical kind of constraint coming from pattern-matching return
         type inference *)
      (match choose_less_dependent_instance evk2 evd term1 args2 with
      | Some evd -> Success evd
      | None ->
         let reason = ProblemBeyondCapabilities in
         UnifFailure (evd, CannotSolveConstraint ((pbty,env,t1,t2),reason)))
  | Evar (evk1,args1), Evar (evk2,args2) when Evar.equal evk1 evk2 ->
     let f flags ontype env evd pbty x y =
       let reds =
         match ontype with
         | TypeUnification -> TransparentState.full
         | TermUnification -> flags.open_ts
       in is_fconv ~reds pbty env evd x y
     in
      Success (solve_refl ~can_drop:true f flags env evd
                 (position_problem true pbty) evk1 args1 args2)
  | Evar (evk1,_ as ev1), Evar ev2 when app_empty ->
    (* solve_evar_evar handles the cases ev1 and/or ev2 are frozen *)
      (try
        Success (solve_evar_evar ~force:true
                 (evar_define evar_unify flags ~choose:true)
                 evar_unify flags env evd
                 (position_problem true pbty) ev1 ev2)
      with IllTypedInstance (env,evd,t,u) ->
            UnifFailure (evd,InstanceNotSameType (evk1,env,t,u)))
  | Evar ev1,_ when is_evar_allowed flags (fst ev1) && Array.length l1 <= Array.length l2 ->
      (* On "?n t1 .. tn = u u1 .. u(n+p)", try first-order unification *)
      (* and otherwise second-order matching *)
      ise_try evd
        [(fun evd -> first_order_unification flags env evd (ev1,l1) appr2);
         (fun evd ->
           second_order_matching_with_args flags env evd with_ho pbty ev1 l1 t2)]
  | _,Evar ev2 when is_evar_allowed flags (fst ev2) && Array.length l2 <= Array.length l1 ->
      (* On "u u1 .. u(n+p) = ?n t1 .. tn", try first-order unification *)
      (* and otherwise second-order matching *)
      ise_try evd
        [(fun evd -> first_order_unification flags env evd (ev2,l2) appr1);
         (fun evd ->
           second_order_matching_with_args flags env evd with_ho pbty ev2 l2 t1)]
  | Evar ev1,_ when is_evar_allowed flags (fst ev1) ->
      (* Try second-order pattern-matching *)
      second_order_matching_with_args flags env evd with_ho pbty ev1 l1 t2
  | _,Evar ev2 when is_evar_allowed flags (fst ev2) ->
      (* Try second-order pattern-matching *)
      second_order_matching_with_args flags env evd with_ho pbty ev2 l2 t1
  | _ ->
      (* Some head evar have been instantiated, or unknown kind of problem *)
      evar_conv_x flags env evd pbty t1 t2

let error_cannot_unify env evd pb ?reason t1 t2 =
  Pretype_errors.error_cannot_unify
    ?loc:(loc_of_conv_pb evd pb) env
    evd ?reason (t1, t2)

let check_problems_are_solved env evd =
  match snd (extract_all_conv_pbs evd) with
  | (pbty,env,t1,t2) as pb::_ -> error_cannot_unify env evd pb t1 t2
  | _ -> ()

exception MaxUndefined of (Evar.t * evar_info * EConstr.t list)

let max_undefined_with_candidates evd =
  let fold evk evi () = match evi.evar_candidates with
  | None -> ()
  | Some l -> raise (MaxUndefined (evk, evi, l))
  in
  (* [fold_right] traverses the undefined map in decreasing order of
     indices.  The evar with candidates of maximum index is thus the
     first evar with candidates found by a [fold_right]
     traversal. This has a significant impact on performance. *)
  try
    let () = Evar.Map.fold_right fold (Evd.undefined_map evd) () in
    None
  with MaxUndefined ans ->
    Some ans

let rec solve_unconstrained_evars_with_candidates flags env evd =
  (* max_undefined is supposed to return the most recent, hence
     possibly most dependent evar *)
  match max_undefined_with_candidates evd with
  | None -> evd
  | Some (evk,ev_info,l) ->
      let rec aux = function
      | [] -> user_err Pp.(str "Unsolvable existential variables.")
      | a::l ->
          (* In case of variables, most recent ones come first *)
          try
            let evd = instantiate_evar evar_unify flags env evd evk a in
            match reconsider_unif_constraints evar_unify flags evd with
            | Success evd -> solve_unconstrained_evars_with_candidates flags env evd
            | UnifFailure _ -> aux l
          with
          | IllTypedInstance _ -> aux l
          | e when Pretype_errors.precatchable_exception e -> aux l in
      (* Expected invariant: most dependent solutions come first *)
      (* so as to favor progress when used with the refine tactics *)
      let evd = aux l in
      solve_unconstrained_evars_with_candidates flags env evd

let solve_unconstrained_impossible_cases env evd =
  Evd.fold_undefined (fun evk ev_info evd' ->
    match ev_info.evar_source with
    | loc,Evar_kinds.ImpossibleCase ->
      let evd', j = coq_unit_judge env evd' in
      let ty = j_type j in
      let flags = default_flags env in
      instantiate_evar evar_unify flags env evd' evk ty (* should we protect from raising IllTypedInstance? *)
    | _ -> evd') evd evd

let solve_unif_constraints_with_heuristics env
    ?(flags=default_flags env) ?(with_ho=false) evd =
  let evd = solve_unconstrained_evars_with_candidates flags env evd in
  let rec aux evd pbs progress stuck =
    match pbs with
    | (pbty,env,t1,t2 as pb) :: pbs ->
        (match apply_conversion_problem_heuristic flags env evd with_ho pbty t1 t2 with
        | Success evd' ->
           let evd' = solve_unconstrained_evars_with_candidates flags env evd' in
           let (evd', rest) = extract_all_conv_pbs evd' in
           begin match rest with
            | [] -> aux evd' pbs true stuck
            | l ->
               (* Unification got actually stuck, postpone *)
               let reason = CannotSolveConstraint (pb,ProblemBeyondCapabilities) in
               aux evd pbs progress ((pb, reason):: stuck)
            end
        | UnifFailure (evd,reason) ->
           if is_beyond_capabilities reason then
             aux evd pbs progress ((pb,reason) :: stuck)
           else aux evd [] false ((pb,reason) :: stuck))
    | _ ->
        if progress then aux evd (List.map fst stuck) false []
        else
          match stuck with
          | [] -> (* We're finished *) evd
          | ((pbty,env,t1,t2 as pb), reason) :: _ ->
              (* There remains stuck problems *)
              Pretype_errors.error_cannot_unify ?loc:(loc_of_conv_pb evd pb)
                env evd ~reason (t1, t2)
  in
  let (evd,pbs) = extract_all_conv_pbs evd in
  let heuristic_solved_evd = aux evd pbs false [] in
  check_problems_are_solved env heuristic_solved_evd;
  solve_unconstrained_impossible_cases env heuristic_solved_evd

(* Main entry points *)

exception UnableToUnify of evar_map * unification_error

let unify_delay ?flags env evd t1 t2 =
  let flags =
    match flags with
    | None -> default_flags_of (default_transparent_state env)
    | Some flags -> flags
  in
  match evar_conv_x flags env evd CONV t1 t2 with
  | Success evd' -> evd'
  | UnifFailure (evd',e) -> raise (UnableToUnify (evd',e))

let unify_leq_delay ?flags env evd t1 t2 =
  let flags =
    match flags with
    | None -> default_flags_of (default_transparent_state env)
    | Some flags -> flags
  in
  match evar_conv_x flags env evd CUMUL t1 t2 with
  | Success evd' -> evd'
  | UnifFailure (evd',e) -> raise (UnableToUnify (evd',e))

let unify ?flags ?(with_ho=true) env evd cv_pb ty1 ty2 =
  let flags =
    match flags with
    | None -> default_flags_of (default_transparent_state env)
    | Some flags -> flags
  in
  let res = evar_conv_x flags env evd cv_pb ty1 ty2 in
  match res with
  | Success evd ->
     solve_unif_constraints_with_heuristics ~flags ~with_ho env evd
  | UnifFailure (evd, reason) ->
     raise (PretypeError (env, evd, CannotUnify (ty1, ty2, Some reason)))
