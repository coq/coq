(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Nameops
open Constr
open Vars
open Termops
open Environ
open Reductionops
open Inductiveops
open Typing
open Retyping

module NamedDecl = Context.Named.Declaration

type refiner_error =

  (* Errors raised by the refiner *)
  | BadType of constr * constr * EConstr.t
  | UnresolvedBindings of Name.t list
  | CannotApply of constr * constr
  | NonLinearProof of constr
  | MetaInType of EConstr.constr

  (* Errors raised by the tactics *)
  | IntroNeedsProduct
  | NoSuchHyp of Id.t

exception RefinerError of Environ.env * Evd.evar_map * refiner_error


let error_no_such_hypothesis env sigma id = raise (RefinerError (env, sigma, NoSuchHyp id))

(* The check flag tells if the refiner should check that the submitted rules do
   not produce invalid subgoals *)

let check_typability ~check env sigma c =
  if check then fst (type_of env sigma (EConstr.of_constr c)) else sigma

(************************************************************************)
(************************************************************************)
(* Implementation of the structural rules (moving and deleting
   hypotheses around) *)

(* The ClearBody tactic *)

(* Reordering of the context *)

(* faire le minimum d'echanges pour que l'ordre donne soit un *)
(* sous-ordre du resultat. Par exemple, 2 hyps non mentionnee ne sont *)
(* pas echangees. Choix: les hyps mentionnees ne peuvent qu'etre *)
(* reculees par rapport aux autres (faire le contraire!) *)

let mt_q = (Id.Map.empty,[])
let push_val y = function
    (_,[] as q) -> q
  | (m, (x,l)::q) -> (m, (x,Id.Set.add y l)::q)
let push_item x v (m,l) =
  (Id.Map.add x v m, (x,Id.Set.empty)::l)
let mem_q x (m,_) = Id.Map.mem x m
let find_q x (m,q) =
  let v = Id.Map.find x m in
  let m' = Id.Map.remove x m in
  let rec find accs acc = function
      [] -> raise Not_found
    | [(x',l)] ->
        if Id.equal x x' then ((v,Id.Set.union accs l),(m',List.rev acc))
        else raise Not_found
    | (x',l as i)::((x'',l'')::q as itl) ->
        if Id.equal x x' then
          ((v,Id.Set.union accs l),
           (m',List.rev acc@(x'',Id.Set.add x (Id.Set.union l l''))::q))
        else find (Id.Set.union l accs) (i::acc) itl in
  find Id.Set.empty [] q

let occur_vars_in_decl env sigma hyps d =
  if Id.Set.is_empty hyps then false else
    let ohyps = global_vars_set_of_decl env sigma d in
    Id.Set.exists (fun h -> Id.Set.mem h ohyps) hyps

let reorder_context env sigma sign ord =
  let ords = List.fold_right Id.Set.add ord Id.Set.empty in
  if not (Int.equal (List.length ord) (Id.Set.cardinal ords)) then
    user_err Pp.(str "Order list has duplicates");
  let rec step ord expected ctxt_head moved_hyps ctxt_tail =
    match ord with
      | [] -> List.rev ctxt_tail @ ctxt_head
      | top::ord' when mem_q top moved_hyps ->
          let ((d,h),mh) = find_q top moved_hyps in
          if occur_vars_in_decl env sigma h d then
            user_err ~hdr:"reorder_context"
              (str "Cannot move declaration " ++ Id.print top ++ spc() ++
              str "before " ++
              pr_sequence Id.print
                (Id.Set.elements (Id.Set.inter h
                  (global_vars_set_of_decl env sigma d))));
          step ord' expected ctxt_head mh (d::ctxt_tail)
      | _ ->
          (match ctxt_head with
            | [] -> error_no_such_hypothesis env sigma (List.hd ord)
            | d :: ctxt ->
                let x = NamedDecl.get_id d in
                if Id.Set.mem x expected then
                  step ord (Id.Set.remove x expected)
                    ctxt (push_item x d moved_hyps) ctxt_tail
                else
                  step ord expected
                    ctxt (push_val x moved_hyps) (d::ctxt_tail)) in
  step ord ords sign mt_q []

let reorder_val_context env sigma sign ord =
match ord with
| [] | [_] ->
  (* Single variable-free definitions need not be reordered *)
  sign
| _ :: _ :: _ ->
  let open EConstr in
  val_of_named_context (reorder_context env sigma (named_context_of_val sign) ord)

let check_decl_position env sigma sign d =
  let open EConstr in
  let x = NamedDecl.get_id d in
  let needed = global_vars_set_of_decl env sigma d in
  let deps = dependency_closure env sigma (named_context_of_val sign) needed in
  if Id.List.mem x deps then
    user_err ~hdr:"Logic.check_decl_position"
      (str "Cannot create self-referring hypothesis " ++ Id.print x);
  x::deps

(* Auxiliary functions for primitive MOVE tactic
 *
 * [move_hyp with_dep toleft (left,(hfrom,typfrom),right) hto] moves
 * hyp [hfrom] at location [hto] which belongs to the hyps on the
 * left side [left] of the full signature if [toleft=true] or to the hyps
 * on the right side [right] if [toleft=false].
 * If [with_dep] then dependent hypotheses are moved accordingly. *)

(** Move destination for hypothesis *)

type 'id move_location =
  | MoveAfter of 'id
  | MoveBefore of 'id
  | MoveFirst
  | MoveLast (** can be seen as "no move" when doing intro *)

(** Printing of [move_location] *)

let pr_move_location pr_id = function
  | MoveAfter id -> brk(1,1) ++ str "after " ++ pr_id id
  | MoveBefore id -> brk(1,1) ++ str "before " ++ pr_id id
  | MoveFirst -> str " at top"
  | MoveLast -> str " at bottom"

let move_location_eq m1 m2 = match m1, m2 with
| MoveAfter id1, MoveAfter id2 -> Id.equal id1 id2
| MoveBefore id1, MoveBefore id2 -> Id.equal id1 id2
| MoveLast, MoveLast -> true
| MoveFirst, MoveFirst -> true
| _ -> false

let mem_id_context id ctx = Id.Map.mem id ctx.Environ.env_named_map

let split_sign env sigma hfrom l =
  let () = if not (mem_id_context hfrom l) then error_no_such_hypothesis env sigma hfrom in
  let rec splitrec left sign = match EConstr.match_named_context_val sign with
  | None -> assert false
  | Some (d, _, right) ->
    let hyp = NamedDecl.get_id d in
    if Id.equal hyp hfrom then (left, right, d)
    else splitrec (d :: left) right
  in
  splitrec [] l

let move_hyp env sigma toleft (left,declfrom,right) hto =
  let open EConstr in
  let push prefix sign = List.fold_right push_named_context_val prefix sign in
  let push_rev prefix sign = List.fold_left (fun accu d -> push_named_context_val d accu) sign prefix in
  let rec moverec_toleft ans first middle midvars = function
    | [] -> push middle @@ push first ans
    | d :: _ as right when move_location_eq hto (MoveBefore (NamedDecl.get_id d)) ->
      push_rev right @@ push middle @@ push first ans
    | d :: right ->
        let hyp = NamedDecl.get_id d in
        let (first', middle', midvars') =
          if occur_vars_in_decl env sigma midvars d then
            if not (move_location_eq hto (MoveAfter hyp)) then
              (first, d :: middle, Id.Set.add hyp midvars)
            else
              user_err ~hdr:"move_hyp" (str "Cannot move " ++ Id.print (NamedDecl.get_id declfrom) ++
                pr_move_location Id.print hto ++
                str ": it occurs in the type of "
                ++ Id.print hyp ++ str ".")
          else
            (d::first, middle, midvars)
        in
        if move_location_eq hto (MoveAfter hyp) then
          push_rev right @@ push middle' @@ push first' ans
        else
          moverec_toleft ans first' middle' midvars' right
  in
  let rec moverec_toright first middle depvars right = match EConstr.match_named_context_val right with
    | None -> push_rev first @@ push_rev middle right
    | Some (d, _, _) when move_location_eq hto (MoveBefore (NamedDecl.get_id d)) ->
        push_rev first @@ push_rev middle @@ right
    | Some (d, _, right) ->
        let hyp = NamedDecl.get_id d in
        let (first', middle', depvars') =
          if Id.Set.mem hyp depvars then
            if not (move_location_eq hto (MoveAfter hyp)) then
              let vars = global_vars_set_of_decl env sigma d in
              let depvars = Id.Set.union vars depvars in
              (first, d::middle, depvars)
            else
              user_err ~hdr:"move_hyp" (str "Cannot move " ++ Id.print (NamedDecl.get_id declfrom) ++
                pr_move_location Id.print hto ++
                str ": it depends on "
                ++ Id.print hyp ++ str ".")
          else
            (d::first, middle, depvars)
        in
        if move_location_eq hto (MoveAfter hyp) then
          push_rev first' @@ push_rev middle' @@ right
        else
          moverec_toright first' middle' depvars' right
  in
  if toleft then
    let id = NamedDecl.get_id declfrom in
    moverec_toleft right [] [declfrom] (Id.Set.singleton id) left
  else
    let depvars = global_vars_set_of_decl env sigma declfrom in
    let right = moverec_toright [] [declfrom] depvars right in
    push_rev left @@ right

let move_hyp_in_named_context env sigma hfrom hto sign =
  let (left, right, declfrom) = split_sign env sigma hfrom sign in
  let toleft = match hto with
  | MoveLast -> true
  | MoveAfter id | MoveBefore id ->
    if mem_id_context id right then false
    else if mem_id_context id sign then true
    else error_no_such_hypothesis env sigma id
  | MoveFirst -> false
  in
  move_hyp env sigma toleft (left,declfrom,right) hto

let insert_decl_in_named_context env sigma decl hto sign =
  move_hyp env sigma false ([],decl,sign) hto

(**********************************************************************)


(************************************************************************)
(************************************************************************)
(* Implementation of the logical rules *)

(* Will only be used on terms given to the Refine rule which have meta
variables only in Application and Case *)

let error_unsupported_deep_meta c =
  user_err  (strbrk "Application of lemmas whose beta-iota normal " ++
    strbrk "form contains metavariables deep inside the term is not " ++
    strbrk "supported; try \"refine\" instead.")

let collect_meta_variables c =
  let rec collrec deep acc c = match kind c with
    | Meta mv -> if deep then error_unsupported_deep_meta () else mv::acc
    | Cast(c,_,_) -> collrec deep acc c
    | Case(ci,u,pms,p,iv,c,br) ->
      let acc = Array.fold_left (collrec deep) acc pms in
      let acc = Constr.fold (collrec deep) acc (snd p) in
      let acc = Constr.fold_invert (collrec deep) acc iv in
      let acc = Constr.fold (collrec deep) acc c in
      Array.fold_left (fun accu (_, br) -> collrec deep accu br) acc br
    | App _ -> Constr.fold (collrec deep) acc c
    | Proj (_, c) -> collrec deep acc c
    | _ -> Constr.fold (collrec true) acc c
  in
  List.rev (collrec false [] c)

let check_meta_variables env sigma c =
  if not (List.distinct_f Int.compare (collect_meta_variables c)) then
    raise (RefinerError (env, sigma, NonLinearProof c))

let check_conv_leq_goal ~check env sigma arg ty conclty =
  if check then
    let ans = Reductionops.infer_conv env sigma (EConstr.of_constr ty) conclty in
    match ans with
    | Some evm -> evm
    | None -> raise (RefinerError (env, sigma, BadType (arg,ty,conclty)))
  else sigma

exception Stop of EConstr.t list
let meta_free_prefix sigma a =
  try
    let a = Array.map EConstr.of_constr a in
    let _ = Array.fold_left (fun acc a ->
      if occur_meta sigma a then raise (Stop acc)
      else a :: acc) [] a
    in a
  with Stop acc -> Array.rev_of_list acc

let goal_type_of ~check env sigma c =
  if check then
    let (sigma,t) = type_of env sigma (EConstr.of_constr c) in
    (sigma, EConstr.Unsafe.to_constr t)
  else (sigma, EConstr.Unsafe.to_constr (Retyping.get_type_of env sigma (EConstr.of_constr c)))

let rec mk_refgoals ~check env sigma goalacc conclty trm =
  let hyps = Environ.named_context_val env in
  let mk_goal hyps concl =
    Goal.V82.mk_goal sigma hyps concl
  in
    if (not check) && not (occur_meta sigma (EConstr.of_constr trm)) then
      let t'ty = Retyping.get_type_of env sigma (EConstr.of_constr trm) in
      let t'ty = EConstr.Unsafe.to_constr t'ty in
      let sigma = check_conv_leq_goal ~check env sigma trm t'ty conclty in
        (goalacc,t'ty,sigma,trm)
    else
      match kind trm with
      | Meta _ ->
        let conclty = nf_betaiota env sigma conclty in
          if check && occur_meta sigma conclty then
            raise (RefinerError (env, sigma, MetaInType conclty));
          let (gl,ev,sigma) = mk_goal hyps conclty in
          let ev = EConstr.Unsafe.to_constr ev in
          let conclty = EConstr.Unsafe.to_constr conclty in
          gl::goalacc, conclty, sigma, ev

      | Cast (t,k, ty) ->
        let sigma = check_typability ~check env sigma ty in
        let sigma = check_conv_leq_goal ~check env sigma trm ty conclty in
        let res = mk_refgoals ~check env sigma goalacc (EConstr.of_constr ty) t in
        (* we keep the casts (in particular VMcast and NATIVEcast) except
           when they are annotating metas *)
        if isMeta t then begin
          assert (k != VMcast && k != NATIVEcast);
          res
        end else
          let (gls,cty,sigma,ans) = res in
          let ans = if ans == t then trm else mkCast(ans,k,ty) in
          (gls,cty,sigma,ans)

      | App (f,l) ->
        let (acc',hdty,sigma,applicand) =
          if Termops.is_template_polymorphic_ind env sigma (EConstr.of_constr f) then
            let ty =
              (* Template polymorphism of definitions and inductive types *)
              let firstmeta = Array.findi (fun i x -> occur_meta sigma (EConstr.of_constr x)) l in
              let args, _ = Option.cata (fun i -> CArray.chop i l) (l, [||]) firstmeta in
                type_of_global_reference_knowing_parameters env sigma (EConstr.of_constr f) (Array.map EConstr.of_constr args)
            in
            let ty = EConstr.Unsafe.to_constr ty in
              goalacc, ty, sigma, f
          else
            mk_hdgoals ~check env sigma goalacc f
        in
        let ((acc'',conclty',sigma), args) = mk_arggoals ~check env sigma acc' hdty l in
        let sigma = check_conv_leq_goal ~check env sigma trm conclty' conclty in
        let ans = if applicand == f && args == l then trm else mkApp (applicand, args) in
        (acc'',conclty',sigma, ans)

      | Proj (p,c) ->
        let (acc',cty,sigma,c') = mk_hdgoals ~check env sigma goalacc c in
        let c = mkProj (p, c') in
        let ty = get_type_of env sigma (EConstr.of_constr c) in
        let ty = EConstr.Unsafe.to_constr ty in
          (acc',ty,sigma,c)

      | Case (ci, u, pms, p, iv, c, lf) ->
        (* XXX Is ignoring iv OK? *)
        let (ci, p, iv, c, lf) = Inductive.expand_case env (ci, u, pms, p, iv, c, lf) in
        let (acc',lbrty,conclty',sigma,p',c') = mk_casegoals ~check env sigma goalacc p c in
        let sigma = check_conv_leq_goal ~check env sigma trm conclty' conclty in
        let (acc'',sigma,rbranches) = treat_case ~check env sigma ci lbrty lf acc' in
        let lf' = Array.rev_of_list rbranches in
        let ans =
          if p' == p && c' == c && Array.equal (==) lf' lf then trm
          else mkCase (Inductive.contract_case env (ci,p',iv,c',lf'))
        in
        (acc'',conclty',sigma, ans)

      | _ ->
        if occur_meta sigma (EConstr.of_constr trm) then
          anomaly (Pp.str "refiner called with a meta in non app/case subterm.");
        let (sigma, t'ty) = goal_type_of ~check env sigma trm in
        let sigma = check_conv_leq_goal ~check env sigma trm t'ty conclty in
          (goalacc,t'ty,sigma, trm)

(* Same as mkREFGOALS but without knowing the type of the term. Therefore,
 * Metas should be casted. *)

and mk_hdgoals ~check env sigma goalacc trm =
  let hyps = Environ.named_context_val env in
  let mk_goal hyps concl =
    Goal.V82.mk_goal sigma hyps concl in
  match kind trm with
    | Cast (c,_, ty) when isMeta c ->
        let sigma = check_typability ~check env sigma ty in
        let (gl,ev,sigma) = mk_goal hyps (nf_betaiota env sigma (EConstr.of_constr ty)) in
        let ev = EConstr.Unsafe.to_constr ev in
        gl::goalacc,ty,sigma,ev

    | Cast (t,_, ty) ->
        let sigma = check_typability ~check env sigma ty in
        mk_refgoals ~check env sigma goalacc (EConstr.of_constr ty) t

    | App (f,l) ->
        let (acc',hdty,sigma,applicand) =
          if Termops.is_template_polymorphic_ind env sigma (EConstr.of_constr f)
          then
            let l' = meta_free_prefix sigma l in
           (goalacc,EConstr.Unsafe.to_constr (type_of_global_reference_knowing_parameters env sigma (EConstr.of_constr f) l'),sigma,f)
          else mk_hdgoals ~check env sigma goalacc f
        in
        let ((acc'',conclty',sigma), args) = mk_arggoals ~check env sigma acc' hdty l in
        let ans = if applicand == f && args == l then trm else mkApp (applicand, args) in
        (acc'',conclty',sigma, ans)

    | Case (ci, u, pms, p, iv, c, lf) ->
        (* XXX is ignoring iv OK? *)
        let (ci, p, iv, c, lf) = Inductive.expand_case env (ci, u, pms, p, iv, c, lf) in
        let (acc',lbrty,conclty',sigma,p',c') = mk_casegoals ~check env sigma goalacc p c in
        let (acc'',sigma,rbranches) = treat_case ~check env sigma ci lbrty lf acc' in
        let lf' = Array.rev_of_list rbranches in
        let ans =
          if p' == p && c' == c && Array.equal (==) lf' lf then trm
          else mkCase (Inductive.contract_case env (ci,p',iv,c',lf'))
        in
        (acc'',conclty',sigma, ans)

    | Proj (p,c) ->
         let (acc',cty,sigma,c') = mk_hdgoals ~check env sigma goalacc c in
         let c = mkProj (p, c') in
         let ty = get_type_of env sigma (EConstr.of_constr c) in
         let ty = EConstr.Unsafe.to_constr ty in
           (acc',ty,sigma,c)

    | _ ->
        if check && occur_meta sigma (EConstr.of_constr trm) then
          anomaly (Pp.str "refine called with a dependent meta.");
        let (sigma, ty) = goal_type_of env ~check sigma trm in
        goalacc, ty, sigma, trm

and mk_arggoals ~check env sigma goalacc funty allargs =
  let foldmap (goalacc, funty, sigma) harg =
    let t = whd_all env sigma (EConstr.of_constr funty) in
    let t = EConstr.Unsafe.to_constr t in
    let rec collapse t = match kind t with
    | LetIn (_, c1, _, b) -> collapse (subst1 c1 b)
    | _ -> t
    in
    let t = collapse t in
    match kind t with
    | Prod (_, c1, b) ->
      let (acc, hargty, sigma, arg) = mk_refgoals ~check env sigma goalacc (EConstr.of_constr c1) harg in
      (acc, subst1 harg b, sigma), arg
    | _ ->
      raise (RefinerError (env,sigma,CannotApply (t, harg)))
  in
  Array.Smart.fold_left_map foldmap (goalacc, funty, sigma) allargs

and mk_casegoals ~check env sigma goalacc p c =
  let (acc',ct,sigma,c') = mk_hdgoals ~check env sigma goalacc c in
  let ct = EConstr.of_constr ct in
  let (acc'',pt,sigma,p') = mk_hdgoals ~check env sigma acc' p in
  let ((ind, u), spec) =
    try Tacred.find_hnf_rectype env sigma ct
    with Not_found -> anomaly (Pp.str "mk_casegoals.") in
  let indspec = ((ind, EConstr.EInstance.kind sigma u), spec) in
  let (lbrty,conclty) = type_case_branches_with_names env sigma indspec p c in
  (acc'',lbrty,conclty,sigma,p',c')

and treat_case ~check env sigma ci lbrty lf acc' =
  let rec strip_outer_cast c = match kind c with
  | Cast (c,_,_) -> strip_outer_cast c
  | _ -> c in
  let decompose_app_vect c = match kind c with
  | App (f,cl) -> (f, cl)
  | _ -> (c,[||]) in
  Array.fold_left3
    (fun (lacc,sigma,bacc) ty fi n ->
        (* Deal with a branch in expanded form of the form
           Case(ci,p,c,[|eta-let-exp(Meta);...;eta-let-exp(Meta)|]) as
           if it were not so, so as to preserve compatibility with when
           destruct/case generated schemes of the form
           Case(ci,p,c,[|Meta;...;Meta|];
           CAUTION: it does not deal with the general case of eta-zeta
           reduced branches having a form different from Meta, as it
           would be theoretically the case with third-party code *)
        let ctx, body = Term.decompose_lam_n_decls n fi in
        let head, args = decompose_app_vect body in
        (* Strip cast because clenv_cast_meta adds a cast when the branch is
           eta-expanded but when not when the branch has the single-meta
           form [Meta] *)
        let head = strip_outer_cast head in
        if isMeta head then begin
          assert (args = Context.Rel.instance mkRel 0 ctx);
          let (r,_,s,head'') = mk_refgoals ~check env sigma lacc ty head in
          let fi' = it_mkLambda_or_LetIn (mkApp (head'',args)) ctx in
          (r,s,fi'::bacc)
        end
        else
          (* Supposed to be meta-free *)
          let sigma, t'ty = goal_type_of ~check env sigma fi in
          let sigma = check_conv_leq_goal ~check env sigma fi t'ty ty in
          (lacc,sigma,fi::bacc))
    (acc',sigma,[]) lbrty lf ci.ci_cstr_ndecls

let convert_hyp ~check ~reorder env sigma d =
  let id = NamedDecl.get_id d in
  let b = NamedDecl.get_value d in
  let sign = Environ.named_context_val env in
  match lookup_named_ctxt id sign with
  | exception Not_found ->
    if check then error_no_such_hypothesis env sigma id
    else sign
  | d' ->
    let c = Option.map EConstr.of_constr (NamedDecl.get_value d') in
    if check && not (is_conv env sigma (NamedDecl.get_type d) (EConstr.of_constr (NamedDecl.get_type d'))) then
      user_err ~hdr:"Logic.convert_hyp"
        (str "Incorrect change of the type of " ++ Id.print id ++ str ".");
    if check && not (Option.equal (is_conv env sigma) b c) then
      user_err ~hdr:"Logic.convert_hyp"
        (str "Incorrect change of the body of "++ Id.print id ++ str ".");
    let sign' = apply_to_hyp sign id (fun _ _ _ -> EConstr.Unsafe.to_named_decl d) in
    if reorder then reorder_val_context env sigma sign' (check_decl_position env sigma sign d)
    else sign'

(************************************************************************)
(************************************************************************)
(* Primitive tactics are handled here *)

let refiner ~check r =
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  let env = Proofview.Goal.env gl in
  let st = Proofview.Goal.state gl in
  let cl = Proofview.Goal.concl gl in
  check_meta_variables env sigma r;
  let (sgl,cl',sigma,oterm) = mk_refgoals ~check env sigma [] cl r in
  let map gl = Proofview.goal_with_state gl st in
  let sgl = List.rev_map map sgl in
  let sigma = Goal.V82.partial_solution env sigma (Proofview.Goal.goal gl) (EConstr.of_constr oterm) in
  Proofview.Unsafe.tclEVARS sigma <*>
  Proofview.Unsafe.tclSETGOALS sgl
  end
