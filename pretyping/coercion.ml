(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Hugo Herbelin for Coq V7 by isolating the coercion
   mechanism out of the type inference algorithm in file trad.ml from
   Coq V6.3, Nov 1999; The coercion mechanism was implemented in
   trad.ml by Amokrane Saïbi, May 1996 *)
(* Addition of products and sorts in canonical structures by Pierre
   Corbineau, Feb 2008 *)
(* Turned into an abstract compilation unit by Matthieu Sozeau, March 2006 *)

open CErrors
open Util
open Names
open Term
open Constr
open Context
open Environ
open EConstr
open Vars
open Reductionops
open Pretype_errors
open Coercionops
open Evarutil
open Evarconv
open Evd
open Globnames

let get_use_typeclasses_for_conversion =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Typeclass"; "Resolution"; "For"; "Conversion"]
    ~value:true

(* Typing operations dealing with coercions *)
exception NoCoercion
exception NoCoercionNoUnifier of evar_map * unification_error

(* Here, funj is a coercion therefore already typed in global context *)
let apply_coercion_args env sigma check isproj argl funj =
  let rec apply_rec sigma acc typ = function
    | [] ->
      (match isproj with
       | Some p ->
         let npars = Projection.Repr.npars p in
         let p = Projection.make p false in
         let args = List.skipn npars argl in
         let hd, tl = match args with hd :: tl -> hd, tl | [] -> assert false in
         sigma, { uj_val = applist (mkProj (p, hd), tl);
                  uj_type = typ }
       | None ->
         sigma, { uj_val = applist (j_val funj,argl);
                  uj_type = typ })
    | h::restl -> (* On devrait pouvoir s'arranger pour qu'on n'ait pas a faire hnf_constr *)
      match EConstr.kind sigma (whd_all env sigma typ) with
      | Prod (_,c1,c2) ->
        let sigma =
          if check then
            begin match Evarconv.unify_leq_delay env sigma (Retyping.get_type_of env sigma h) c1 with
              | exception Evarconv.UnableToUnify _ -> raise NoCoercion
              | sigma -> sigma
            end
          else sigma
        in
        apply_rec sigma (h::acc) (subst1 h c2) restl
      | _ -> anomaly (Pp.str "apply_coercion_args.")
  in
  apply_rec sigma [] funj.uj_type argl

(* appliquer le chemin de coercions de patterns p *)
let apply_pattern_coercion ?loc pat p =
  List.fold_left
    (fun pat (co,n) ->
       let f i =
         if i<n then (DAst.make ?loc @@ Glob_term.PatVar Anonymous) else pat in
        DAst.make ?loc @@ Glob_term.PatCstr (co, List.init (n+1) f, Anonymous))
    pat p

(* raise Not_found if no coercion found *)
let inh_pattern_coerce_to ?loc env pat ind1 ind2 =
  let p = lookup_pattern_path_between env (ind1,ind2) in
    apply_pattern_coercion ?loc pat p

(* Program coercions *)

open Program

let make_existential ?loc ?(opaque = not (get_proofs_transparency ())) na env sigma c =
  let src = Loc.tag ?loc (Evar_kinds.QuestionMark {
      Evar_kinds.default_question_mark with
      Evar_kinds.qm_obligation=Evar_kinds.Define opaque;
      Evar_kinds.qm_name=na;
  }) in
  let sigma, v = Evarutil.new_evar env sigma ~src c in
  let sigma = Evd.set_obligation_evar sigma (fst (destEvar sigma v)) in
  sigma, v

let app_opt env sigma f t =
  let sigma, t =
  match f with
  | None -> sigma, t
  | Some f -> f sigma t
  in
  sigma, whd_betaiota env sigma t

let pair_of_array a = (a.(0), a.(1))

let disc_subset sigma x =
  match EConstr.kind sigma x with
  | App (c, l) ->
      (match EConstr.kind sigma c with
       Ind (i,_) ->
         let len = Array.length l in
         let sigty = delayed_force sig_typ in
           if Int.equal len 2 && eq_ind i (Globnames.destIndRef sigty)
           then
             let (a, b) = pair_of_array l in
               Some (a, b)
           else None
       | _ -> None)
  | _ -> None

exception NoSubtacCoercion

let hnf env sigma c = whd_all env sigma c
let hnf_nodelta env sigma c = whd_betaiota env sigma c

let lift_args n sign =
  let rec liftrec k = function
    | t::sign -> liftn n k t :: (liftrec (k-1) sign)
    | [] -> []
  in
    liftrec (List.length sign) sign

let coerce ?loc env sigma (x : EConstr.constr) (y : EConstr.constr)
  : evar_map * (evar_map -> EConstr.constr -> evar_map * EConstr.constr) option
  =
  let open Context.Rel.Declaration in
  let rec coerce_unify env sigma x y =
    let x = hnf env sigma x and y = hnf env sigma y in
    try
      Evarconv.unify_leq_delay env sigma x y, None
    with
      Evarconv.UnableToUnify _ -> coerce' env sigma x y
  and coerce' env sigma x y : evar_map * (evar_map -> EConstr.constr -> evar_map * EConstr.constr) option =
    let subco sigma = subset_coerce env sigma x y in
    let dest_prod c =
      match Reductionops.splay_prod_n env sigma 1 c with
      | [LocalAssum (na,t) | LocalDef (na,_,t)], c -> (na, t), c
      | _ -> raise NoSubtacCoercion
    in
    let coerce_application sigma typ typ' c c' l l' =
      let len = Array.length l in
      let rec aux sigma tele typ typ' i co =
        if i < len then
          let hdx = l.(i) and hdy = l'.(i) in
          try
            let sigma = unify_leq_delay env sigma hdx hdy in
            let (n, eqT), restT = dest_prod typ in
            let (n', eqT'), restT' = dest_prod typ' in
            aux sigma (hdx :: tele) (subst1 hdx restT) (subst1 hdy restT') (succ i) co
          with UnableToUnify _ as exn ->
            let _, info = Exninfo.capture exn in
            let (n, eqT), restT = dest_prod typ in
            let (n', eqT'), restT' = dest_prod typ' in
            let sigma =
              try
                unify_leq_delay env sigma eqT eqT'
              with UnableToUnify _ ->
                let e, info = Exninfo.capture exn in
                Exninfo.iraise (NoSubtacCoercion,info)
            in
            (* Disallow equalities on arities *)
            if Reductionops.is_arity env sigma eqT then
              Exninfo.iraise (NoSubtacCoercion,info);
            let restargs = lift_args 1
                (List.rev (Array.to_list (Array.sub l (succ i) (len - (succ i)))))
            in
            let args = List.rev (restargs @ mkRel 1 :: List.map (lift 1) tele) in
            let pred = mkLambda (n, eqT, applist (lift 1 c, args)) in
            let sigma, eq = papp sigma coq_eq_ind [| eqT; hdx; hdy |] in
            let sigma, evar = make_existential ?loc n.binder_name env sigma eq in
            let eq_app sigma x = papp sigma coq_eq_rect
                [| eqT; hdx; pred; x; hdy; evar|]
            in
            aux sigma (hdy :: tele) (subst1 hdx restT)
              (subst1 hdy restT') (succ i)  (fun sigma x -> let sigma, x = co sigma x in eq_app sigma x)
        else
          sigma, Some (fun sigma x ->
              let sigma, term = co sigma x in
              let sigma, term = Typing.solve_evars env sigma term in
              sigma, term)
      in
      if isEvar sigma c || isEvar sigma c' || not (Program.is_program_generalized_coercion ()) then
        (* Second-order unification needed. *)
        raise NoSubtacCoercion;
      aux sigma [] typ typ' 0 (fun sigma x -> sigma, x)
    in
    match (EConstr.kind sigma x, EConstr.kind sigma y) with
    | Sort s, Sort s' ->
      (match ESorts.kind sigma s, ESorts.kind sigma s' with
       | Prop, Prop | Set, Set -> sigma, None
       | (Prop | Set), Type _ -> sigma, None
       | Type x, Type y when Univ.Universe.equal x y -> sigma, None (* false *)
       | _ -> subco sigma)
    | Prod (name, a, b), Prod (name', a', b') ->
      let name' =
        {name' with
         binder_name =
           Name (Namegen.next_ident_away
                   Namegen.default_dependent_ident (Termops.vars_of_env env))}
      in
      let env' = push_rel (LocalAssum (name', a')) env in
      let sigma, c1 = coerce_unify env' sigma (lift 1 a') (lift 1 a) in
      (* env, x : a' |- c1 : lift 1 a' > lift 1 a *)
      let sigma, coec1 = app_opt env' sigma c1 (mkRel 1) in
      (* env, x : a' |- c1[x] : lift 1 a *)
      let sigma, c2 = coerce_unify env' sigma (subst1 coec1 (liftn 1 2 b)) b' in
      (* env, x : a' |- c2 : b[c1[x]/x]] > b' *)
      (match c1, c2 with
       | None, None -> sigma, None
       | _, _ ->
         sigma,
         Some (fun sigma f ->
             let sigma, t = app_opt env' sigma c2
                 (mkApp (lift 1 f, [| coec1 |])) in
             sigma, mkLambda (name', a', t)))

    | App (c, l), App (c', l') ->
      (match EConstr.kind sigma c, EConstr.kind sigma c' with
         Ind (i, u), Ind (i', u') -> (* Inductive types *)
         let len = Array.length l in
         let sigT = delayed_force sigT_typ in
         let prod = delayed_force prod_typ in
         (* Sigma types *)
         if Int.equal len (Array.length l') && Int.equal len 2 && eq_ind i i'
            && (eq_ind i (destIndRef sigT) || eq_ind i (destIndRef prod))
         then
           if eq_ind i (destIndRef sigT)
           then
             begin
               let (a, pb), (a', pb') =
                 pair_of_array l, pair_of_array l'
               in
               let sigma, c1 = coerce_unify env sigma a a' in
               let remove_head sigma a c =
                 match EConstr.kind sigma c with
                 | Lambda (n, t, t') -> sigma, (c, t')
                 | Evar (k, args) ->
                   let (sigma, t) = Evardefine.define_evar_as_lambda env sigma (k,args) in
                   let (n, dom, rng) = destLambda sigma t in
                   let sigma =
                     if isEvar sigma dom then
                       let (domk, args) = destEvar sigma dom in
                       define domk a sigma
                     else sigma
                   in
                   sigma, (t, rng)
                 | _ -> raise NoSubtacCoercion
               in
               let sigma, (pb, b) = remove_head sigma a pb in
               let sigma, (pb', b') = remove_head sigma a' pb' in
               let ra = Retyping.relevance_of_type env sigma a in
               let env' = push_rel
                   (LocalAssum (make_annot (Name Namegen.default_dependent_ident) ra, a))
                   env
               in
               let sigma, c2 = coerce_unify env' sigma b b' in
               match c1, c2 with
               | None, None -> sigma, None
               | _, _ ->
                 sigma,
                 Some (fun sigma x ->
                     let sigma, t1 = papp sigma sigT_proj1 [| a; pb; x |] in
                     let sigma, t2 = papp sigma sigT_proj2 [| a; pb; x |] in
                     let sigma, x =  app_opt env' sigma c1 t1 in
                     let sigma, y = app_opt env' sigma c2 t2 in
                     papp sigma sigT_intro [| a'; pb'; x ; y |])
             end
           else
             begin
               let (a, b), (a', b') =
                 pair_of_array l, pair_of_array l'
               in
               let sigma, c1 = coerce_unify env sigma a a' in
               let sigma, c2 = coerce_unify env sigma b b' in
               match c1, c2 with
               | None, None -> sigma, None
               | _, _ ->
                 sigma,
                 Some (fun sigma x ->
                     let sigma, t1 = papp sigma prod_proj1 [| a; b; x |] in
                     let sigma, t2 = papp sigma prod_proj2 [| a; b; x |] in
                     let sigma, x = app_opt env sigma c1 t1 in
                     let sigma, y = app_opt env sigma c2 t2 in
                     papp sigma prod_intro [| a'; b'; x ; y |])
             end
         else
         if eq_ind i i' && Int.equal len (Array.length l') then
           (try subco sigma
            with NoSubtacCoercion ->
              let sigma, typ = Typing.type_of env sigma c in
              let sigma, typ' = Typing.type_of env sigma c' in
              coerce_application sigma typ typ' c c' l l')
         else
           subco sigma
       | x, y when EConstr.eq_constr sigma c c' ->
         if Int.equal (Array.length l) (Array.length l') then
           let sigma, lam_type = Typing.type_of env sigma c in
           let sigma, lam_type' = Typing.type_of env sigma c' in
           coerce_application sigma lam_type lam_type' c c' l l'
         else subco sigma
       | _ -> subco sigma)
    | _, _ ->  subco sigma

  and subset_coerce env sigma x y =
    match disc_subset sigma x with
      Some (u, p) ->
      let sigma, c = coerce_unify env sigma u y in
      let f sigma x =
        let sigma, t = papp sigma sig_proj1 [| u; p; x |] in
        app_opt env sigma c t
      in sigma, Some f
    | None ->
      match disc_subset sigma y with
        Some (u, p) ->
        let sigma, c = coerce_unify env sigma x u in
        sigma, Some
          (fun sigma x ->
             let sigma, cx = app_opt env sigma c x in
             let sigma, evar = make_existential ?loc Anonymous env sigma (mkApp (p, [| cx |]))
             in
             (papp sigma sig_intro [| u; p; cx; evar |]))
      | None ->
        raise NoSubtacCoercion
  in coerce_unify env sigma x y

let app_coercion env sigma coercion v =
  match coercion with
  | None -> sigma, v
  | Some f ->
    let sigma, v' = f sigma v in
    let sigma, v' = Typing.solve_evars env sigma v' in
    sigma, whd_betaiota env sigma v'

let coerce_itf ?loc env sigma v t c1 =
  let sigma, coercion = coerce ?loc env sigma t c1 in
  app_coercion env sigma coercion v

let saturate_evd env sigma =
  Typeclasses.resolve_typeclasses
    ~filter:Typeclasses.no_goals ~split:true ~fail:false env sigma

type coercion_trace =
  | IdCoe
  | PrimProjCoe of {
      proj : Projection.Repr.t;
      args : econstr list;
      previous : coercion_trace;
    }
  | Coe of {
      head : econstr;
      args : econstr list;
      previous : coercion_trace;
    }
  | ProdCoe of { na : Name.t binder_annot; ty : econstr; dom : coercion_trace; body : coercion_trace }

let empty_coercion_trace = IdCoe

(* similar to iterated apply_coercion_args *)
let rec reapply_coercions sigma trace c = match trace with
  | IdCoe -> c
  | PrimProjCoe { proj; args; previous } ->
    let c = reapply_coercions sigma previous c in
    let args = args@[c] in
    let head, args = match args with [] -> assert false | hd :: tl -> hd, tl in
    applist (mkProj (Projection.make proj false, head), args)
  | Coe {head; args; previous} ->
    let c = reapply_coercions sigma previous c in
    let args = args@[c] in
    applist (head, args)
  | ProdCoe { na; ty; dom; body } ->
    let x = reapply_coercions sigma dom (mkRel 1) in
    let c = beta_applist sigma (lift 1 c, [x]) in
    let c = reapply_coercions sigma body c in
    mkLambda (na, ty, c)

(* Apply coercion path from p to hj; raise NoCoercion if not applicable *)
let apply_coercion env sigma p hj typ_cl =
  let j,t,trace,sigma =
    List.fold_left
      (fun (ja,typ_cl,trace,sigma) i ->
         let isid = i.coe_is_identity in
         let isproj = i.coe_is_projection in
         let sigma, c = new_global sigma i.coe_value in
         let typ = Retyping.get_type_of env sigma c in
         let fv = make_judge c typ in
         let argl = class_args_of env sigma typ_cl in
         let trace =
           if isid then trace
           else match isproj with
           | None -> Coe {head=fv.uj_val;args=argl;previous=trace}
           | Some proj ->
             let args = List.skipn (Projection.Repr.npars proj) argl in
             PrimProjCoe {proj; args; previous=trace }
         in
         let argl = argl@[ja.uj_val] in
         let sigma, jres = apply_coercion_args env sigma true isproj argl fv in
         let jres =
         if isid then
            { uj_val = ja.uj_val; uj_type = jres.uj_type }
          else
            jres
         in
         jres, jres.uj_type, trace, sigma)
      (hj,typ_cl,IdCoe,sigma) p
  in sigma, j, trace

let mu env sigma t =
  let rec aux v =
    let v' = hnf env sigma v in
      match disc_subset sigma v' with
      | Some (u, p) ->
        let sigma, (f, ct, trace) = aux u in
        let p = hnf_nodelta env sigma p in
        let p1 = delayed_force sig_proj1 in
        let sigma, p1 = Evarutil.new_global sigma p1 in
        sigma,
          (Some (fun sigma x ->
                   app_opt env sigma
                     f (mkApp (p1, [| u; p; x |]))),
           ct,
           Coe {head=p1; args=[u;p]; previous=trace})
      | None -> sigma, (None, v, IdCoe)
  in aux t

(* Try to coerce to a funclass; raise NoCoercion if not possible *)
let inh_app_fun_core ~program_mode env sigma j =
  let t = whd_all env sigma j.uj_type in
    match EConstr.kind sigma t with
    | Prod _ -> (sigma,j,IdCoe)
    | Evar ev ->
        let (sigma,t) = Evardefine.define_evar_as_product env sigma ev in
          (sigma,{ uj_val = j.uj_val; uj_type = t },IdCoe)
    | _ ->
        try let t,p =
          lookup_path_to_fun_from env sigma j.uj_type in
            apply_coercion env sigma p j t
       with (Not_found | NoCoercion) as exn ->
         let _, info = Exninfo.capture exn in
         if program_mode then
           try
             let sigma, (coercef, t, trace) = mu env sigma t in
             let sigma, uj_val = app_opt env sigma coercef j.uj_val in
             let res = { uj_val ; uj_type = t } in
             (sigma, res, trace)
           with NoSubtacCoercion | NoCoercion ->
             (sigma,j,IdCoe)
         else Exninfo.iraise (NoCoercion,info)

(* Try to coerce to a funclass; returns [j] if no coercion is applicable *)
let inh_app_fun ~program_mode resolve_tc env sigma j =
  try inh_app_fun_core ~program_mode env sigma j
  with
  | NoCoercion when not resolve_tc
    || not (get_use_typeclasses_for_conversion ()) -> (sigma, j, IdCoe)
  | NoCoercion ->
    try inh_app_fun_core ~program_mode env (saturate_evd env sigma) j
    with NoCoercion -> (sigma, j, IdCoe)

let type_judgment env sigma j =
  match EConstr.kind sigma (whd_all env sigma j.uj_type) with
    | Sort s -> {utj_val = j.uj_val; utj_type = ESorts.kind sigma s }
    | _ -> error_not_a_type env sigma j

let inh_tosort_force ?loc env sigma j =
  try
    let t,p = lookup_path_to_sort_from env sigma j.uj_type in
    let sigma,j1,_trace = apply_coercion env sigma p j t in
    let j2 = Environ.on_judgment_type (whd_evar sigma) j1 in
      (sigma,type_judgment env sigma j2)
  with Not_found | NoCoercion ->
    error_not_a_type ?loc env sigma j

let inh_coerce_to_sort ?loc env sigma j =
  let typ = whd_all env sigma j.uj_type in
    match EConstr.kind sigma typ with
    | Sort s -> (sigma,{ utj_val = j.uj_val; utj_type = ESorts.kind sigma s })
    | Evar ev ->
        let (sigma,s) = Evardefine.define_evar_as_sort env sigma ev in
          (sigma,{ utj_val = j.uj_val; utj_type = s })
    | _ ->
        inh_tosort_force ?loc env sigma j

let inh_coerce_to_base ?loc ~program_mode env sigma j =
  if program_mode then
    let sigma, (ct, typ', _trace) = mu env sigma j.uj_type in
    let sigma, uj_val = app_coercion env sigma ct j.uj_val in
    let res = { uj_val; uj_type = typ' } in
    sigma, res
  else (sigma, j)

let inh_coerce_to_prod ?loc ~program_mode env sigma t =
  if program_mode then
    let sigma, (_, typ', _trace) = mu env sigma t in
    sigma, typ'
  else (sigma, t)

let inh_coerce_to_fail flags env sigma rigidonly v t c1 =
  if rigidonly && not (Heads.is_rigid env (EConstr.Unsafe.to_constr c1) && Heads.is_rigid env (EConstr.Unsafe.to_constr t))
  then
    raise NoCoercion
  else
    let sigma, v', t', trace =
      try
        let t2,t1,p = lookup_path_between env sigma (t,c1) in
        let sigma,j,trace =
          apply_coercion env sigma p
            {uj_val = v; uj_type = t} t2
        in
        sigma, j.uj_val, j.uj_type, trace
      with Not_found -> raise NoCoercion
    in
    try (unify_leq_delay ~flags env sigma t' c1, v', trace)
    with Evarconv.UnableToUnify _ as exn ->
      let _, info = Exninfo.capture exn in
      Exninfo.iraise (NoCoercion,info)

let default_flags_of env =
  default_flags_of TransparentState.full

let rec inh_conv_coerce_to_fail ?loc env sigma ?(flags=default_flags_of env) rigidonly v t c1 =
  try (unify_leq_delay ~flags env sigma t c1, v, IdCoe)
  with UnableToUnify (best_failed_sigma,e) ->
    try inh_coerce_to_fail flags env sigma rigidonly v t c1
    with NoCoercion as exn ->
      let _, info = Exninfo.capture exn in
      match
      EConstr.kind sigma (whd_all env sigma t),
      EConstr.kind sigma (whd_all env sigma c1)
      with
      | Prod (name,t1,t2), Prod (_,u1,u2) ->
          (* Conversion did not work, we may succeed with a coercion. *)
          (* We eta-expand (hence possibly modifying the original term!) *)
          (* and look for a coercion c:u1->t1 s.t. fun x:u1 => v' (c x)) *)
          (* has type forall (x:u1), u2 (with v' recursively obtained) *)
          (* Note: we retype the term because template polymorphism may have *)
          (* weakened its type *)
          let name = map_annot (function
            | Anonymous -> Name Namegen.default_dependent_ident
            | na -> na) name in
          let open Context.Rel.Declaration in
          let env1 = push_rel (LocalAssum (name,u1)) env in
          let (sigma, v1, trace1) =
            inh_conv_coerce_to_fail ?loc env1 sigma rigidonly
              (mkRel 1) (lift 1 u1) (lift 1 t1) in
          let v2 = beta_applist sigma (lift 1 v,[v1]) in
          let t2 = Retyping.get_type_of env1 sigma v2 in
          let (sigma,v2',trace2) = inh_conv_coerce_to_fail ?loc env1 sigma rigidonly v2 t2 u2 in
          let trace = ProdCoe { na=name; ty=u1; dom=trace1; body=trace2 } in
          (sigma, mkLambda (name, u1, v2'), trace)
      | _ ->
        Exninfo.iraise (NoCoercionNoUnifier (best_failed_sigma,e), info)

(* Look for cj' obtained from cj by inserting coercions, s.t. cj'.typ = t *)
let inh_conv_coerce_to_gen ?loc ~program_mode resolve_tc rigidonly flags env sigma cj t =
  let (sigma, val', otrace) =
    try
      let (sigma, val', trace) = inh_conv_coerce_to_fail ?loc env sigma ~flags rigidonly cj.uj_val cj.uj_type t in
      (sigma, val', Some trace)
    with NoCoercionNoUnifier (best_failed_sigma,e) as exn ->
      let _, info = Exninfo.capture exn in
      try
        if program_mode then
          let (sigma, val') = coerce_itf ?loc env sigma cj.uj_val cj.uj_type t in
          (sigma, val', None)
        else Exninfo.iraise (NoSubtacCoercion,info)
      with
      | NoSubtacCoercion as exn when not resolve_tc || not (get_use_typeclasses_for_conversion ()) ->
        let _, info = Exninfo.capture exn in
        error_actual_type ?loc ~info env best_failed_sigma cj t e
      | NoSubtacCoercion as exn ->
        let _, info = Exninfo.capture exn in
        let sigma' = saturate_evd env sigma in
          try
            if sigma' == sigma then
              error_actual_type ?loc ~info env best_failed_sigma cj t e
            else
              let sigma = sigma' in
              let (sigma, val', trace) = inh_conv_coerce_to_fail ?loc env sigma rigidonly cj.uj_val cj.uj_type t in
              (sigma, val', Some trace)
          with NoCoercionNoUnifier (_sigma,_error) as exn ->
            let _, info = Exninfo.capture exn in
            error_actual_type ?loc ~info env best_failed_sigma cj t e
  in
  (sigma,{ uj_val = val'; uj_type = t },otrace)

let inh_conv_coerce_to ?loc ~program_mode resolve_tc env sigma ?(flags=default_flags_of env) =
  inh_conv_coerce_to_gen ?loc ~program_mode resolve_tc false flags env sigma
let inh_conv_coerce_rigid_to ?loc ~program_mode resolve_tc env sigma ?(flags=default_flags_of env) =
  inh_conv_coerce_to_gen ?loc ~program_mode resolve_tc true flags env sigma
