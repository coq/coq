(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
    ~name:"use typeclass resolution during conversion"
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

let make_existential ?loc ?(opaque = not (get_proofs_transparency ())) na env evdref c =
  let src = Loc.tag ?loc (Evar_kinds.QuestionMark {
      Evar_kinds.default_question_mark with
      Evar_kinds.qm_obligation=Evar_kinds.Define opaque;
      Evar_kinds.qm_name=na;
  }) in
  let evd, v = Evarutil.new_evar env !evdref ~src c in
  let evd = Evd.set_obligation_evar evd (fst (destEvar evd v)) in
  evdref := evd;
  v

let app_opt env evdref f t =
  whd_betaiota !evdref (app_opt f t)

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

let hnf env evd c = whd_all env evd c
let hnf_nodelta env evd c = whd_betaiota evd c

let lift_args n sign =
  let rec liftrec k = function
    | t::sign -> liftn n k t :: (liftrec (k-1) sign)
    | [] -> []
  in
    liftrec (List.length sign) sign

let coerce ?loc env evdref (x : EConstr.constr) (y : EConstr.constr)
    : (EConstr.constr -> EConstr.constr) option
    =
  let open Context.Rel.Declaration in
  let rec coerce_unify env x y =
    let x = hnf env !evdref x and y = hnf env !evdref y in
      try
        evdref := Evarconv.unify_leq_delay env !evdref x y;
        None
      with UnableToUnify _ -> coerce' env x y
  and coerce' env x y : (EConstr.constr -> EConstr.constr) option =
    let subco () = subset_coerce env evdref x y in
    let dest_prod c =
      match Reductionops.splay_prod_n env (!evdref) 1 c with
      | [LocalAssum (na,t) | LocalDef (na,_,t)], c -> (na, t), c
      | _ -> raise NoSubtacCoercion
    in
    let coerce_application typ typ' c c' l l' =
      let len = Array.length l in
      let rec aux tele typ typ' i co =
        if i < len then
          let hdx = l.(i) and hdy = l'.(i) in
            try evdref := unify_leq_delay env !evdref hdx hdy;
              let (n, eqT), restT = dest_prod typ in
              let (n', eqT'), restT' = dest_prod typ' in
                aux (hdx :: tele) (subst1 hdx restT) (subst1 hdy restT') (succ i) co
            with UnableToUnify _ ->
              let (n, eqT), restT = dest_prod typ in
              let (n', eqT'), restT' = dest_prod typ' in
              let () =
                try evdref := unify_leq_delay env !evdref eqT eqT'
                with UnableToUnify _ -> raise NoSubtacCoercion
              in
                (* Disallow equalities on arities *)
                if Reductionops.is_arity env !evdref eqT then raise NoSubtacCoercion;
                let restargs = lift_args 1
                  (List.rev (Array.to_list (Array.sub l (succ i) (len - (succ i)))))
                in
                let args = List.rev (restargs @ mkRel 1 :: List.map (lift 1) tele) in
                let pred = mkLambda (n, eqT, applist (lift 1 c, args)) in
                let eq = papp evdref coq_eq_ind [| eqT; hdx; hdy |] in
                let evar = make_existential ?loc n.binder_name env evdref eq in
                let eq_app x = papp evdref coq_eq_rect
                  [| eqT; hdx; pred; x; hdy; evar|]
                in
                  aux (hdy :: tele) (subst1 hdx restT)
                    (subst1 hdy restT') (succ i)  (fun x -> eq_app (co x))
        else Some (fun x ->
          let term = co x in
          let sigma, term = Typing.solve_evars env !evdref term in
          evdref := sigma; term)
      in
        if isEvar !evdref c || isEvar !evdref c' || not (Program.is_program_generalized_coercion ()) then
          (* Second-order unification needed. *)
          raise NoSubtacCoercion;
        aux [] typ typ' 0 (fun x -> x)
    in
      match (EConstr.kind !evdref x, EConstr.kind !evdref y) with
      | Sort s, Sort s' ->
        (match ESorts.kind !evdref s, ESorts.kind !evdref s' with
        | Prop, Prop | Set, Set -> None
        | (Prop | Set), Type _ -> None
        | Type x, Type y when Univ.Universe.equal x y -> None (* false *)
        | _ -> subco ())
      | Prod (name, a, b), Prod (name', a', b') ->
          let name' =
            {name' with
             binder_name =
               Name (Namegen.next_ident_away
                       Namegen.default_dependent_ident (Id.AvoidSet.of_pred (Environ.mem_var env)))}
          in
          let env' = push_rel (LocalAssum (name', a')) env in
          let c1 = coerce_unify env' (lift 1 a') (lift 1 a) in
            (* env, x : a' |- c1 : lift 1 a' > lift 1 a *)
          let coec1 = app_opt env' evdref c1 (mkRel 1) in
            (* env, x : a' |- c1[x] : lift 1 a *)
          let c2 = coerce_unify env' (subst1 coec1 (liftn 1 2 b)) b' in
            (* env, x : a' |- c2 : b[c1[x]/x]] > b' *)
            (match c1, c2 with
             | None, None -> None
             | _, _ ->
                 Some
                   (fun f ->
                      mkLambda (name', a',
                                app_opt env' evdref c2
                                  (mkApp (lift 1 f, [| coec1 |])))))

      | App (c, l), App (c', l') ->
          (match EConstr.kind !evdref c, EConstr.kind !evdref c' with
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
                     let c1 = coerce_unify env a a' in
                     let remove_head a c =
                       match EConstr.kind !evdref c with
                       | Lambda (n, t, t') -> c, t'
                       | Evar (k, args) ->
                           let (evs, t) = Evardefine.define_evar_as_lambda env !evdref (k,args) in
                             evdref := evs;
                             let (n, dom, rng) = destLambda !evdref t in
                               if isEvar !evdref dom then
                                 let (domk, args) = destEvar !evdref dom in
                                   evdref := define domk a !evdref;
                               else ();
                               t, rng
                       | _ -> raise NoSubtacCoercion
                     in
                     let (pb, b), (pb', b') = remove_head a pb, remove_head a' pb' in
                     let ra = Retyping.relevance_of_type env !evdref a in
                     let env' = push_rel
                         (LocalAssum (make_annot (Name Namegen.default_dependent_ident) ra, a))
                         env
                     in
                     let c2 = coerce_unify env' b b' in
                       match c1, c2 with
                       | None, None -> None
                       | _, _ ->
                           Some
                             (fun x ->
                                let x, y =
                                  app_opt env' evdref c1 (papp evdref sigT_proj1
                                                            [| a; pb; x |]),
                                  app_opt env' evdref c2 (papp evdref sigT_proj2
                                                          [| a; pb; x |])
                                in
                                  papp evdref sigT_intro [| a'; pb'; x ; y |])
                   end
                 else
                   begin
                     let (a, b), (a', b') =
                       pair_of_array l, pair_of_array l'
                     in
                     let c1 = coerce_unify env a a' in
                     let c2 = coerce_unify env b b' in
                       match c1, c2 with
                       | None, None -> None
                       | _, _ ->
                           Some
                             (fun x ->
                                let x, y =
                                  app_opt env evdref c1 (papp evdref prod_proj1
                                                           [| a; b; x |]),
                                  app_opt env evdref c2 (papp evdref prod_proj2
                                                           [| a; b; x |])
                                in
                                  papp evdref prod_intro [| a'; b'; x ; y |])
                   end
               else
                 if eq_ind i i' && Int.equal len (Array.length l') then
                   let evm = !evdref in
                     (try subco ()
                      with NoSubtacCoercion ->
                        let typ = Typing.unsafe_type_of env evm c in
                        let typ' = Typing.unsafe_type_of env evm c' in
                          coerce_application typ typ' c c' l l')
                 else
                   subco ()
           | x, y when EConstr.eq_constr !evdref c c' ->
               if Int.equal (Array.length l) (Array.length l') then
                 let evm =  !evdref in
                 let lam_type = Typing.unsafe_type_of env evm c in
                 let lam_type' = Typing.unsafe_type_of env evm c' in
                   coerce_application lam_type lam_type' c c' l l'
               else subco ()
           | _ -> subco ())
      | _, _ ->  subco ()

  and subset_coerce env evdref x y =
    match disc_subset !evdref x with
    Some (u, p) ->
      let c = coerce_unify env u y in
      let f x =
        app_opt env evdref c (papp evdref sig_proj1 [| u; p; x |])
      in Some f
    | None ->
        match disc_subset !evdref y with
        Some (u, p) ->
          let c = coerce_unify env x u in
            Some
              (fun x ->
                 let cx = app_opt env evdref c x in
                 let evar = make_existential ?loc Anonymous env evdref (mkApp (p, [| cx |]))
                 in
                   (papp evdref sig_intro [| u; p; cx; evar |]))
        | None ->
            raise NoSubtacCoercion
  in coerce_unify env x y

let app_coercion env evdref coercion v =
  match coercion with
  | None -> v
  | Some f ->
    let sigma, v' = Typing.solve_evars env !evdref (f v) in
    evdref := sigma;
    whd_betaiota !evdref v'

let coerce_itf ?loc env evd v t c1 =
  let evdref = ref evd in
  let coercion = coerce ?loc env evdref t c1 in
  let t = app_coercion env evdref coercion v in
  !evdref, t

let saturate_evd env evd =
  Typeclasses.resolve_typeclasses
    ~filter:Typeclasses.no_goals ~split:true ~fail:false env evd

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
  let j,t,trace,evd =
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
  in evd, j, trace

let mu env evdref t =
  let rec aux v =
    let v' = hnf env !evdref v in
      match disc_subset !evdref v' with
      | Some (u, p) ->
        let f, ct, trace = aux u in
        let p = hnf_nodelta env !evdref p in
        let p1 = delayed_force sig_proj1 in
        let evd, p1 = Evarutil.new_global !evdref p1 in
        evdref := evd;
          (Some (fun x ->
                   app_opt env evdref
                     f (mkApp (p1, [| u; p; x |]))),
           ct,
           Coe {head=p1; args=[u;p]; previous=trace})
      | None -> (None, v, IdCoe)
  in aux t

(* Try to coerce to a funclass; raise NoCoercion if not possible *)
let inh_app_fun_core ~program_mode env evd j =
  let t = whd_all env evd j.uj_type in
    match EConstr.kind evd t with
    | Prod _ -> (evd,j,IdCoe)
    | Evar ev ->
        let (evd',t) = Evardefine.define_evar_as_product env evd ev in
          (evd',{ uj_val = j.uj_val; uj_type = t },IdCoe)
    | _ ->
        try let t,p =
          lookup_path_to_fun_from env evd j.uj_type in
            apply_coercion env evd p j t
       with Not_found | NoCoercion ->
         if program_mode then
           try
             let evdref = ref evd in
             let coercef, t, trace = mu env evdref t in
             let res = { uj_val = app_opt env evdref coercef j.uj_val; uj_type = t } in
             (!evdref, res, trace)
           with NoSubtacCoercion | NoCoercion ->
             (evd,j,IdCoe)
         else raise NoCoercion

(* Try to coerce to a funclass; returns [j] if no coercion is applicable *)
let inh_app_fun ~program_mode resolve_tc env evd j =
  try inh_app_fun_core ~program_mode env evd j
  with
  | NoCoercion when not resolve_tc
    || not (get_use_typeclasses_for_conversion ()) -> (evd, j, IdCoe)
  | NoCoercion ->
    try inh_app_fun_core ~program_mode env (saturate_evd env evd) j
    with NoCoercion -> (evd, j, IdCoe)

let type_judgment env sigma j =
  match EConstr.kind sigma (whd_all env sigma j.uj_type) with
    | Sort s -> {utj_val = j.uj_val; utj_type = ESorts.kind sigma s }
    | _ -> error_not_a_type env sigma j

let inh_tosort_force ?loc env evd j =
  try
    let t,p = lookup_path_to_sort_from env evd j.uj_type in
    let evd,j1,_trace = apply_coercion env evd p j t in
    let j2 = Environ.on_judgment_type (whd_evar evd) j1 in
      (evd,type_judgment env evd j2)
  with Not_found | NoCoercion ->
    error_not_a_type ?loc env evd j

let inh_coerce_to_sort ?loc env evd j =
  let typ = whd_all env evd j.uj_type in
    match EConstr.kind evd typ with
    | Sort s -> (evd,{ utj_val = j.uj_val; utj_type = ESorts.kind evd s })
    | Evar ev ->
        let (evd',s) = Evardefine.define_evar_as_sort env evd ev in
          (evd',{ utj_val = j.uj_val; utj_type = s })
    | _ ->
        inh_tosort_force ?loc env evd j

let inh_coerce_to_base ?loc ~program_mode env evd j =
  if program_mode then
    let evdref = ref evd in
    let ct, typ', trace = mu env evdref j.uj_type in
    let res =
      { uj_val = (app_coercion env evdref ct j.uj_val);
        uj_type = typ' }
    in !evdref, res
  else (evd, j)

let inh_coerce_to_prod ?loc ~program_mode env evd t =
  if program_mode then
    let evdref = ref evd in
    let _, typ', _trace = mu env evdref t in
      !evdref, typ'
  else (evd, t)

let inh_coerce_to_fail flags env evd rigidonly v t c1 =
  if rigidonly && not (Heads.is_rigid env (EConstr.Unsafe.to_constr c1) && Heads.is_rigid env (EConstr.Unsafe.to_constr t))
  then
    raise NoCoercion
  else
    let evd, v', t', trace =
      try
        let t2,t1,p = lookup_path_between env evd (t,c1) in
        let evd,j,trace =
          apply_coercion env evd p
            {uj_val = v; uj_type = t} t2
        in
        evd, j.uj_val, j.uj_type, trace
      with Not_found -> raise NoCoercion
    in
    try (unify_leq_delay ~flags env evd t' c1, v', trace)
    with UnableToUnify _ -> raise NoCoercion

let default_flags_of env =
  default_flags_of TransparentState.full

let rec inh_conv_coerce_to_fail ?loc env evd ?(flags=default_flags_of env) rigidonly v t c1 =
  try (unify_leq_delay ~flags env evd t c1, v, IdCoe)
  with UnableToUnify (best_failed_evd,e) ->
    try inh_coerce_to_fail flags env evd rigidonly v t c1
    with NoCoercion ->
      match
      EConstr.kind evd (whd_all env evd t),
      EConstr.kind evd (whd_all env evd c1)
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
          let (evd', v1, trace1) =
            inh_conv_coerce_to_fail ?loc env1 evd rigidonly
              (mkRel 1) (lift 1 u1) (lift 1 t1) in
          let v2 = beta_applist evd' (lift 1 v,[v1]) in
          let t2 = Retyping.get_type_of env1 evd' v2 in
          let (evd'',v2',trace2) = inh_conv_coerce_to_fail ?loc env1 evd' rigidonly v2 t2 u2 in
          let trace = ProdCoe { na=name; ty=u1; dom=trace1; body=trace2 } in
          (evd'', mkLambda (name, u1, v2'), trace)
      | _ -> raise (NoCoercionNoUnifier (best_failed_evd,e))

(* Look for cj' obtained from cj by inserting coercions, s.t. cj'.typ = t *)
let inh_conv_coerce_to_gen ?loc ~program_mode resolve_tc rigidonly flags env evd cj t =
  let (evd', val', otrace) =
    try
      let (evd', val', trace) = inh_conv_coerce_to_fail ?loc env evd ~flags rigidonly cj.uj_val cj.uj_type t in
      (evd', val', Some trace)
    with NoCoercionNoUnifier (best_failed_evd,e) ->
      try
        if program_mode then
          let (evd', val') = coerce_itf ?loc env evd cj.uj_val cj.uj_type t in
          (evd', val', None)
        else raise NoSubtacCoercion
      with
      | NoSubtacCoercion when not resolve_tc || not (get_use_typeclasses_for_conversion ()) ->
          error_actual_type ?loc env best_failed_evd cj t e
      | NoSubtacCoercion ->
        let evd' = saturate_evd env evd in
          try
            if evd' == evd then
              error_actual_type ?loc env best_failed_evd cj t e
            else
              let (evd', val', trace) = inh_conv_coerce_to_fail ?loc env evd' rigidonly cj.uj_val cj.uj_type t in
              (evd', val', Some trace)
          with NoCoercionNoUnifier (_evd,_error) ->
            error_actual_type ?loc env best_failed_evd cj t e
  in
  (evd',{ uj_val = val'; uj_type = t },otrace)

let inh_conv_coerce_to ?loc ~program_mode resolve_tc env evd ?(flags=default_flags_of env) =
  inh_conv_coerce_to_gen ?loc ~program_mode resolve_tc false flags env evd
let inh_conv_coerce_rigid_to ?loc ~program_mode resolve_tc env evd ?(flags=default_flags_of env) =
  inh_conv_coerce_to_gen ?loc ~program_mode resolve_tc true flags env evd
