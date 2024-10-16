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
open Globnames
open Nameops
open Constr
open Context
open Glob_term
open Pp
open Mod_subst
open Pattern
open Environ

let case_info_pattern_eq env i1 i2 =
  i1.cip_style == i2.cip_style &&
  Option.equal (fun i1 i2 -> QInd.equal env i1 i2) i1.cip_ind i2.cip_ind &&
  i1.cip_extensible == i2.cip_extensible

let rec constr_pattern_eq env (p1:constr_pattern) p2 = match p1, p2 with
| PRef r1, PRef r2 -> QGlobRef.equal env r1 r2
| PVar v1, PVar v2 -> Id.equal v1 v2
| PEvar (ev1, ctx1), PEvar (ev2, ctx2) ->
  Evar.equal ev1 ev2 && List.equal (fun c1 c2 -> constr_pattern_eq env c1 c2) ctx1 ctx2
| PRel i1, PRel i2 ->
  Int.equal i1 i2
| PApp (t1, arg1), PApp (t2, arg2) ->
  constr_pattern_eq env t1 t2 && Array.equal (fun c1 c2 -> constr_pattern_eq env c1 c2) arg1 arg2
| PSoApp (id1, arg1), PSoApp (id2, arg2) ->
  Id.equal id1 id2 && List.equal (fun c1 c2 -> constr_pattern_eq env c1 c2) arg1 arg2
| PLambda (v1, t1, b1), PLambda (v2, t2, b2) ->
  Name.equal v1 v2 && constr_pattern_eq env t1 t2 && constr_pattern_eq env b1 b2
| PProd (v1, t1, b1), PProd (v2, t2, b2) ->
  Name.equal v1 v2 && constr_pattern_eq env t1 t2 && constr_pattern_eq env b1 b2
| PLetIn (v1, b1, t1, c1), PLetIn (v2, b2, t2, c2) ->
  Name.equal v1 v2 && constr_pattern_eq env b1 b2 &&
  Option.equal (fun c1 c2 -> constr_pattern_eq env c1 c2) t1 t2 && constr_pattern_eq env c1 c2
| PSort s1, PSort s2 -> Sorts.family_equal s1 s2
| PMeta m1, PMeta m2 -> Option.equal Id.equal m1 m2
| PIf (t1, l1, r1), PIf (t2, l2, r2) ->
  constr_pattern_eq env t1 t2 && constr_pattern_eq env l1 l2 && constr_pattern_eq env r1 r2
| PCase (info1, p1, r1, l1), PCase (info2, p2, r2, l2) ->
  case_info_pattern_eq env info1 info2 &&
  Option.equal (fun (nas1, p1) (nas2, p2) -> Array.equal Name.equal nas1 nas2 && constr_pattern_eq env p1 p2) p1 p2 &&
  constr_pattern_eq env r1 r2 &&
  List.equal (fun p1 p2 -> pattern_eq env p1 p2) l1 l2
| PFix ((ln1,i1),f1), PFix ((ln2,i2),f2) ->
  Array.equal Int.equal ln1 ln2 && Int.equal i1 i2 && rec_declaration_eq env f1 f2
| PCoFix (i1,f1), PCoFix (i2,f2) ->
  Int.equal i1 i2 && rec_declaration_eq env f1 f2
| PProj (p1, t1), PProj (p2, t2) ->
   QProjection.equal env p1 p2 && constr_pattern_eq env t1 t2
| PInt i1, PInt i2 ->
   Uint63.equal i1 i2
| PFloat f1, PFloat f2 ->
   Float64.equal f1 f2
| PString s1, PString s2 ->
   Pstring.equal s1 s2
| PArray (t1, def1, ty1), PArray (t2, def2, ty2) ->
  Array.equal (fun c1 c2 -> constr_pattern_eq env c1 c2) t1 t2 && constr_pattern_eq env def1 def2
  && constr_pattern_eq env ty1 ty2
| PUninstantiated _, _ -> .
| (PRef _ | PVar _ | PEvar _ | PRel _ | PApp _ | PSoApp _
   | PLambda _ | PProd _ | PLetIn _ | PSort _ | PMeta _
   | PIf _ | PCase _ | PFix _ | PCoFix _ | PProj _ | PInt _
   | PFloat _ | PString _ | PArray _), _ -> false
(** FIXME: fixpoint and cofixpoint should be relativized to pattern *)

and pattern_eq env (i1, j1, p1) (i2, j2, p2) =
  Int.equal i1 i2 && Array.equal Name.equal j1 j2 && constr_pattern_eq env p1 p2

and rec_declaration_eq env (n1, c1, r1) (n2, c2, r2) =
  Array.equal Name.equal n1 n2 &&
  Array.equal (fun c1 c2 -> constr_pattern_eq env c1 c2) c1 c2 &&
  Array.equal (fun c1 c2 -> constr_pattern_eq env c1 c2) r1 r2

let rec occurn_pattern : 'a. _ -> 'a constr_pattern_r -> _
  = fun (type a) n (p:a constr_pattern_r) -> match p with
  | PRel p -> Int.equal n p
  | PApp (f,args) ->
      (occurn_pattern n f) || (Array.exists (occurn_pattern n) args)
  | PProj (_,arg) -> occurn_pattern n arg
  | PLambda (na,t,c)  -> (occurn_pattern n t) || (occurn_pattern (n+1) c)
  | PProd (na,t,c)  -> (occurn_pattern n t) || (occurn_pattern (n+1) c)
  | PLetIn (na,b,t,c)  ->
     Option.fold_left (fun b t -> b || occurn_pattern n t) (occurn_pattern n b) t ||
     (occurn_pattern (n+1) c)
  | PIf (c,c1,c2)  ->
      (occurn_pattern n c) ||
      (occurn_pattern n c1) || (occurn_pattern n c2)
  | PCase(_, p, c, br) ->
      Option.cata (fun (nas, p) -> occurn_pattern (Array.length nas + n) p) false p ||
      (occurn_pattern n c) ||
      (List.exists (fun (_, nas, p) -> occurn_pattern (Array.length nas + n) p) br)
  | PMeta _ | PSoApp _ -> true
  | PEvar (_,args) -> List.exists (occurn_pattern n) args
  | PVar _ | PRef _ | PSort _ | PInt _ | PFloat _ | PString _ -> false
  | PFix (_,(_,tl,bl)) ->
     Array.exists (occurn_pattern n) tl || Array.exists (occurn_pattern (n+Array.length tl)) bl
  | PCoFix (_,(_,tl,bl)) ->
     Array.exists (occurn_pattern n) tl || Array.exists (occurn_pattern (n+Array.length tl)) bl
  | PArray (t,def,ty) ->
    Array.exists (occurn_pattern n) t || occurn_pattern n def || occurn_pattern n ty
  | PUninstantiated (PGenarg _) -> false

let noccurn_pattern n c = not (occurn_pattern n c)

exception BoundPattern;;

let rec head_pattern_bound (t:constr_pattern) =
  match t with
    | PProd (_,_,b)  -> head_pattern_bound b
    | PLetIn (_,_,_,b) -> head_pattern_bound b
    | PApp (c,args)  -> head_pattern_bound c
    | PIf (c,_,_)  -> head_pattern_bound c
    | PCase (_,p,c,br) -> head_pattern_bound c
    | PRef r         -> r
    | PVar id        -> GlobRef.VarRef id
    | PEvar _ | PRel _ | PMeta _ | PSoApp _  | PSort _ | PFix _ | PProj _
        -> raise BoundPattern
    (* Perhaps they were arguments, but we don't beta-reduce *)
    | PLambda _ -> raise BoundPattern
    | PCoFix _ | PInt _ | PFloat _ | PString _ | PArray _ ->
      anomaly ~label:"head_pattern_bound" (Pp.str "not a type.")
    | PUninstantiated _ -> .

let head_of_constr_reference sigma c = match EConstr.kind sigma c with
  | Const (sp,_) -> GlobRef.ConstRef sp
  | Construct (sp,_) -> GlobRef.ConstructRef sp
  | Ind (sp,_) -> GlobRef.IndRef sp
  | Var id -> GlobRef.VarRef id
  | _ -> anomaly (Pp.str "Not a rigid reference.")

let mkPRef env gr =
  PRef (Environ.QGlobRef.canonize env gr)

let pattern_of_constr ~broken env sigma t =
  let t = EConstr.Unsafe.to_constr t in
  let kind = if broken then Constr.kind else fun c -> EConstr.kind_upto sigma c in
  let rec pattern_of_constr env t =
  let open Context.Rel.Declaration in
  match kind t with
    | Rel n  -> PRel n
    | Meta n -> PMeta (Some (Id.of_string ("META" ^ string_of_int n)))
    | Var id -> PVar id
    | Sort s -> PSort (EConstr.ESorts.family sigma (EConstr.ESorts.make s))
    | Cast (c,_,_)      -> pattern_of_constr env c
    | LetIn (na,c,t,b) -> PLetIn (na.binder_name,
                                  pattern_of_constr env c,Some (pattern_of_constr env t),
                                  pattern_of_constr (push_rel (LocalDef (na,c,t)) env) b)
    | Prod (na,c,b)   -> PProd (na.binder_name,
                                pattern_of_constr env c,
                                pattern_of_constr (push_rel (LocalAssum (na, c)) env) b)
    | Lambda (na,c,b) -> PLambda (na.binder_name,
                                  pattern_of_constr env c,
                                  pattern_of_constr (push_rel (LocalAssum (na, c)) env) b)
    | App (f,a) ->
        (match
          match kind f with
          | Evar (evk,args) ->
            let EvarInfo evi = Evd.find sigma evk in
            (match snd (Evd.evar_source evi) with
              Evar_kinds.MatchingVar (Evar_kinds.SecondOrderPatVar id) -> Some id
            | _ -> None)
          | _ -> None
         with
         | Some n -> PSoApp (n,Array.to_list (Array.map (pattern_of_constr env) a))
         | None -> PApp (pattern_of_constr env f,Array.map (pattern_of_constr env) a))
    | Const (sp,u)  -> mkPRef env (GlobRef.ConstRef sp)
    | Ind (sp,u)    -> mkPRef env (GlobRef.IndRef sp)
    | Construct (sp,u) -> mkPRef env (GlobRef.ConstructRef sp)
    | Proj (p, _, c) ->
      pattern_of_constr env (EConstr.Unsafe.to_constr (Retyping.expand_projection env sigma p (EConstr.of_constr c) []))
    | Evar (evk,ctxt as ev) ->
      let EvarInfo evi = Evd.find sigma evk in
      (match snd (Evd.evar_source evi) with
      | Evar_kinds.MatchingVar (Evar_kinds.FirstOrderPatVar id) ->
        PMeta (Some id)
      | Evar_kinds.GoalEvar | Evar_kinds.VarInstance _ ->
        (* These are the two evar kinds used for existing goals *)
        (* see Proofview.mark_in_evm *)
        begin match Evd.existential_opt_value0 sigma ev with
        | Some v -> pattern_of_constr env v
        | None ->
          let ctxt = Evd.expand_existential sigma (EConstr.of_existential ev) in
          PEvar (evk,List.map (fun c -> pattern_of_constr env (EConstr.Unsafe.to_constr c)) ctxt)
        end
      | Evar_kinds.MatchingVar (Evar_kinds.SecondOrderPatVar ido) -> assert false
      | _ ->
        PMeta None)
    | Case (ci, u, pms, p0, iv, a, br0) ->
        let (ci, (p,_), iv, a, br) = Inductive.expand_case env (ci, u, pms, p0, iv, a, br0) in
        let pattern_of_ctx c (nas, c0) =
          let ctx, c = Term.decompose_lambda_n_decls (Array.length nas) c in
          let env = push_rel_context ctx env in
          let c = pattern_of_constr env c in
          (Array.map Context.binder_name nas, c)
        in
        let p = pattern_of_ctx p (fst p0) in
        let cip =
          { cip_style = ci.ci_pp_info.style;
            cip_ind = Some ci.ci_ind;
            cip_extensible = false }
        in
        let branch_of_constr i c =
          let nas, c = pattern_of_ctx c br0.(i) in
          (i, nas, c)
        in
        PCase (cip, Some p, pattern_of_constr env a,
                Array.to_list (Array.mapi branch_of_constr br))
    | Fix (lni,(lna,tl,bl)) ->
       let push env na2 c2 = push_rel (LocalAssum (na2,c2)) env in
       let env' = Array.fold_left2 push env lna tl in
       PFix (lni,(Array.map binder_name lna,Array.map (pattern_of_constr env) tl,
                  Array.map (pattern_of_constr env') bl))
    | CoFix (ln,(lna,tl,bl)) ->
       let push env na2 c2 = push_rel (LocalAssum (na2,c2)) env in
       let env' = Array.fold_left2 push env lna tl in
       PCoFix (ln,(Array.map binder_name lna,Array.map (pattern_of_constr env) tl,
                  Array.map (pattern_of_constr env') bl))
    | Int i -> PInt i
    | Float f -> PFloat f
    | String s -> PString s
    | Array (_u, t, def, ty) ->
      PArray (Array.map (pattern_of_constr env) t, pattern_of_constr env def, pattern_of_constr env ty)
    in
  pattern_of_constr env t

let legacy_bad_pattern_of_constr env sigma c : constr_pattern = pattern_of_constr ~broken:true env sigma c
let pattern_of_constr env sigma c = pattern_of_constr ~broken:false env sigma c

(* To process patterns, we need a translation without typing at all. *)

let map_pattern_with_binders_gen (type a b) g f fgen l : a constr_pattern_r -> b constr_pattern_r = function
  | PApp (p,pl) -> PApp (f l p, Array.map (f l) pl)
  | PSoApp (n,pl) -> PSoApp (n, List.map (f l) pl)
  | PLambda (n,a,b) -> PLambda (n,f l a,f (g n l) b)
  | PProd (n,a,b) -> PProd (n,f l a,f (g n l) b)
  | PLetIn (n,a,t,b) -> PLetIn (n,f l a,Option.map (f l) t,f (g n l) b)
  | PIf (c,b1,b2) -> PIf (f l c,f l b1,f l b2)
  | PCase (ci,po,p,pl) ->
    let fold nas l = Array.fold_left (fun l na -> g na l) l nas in
    let map_branch (i, n, c) = (i, n, f (fold n l) c) in
    let po = Option.map (fun (nas, po) -> nas, (f (fold nas l) po)) po in
    PCase (ci,po,f l p, List.map map_branch pl)
  | PProj (p,pc) -> PProj (p, f l pc)
  | PFix (lni,(lna,tl,bl)) ->
     let l' = Array.fold_left (fun l na -> g na l) l lna in
     PFix (lni,(lna,Array.map (f l) tl,Array.map (f l') bl))
  | PCoFix (ln,(lna,tl,bl)) ->
     let l' = Array.fold_left (fun l na -> g na l) l lna in
     PCoFix (ln,(lna,Array.map (f l) tl,Array.map (f l') bl))
  | PArray (t,def,ty) -> PArray (Array.map (f l) t, f l def, f l ty)
  | PEvar (ev,ps) -> PEvar (ev, List.map (f l) ps)
  | PUninstantiated (PGenarg _ as x) -> fgen (x:a uninstantiated_pattern)
  (* Non recursive *)
  | (PVar _ | PRel _ | PRef _  | PSort _  | PMeta _ | PInt _
    | PFloat _ | PString _ as x) -> x

let map_pattern_with_binders (type a) g f l (p:a constr_pattern_r) : a constr_pattern_r =
  let fgen : a uninstantiated_pattern -> a constr_pattern_r = function
    | PGenarg _ as x -> PUninstantiated x
  in
  map_pattern_with_binders_gen g f fgen l p

let rec liftn_pattern k n = function
  | PRel i as x -> if i >= n then PRel (i+k) else x
  | c -> map_pattern_with_binders (fun _ -> succ) (liftn_pattern k) n c

let lift_pattern k = liftn_pattern k 1

let rec subst_pattern
  : 'a. _ -> _ -> _ -> 'a constr_pattern_r -> 'a constr_pattern_r
  = fun (type a) env sigma subst (pat: a constr_pattern_r) ->
  match pat with
  | PRef ref ->
    let ref',t = subst_global subst ref in
    if ref' == ref then pat else (match t with
        | None -> PRef ref'
        | Some t ->
          pattern_of_constr env sigma (EConstr.of_constr t.UVars.univ_abstracted_value))
  | PVar _
  | PEvar _
  | PRel _
  | PInt _
  | PFloat _
  | PString _ -> pat
  | PUninstantiated (PGenarg g) -> PUninstantiated (PGenarg (Gensubst.generic_substitute subst g))
  | PProj (p,c) ->
      let p' = Projection.map (subst_mind subst) p in
      let c' = subst_pattern env sigma subst c in
        if p' == p && c' == c then pat else
          PProj(p',c')
  | PApp (f,args) ->
      let f' = subst_pattern env sigma subst f in
      let args' = Array.Smart.map (subst_pattern env sigma subst) args in
        if f' == f && args' == args then pat else
          PApp (f',args')
  | PSoApp (i,args) ->
      let args' = List.Smart.map (subst_pattern env sigma subst) args in
        if args' == args then pat else
          PSoApp (i,args')
  | PLambda (name,c1,c2) ->
      let c1' = subst_pattern env sigma subst c1 in
      let c2' = subst_pattern env sigma subst c2 in
        if c1' == c1 && c2' == c2 then pat else
          PLambda (name,c1',c2')
  | PProd (name,c1,c2) ->
      let c1' = subst_pattern env sigma subst c1 in
      let c2' = subst_pattern env sigma subst c2 in
        if c1' == c1 && c2' == c2 then pat else
          PProd (name,c1',c2')
  | PLetIn (name,c1,t,c2) ->
      let c1' = subst_pattern env sigma subst c1 in
      let t' = Option.Smart.map (subst_pattern env sigma subst) t in
      let c2' = subst_pattern env sigma subst c2 in
        if c1' == c1 && t' == t && c2' == c2 then pat else
          PLetIn (name,c1',t',c2')
  | PSort _
  | PMeta _ -> pat
  | PIf (c,c1,c2) ->
      let c' = subst_pattern env sigma subst c in
      let c1' = subst_pattern env sigma subst c1 in
      let c2' = subst_pattern env sigma subst c2 in
        if c' == c && c1' == c1 && c2' == c2 then pat else
          PIf (c',c1',c2')
  | PCase (cip,typ,c,branches) ->
      let ind = cip.cip_ind in
      let ind' = Option.Smart.map (subst_ind subst) ind in
      let cip' = if ind' == ind then cip else { cip with cip_ind = ind' } in
      let map ((nas, typ) as t) =
        let typ' = subst_pattern env sigma subst typ in
        if typ' == typ then t else (nas, typ')
      in
      let typ' = Option.Smart.map map typ in
      let c' = subst_pattern env sigma subst c in
      let subst_branch ((i,n,c) as br) =
        let c' = subst_pattern env sigma subst c in
        if c' == c then br else (i,n,c')
      in
      let branches' = List.Smart.map subst_branch branches in
      if cip' == cip && typ' == typ && c' == c && branches' == branches
      then pat
      else PCase(cip', typ', c', branches')
  | PFix (lni,(lna,tl,bl)) ->
      let tl' = Array.Smart.map (subst_pattern env sigma subst) tl in
      let bl' = Array.Smart.map (subst_pattern env sigma subst) bl in
      if bl' == bl && tl' == tl then pat
      else PFix (lni,(lna,tl',bl'))
  | PCoFix (ln,(lna,tl,bl)) ->
      let tl' = Array.Smart.map (subst_pattern env sigma subst) tl in
      let bl' = Array.Smart.map (subst_pattern env sigma subst) bl in
      if bl' == bl && tl' == tl then pat
      else PCoFix (ln,(lna,tl',bl'))
  | PArray (t,def,ty) ->
      let t' = Array.Smart.map (subst_pattern env sigma subst) t in
      let def' = subst_pattern env sigma subst def in
      let ty' = subst_pattern env sigma subst ty in
      if def' == def && t' == t && ty' == ty then pat
      else PArray (t',def',ty')

let mkPLetIn na b t c = PLetIn(na,b,t,c)
let mkPProd na t u = PProd(na,t,u)
let mkPLambda na t b = PLambda(na,t,b)

let mkPProd_or_LetIn (na,_,bo,t) c =
  match bo with
  | None -> mkPProd na t c
  | Some b -> mkPLetIn na b (Some t) c

let mkPLambda_or_LetIn (na,_,bo,t) c =
  match bo with
  | None -> mkPLambda na t c
  | Some b -> mkPLetIn na b (Some t) c

let it_mkPProd_or_LetIn x y = List.fold_left (fun c d -> mkPProd_or_LetIn d c) x y
let it_mkPLambda_or_LetIn x y = List.fold_left (fun c d -> mkPLambda_or_LetIn d c) x y

type 'a pat_interp_fun = Environ.env -> Evd.evar_map -> Ltac_pretype.ltac_var_map
  -> 'a -> Pattern.constr_pattern

module InterpPatObj =
struct
  type (_, 'g, _) obj = 'g pat_interp_fun
  let name = "interp_pat"
  let default _ = None
end

module InterpPat = Genarg.Register(InterpPatObj)

let interp_pat = InterpPat.obj

let register_interp_pat = InterpPat.register0

let interp_pattern env sigma ist p =
  let fgen = function
    | PGenarg (GenArg (Glbwit tag,g)) -> interp_pat tag env sigma ist g
  in
  let rec aux p =
    map_pattern_with_binders_gen (fun _ () -> ()) (fun () p -> aux p) fgen () p
  in
  aux p

let err ?loc pp = user_err ?loc pp

let warn_cast_in_pattern =
  CWarnings.create ~name:"cast-in-pattern" ~category:CWarnings.CoreCategories.automation
    (fun () -> Pp.strbrk "Cast types are ignored in patterns")

type meta_accu =
  | Metas of Id.Set.t ref
  | InCastType of Loc.t option

let push_meta metas n = match metas with
  | Metas metas -> metas := Id.Set.add n !metas
  | InCastType loc ->
    CErrors.user_err ?loc
      Pp.(str "Cannot bind pattern variable in cast type:"
          ++ spc() ++ str "cast types are ignored in patterns.")

let in_cast_type loc = function
  | Metas _ -> InCastType loc
  | InCastType _ as v ->
    (* We report the error with the loc of the outermost cast
       Alternatively we could use the loc of the meta, or the loc of the innermost cast. *)
    v

let pat_of_raw env (type pkind) (kind:pkind pattern_kind) metas vars p =

let rec pat_of_raw metas vars : _ -> pkind constr_pattern_r = DAst.with_loc_val (fun ?loc -> function
  | GVar id ->
      (try PRel (List.index Name.equal (Name id) vars)
       with Not_found -> PVar id)
  | GPatVar (Evar_kinds.FirstOrderPatVar n) ->
      push_meta metas n; PMeta (Some n)
  | GRef (gr,_) ->
      PRef (Environ.QGlobRef.canonize env gr)
  (* Hack to avoid rewriting a complete interpretation of patterns *)
  | GApp (c, cl) ->
    begin match DAst.get c with
    | GPatVar (Evar_kinds.SecondOrderPatVar n) ->
      push_meta metas n; PSoApp (n, List.map (pat_of_raw metas vars) cl)
    | _ ->
      PApp (pat_of_raw metas vars c,
            Array.of_list (List.map (pat_of_raw metas vars) cl))
    end
  | GProj ((p,_), cl, c) ->
    if Structures.PrimitiveProjections.mem p then
      let p = Option.get @@ Structures.PrimitiveProjections.find_opt p in
      let p = Projection.make p false in
      PProj (p, pat_of_raw metas vars c)
    else
      PApp (PRef (GlobRef.ConstRef p), Array.map_of_list (pat_of_raw metas vars) (cl @ [c]))
  | GLambda (na,_,bk,c1,c2) ->
      Name.iter (fun n -> push_meta metas n) na;
      PLambda (na, pat_of_raw metas vars c1,
               pat_of_raw metas (na::vars) c2)
  | GProd (na,_,bk,c1,c2) ->
      Name.iter (fun n -> push_meta metas n) na;
      PProd (na, pat_of_raw metas vars c1,
               pat_of_raw metas (na::vars) c2)
  | GLetIn (na,_,c1,t,c2) ->
      Name.iter (fun n -> push_meta metas n) na;
      PLetIn (na, pat_of_raw metas vars c1,
               Option.map (pat_of_raw metas vars) t,
               pat_of_raw metas (na::vars) c2)
  | GSort gs ->
     (try PSort (Glob_ops.glob_sort_family gs)
      with Glob_ops.ComplexSort -> user_err ?loc (str "Unexpected universe in pattern."))
  | GHole _ -> PMeta None
  | GGenarg (GenArg (Glbwit tag, _) as g) -> begin match kind with
      | Uninstantiated ->
        let () = if not (InterpPat.mem tag) then
            let name = Genarg.(ArgT.repr (get_arg_tag tag)) in
            user_err ?loc (str "This quotation is not supported in patterns (" ++ str name ++ str ").")
        in
        PUninstantiated (PGenarg g)
      | Any -> user_err ?loc (str "Quotations not allowed in this pattern.")
    end
  | GCast (c,_,t) ->
      let () =
        (* Checks that there are no pattern variables in the type *)
        let _ : pkind constr_pattern_r = pat_of_raw (in_cast_type t.loc metas) vars t in
        ()
      in
      warn_cast_in_pattern ?loc ();
      pat_of_raw metas vars c
  | GIf (c,(_,None),b1,b2) ->
      PIf (pat_of_raw metas vars c,
           pat_of_raw metas vars b1,pat_of_raw metas vars b2)
  | GLetTuple (nal,(_,None),b,c) ->
      let cip =
        { cip_style = LetStyle;
          cip_ind = None;
          cip_extensible = false }
      in
      let tags = Array.of_list nal (* Approximation which can be without let-ins... *) in
      PCase (cip, None, pat_of_raw metas vars b,
             [0,tags,pat_of_raw metas (List.rev_append (Array.to_list tags) vars) c])
  | GCases (sty,p,[c,(na,indnames)],brs) ->
      let get_ind p = match DAst.get p with
      | PatCstr((ind,_),_,_) -> Some ind
      | _ -> None
      in
      let get_ind = function
        | {CAst.v=(_,[p],_)}::_ -> get_ind p
        | _ -> None
      in
      let ind_tags,ind = match indnames with
        | Some {CAst.v=(ind,nal)} -> Some (List.length nal), Some ind
        | None -> None, get_ind brs
      in
      let ext,brs = pats_of_glob_branches loc metas vars ind brs
      in
      let pred = match p,indnames with
        | Some p, Some {CAst.v=(_,nal)} ->
          let nvars = na :: List.rev nal @ vars in
          Some (Array.rev_of_list (na :: List.rev nal), pat_of_raw metas nvars p)
        | None, _ -> None
        | Some p, None ->
          match DAst.get p with
          | GHole _ -> None
          | _ ->
            user_err ?loc  (strbrk "Clause \"in\" expected in patterns over \"match\" expressions with an explicit \"return\" clause.")
      in
      let info =
        { cip_style = sty;
          cip_ind = ind;
          cip_extensible = ext }
      in
      (* Nota : when we have a non-trivial predicate,
         the inductive type is known. Same when we have at least
         one non-trivial branch. These facts are used in [Constrextern]. *)
      PCase (info, pred, pat_of_raw metas vars c, brs)

  | GRec (GFix (ln,n), ids, decls, tl, cl) ->
    let get_struct_arg = function
      | Some n -> n
      | None -> err ?loc (Pp.str "\"struct\" annotation is expected.")
        (* TODO why can't the annotation be omitted? *)
    in
    let ln = Array.map get_struct_arg ln in
    let ctxtl = Array.map2 (pat_of_glob_in_context metas vars) decls tl in
    let tl = Array.map (fun (ctx,tl) -> it_mkPProd_or_LetIn tl ctx) ctxtl in
    let vars = Array.fold_left (fun vars na -> Name na::vars) vars ids in
    let ctxtl = Array.map2 (pat_of_glob_in_context metas vars) decls cl in
    let cl = Array.map (fun (ctx,cl) -> it_mkPLambda_or_LetIn cl ctx) ctxtl in
    let names = Array.map (fun id -> Name id) ids in
    PFix ((ln,n), (names, tl, cl))

  | GRec (GCoFix n, ids, decls, tl, cl) ->
      let ctxtl = Array.map2 (pat_of_glob_in_context metas vars) decls tl in
      let tl = Array.map (fun (ctx,tl) -> it_mkPProd_or_LetIn tl ctx) ctxtl in
      let vars = Array.fold_left (fun vars na -> Name na::vars) vars ids in
      let ctxtl = Array.map2 (pat_of_glob_in_context metas vars) decls cl in
      let cl = Array.map (fun (ctx,cl) -> it_mkPLambda_or_LetIn cl ctx) ctxtl in
      let names = Array.map (fun id -> Name id) ids in
      PCoFix (n, (names, tl, cl))

  | GInt i -> PInt i
  | GFloat f -> PFloat f
  | GString s -> PString s
  | GPatVar _ | GIf _ | GLetTuple _ | GCases _ | GEvar _ | GArray _ ->
      err ?loc (Pp.str "Non supported pattern."))

and pat_of_glob_in_context metas vars decls c =
  let rec aux acc vars = function
    | (na,_,bk,b,t) :: decls ->
       let decl = (na,bk,Option.map (pat_of_raw metas vars) b,pat_of_raw metas vars t) in
       aux (decl::acc) (na::vars) decls
    | [] ->
       acc, pat_of_raw metas vars c
  in aux [] vars decls

and pats_of_glob_branches loc metas vars ind brs =
  let get_arg p = match DAst.get p with
    | PatVar na ->
      Name.iter (fun n -> push_meta metas n) na;
      na
    | PatCstr(_,_,_) -> err ?loc:p.CAst.loc (Pp.str "Non supported pattern.")
  in
  let rec get_pat indexes = function
    | [] -> false, []
    | {CAst.loc=loc';v=(_,[p], br)} :: brs ->
      begin match DAst.get p, DAst.get br, brs with
      | PatVar Anonymous, GHole _, [] ->
        true, [] (* ends with _ => _ *)
      | PatCstr((indsp,j),lv,_), _, _ ->
        let () = match ind with
        | Some sp when Ind.UserOrd.equal sp indsp -> ()
        | _ ->
          err ?loc (Pp.str "All constructors must be in the same inductive type.")
        in
        if Int.Set.mem (j-1) indexes then
          err ?loc
            (str "No unique branch for " ++ int j ++ str"-th constructor.");
        let lna = List.map get_arg lv in
        let vars' = List.rev_append lna vars in
        let tags = Array.of_list lna in
        let pat = pat_of_raw metas vars' br in
        let ext,pats = get_pat (Int.Set.add (j-1) indexes) brs in
        ext, ((j-1, tags, pat) :: pats)
      | _ ->
        err ?loc:loc' (Pp.str "Non supported pattern.")
      end
    | {CAst.loc;v=(_,_,_)} :: _ -> err ?loc (Pp.str "Non supported pattern.")
  in
  get_pat Int.Set.empty brs

in pat_of_raw metas vars p

let pattern_of_glob_constr env c =
  let metas = ref Id.Set.empty in
  let p = pat_of_raw env Any (Metas metas) [] c in
  (!metas, p)

let uninstantiated_pattern_of_glob_constr env c =
  let metas = ref Id.Set.empty in
  let p = pat_of_raw env Uninstantiated (Metas metas) [] c in
  (!metas, p)
