(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
open Term
open Constr
open Glob_term
open Pp
open Mod_subst
open Decl_kinds
open Pattern
open Environ

let case_info_pattern_eq i1 i2 =
  i1.cip_style == i2.cip_style &&
  Option.equal eq_ind i1.cip_ind i2.cip_ind &&
  Option.equal (List.equal (==)) i1.cip_ind_tags i2.cip_ind_tags &&
  i1.cip_extensible == i2.cip_extensible

let rec constr_pattern_eq p1 p2 = match p1, p2 with
| PRef r1, PRef r2 -> GlobRef.equal r1 r2
| PVar v1, PVar v2 -> Id.equal v1 v2
| PEvar (ev1, ctx1), PEvar (ev2, ctx2) ->
  Evar.equal ev1 ev2 && Array.equal constr_pattern_eq ctx1 ctx2
| PRel i1, PRel i2 ->
  Int.equal i1 i2
| PApp (t1, arg1), PApp (t2, arg2) ->
  constr_pattern_eq t1 t2 && Array.equal constr_pattern_eq arg1 arg2
| PSoApp (id1, arg1), PSoApp (id2, arg2) ->
  Id.equal id1 id2 && List.equal constr_pattern_eq arg1 arg2
| PLambda (v1, t1, b1), PLambda (v2, t2, b2) ->
  Name.equal v1 v2 && constr_pattern_eq t1 t2 && constr_pattern_eq b1 b2
| PProd (v1, t1, b1), PProd (v2, t2, b2) ->
  Name.equal v1 v2 && constr_pattern_eq t1 t2 && constr_pattern_eq b1 b2
| PLetIn (v1, b1, t1, c1), PLetIn (v2, b2, t2, c2) ->
  Name.equal v1 v2 && constr_pattern_eq b1 b2 &&
  Option.equal constr_pattern_eq t1 t2 && constr_pattern_eq c1 c2
| PSort s1, PSort s2 -> Glob_ops.glob_sort_eq s1 s2
| PMeta m1, PMeta m2 -> Option.equal Id.equal m1 m2
| PIf (t1, l1, r1), PIf (t2, l2, r2) ->
  constr_pattern_eq t1 t2 && constr_pattern_eq l1 l2 && constr_pattern_eq r1 r2
| PCase (info1, p1, r1, l1), PCase (info2, p2, r2, l2) ->
  case_info_pattern_eq info1 info2 &&
  constr_pattern_eq p1 p2 &&
  constr_pattern_eq r1 r2 &&
  List.equal pattern_eq l1 l2
| PFix ((ln1,i1),f1), PFix ((ln2,i2),f2) ->
  Array.equal Int.equal ln1 ln2 && Int.equal i1 i2 && rec_declaration_eq f1 f2
| PCoFix (i1,f1), PCoFix (i2,f2) ->
  Int.equal i1 i2 && rec_declaration_eq f1 f2
| PProj (p1, t1), PProj (p2, t2) ->
   Projection.equal p1 p2 && constr_pattern_eq t1 t2
| PInt i1, PInt i2 ->
   Uint63.equal i1 i2
| (PRef _ | PVar _ | PEvar _ | PRel _ | PApp _ | PSoApp _
   | PLambda _ | PProd _ | PLetIn _ | PSort _ | PMeta _
   | PIf _ | PCase _ | PFix _ | PCoFix _ | PProj _ | PInt _), _ -> false
(** FIXME: fixpoint and cofixpoint should be relativized to pattern *)

and pattern_eq (i1, j1, p1) (i2, j2, p2) =
  Int.equal i1 i2 && List.equal (==) j1 j2 && constr_pattern_eq p1 p2

and rec_declaration_eq (n1, c1, r1) (n2, c2, r2) =
  Array.equal Name.equal n1 n2 &&
  Array.equal constr_pattern_eq c1 c2 &&
  Array.equal constr_pattern_eq r1 r2

let rec occur_meta_pattern = function
  | PApp (f,args) ->
      (occur_meta_pattern f) || (Array.exists occur_meta_pattern args)
  | PProj (_,arg) -> occur_meta_pattern arg
  | PLambda (na,t,c)  -> (occur_meta_pattern t) || (occur_meta_pattern c)
  | PProd (na,t,c)  -> (occur_meta_pattern t) || (occur_meta_pattern c)
  | PLetIn (na,b,t,c)  ->
     Option.fold_left (fun b t -> b || occur_meta_pattern t) (occur_meta_pattern b) t || (occur_meta_pattern c)
  | PIf (c,c1,c2)  ->
      (occur_meta_pattern c) ||
      (occur_meta_pattern c1) || (occur_meta_pattern c2)
  | PCase(_,p,c,br) ->
      (occur_meta_pattern p) ||
      (occur_meta_pattern c) ||
      (List.exists (fun (_,_,p) -> occur_meta_pattern p) br)
  | PMeta _ | PSoApp _ -> true
  | PEvar _ | PVar _ | PRef _ | PRel _ | PSort _ | PFix _ | PCoFix _
    | PInt _ -> false

let rec occurn_pattern n = function
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
  | PCase(_,p,c,br) ->
      (occurn_pattern n p) ||
      (occurn_pattern n c) ||
      (List.exists (fun (_,_,p) -> occurn_pattern n p) br)
  | PMeta _ | PSoApp _ -> true
  | PEvar (_,args) -> Array.exists (occurn_pattern n) args
  | PVar _ | PRef _ | PSort _ | PInt _ -> false
  | PFix (_,(_,tl,bl)) ->
     Array.exists (occurn_pattern n) tl || Array.exists (occurn_pattern (n+Array.length tl)) bl
  | PCoFix (_,(_,tl,bl)) ->
     Array.exists (occurn_pattern n) tl || Array.exists (occurn_pattern (n+Array.length tl)) bl

let noccurn_pattern n c = not (occurn_pattern n c)

exception BoundPattern;;

let rec head_pattern_bound t =
  match t with
    | PProd (_,_,b)  -> head_pattern_bound b
    | PLetIn (_,_,_,b) -> head_pattern_bound b
    | PApp (c,args)  -> head_pattern_bound c
    | PIf (c,_,_)  -> head_pattern_bound c
    | PCase (_,p,c,br) -> head_pattern_bound c
    | PRef r         -> r
    | PVar id        -> VarRef id
    | PEvar _ | PRel _ | PMeta _ | PSoApp _  | PSort _ | PFix _ | PProj _
	-> raise BoundPattern
    (* Perhaps they were arguments, but we don't beta-reduce *)
    | PLambda _ -> raise BoundPattern
    | PCoFix _ | PInt _ -> anomaly ~label:"head_pattern_bound" (Pp.str "not a type.")

let head_of_constr_reference sigma c = match EConstr.kind sigma c with
  | Const (sp,_) -> ConstRef sp
  | Construct (sp,_) -> ConstructRef sp
  | Ind (sp,_) -> IndRef sp
  | Var id -> VarRef id
  | _ -> anomaly (Pp.str "Not a rigid reference.")

let pattern_of_constr env sigma t =
  let rec pattern_of_constr env t =
  let open Context.Rel.Declaration in
  match kind t with
    | Rel n  -> PRel n
    | Meta n -> PMeta (Some (Id.of_string ("META" ^ string_of_int n)))
    | Var id -> PVar id
    | Sort Prop -> PSort GProp
    | Sort Set -> PSort GSet
    | Sort (Type _) -> PSort (GType [])
    | Cast (c,_,_)      -> pattern_of_constr env c
    | LetIn (na,c,t,b) -> PLetIn (na,pattern_of_constr env c,Some (pattern_of_constr env t),
				  pattern_of_constr (push_rel (LocalDef (na,c,t)) env) b)
    | Prod (na,c,b)   -> PProd (na,pattern_of_constr env c,
				pattern_of_constr (push_rel (LocalAssum (na, c)) env) b)
    | Lambda (na,c,b) -> PLambda (na,pattern_of_constr env c,
				  pattern_of_constr (push_rel (LocalAssum (na, c)) env) b)
    | App (f,a) ->
        (match
          match kind f with
          | Evar (evk,args) ->
            (match snd (Evd.evar_source evk sigma) with
              Evar_kinds.MatchingVar (Evar_kinds.SecondOrderPatVar id) -> Some id
            | _ -> None)
          | _ -> None
         with
         | Some n -> PSoApp (n,Array.to_list (Array.map (pattern_of_constr env) a))
         | None -> PApp (pattern_of_constr env f,Array.map (pattern_of_constr env) a))
    | Const (sp,u)  -> PRef (ConstRef (Constant.make1 (Constant.canonical sp)))
    | Ind (sp,u)    -> PRef (canonical_gr (IndRef sp))
    | Construct (sp,u) -> PRef (canonical_gr (ConstructRef sp))
    | Proj (p, c) -> 
      pattern_of_constr env (EConstr.Unsafe.to_constr (Retyping.expand_projection env sigma p (EConstr.of_constr c) []))
    | Evar (evk,ctxt as ev) ->
      (match snd (Evd.evar_source evk sigma) with
      | Evar_kinds.MatchingVar (Evar_kinds.FirstOrderPatVar id) ->
        PMeta (Some id)
      | Evar_kinds.GoalEvar | Evar_kinds.VarInstance _ ->
        (* These are the two evar kinds used for existing goals *)
        (* see Proofview.mark_in_evm *)
         if Evd.is_defined sigma evk then pattern_of_constr env (Evd.existential_value0 sigma ev)
         else PEvar (evk,Array.map (pattern_of_constr env) ctxt)
      | Evar_kinds.MatchingVar (Evar_kinds.SecondOrderPatVar ido) -> assert false
      | _ -> 
	 PMeta None)
    | Case (ci,p,a,br) ->
        let cip =
	  { cip_style = ci.ci_pp_info.style;
	    cip_ind = Some ci.ci_ind;
	    cip_ind_tags = Some ci.ci_pp_info.ind_tags;
	    cip_extensible = false }
	in
	let branch_of_constr i c =
	  (i, ci.ci_pp_info.cstr_tags.(i), pattern_of_constr env c)
	in
	PCase (cip, pattern_of_constr env p, pattern_of_constr env a,
	       Array.to_list (Array.mapi branch_of_constr br))
    | Fix (lni,(lna,tl,bl)) ->
       let push env na2 c2 = push_rel (LocalAssum (na2,c2)) env in
       let env' = Array.fold_left2 push env lna tl in
       PFix (lni,(lna,Array.map (pattern_of_constr env) tl,
                  Array.map (pattern_of_constr env') bl))
    | CoFix (ln,(lna,tl,bl)) ->
       let push env na2 c2 = push_rel (LocalAssum (na2,c2)) env in
       let env' = Array.fold_left2 push env lna tl in
       PCoFix (ln,(lna,Array.map (pattern_of_constr env) tl,
                  Array.map (pattern_of_constr env') bl))
    | Int i -> PInt i in
  pattern_of_constr env t

(* To process patterns, we need a translation without typing at all. *)

let map_pattern_with_binders g f l = function
  | PApp (p,pl) -> PApp (f l p, Array.map (f l) pl)
  | PSoApp (n,pl) -> PSoApp (n, List.map (f l) pl)
  | PLambda (n,a,b) -> PLambda (n,f l a,f (g n l) b)
  | PProd (n,a,b) -> PProd (n,f l a,f (g n l) b)
  | PLetIn (n,a,t,b) -> PLetIn (n,f l a,Option.map (f l) t,f (g n l) b)
  | PIf (c,b1,b2) -> PIf (f l c,f l b1,f l b2)
  | PCase (ci,po,p,pl) ->
    PCase (ci,f l po,f l p, List.map (fun (i,n,c) -> (i,n,f l c)) pl)
  | PProj (p,pc) -> PProj (p, f l pc)
  | PFix (lni,(lna,tl,bl)) ->
     let l' = Array.fold_left (fun l na -> g na l) l lna in
     PFix (lni,(lna,Array.map (f l) tl,Array.map (f l') bl))
  | PCoFix (ln,(lna,tl,bl)) ->
     let l' = Array.fold_left (fun l na -> g na l) l lna in
     PCoFix (ln,(lna,Array.map (f l) tl,Array.map (f l') bl))
  (* Non recursive *)
  | (PVar _ | PEvar _ | PRel _ | PRef _  | PSort _  | PMeta _ | PInt _ as x) -> x

let error_instantiate_pattern id l =
  let is = match l with
  | [_] -> "is" 
  | _ -> "are"
  in
  user_err  (str "Cannot substitute the term bound to " ++ Id.print id
    ++ strbrk " in pattern because the term refers to " ++ pr_enum Id.print l
    ++ strbrk " which " ++ str is ++ strbrk " not bound in the pattern.")

let instantiate_pattern env sigma lvar c =
  let open EConstr in
  let open Vars in
  let rec aux vars = function
  | PVar id as x ->
      (try
	let ctx,c = Id.Map.find id lvar in
	try
	  let inst =
	    List.map
              (fun id -> mkRel (List.index Name.equal (Name id) vars))
              ctx
          in
	  let c = substl inst c in
          (* FIXME: Stupid workaround to pattern_of_constr being evar sensitive *)
	  let c = Evarutil.nf_evar sigma c in
	  pattern_of_constr env sigma (EConstr.Unsafe.to_constr c)
	with Not_found (* List.index failed *) ->
	  let vars =
	    List.map_filter (function Name id -> Some id | _ -> None) vars in
	  error_instantiate_pattern id (List.subtract Id.equal ctx vars)
       with Not_found (* Map.find failed *) ->
	 x)
  | c ->
      map_pattern_with_binders (fun id vars -> id::vars) aux vars c in
  aux [] c

let rec liftn_pattern k n = function
  | PRel i as x -> if i >= n then PRel (i+k) else x
  | c -> map_pattern_with_binders (fun _ -> succ) (liftn_pattern k) n c

let lift_pattern k = liftn_pattern k 1

let rec subst_pattern subst pat =
  match pat with
  | PRef ref ->
    let ref',t = subst_global subst ref in
    if ref' == ref then pat else (match t with
        | None -> PRef ref'
        | Some t ->
          let env = Global.env () in
          let evd = Evd.from_env env in
          pattern_of_constr env evd t.Univ.univ_abstracted_value)
  | PVar _
  | PEvar _
  | PRel _
  | PInt _ -> pat
  | PProj (p,c) -> 
      let p' = Projection.map (subst_mind subst) p in
      let c' = subst_pattern subst c in
	if p' == p && c' == c then pat else
	  PProj(p',c')
  | PApp (f,args) ->
      let f' = subst_pattern subst f in
      let args' = Array.Smart.map (subst_pattern subst) args in
	if f' == f && args' == args then pat else
	  PApp (f',args')
  | PSoApp (i,args) ->
      let args' = List.Smart.map (subst_pattern subst) args in
	if args' == args then pat else
	  PSoApp (i,args')
  | PLambda (name,c1,c2) ->
      let c1' = subst_pattern subst c1 in
      let c2' = subst_pattern subst c2 in
	if c1' == c1 && c2' == c2 then pat else
	  PLambda (name,c1',c2')
  | PProd (name,c1,c2) ->
      let c1' = subst_pattern subst c1 in
      let c2' = subst_pattern subst c2 in
	if c1' == c1 && c2' == c2 then pat else
	  PProd (name,c1',c2')
  | PLetIn (name,c1,t,c2) ->
      let c1' = subst_pattern subst c1 in
      let t' = Option.Smart.map (subst_pattern subst) t in
      let c2' = subst_pattern subst c2 in
	if c1' == c1 && t' == t && c2' == c2 then pat else
	  PLetIn (name,c1',t',c2')
  | PSort _
  | PMeta _ -> pat
  | PIf (c,c1,c2) ->
      let c' = subst_pattern subst c in
      let c1' = subst_pattern subst c1 in
      let c2' = subst_pattern subst c2 in
	if c' == c && c1' == c1 && c2' == c2 then pat else
	  PIf (c',c1',c2')
  | PCase (cip,typ,c,branches) ->
      let ind = cip.cip_ind in
      let ind' = Option.Smart.map (subst_ind subst) ind in
      let cip' = if ind' == ind then cip else { cip with cip_ind = ind' } in
      let typ' = subst_pattern subst typ in
      let c' = subst_pattern subst c in
      let subst_branch ((i,n,c) as br) =
	let c' = subst_pattern subst c in
	if c' == c then br else (i,n,c')
      in
      let branches' = List.Smart.map subst_branch branches in
      if cip' == cip && typ' == typ && c' == c && branches' == branches
      then pat
      else PCase(cip', typ', c', branches')
  | PFix (lni,(lna,tl,bl)) ->
      let tl' = Array.Smart.map (subst_pattern subst) tl in
      let bl' = Array.Smart.map (subst_pattern subst) bl in
      if bl' == bl && tl' == tl then pat
      else PFix (lni,(lna,tl',bl'))
  | PCoFix (ln,(lna,tl,bl)) ->
      let tl' = Array.Smart.map (subst_pattern subst) tl in
      let bl' = Array.Smart.map (subst_pattern subst) bl in
      if bl' == bl && tl' == tl then pat
      else PCoFix (ln,(lna,tl',bl'))

let mkPLetIn na b t c = PLetIn(na,b,t,c)
let mkPProd na t u = PProd(na,t,u)
let mkPLambda na t b = PLambda(na,t,b)
let mkPLambdaUntyped na b = PLambda(na,PMeta None,b)
let rev_it_mkPLambdaUntyped = List.fold_right mkPLambdaUntyped

let mkPProd_or_LetIn (na,_,bo,t) c =
  match bo with
  | None -> mkPProd na t c
  | Some b -> mkPLetIn na b (Some t) c

let mkPLambda_or_LetIn (na,_,bo,t) c =
  match bo with
  | None -> mkPLambda na t c
  | Some b -> mkPLetIn na b (Some t) c

let it_mkPProd_or_LetIn = List.fold_left (fun c d -> mkPProd_or_LetIn d c)
let it_mkPLambda_or_LetIn = List.fold_left (fun c d -> mkPLambda_or_LetIn d c)

let err ?loc pp = user_err ?loc ~hdr:"pattern_of_glob_constr" pp

let warn_cast_in_pattern =
  CWarnings.create ~name:"cast-in-pattern" ~category:"automation"
    (fun () -> Pp.strbrk "Casts are ignored in patterns")

let rec pat_of_raw metas vars = DAst.with_loc_val (fun ?loc -> function
  | GVar id ->
      (try PRel (List.index Name.equal (Name id) vars)
       with Not_found -> PVar id)
  | GPatVar (Evar_kinds.FirstOrderPatVar n) ->
      metas := n::!metas; PMeta (Some n)
  | GRef (gr,_) ->
      PRef (canonical_gr gr)
  (* Hack to avoid rewriting a complete interpretation of patterns *)
  | GApp (c, cl) ->
    begin match DAst.get c with
    | GPatVar (Evar_kinds.SecondOrderPatVar n) ->
      metas := n::!metas; PSoApp (n, List.map (pat_of_raw metas vars) cl)
    | _ ->
      PApp (pat_of_raw metas vars c,
	    Array.of_list (List.map (pat_of_raw metas vars) cl))
    end
  | GLambda (na,bk,c1,c2) ->
      Name.iter (fun n -> metas := n::!metas) na;
      PLambda (na, pat_of_raw metas vars c1,
	       pat_of_raw metas (na::vars) c2)
  | GProd (na,bk,c1,c2) ->
      Name.iter (fun n -> metas := n::!metas) na;
      PProd (na, pat_of_raw metas vars c1,
	       pat_of_raw metas (na::vars) c2)
  | GLetIn (na,c1,t,c2) ->
      Name.iter (fun n -> metas := n::!metas) na;
      PLetIn (na, pat_of_raw metas vars c1,
               Option.map (pat_of_raw metas vars) t,
	       pat_of_raw metas (na::vars) c2)
  | GSort s ->
      PSort s
  | GHole _ ->
      PMeta None
  | GCast (c,_) ->
      warn_cast_in_pattern ();
      pat_of_raw metas vars c
  | GIf (c,(_,None),b1,b2) ->
      PIf (pat_of_raw metas vars c,
           pat_of_raw metas vars b1,pat_of_raw metas vars b2)
  | GLetTuple (nal,(_,None),b,c) ->
      let mkGLambda na c = DAst.make ?loc @@
        GLambda (na,Explicit, DAst.make @@ GHole (Evar_kinds.InternalHole, Namegen.IntroAnonymous, None),c) in
      let c = List.fold_right mkGLambda nal c in
      let cip =
	{ cip_style = LetStyle;
	  cip_ind = None;
	  cip_ind_tags = None;
	  cip_extensible = false }
      in
      let tags = List.map (fun _ -> false) nal (* Approximation which can be without let-ins... *) in
      PCase (cip, PMeta None, pat_of_raw metas vars b,
             [0,tags,pat_of_raw metas vars c])
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
          rev_it_mkPLambdaUntyped nal (mkPLambdaUntyped na (pat_of_raw metas nvars p))
        | None, _ -> PMeta None
	| Some p, None ->
          match DAst.get p with
          | GHole _ -> PMeta None
          | _ ->
            user_err ?loc  (strbrk "Clause \"in\" expected in patterns over \"match\" expressions with an explicit \"return\" clause.")
      in
      let info =
	{ cip_style = sty;
	  cip_ind = ind;
	  cip_ind_tags = None;
	  cip_extensible = ext }
      in
      (* Nota : when we have a non-trivial predicate,
	 the inductive type is known. Same when we have at least
	 one non-trivial branch. These facts are used in [Constrextern]. *)
      PCase (info, pred, pat_of_raw metas vars c, brs)

  | GRec (GFix (ln,n), ids, decls, tl, cl) ->
    if Array.exists (function (Some n, GStructRec) -> false | _ -> true) ln then
      err ?loc (Pp.str "\"struct\" annotation is expected.")
    else
      let ln = Array.map (fst %> Option.get) ln in
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
  | GPatVar _ | GIf _ | GLetTuple _ | GCases _ | GEvar _ ->
      err ?loc (Pp.str "Non supported pattern."))

and pat_of_glob_in_context metas vars decls c =
  let rec aux acc vars = function
    | (na,bk,b,t) :: decls ->
       let decl = (na,bk,Option.map (pat_of_raw metas vars) b,pat_of_raw metas vars t) in
       aux (decl::acc) (na::vars) decls
    | [] ->
       acc, pat_of_raw metas vars c
  in aux [] vars decls

and pats_of_glob_branches loc metas vars ind brs =
  let get_arg p = match DAst.get p with
    | PatVar na ->
      Name.iter (fun n -> metas := n::!metas) na;
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
        | Some sp when eq_ind sp indsp -> ()
        | _ ->
          err ?loc (Pp.str "All constructors must be in the same inductive type.")
        in
        if Int.Set.mem (j-1) indexes then
          err ?loc
            (str "No unique branch for " ++ int j ++ str"-th constructor.");
        let lna = List.map get_arg lv in
        let vars' = List.rev lna @ vars in
        let pat = rev_it_mkPLambdaUntyped lna (pat_of_raw metas vars' br) in
        let ext,pats = get_pat (Int.Set.add (j-1) indexes) brs in
        let tags = List.map (fun _ -> false) lv (* approximation, w/o let-in *) in
        ext, ((j-1, tags, pat) :: pats)
      | _ ->
        err ?loc:loc' (Pp.str "Non supported pattern.")
      end
    | {CAst.loc;v=(_,_,_)} :: _ -> err ?loc (Pp.str "Non supported pattern.")
  in
  get_pat Int.Set.empty brs

let pattern_of_glob_constr c =
  let metas = ref [] in
  let p = pat_of_raw metas [] c in
  (!metas,p)
