(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

module RelDecl = Context.Rel.Declaration

(*********************)
(*     Occurring     *)
(*********************)

exception LocalOccur

(* (closedn n M) raises FreeVar if a variable of height greater than n
   occurs in M, returns () otherwise *)

let closedn n c =
  let rec closed_rec n c = match Constr.kind c with
    | Constr.Rel m -> if m>n then raise_notrace LocalOccur
    | _ -> Constr.iter_with_binders succ closed_rec n c
  in
  try closed_rec n c; true with LocalOccur -> false

(* [closed0 M] is true iff [M] is a (de Bruijn) closed term *)

let closed0 c = closedn 0 c

(* (noccurn n M) returns true iff (Rel n) does NOT occur in term M  *)

let noccurn n term =
  let rec occur_rec n c = match Constr.kind c with
    | Constr.Rel m -> if Int.equal m n then raise_notrace LocalOccur
    | _ -> Constr.iter_with_binders succ occur_rec n c
  in
  try occur_rec n term; true with LocalOccur -> false

(* (noccur_between n m M) returns true iff (Rel p) does NOT occur in term M
  for n <= p < n+m *)

let noccur_between n m term =
  let rec occur_rec n c = match Constr.kind c with
    | Constr.Rel p -> if n<=p && p<n+m then raise_notrace LocalOccur
    | _        -> Constr.iter_with_binders succ occur_rec n c
  in
  try occur_rec n term; true with LocalOccur -> false

(* Checking function for terms containing existential variables.
 The function [noccur_with_meta] considers the fact that
 each existential variable (as well as each isevar)
 in the term appears applied to its local context,
 which may contain the CoFix variables. These occurrences of CoFix variables
 are not considered *)

let isMeta c = match Constr.kind c with
| Constr.Meta _ -> true
| _ -> false

let noccur_with_meta n m term =
  let rec occur_rec n c = match Constr.kind c with
    | Constr.Rel p -> if n<=p && p<n+m then raise_notrace LocalOccur
    | Constr.App(f,_cl) ->
        (match Constr.kind f with
           | Constr.Cast (c,_,_) when isMeta c -> ()
           | Constr.Meta _ -> ()
           | _ -> Constr.iter_with_binders succ occur_rec n c)
    | Constr.Evar (_, _) -> ()
    | _ -> Constr.iter_with_binders succ occur_rec n c
  in
  try (occur_rec n term; true) with LocalOccur -> false

(*********************)
(*      Lifting      *)
(*********************)

let exliftn = Constr.exliftn
let liftn = Constr.liftn
let lift = Constr.lift

let liftn_rel_context n k =
  Context.Rel.map_with_binders (fun i -> liftn n (i+k-1))

let lift_rel_context n =
  Context.Rel.map_with_binders (liftn n)

(*********************)
(*   Substituting    *)
(*********************)

(* [lift_with n k c' c] is [liftn n k c]
   assuming [c'] is [liftn n' k c] for some [n' <> 0].
   It relies on [liftn n' k c = c -> closedn k c] which then implies [liftn n k c = c].
   (may be [closedn (k-1) c] if I lost track of which ones are 1-based,
   the correct one is the one that works)
*)
let rec lift_with n k c' c =
  let open Constr in
  if c' == c then c
  else match kind c with
    | Rel i ->
      (* otherwise should have c0 == c *)
      assert (k <= i);
      mkRel (i+n)
    | Meta _ | Var _ | Sort _ | Const _ | Ind _ | Construct _ | Int _ | Float _ | String _ ->
      (* otherwise should have c0 == c *)
      assert false
    | Cast (c1,kk,c2) ->
      let c1', _, c2' = destCast c' in
      let c1 = lift_with n k c1' c1 in
      let c2 = lift_with n k c2' c2 in
      mkCast (c1, kk, c2)
    | Prod (na,c1,c2) ->
      let _, c1', c2' = destProd c' in
      let c1 = lift_with n k c1' c1 in
      let c2 = lift_with n (k+1) c2' c2 in
      mkProd (na,c1,c2)
    | Lambda (na,c1,c2) ->
      let _, c1', c2' = destLambda c' in
      let c1 = lift_with n k c1' c1 in
      let c2 = lift_with n (k+1) c2' c2 in
      mkLambda (na,c1,c2)
    | LetIn (na,c1,c2,c3) ->
      let _, c1', c2', c3' = destLetIn c' in
      let c1 = lift_with n k c1' c1 in
      let c2 = lift_with n k c2' c2 in
      let c3 = lift_with n (k+1) c3' c3 in
      mkLetIn (na,c1,c2,c3)
    | App (h,args) ->
      let h', args' = destApp c' in
      let h = lift_with n k h' h in
      let args = lift_array_with n k args' args in
      mkApp (h,args)
    | Proj (p,r,c) ->
      let _,_,c' = destProj c' in
      let c = lift_with n k c' c in
      mkProj (p,r,c)
    | Evar (e,args) ->
      let _, args' = destEvar c' in
      let args = SList.Skip.map2 (fun arg arg' ->
          lift_with n k arg' arg)
          args
          args'
      in
      mkEvar (e,args)
    | Case (ci,u,pms,(p,r as pr),iv,c,bl) ->
      let _,_,pms',(p',_),iv',c',bl' = destCase c' in
      let pms = lift_array_with n k pms' pms in
      let pr =
        if p' == p then pr
        else
          let p = lift_ctx_with n k p' p in
          p, r
      in
      let iv = if iv' == iv then iv
        else match iv with
          | NoInvert -> assert false
          | CaseInvert {indices=i} ->
            let i' = match iv' with
              | NoInvert -> assert false
              | CaseInvert {indices=i'} -> i'
            in
            let i = lift_array_with n k i' i in
            CaseInvert {indices=i}
      in
      let c = lift_with n k c' c in
      let bl =
        if bl' == bl then bl
        else
          Array.map2 (fun b b' ->
              lift_ctx_with n k b' b)
            bl bl'
      in
      mkCase (ci,u,pms,pr,iv,c,bl)
    | Fix (ln, rdata) ->
      let _, rdata' = destFix c' in
      mkFix (ln, lift_rec_with n k rdata' rdata)
    | CoFix (ln, rdata) ->
      let _, rdata' = destCoFix c' in
      mkCoFix (ln, lift_rec_with n k rdata' rdata)
    | Array (u,elems,def,ty) ->
      let _, elems', def', ty' = destArray c' in
      let elems = lift_array_with n k elems' elems in
      let def = lift_with n k def' def in
      let ty = lift_with n k ty' ty in
      mkArray (u,elems,def,ty)

and lift_ctx_with n k (_,c') (nas,c as orig) =
  if c' == c then orig
  else
    let c = lift_with n (k+Array.length nas) c' c in
    (nas, c)

and lift_array_with n k a' a =
  if a' == a then a
  else
    Array.map2 (fun v v' -> lift_with n k v' v) a a'

and lift_rec_with n k (_,tys',bdys') (nas,tys,bdys) =
  let tys = lift_array_with n k tys' tys in
  let bdys = lift_array_with n (k+Array.length tys) bdys' bdys in
  (nas,tys,bdys)

(* (subst1 M c) substitutes M for Rel(1) in c
   we generalise it to (substl [M1,...,Mn] c) which substitutes in parallel
   M1,...,Mn for respectively Rel(1),...,Rel(n) in c *)

(* 1st : general case *)

module IntTbl = Hashtbl.Make(Int)

type info = Closed | Open of Constr.t IntTbl.t | Unknown
type substituend = { mutable sinfo: info; sit: Constr.t }

let lift_substituend depth s =
  match s.sinfo with
    | Closed -> s.sit
    | Open cache ->
      begin match IntTbl.find_opt cache depth with
      | Some v -> v
      | None ->
        let v' =
          let exception Found of Constr.t in
          try IntTbl.iter (fun _ c -> raise (Found c)) cache; assert false
          with Found c -> c
        in
        let v = lift_with depth 1 v' s.sit in
        let () = IntTbl.add cache depth v in
        v
      end
    | Unknown ->
      let sit = s.sit in
      if closed0 sit then
        let () = s.sinfo <- Closed in
        sit
      else
        let v = lift depth sit in
        let cache = IntTbl.create 13 in
        let () = IntTbl.add cache depth v in
        let () = s.sinfo <- Open cache in
        v

let lift_substituend depth s = if Int.equal depth 0 then s.sit else lift_substituend depth s

let make_substituend c = { sinfo=Unknown; sit=c }

let substn_many lamv n c =
  let lv = Array.length lamv in
  if Int.equal lv 0 then c
  else
    let rec substrec depth c = match Constr.kind c with
      | Constr.Rel k     ->
          if k<=depth then c
          else if k-depth <= lv then lift_substituend depth (Array.unsafe_get lamv (k-depth-1))
          else Constr.mkRel (k-lv)
      | _ -> Constr.map_with_binders succ substrec depth c in
    substrec n c

let make_subst = function
| [] -> [||]
| hd :: tl ->
  let len = List.length tl in
  let subst = Array.make (1 + len) (make_substituend hd) in
  let s = ref tl in
  for i = 1 to len do
    match !s with
    | [] -> assert false
    | x :: tl ->
      Array.unsafe_set subst i (make_substituend x);
      s := tl
  done;
  subst

(* The type of substitutions, with term substituting most recent
    binder at the head *)

type substl = Constr.t list

let substnl laml n c = substn_many (make_subst laml) n c
let substl laml c = substn_many (make_subst laml) 0 c
let subst1 lam c = substn_many [|make_substituend lam|] 0 c

let substnl_decl laml k r = RelDecl.map_constr (fun c -> substnl laml k c) r
let substl_decl laml r = RelDecl.map_constr (fun c -> substnl laml 0 c) r
let subst1_decl lam r = RelDecl.map_constr (fun c -> subst1 lam c) r

let substnl_rel_context laml k r =
  Context.Rel.map_with_binders (fun i -> substnl laml (i+k-1)) r

let substl_rel_context laml r = substnl_rel_context laml 0 r
let subst1_rel_context lam r = substnl_rel_context [lam] 0 r

let esubst mk subst c =
  let rec esubst subst c = match Constr.kind c with
  | Constr.Rel i ->
    let open Esubst in
    begin match expand_rel i subst with
    | Util.Inl (k, v) -> mk k v
    | Util.Inr (m, _) -> Constr.mkRel m
    end
  | _ ->
    Constr.map_with_binders Esubst.subs_lift esubst subst c
  in
  if Esubst.is_subs_id subst then c else esubst subst c

(* Instance of contexts *)

type instance = Constr.t array
type instance_list = Constr.t list

(* Build a substitution from an instance, inserting missing let-ins *)

let subst_of_rel_context_instance_list sign l =
  let rec aux subst sign l =
    let open RelDecl in
    match sign, l with
    | LocalAssum _ :: sign', a::args' -> aux (a::subst) sign' args'
    | LocalDef (_,c,_)::sign', args' ->
        aux (substl subst c :: subst) sign' args'
    | [], [] -> subst
    | _ -> CErrors.anomaly (Pp.str "Instance and signature do not match.")
  in aux [] (List.rev sign) l

let subst_of_rel_context_instance sign v =
  subst_of_rel_context_instance_list sign (Array.to_list v)

let adjust_rel_to_rel_context sign n =
  let rec aux sign =
    let open RelDecl in
    match sign with
    | LocalAssum _ :: sign' -> let (n',p) = aux sign' in (n'+1,p)
    | LocalDef (_,_c,_)::sign' -> let (n',p) = aux sign' in (n'+1,if n'<n then p+1 else p)
    | [] -> (0,n)
  in snd (aux sign)

(* (thin_val sigma) removes identity substitutions from sigma *)

let rec thin_val = function
  | [] -> []
  | (id, c) :: tl ->
    match Constr.kind c with
    | Constr.Var v ->
      if Id.equal id v then thin_val tl
      else (id, make_substituend c) :: (thin_val tl)
    | _ -> (id, make_substituend c) :: (thin_val tl)

let find_var id vars = CList.assoc_f Id.equal id vars

(* (replace_vars sigma M) applies substitution sigma to term M *)
let replace_vars var_alist x =
  let var_alist = thin_val var_alist in
  match var_alist with
  | [] -> x
  | _ ->
    let rec substrec n c = match Constr.kind c with
    | Constr.Var x ->
      begin match find_var x var_alist with
      | var -> lift_substituend n var
      | exception Not_found -> c
      end
    | Constr.Evar _ ->
      CErrors.anomaly (Pp.str "Substituting an evar in the kernel")
    | _ -> Constr.map_with_binders succ substrec n c
    in
    substrec 0 x

(* (subst_var str t) substitute (Var str) by (Rel 1) in t *)
let subst_var str t = replace_vars [(str, Constr.mkRel 1)] t

(* (subst_vars [id1;...;idn] t) substitute (Var idj) by (Rel j) in t *)
let substn_vars p vars c =
  let _,subst =
    List.fold_left (fun (n,l) var -> ((n+1),(var,Constr.mkRel n)::l)) (p,[]) vars
  in replace_vars (List.rev subst) c

let subst_vars subst c = substn_vars 1 subst c

let smash_rel_context sign =
  let open Context.Rel.Declaration in
  let open Esubst in
  snd (List.fold_right
    (fun decl (subst, sign) ->
       match get_value decl with
       | Some b -> (subs_cons (make_substituend (esubst lift_substituend subst b)) subst, sign)
       | None -> (subs_lift subst, map_constr (esubst lift_substituend subst) decl :: sign))
    sign (subs_id 0, []))

(** Universe substitutions *)
open Constr

let map_annot_relevance f na =
  let open Context in
  let r = na.binder_relevance in
  let r' = f r in
  if r' == r then na else { na with binder_relevance = r' }

let map_case_under_context_relevance f (nas,x as v) =
  let nas' = CArray.Smart.map (map_annot_relevance f) nas in
  if nas' == nas then v else (nas',x)

let map_rec_declaration_relevance f (i,(nas,x,y) as v) =
let nas' = CArray.Smart.map (map_annot_relevance f) nas in
  if nas' == nas then v else (i,(nas',x,y))

let map_constr_relevance f c =
  match kind c with
  | Rel _ | Var _ | Meta _ | Evar _
  |  Sort _ | Cast _ | App _
  | Const _ | Ind _ | Construct _
  | Int _ | Float _ | String _ | Array _ -> c

  | Prod (na,x,y) ->
    let na' = map_annot_relevance f na in
    if na' == na then c else mkProd (na',x,y)

  | Lambda (na,x,y) ->
    let na' = map_annot_relevance f na in
    if na' == na then c else mkLambda (na',x,y)

  | LetIn (na,x,y,z) ->
    let na' = map_annot_relevance f na in
    if na' == na then c else mkLetIn (na',x,y,z)

  | Case (ci,u,params,(ret,r),iv,v,brs) ->
    let r' = f r in
    let ret' = map_case_under_context_relevance f ret in
    let brs' = CArray.Smart.map (map_case_under_context_relevance f) brs in
    if r' == r && ret' == ret && brs' == brs then c
    else mkCase (ci,u,params,(ret',r'),iv,v,brs')

  | Fix data ->
    let data' = map_rec_declaration_relevance f data in
    if data' == data then c else mkFix data'

  | CoFix data ->
    let data' = map_rec_declaration_relevance f data in
    if data' == data then c else mkCoFix data'

  | Proj (p, r, v) ->
    let r' = f r in
    if r' == r then c else mkProj (p, r', v)

let fold_annot_relevance f acc na =
  f acc na.Context.binder_relevance

let fold_case_under_context_relevance f acc (nas,_) =
  Array.fold_left (fold_annot_relevance f) acc nas

let fold_rec_declaration_relevance f acc (nas,_,_) =
  Array.fold_left (fold_annot_relevance f) acc nas

let fold_constr_relevance f acc c =
  match kind c with
  | Rel _ | Var _ | Meta _ | Evar _
  |  Sort _ | Cast _ | App _
  | Const _ | Ind _ | Construct _
  | Int _ | Float _ | String _ | Array _ -> acc

  | Prod (na,_,_) | Lambda (na,_,_) | LetIn (na,_,_,_) ->
    fold_annot_relevance f acc na

  | Case (_,_u,_params,(ret,r),_iv,_v,brs) ->
    let acc = f acc r in
    let acc = fold_case_under_context_relevance f acc ret in
    let acc = CArray.fold_left (fold_case_under_context_relevance f) acc brs in
    acc

  | Proj (_, r, _) -> f acc r

  | Fix (_,data)
  | CoFix (_,data) ->
    fold_rec_declaration_relevance f acc data

let subst_univs_level_constr subst c =
  if UVars.is_empty_sort_subst subst then c
  else
    let f = UVars.subst_sort_level_instance subst in
    (* XXX shouldn't Constr.map return the pointer equal term when unchanged instead? *)
    let changed = ref false in
    let rec aux t =
      let t' = map_constr_relevance (UVars.subst_sort_level_relevance subst) t in
      let t = if t' == t then t else (changed := true; t') in
      match kind t with
      | Const (c, u) ->
        if UVars.Instance.is_empty u then t
        else
          let u' = f u in
            if u' == u then t
            else (changed := true; mkConstU (c, u'))
      | Ind (i, u) ->
        if UVars.Instance.is_empty u then t
        else
          let u' = f u in
            if u' == u then t
            else (changed := true; mkIndU (i, u'))
      | Construct (c, u) ->
        if UVars.Instance.is_empty u then t
        else
          let u' = f u in
            if u' == u then t
            else (changed := true; mkConstructU (c, u'))
      | Sort s ->
        let s' = UVars.subst_sort_level_sort subst s in
        if s' == s then t
        else
          (changed := true; mkSort s')

      | Case (ci, u, pms, p, iv, c, br) ->
        if UVars.Instance.is_empty u then Constr.map aux t
        else
          let u' = f u in
          if u' == u then Constr.map aux t
          else (changed:=true; Constr.map aux (mkCase (ci,u',pms,p,iv,c,br)))

      | Array (u,elems,def,ty) ->
        let u' = f u in
        let elems' = CArray.Smart.map aux elems in
        let def' = aux def in
        let ty' = aux ty in
        if u == u' && elems == elems' && def == def' && ty == ty' then t
        else (changed := true; mkArray (u',elems',def',ty'))

      | _ -> Constr.map aux t
    in
    let c' = aux c in
      if !changed then c' else c

let subst_univs_level_context s ctx =
  CList.Smart.map (fun d ->
      let d = RelDecl.map_relevance (UVars.subst_sort_level_relevance s) d in
      RelDecl.map_constr (subst_univs_level_constr s) d)
    ctx

let subst_instance_constr subst c =
  if UVars.Instance.is_empty subst then c
  else
    let f u = UVars.subst_instance_instance subst u in
    let rec aux t =
      let t = if CArray.is_empty (fst (UVars.Instance.to_array subst)) then t
        else map_constr_relevance (UVars.subst_instance_relevance subst) t
      in
      match kind t with
      | Const (c, u) ->
       if UVars.Instance.is_empty u then t
       else
          let u' = f u in
           if u' == u then t
           else (mkConstU (c, u'))
      | Ind (i, u) ->
       if UVars.Instance.is_empty u then t
       else
         let u' = f u in
           if u' == u then t
           else (mkIndU (i, u'))
      | Construct (c, u) ->
       if UVars.Instance.is_empty u then t
       else
          let u' = f u in
           if u' == u then t
           else (mkConstructU (c, u'))
      | Sort s ->
        let s' = UVars.subst_instance_sort subst s in
        if s' == s then t else mkSort s'

      | Case (ci, u, pms, p, iv, c, br) ->
        let u' = f u in
        if u' == u then Constr.map aux t
        else Constr.map aux (mkCase (ci,u',pms,p,iv,c,br))

      | Array (u,elems,def,ty) ->
        let u' = f u in
        let elems' = CArray.Smart.map aux elems in
        let def' = aux def in
        let ty' = aux ty in
        if u == u' && elems == elems' && def == def' && ty == ty' then t
        else mkArray (u',elems',def',ty')

      | _ -> Constr.map aux t
    in
    aux c

let univ_instantiate_constr u c =
  let open UVars in
  assert (UVars.eq_sizes (Instance.length u) (AbstractContext.size c.univ_abstracted_binder));
  subst_instance_constr u c.univ_abstracted_value

let subst_instance_context s ctx =
  if UVars.Instance.is_empty s then ctx
  else
    CList.Smart.map (fun d ->
        let d = RelDecl.map_relevance (UVars.subst_instance_relevance s) d in
        RelDecl.map_constr (subst_instance_constr s) d)
      ctx

let add_qvars_and_univs_of_instance (qs,us) u =
  let qs', us' = UVars.Instance.to_array u in
  let qs = Array.fold_left (fun qs q ->
      let open Sorts.Quality in
      match q with
      | QVar q -> Sorts.QVar.Set.add q qs
      | QConstant _ -> qs)
      qs qs'
  in
  let us = Array.fold_left (fun acc x -> Univ.Level.Set.add x acc) us us' in
  qs, us

let add_relevance (qs,us as v) = let open Sorts in function
  | Irrelevant | Relevant -> v
  | RelevanceVar q -> QVar.Set.add q qs, us

let sort_and_universes_of_constr c =
  let open Univ in
  let rec aux s c =
    let s = fold_constr_relevance add_relevance s c in
    match kind c with
    | Const (_, u) | Ind (_, u) | Construct (_,u) -> add_qvars_and_univs_of_instance s u
    | Sort (Sorts.Type u) ->
      Util.on_snd (Level.Set.union (Universe.levels u)) s
    | Sort (Sorts.QSort (q,u)) ->
      let qs, us = s in
      Sorts.QVar.Set.add q qs, Level.Set.union us (Universe.levels u)
    | Array (u,_,_,_) ->
      let s = add_qvars_and_univs_of_instance s u in
      Constr.fold aux s c
    | Case (_, u, _, _, _,_ ,_) ->
      let s = add_qvars_and_univs_of_instance s u in
      Constr.fold aux s c
    | _ -> Constr.fold aux s c
  in aux (Sorts.QVar.Set.empty,Level.Set.empty) c

let sort_and_universes_of_constr c =
  NewProfile.profile "sort_and_universes_of_constr" (fun () ->
      sort_and_universes_of_constr c)
    ()

let universes_of_constr c = snd (sort_and_universes_of_constr c)
