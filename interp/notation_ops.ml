(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Nameops
open Globnames
open Misctypes
open Glob_term
open Glob_ops
open Mod_subst
open Notation_term
open Decl_kinds

(**********************************************************************)
(* Re-interpret a notation as a glob_constr, taking care of binders     *)

let name_to_ident = function
  | Anonymous -> Errors.error "This expression should be a simple identifier."
  | Name id -> id

let to_id g e id = let e,na = g e (Name id) in e,name_to_ident na

let rec cases_pattern_fold_map loc g e = function
  | PatVar (_,na) ->
      let e',na' = g e na in e', PatVar (loc,na')
  | PatCstr (_,cstr,patl,na) ->
      let e',na' = g e na in
      let e',patl' = List.fold_map (cases_pattern_fold_map loc g) e patl in
      e', PatCstr (loc,cstr,patl',na')

let rec subst_glob_vars l = function
  | GVar (_,id) as r -> (try Id.List.assoc id l with Not_found -> r)
  | GProd (loc,Name id,bk,t,c) ->
      let id =
	try match Id.List.assoc id l with GVar(_,id') -> id' | _ -> id
	with Not_found -> id in
      GProd (loc,Name id,bk,subst_glob_vars l t,subst_glob_vars l c)
  | GLambda (loc,Name id,bk,t,c) ->
      let id =
	try match Id.List.assoc id l with GVar(_,id') -> id' | _ -> id
	with Not_found -> id in
      GLambda (loc,Name id,bk,subst_glob_vars l t,subst_glob_vars l c)
  | r -> map_glob_constr (subst_glob_vars l) r (* assume: id is not binding *)

let ldots_var = Id.of_string ".."

let glob_constr_of_notation_constr_with_binders loc g f e = function
  | NVar id -> GVar (loc,id)
  | NApp (a,args) -> GApp (loc,f e a, List.map (f e) args)
  | NList (x,y,iter,tail,swap) ->
      let t = f e tail in let it = f e iter in
      let innerl = (ldots_var,t)::(if swap then [] else [x,GVar(loc,y)]) in
      let inner = GApp (loc,GVar (loc,ldots_var),[subst_glob_vars innerl it]) in
      let outerl = (ldots_var,inner)::(if swap then [x,GVar(loc,y)] else []) in
      subst_glob_vars outerl it
  | NBinderList (x,y,iter,tail) ->
      let t = f e tail in let it = f e iter in
      let innerl = [(ldots_var,t);(x,GVar(loc,y))] in
      let inner = GApp (loc,GVar (loc,ldots_var),[subst_glob_vars innerl it]) in
      let outerl = [(ldots_var,inner)] in
      subst_glob_vars outerl it
  | NLambda (na,ty,c) ->
      let e',na = g e na in GLambda (loc,na,Explicit,f e ty,f e' c)
  | NProd (na,ty,c) ->
      let e',na = g e na in GProd (loc,na,Explicit,f e ty,f e' c)
  | NLetIn (na,b,c) ->
      let e',na = g e na in GLetIn (loc,na,f e b,f e' c)
  | NCases (sty,rtntypopt,tml,eqnl) ->
      let e',tml' = List.fold_right (fun (tm,(na,t)) (e',tml') ->
	let e',t' = match t with
	| None -> e',None
	| Some (ind,nal) ->
	  let e',nal' = List.fold_right (fun na (e',nal) ->
	      let e',na' = g e' na in e',na'::nal) nal (e',[]) in
	  e',Some (loc,ind,nal') in
	let e',na' = g e' na in
	(e',(f e tm,(na',t'))::tml')) tml (e,[]) in
      let fold (idl,e) na = let (e,na) = g e na in ((name_cons na idl,e),na) in
      let eqnl' = List.map (fun (patl,rhs) ->
	let ((idl,e),patl) =
	  List.fold_map (cases_pattern_fold_map loc fold) ([],e) patl in
	(loc,idl,patl,f e rhs)) eqnl in
      GCases (loc,sty,Option.map (f e') rtntypopt,tml',eqnl')
  | NLetTuple (nal,(na,po),b,c) ->
      let e',nal = List.fold_map g e nal in
      let e'',na = g e na in
      GLetTuple (loc,nal,(na,Option.map (f e'') po),f e b,f e' c)
  | NIf (c,(na,po),b1,b2) ->
      let e',na = g e na in
      GIf (loc,f e c,(na,Option.map (f e') po),f e b1,f e b2)
  | NRec (fk,idl,dll,tl,bl) ->
      let e,dll = Array.fold_map (List.fold_map (fun e (na,oc,b) ->
	  let e,na = g e na in
	  (e,(na,Explicit,Option.map (f e) oc,f e b)))) e dll in
      let e',idl = Array.fold_map (to_id g) e idl in
      GRec (loc,fk,idl,dll,Array.map (f e) tl,Array.map (f e') bl)
  | NCast (c,k) -> GCast (loc,f e c,Miscops.map_cast_type (f e) k)
  | NSort x -> GSort (loc,x)
  | NHole (x, naming, arg)  -> GHole (loc, x, naming, arg)
  | NPatVar n -> GPatVar (loc,(false,n))
  | NRef x -> GRef (loc,x,None)

let glob_constr_of_notation_constr loc x =
  let rec aux () x =
    glob_constr_of_notation_constr_with_binders loc (fun () id -> ((),id)) aux () x
  in aux () x

(****************************************************************************)
(* Translating a glob_constr into a notation, interpreting recursive patterns *)

let add_id r id = r := (id :: pi1 !r, pi2 !r, pi3 !r)
let add_name r = function Anonymous -> () | Name id -> add_id r id

let split_at_recursive_part c =
  let sub = ref None in
  let rec aux = function
  | GApp (loc0,GVar(loc,v),c::l) when Id.equal v ldots_var ->
      begin match !sub with
      | None ->
        let () = sub := Some c in
        begin match l with
        | [] -> GVar (loc, ldots_var)
        | _ :: _ -> GApp (loc0, GVar (loc, ldots_var), l)
        end
      | Some _ ->
        (* Not narrowed enough to find only one recursive part *)
        raise Not_found
      end
  | c -> map_glob_constr aux c in
  let outer_iterator = aux c in
  match !sub with
  | None -> (* No recursive pattern found *) raise Not_found
  | Some c ->
  match outer_iterator with
  | GVar (_,v) when Id.equal v ldots_var -> (* Not enough context *) raise Not_found
  | _ -> outer_iterator, c

let on_true_do b f c = if b then (f c; b) else b

let compare_glob_constr f add t1 t2 = match t1,t2 with
  | GRef (_,r1,_), GRef (_,r2,_) -> eq_gr r1 r2
  | GVar (_,v1), GVar (_,v2) -> on_true_do (Id.equal v1 v2) add (Name v1)
  | GApp (_,f1,l1), GApp (_,f2,l2) -> f f1 f2 && List.for_all2eq f l1 l2
  | GLambda (_,na1,bk1,ty1,c1), GLambda (_,na2,bk2,ty2,c2)
    when Name.equal na1 na2 && Constrexpr_ops.binding_kind_eq bk1 bk2 ->
    on_true_do (f ty1 ty2 && f c1 c2) add na1
  | GProd (_,na1,bk1,ty1,c1), GProd (_,na2,bk2,ty2,c2)
    when Name.equal na1 na2 && Constrexpr_ops.binding_kind_eq bk1 bk2 ->
      on_true_do (f ty1 ty2 && f c1 c2) add na1
  | GHole _, GHole _ -> true
  | GSort (_,s1), GSort (_,s2) -> Miscops.glob_sort_eq s1 s2
  | GLetIn (_,na1,b1,c1), GLetIn (_,na2,b2,c2) when Name.equal na1 na2 ->
      on_true_do (f b1 b2 && f c1 c2) add na1
  | (GCases _ | GRec _
    | GPatVar _ | GEvar _ | GLetTuple _ | GIf _ | GCast _),_
  | _,(GCases _ | GRec _
      | GPatVar _ | GEvar _ | GLetTuple _ | GIf _ | GCast _)
      -> error "Unsupported construction in recursive notations."
  | (GRef _ | GVar _ | GApp _ | GLambda _ | GProd _
    | GHole _ | GSort _ | GLetIn _), _
      -> false

let rec eq_glob_constr t1 t2 = compare_glob_constr eq_glob_constr (fun _ -> ()) t1 t2

let subtract_loc loc1 loc2 = Loc.make_loc (fst (Loc.unloc loc1),fst (Loc.unloc loc2)-1)

let check_is_hole id = function GHole _ -> () | t ->
  user_err_loc (loc_of_glob_constr t,"",
    strbrk "In recursive notation with binders, " ++ pr_id id ++
    strbrk " is expected to come without type.")

let compare_recursive_parts found f (iterator,subc) =
  let diff = ref None in
  let terminator = ref None in
  let rec aux c1 c2 = match c1,c2 with
  | GVar(_,v), term when Id.equal v ldots_var ->
      (* We found the pattern *)
      assert (match !terminator with None -> true | Some _ -> false);
      terminator := Some term;
      true
  | GApp (_,GVar(_,v),l1), GApp (_,term,l2) when Id.equal v ldots_var ->
      (* We found the pattern, but there are extra arguments *)
      (* (this allows e.g. alternative (recursive) notation of application) *)
      assert (match !terminator with None -> true | Some _ -> false);
      terminator := Some term;
      List.for_all2eq aux l1 l2
  | GVar (_,x), GVar (_,y) when not (Id.equal x y) ->
      (* We found the position where it differs *)
      let lassoc = match !terminator with None -> false | Some _ -> true in
      let x,y = if lassoc then y,x else x,y in
      begin match !diff with
      | None ->
        let () = diff := Some (x, y, Some lassoc) in
        true
      | Some _ -> false
      end
  | GLambda (_,Name x,_,t_x,c), GLambda (_,Name y,_,t_y,term)
  | GProd (_,Name x,_,t_x,c), GProd (_,Name y,_,t_y,term) ->
      (* We found a binding position where it differs *)
      check_is_hole x t_x;
      check_is_hole y t_y;
      begin match !diff with
      | None ->
        let () = diff := Some (x, y, None) in
        aux c term
      | Some _ -> false
      end
  | _ ->
      compare_glob_constr aux (add_name found) c1 c2 in
  if aux iterator subc then
    match !diff with
    | None ->
	let loc1 = loc_of_glob_constr iterator in
	let loc2 = loc_of_glob_constr (Option.get !terminator) in
	(* Here, we would need a loc made of several parts ... *)
	user_err_loc (subtract_loc loc1 loc2,"",
          str "Both ends of the recursive pattern are the same.")
    | Some (x,y,Some lassoc) ->
	let newfound = (pi1 !found, (x,y) :: pi2 !found, pi3 !found) in
	let iterator =
	  f (if lassoc then subst_glob_vars [y,GVar(Loc.ghost,x)] iterator
	  else iterator) in
	(* found have been collected by compare_constr *)
	found := newfound;
	NList (x,y,iterator,f (Option.get !terminator),lassoc)
    | Some (x,y,None) ->
	let newfound = (pi1 !found, pi2 !found, (x,y) :: pi3 !found) in
	let iterator = f iterator in
	(* found have been collected by compare_constr *)
	found := newfound;
	NBinderList (x,y,iterator,f (Option.get !terminator))
  else
    raise Not_found

let notation_constr_and_vars_of_glob_constr a =
  let found = ref ([],[],[]) in
  let rec aux c =
    let keepfound = !found in
    (* n^2 complexity but small and done only once per notation *)
    try compare_recursive_parts found aux' (split_at_recursive_part c)
    with Not_found ->
    found := keepfound;
    match c with
    | GApp (_,GVar (loc,f),[c]) when Id.equal f ldots_var ->
	(* Fall on the second part of the recursive pattern w/o having
	   found the first part *)
	user_err_loc (loc,"",
	str "Cannot find where the recursive pattern starts.")
    | c ->
	aux' c
  and aux' = function
  | GVar (_,id) -> add_id found id; NVar id
  | GApp (_,g,args) -> NApp (aux g, List.map aux args)
  | GLambda (_,na,bk,ty,c) -> add_name found na; NLambda (na,aux ty,aux c)
  | GProd (_,na,bk,ty,c) -> add_name found na; NProd (na,aux ty,aux c)
  | GLetIn (_,na,b,c) -> add_name found na; NLetIn (na,aux b,aux c)
  | GCases (_,sty,rtntypopt,tml,eqnl) ->
      let f (_,idl,pat,rhs) = List.iter (add_id found) idl; (pat,aux rhs) in
      NCases (sty,Option.map aux rtntypopt,
        List.map (fun (tm,(na,x)) ->
	  add_name found na;
	  Option.iter
	    (fun (_,_,nl) -> List.iter (add_name found) nl) x;
          (aux tm,(na,Option.map (fun (_,ind,nal) -> (ind,nal)) x))) tml,
        List.map f eqnl)
  | GLetTuple (loc,nal,(na,po),b,c) ->
      add_name found na;
      List.iter (add_name found) nal;
      NLetTuple (nal,(na,Option.map aux po),aux b,aux c)
  | GIf (loc,c,(na,po),b1,b2) ->
      add_name found na;
      NIf (aux c,(na,Option.map aux po),aux b1,aux b2)
  | GRec (_,fk,idl,dll,tl,bl) ->
      Array.iter (add_id found) idl;
      let dll = Array.map (List.map (fun (na,bk,oc,b) ->
	 if bk != Explicit then
	   error "Binders marked as implicit not allowed in notations.";
	 add_name found na; (na,Option.map aux oc,aux b))) dll in
      NRec (fk,idl,dll,Array.map aux tl,Array.map aux bl)
  | GCast (_,c,k) -> NCast (aux c,Miscops.map_cast_type aux k)
  | GSort (_,s) -> NSort s
  | GHole (_,w,naming,arg) -> NHole (w, naming, arg)
  | GRef (_,r,_) -> NRef r
  | GPatVar (_,(_,n)) -> NPatVar n
  | GEvar _ ->
      error "Existential variables not allowed in notations."

  in
  let t = aux a in
  (* Side effect *)
  t, !found

let pair_equal eq1 eq2 (a,b) (a',b') = eq1 a a' && eq2 b b'

let check_variables nenv (found,foundrec,foundrecbinding) =
  let recvars = nenv.ninterp_rec_vars in
  let fold _ y accu = Id.Set.add y accu in
  let useless_vars = Id.Map.fold fold recvars Id.Set.empty in
  let filter y _ = not (Id.Set.mem y useless_vars) in
  let vars = Id.Map.filter filter nenv.ninterp_var_type in
  let check_recvar x =
    if Id.List.mem x found then
      errorlabstrm "" (pr_id x ++
	strbrk " should only be used in the recursive part of a pattern.") in
  let check (x, y) = check_recvar x; check_recvar y in
  let () = List.iter check foundrec in
  let () = List.iter check foundrecbinding in
  let check_bound x =
    if not (Id.List.mem x found) then
      if Id.List.mem_assoc x foundrec ||
         Id.List.mem_assoc x foundrecbinding ||
         Id.List.mem_assoc_sym x foundrec ||
         Id.List.mem_assoc_sym x foundrecbinding
      then
	error
          (Id.to_string x ^
          " should not be bound in a recursive pattern of the right-hand side.")
      else nenv.ninterp_only_parse <- true
  in
  let check_pair s x y where =
    if not (List.mem_f (pair_equal Id.equal Id.equal) (x,y) where) then
      errorlabstrm "" (strbrk "in the right-hand side, " ++ pr_id x ++
	str " and " ++ pr_id y ++ strbrk " should appear in " ++ str s ++
	str " position as part of a recursive pattern.") in
  let check_type x typ =
    match typ with
    | NtnInternTypeConstr ->
	begin
	  try check_pair "term" x (Id.Map.find x recvars) foundrec
	  with Not_found -> check_bound x
	end
    | NtnInternTypeBinder ->
	begin
	  try check_pair "binding" x (Id.Map.find x recvars) foundrecbinding
	  with Not_found -> check_bound x
	end
    | NtnInternTypeIdent -> check_bound x in
  Id.Map.iter check_type vars

let notation_constr_of_glob_constr nenv a =
  let a, found = notation_constr_and_vars_of_glob_constr a in
  let () = check_variables nenv found in
  a

(* Substitution of kernel names, avoiding a list of bound identifiers *)

let notation_constr_of_constr avoiding t =
  let t = Detyping.detype false avoiding (Global.env()) Evd.empty t in
  let nenv = {
    ninterp_var_type = Id.Map.empty;
    ninterp_rec_vars = Id.Map.empty;
    ninterp_only_parse = false;
  } in
  notation_constr_of_glob_constr nenv t

let rec subst_pat subst pat =
  match pat with
  | PatVar _ -> pat
  | PatCstr (loc,((kn,i),j),cpl,n) ->
      let kn' = subst_mind subst kn
      and cpl' = List.smartmap (subst_pat subst) cpl in
        if kn' == kn && cpl' == cpl then pat else
          PatCstr (loc,((kn',i),j),cpl',n)

let rec subst_notation_constr subst bound raw =
  match raw with
  | NRef ref ->
      let ref',t = subst_global subst ref in
	if ref' == ref then raw else
	  notation_constr_of_constr bound t

  | NVar _ -> raw

  | NApp (r,rl) ->
      let r' = subst_notation_constr subst bound r
      and rl' = List.smartmap (subst_notation_constr subst bound) rl in
	if r' == r && rl' == rl then raw else
	  NApp(r',rl')

  | NList (id1,id2,r1,r2,b) ->
      let r1' = subst_notation_constr subst bound r1
      and r2' = subst_notation_constr subst bound r2 in
	if r1' == r1 && r2' == r2 then raw else
	  NList (id1,id2,r1',r2',b)

  | NLambda (n,r1,r2) ->
      let r1' = subst_notation_constr subst bound r1
      and r2' = subst_notation_constr subst bound r2 in
	if r1' == r1 && r2' == r2 then raw else
	  NLambda (n,r1',r2')

  | NProd (n,r1,r2) ->
      let r1' = subst_notation_constr subst bound r1
      and r2' = subst_notation_constr subst bound r2 in
	if r1' == r1 && r2' == r2 then raw else
	  NProd (n,r1',r2')

  | NBinderList (id1,id2,r1,r2) ->
      let r1' = subst_notation_constr subst bound r1
      and r2' = subst_notation_constr subst bound r2 in
	if r1' == r1 && r2' == r2 then raw else
	  NBinderList (id1,id2,r1',r2')

  | NLetIn (n,r1,r2) ->
      let r1' = subst_notation_constr subst bound r1
      and r2' = subst_notation_constr subst bound r2 in
	if r1' == r1 && r2' == r2 then raw else
	  NLetIn (n,r1',r2')

  | NCases (sty,rtntypopt,rl,branches) ->
      let rtntypopt' = Option.smartmap (subst_notation_constr subst bound) rtntypopt
      and rl' = List.smartmap
        (fun (a,(n,signopt) as x) ->
	  let a' = subst_notation_constr subst bound a in
	  let signopt' = Option.map (fun ((indkn,i),nal as z) ->
	    let indkn' = subst_mind subst indkn in
	    if indkn == indkn' then z else ((indkn',i),nal)) signopt in
	  if a' == a && signopt' == signopt then x else (a',(n,signopt')))
        rl
      and branches' = List.smartmap
                        (fun (cpl,r as branch) ->
                           let cpl' = List.smartmap (subst_pat subst) cpl
                           and r' = subst_notation_constr subst bound r in
                             if cpl' == cpl && r' == r then branch else
                               (cpl',r'))
                        branches
      in
        if rtntypopt' == rtntypopt && rtntypopt == rtntypopt' &&
          rl' == rl && branches' == branches then raw else
          NCases (sty,rtntypopt',rl',branches')

  | NLetTuple (nal,(na,po),b,c) ->
      let po' = Option.smartmap (subst_notation_constr subst bound) po
      and b' = subst_notation_constr subst bound b
      and c' = subst_notation_constr subst bound c in
	if po' == po && b' == b && c' == c then raw else
	  NLetTuple (nal,(na,po'),b',c')

  | NIf (c,(na,po),b1,b2) ->
      let po' = Option.smartmap (subst_notation_constr subst bound) po
      and b1' = subst_notation_constr subst bound b1
      and b2' = subst_notation_constr subst bound b2
      and c' = subst_notation_constr subst bound c in
	if po' == po && b1' == b1 && b2' == b2 && c' == c then raw else
	  NIf (c',(na,po'),b1',b2')

  | NRec (fk,idl,dll,tl,bl) ->
      let dll' =
	Array.smartmap (List.smartmap (fun (na,oc,b as x) ->
	  let oc' =  Option.smartmap (subst_notation_constr subst bound) oc in
	  let b' =  subst_notation_constr subst bound b in
	  if oc' == oc && b' == b then x else (na,oc',b'))) dll in
      let tl' = Array.smartmap (subst_notation_constr subst bound) tl in
      let bl' = Array.smartmap (subst_notation_constr subst bound) bl in
      if dll' == dll && tl' == tl && bl' == bl then raw else
	  NRec (fk,idl,dll',tl',bl')

  | NPatVar _ | NSort _ -> raw

  | NHole (knd, naming, solve) ->
    let nknd = match knd with
    | Evar_kinds.ImplicitArg (ref, i, b) ->
      let nref, _ = subst_global subst ref in
      if nref == ref then knd else Evar_kinds.ImplicitArg (nref, i, b)
    | _ -> knd
    in
    let nsolve = Option.smartmap (Genintern.generic_substitute subst) solve in
    if nsolve == solve && nknd == knd then raw
    else NHole (nknd, naming, nsolve)

  | NCast (r1,k) ->
      let r1' = subst_notation_constr subst bound r1 in
      let k' = Miscops.smartmap_cast_type (subst_notation_constr subst bound) k in
      if r1' == r1 && k' == k then raw else NCast(r1',k')

let subst_interpretation subst (metas,pat) =
  let bound = List.map fst metas in
  (metas,subst_notation_constr subst bound pat)

(* Pattern-matching glob_constr and notation_constr *)

let abstract_return_type_context pi mklam tml rtno =
  Option.map (fun rtn ->
    let nal =
      List.flatten (List.map (fun (_,(na,t)) ->
	match t with Some x -> (pi x)@[na] | None -> [na]) tml) in
    List.fold_right mklam nal rtn)
    rtno

let abstract_return_type_context_glob_constr =
  abstract_return_type_context (fun (_,_,nal) -> nal)
    (fun na c ->
      GLambda(Loc.ghost,na,Explicit,GHole(Loc.ghost,Evar_kinds.InternalHole,Misctypes.IntroAnonymous,None),c))

let abstract_return_type_context_notation_constr =
  abstract_return_type_context snd
    (fun na c -> NLambda(na,NHole (Evar_kinds.InternalHole, Misctypes.IntroAnonymous, None),c))

exception No_match

let rec alpha_var id1 id2 = function
  | (i1,i2)::_ when Id.equal i1 id1 -> Id.equal i2 id2
  | (i1,i2)::_ when Id.equal i2 id2 -> Id.equal i1 id1
  | _::idl -> alpha_var id1 id2 idl
  | [] -> Id.equal id1 id2

let add_env alp (sigma,sigmalist,sigmabinders) var v =
  (* Check that no capture of binding variables occur *)
  if List.exists (fun (id,_) ->occur_glob_constr id v) alp then raise No_match;
  (* TODO: handle the case of multiple occs in different scopes *)
  ((var,v)::sigma,sigmalist,sigmabinders)

let bind_env alp (sigma,sigmalist,sigmabinders as fullsigma) var v =
  try
    let v' = Id.List.assoc var sigma in
    match v, v' with
    | GHole _, _ -> fullsigma
    | _, GHole _ ->
      add_env alp (Id.List.remove_assoc var sigma,sigmalist,sigmabinders) var v
    | _, _ ->
        if glob_constr_eq v v' then fullsigma
        else raise No_match
  with Not_found -> add_env alp fullsigma var v

let bind_binder (sigma,sigmalist,sigmabinders) x bl =
  (sigma,sigmalist,(x,List.rev bl)::sigmabinders)

let match_fix_kind fk1 fk2 =
  match (fk1,fk2) with
  | GCoFix n1, GCoFix n2 -> Int.equal n1 n2
  | GFix (nl1,n1), GFix (nl2,n2) ->
      let test (n1, _) (n2, _) = match n1, n2 with
      | _, None -> true
      | Some id1, Some id2 -> Int.equal id1 id2
      | _ -> false
      in
      Int.equal n1 n2 &&
      Array.for_all2 test nl1 nl2
  | _ -> false

let match_opt f sigma t1 t2 = match (t1,t2) with
  | None, None -> sigma
  | Some t1, Some t2 -> f sigma t1 t2
  | _ -> raise No_match

let match_names metas (alp,sigma) na1 na2 = match (na1,na2) with
  | (_,Name id2) when Id.List.mem id2 (fst metas) ->
      let rhs = match na1 with
      | Name id1 -> GVar (Loc.ghost,id1)
      | Anonymous -> GHole (Loc.ghost,Evar_kinds.InternalHole,Misctypes.IntroAnonymous,None) in
      alp, bind_env alp sigma id2 rhs
  | (Name id1,Name id2) -> (id1,id2)::alp,sigma
  | (Anonymous,Anonymous) -> alp,sigma
  | _ -> raise No_match

let rec match_cases_pattern_binders metas acc pat1 pat2 =
  match (pat1,pat2) with
  | PatVar (_,na1), PatVar (_,na2) -> match_names metas acc na1 na2
  | PatCstr (_,c1,patl1,na1), PatCstr (_,c2,patl2,na2)
      when eq_constructor c1 c2 && Int.equal (List.length patl1) (List.length patl2) ->
      List.fold_left2 (match_cases_pattern_binders metas)
	(match_names metas acc na1 na2) patl1 patl2
  | _ -> raise No_match

let glue_letin_with_decls = true

let rec match_iterated_binders islambda decls = function
  | GLambda (_,na,bk,t,b) when islambda ->
      match_iterated_binders islambda ((na,bk,None,t)::decls) b
  | GProd (_,(Name _ as na),bk,t,b) when not islambda ->
      match_iterated_binders islambda ((na,bk,None,t)::decls) b
  | GLetIn (loc,na,c,b) when glue_letin_with_decls ->
      match_iterated_binders islambda
	((na,Explicit (*?*), Some c,GHole(loc,Evar_kinds.BinderType na,Misctypes.IntroAnonymous,None))::decls) b
  | b -> (decls,b)

let remove_sigma x (sigmavar,sigmalist,sigmabinders) =
  (Id.List.remove_assoc x sigmavar,sigmalist,sigmabinders)

let match_abinderlist_with_app match_fun metas sigma rest x iter termin =
  let rec aux sigma acc rest =
    try
      let sigma = match_fun (ldots_var::fst metas,snd metas) sigma rest iter in
      let rest = Id.List.assoc ldots_var (pi1 sigma) in
      let b =
        match Id.List.assoc x (pi3 sigma) with [b] -> b | _ ->assert false
      in
      let sigma = remove_sigma x (remove_sigma ldots_var sigma) in
      aux sigma (b::acc) rest
    with No_match when not (List.is_empty acc) ->
      acc, match_fun metas sigma rest termin in
  let bl,sigma = aux sigma [] rest in
  bind_binder sigma x bl

let match_alist match_fun metas sigma rest x iter termin lassoc =
  let rec aux sigma acc rest =
    try
      let sigma = match_fun (ldots_var::fst metas,snd metas) sigma rest iter in
      let rest = Id.List.assoc ldots_var (pi1 sigma) in
      let t = Id.List.assoc x (pi1 sigma) in
      let sigma = remove_sigma x (remove_sigma ldots_var sigma) in
      aux sigma (t::acc) rest
    with No_match when not (List.is_empty acc) ->
      acc, match_fun metas sigma rest termin in
  let l,sigma = aux sigma [] rest in
  (pi1 sigma, (x,if lassoc then l else List.rev l)::pi2 sigma, pi3 sigma)

let does_not_come_from_already_eta_expanded_var =
  (* This is hack to avoid looping on a rule with rhs of the form *)
  (* "?f (fun ?x => ?g)" since otherwise, matching "F H" expands in *)
  (* "F (fun x => H x)" and "H x" is recursively matched against the same *)
  (* rule, giving "H (fun x' => x x')" and so on. *)
  (* Ideally, we would need the type of the expression to know which of *)
  (* the arguments applied to it can be eta-expanded without looping. *)
  (* The following test is then an approximation of what can be done *)
  (* optimally (whether other looping situations can occur remains to be *)
  (* checked). *)
  function GVar _ -> false | _ -> true

let rec match_ inner u alp (tmetas,blmetas as metas) sigma a1 a2 =
  match (a1,a2) with

  (* Matching notation variable *)
  | r1, NVar id2 when Id.List.mem id2 tmetas -> bind_env alp sigma id2 r1

  (* Matching recursive notations for terms *)
  | r1, NList (x,_,iter,termin,lassoc) ->
      match_alist (match_hd u alp) metas sigma r1 x iter termin lassoc

  (* Matching recursive notations for binders: ad hoc cases supporting let-in *)
  | GLambda (_,na1,bk,t1,b1), NBinderList (x,_,NLambda (Name id2,_,b2),termin)->
      let (decls,b) = match_iterated_binders true [(na1,bk,None,t1)] b1 in
      (* TODO: address the possibility that termin is a Lambda itself *)
      match_in u alp metas (bind_binder sigma x decls) b termin
  | GProd (_,na1,bk,t1,b1), NBinderList (x,_,NProd (Name id2,_,b2),termin)
      when na1 != Anonymous ->
      let (decls,b) = match_iterated_binders false [(na1,bk,None,t1)] b1 in
      (* TODO: address the possibility that termin is a Prod itself *)
      match_in u alp metas (bind_binder sigma x decls) b termin
  (* Matching recursive notations for binders: general case *)
  | r, NBinderList (x,_,iter,termin) ->
      match_abinderlist_with_app (match_hd u alp) metas sigma r x iter termin

  (* Matching individual binders as part of a recursive pattern *)
  | GLambda (_,na,bk,t,b1), NLambda (Name id,_,b2) when Id.List.mem id blmetas ->
      match_in u alp metas (bind_binder sigma id [(na,bk,None,t)]) b1 b2
  | GProd (_,na,bk,t,b1), NProd (Name id,_,b2)
      when Id.List.mem id blmetas && na != Anonymous ->
      match_in u alp metas (bind_binder sigma id [(na,bk,None,t)]) b1 b2

  (* Matching compositionally *)
  | GVar (_,id1), NVar id2 when alpha_var id1 id2 alp -> sigma
  | GRef (_,r1,_), NRef r2 when (eq_gr r1 r2) -> sigma
  | GPatVar (_,(_,n1)), NPatVar n2 when Id.equal n1 n2 -> sigma
  | GApp (loc,f1,l1), NApp (f2,l2) ->
      let n1 = List.length l1 and n2 = List.length l2 in
      let f1,l1,f2,l2 =
	if n1 < n2 then
	  let l21,l22 = List.chop (n2-n1) l2 in f1,l1, NApp (f2,l21), l22
	else if n1 > n2 then
	  let l11,l12 = List.chop (n1-n2) l1 in GApp (loc,f1,l11),l12, f2,l2
	else f1,l1, f2, l2 in
      let may_use_eta = does_not_come_from_already_eta_expanded_var f1 in
      List.fold_left2 (match_ may_use_eta u alp metas)
        (match_in u alp metas sigma f1 f2) l1 l2
  | GLambda (_,na1,_,t1,b1), NLambda (na2,t2,b2) ->
     match_binders u alp metas na1 na2 (match_in u alp metas sigma t1 t2) b1 b2
  | GProd (_,na1,_,t1,b1), NProd (na2,t2,b2) ->
     match_binders u alp metas na1 na2 (match_in u alp metas sigma t1 t2) b1 b2
  | GLetIn (_,na1,t1,b1), NLetIn (na2,t2,b2) ->
     match_binders u alp metas na1 na2 (match_in u alp metas sigma t1 t2) b1 b2
  | GCases (_,sty1,rtno1,tml1,eqnl1), NCases (sty2,rtno2,tml2,eqnl2)
      when sty1 == sty2
	 && Int.equal (List.length tml1) (List.length tml2)
	 && Int.equal (List.length eqnl1) (List.length eqnl2) ->
      let rtno1' = abstract_return_type_context_glob_constr tml1 rtno1 in
      let rtno2' = abstract_return_type_context_notation_constr tml2 rtno2 in
      let sigma =
	try Option.fold_left2 (match_in u alp metas) sigma rtno1' rtno2'
	with Option.Heterogeneous -> raise No_match
      in
      let sigma = List.fold_left2
      (fun s (tm1,_) (tm2,_) ->
        match_in u alp metas s tm1 tm2) sigma tml1 tml2 in
      List.fold_left2 (match_equations u alp metas) sigma eqnl1 eqnl2
  | GLetTuple (_,nal1,(na1,to1),b1,c1), NLetTuple (nal2,(na2,to2),b2,c2)
      when Int.equal (List.length nal1) (List.length nal2) ->
      let sigma = match_opt (match_binders u alp metas na1 na2) sigma to1 to2 in
      let sigma = match_in u alp metas sigma b1 b2 in
      let (alp,sigma) =
	List.fold_left2 (match_names metas) (alp,sigma) nal1 nal2 in
      match_in u alp metas sigma c1 c2
  | GIf (_,a1,(na1,to1),b1,c1), NIf (a2,(na2,to2),b2,c2) ->
      let sigma = match_opt (match_binders u alp metas na1 na2) sigma to1 to2 in
      List.fold_left2 (match_in u alp metas) sigma [a1;b1;c1] [a2;b2;c2]
  | GRec (_,fk1,idl1,dll1,tl1,bl1), NRec (fk2,idl2,dll2,tl2,bl2)
      when match_fix_kind fk1 fk2 && Int.equal (Array.length idl1) (Array.length idl2) &&
	Array.for_all2 (fun l1 l2 -> Int.equal (List.length l1) (List.length l2)) dll1 dll2
	->
      let alp,sigma = Array.fold_left2
	(List.fold_left2 (fun (alp,sigma) (na1,_,oc1,b1) (na2,oc2,b2) ->
	  let sigma =
	    match_in u alp metas
              (match_opt (match_in u alp metas) sigma oc1 oc2) b1 b2
	  in match_names metas (alp,sigma) na1 na2)) (alp,sigma) dll1 dll2 in
      let sigma = Array.fold_left2 (match_in u alp metas) sigma tl1 tl2 in
      let alp,sigma = Array.fold_right2 (fun id1 id2 alsig ->
	match_names metas alsig (Name id1) (Name id2)) idl1 idl2 (alp,sigma) in
      Array.fold_left2 (match_in u alp metas) sigma bl1 bl2
  | GCast(_,c1,CastConv t1), NCast (c2,CastConv t2)
  | GCast(_,c1,CastVM t1), NCast (c2,CastVM t2) ->
      match_in u alp metas (match_in u alp metas sigma c1 c2) t1 t2
  | GCast(_,c1, CastCoerce), NCast(c2, CastCoerce) ->
      match_in u alp metas sigma c1 c2
  | GSort (_,GType _), NSort (GType _) when not u -> sigma
  | GSort (_,s1), NSort s2 when Miscops.glob_sort_eq s1 s2 -> sigma
  | GPatVar _, NHole _ -> (*Don't hide Metas, they bind in ltac*) raise No_match
  | a, NHole _ -> sigma

  (* On the fly eta-expansion so as to use notations of the form
     "exists x, P x" for "ex P"; ensure at least one constructor is
     consumed to avoid looping; expects type not given because don't know
     otherwise how to ensure it corresponds to a well-typed eta-expansion;
     we make an exception for types which are metavariables: this is useful e.g.
     to print "{x:_ & P x}" knowing that notation "{x & P x}" is not defined. *)
  | b1, NLambda (Name id,(NHole _ | NVar _ as t2),b2) when inner ->
      let id' = Namegen.next_ident_away id (free_glob_vars b1) in
      let t1 = GHole(Loc.ghost,Evar_kinds.BinderType (Name id'),Misctypes.IntroAnonymous,None) in
      let sigma = match t2 with
      | NHole _ -> sigma
      | NVar id2 -> bind_env alp sigma id2 t1
      | _ -> assert false in
      match_in u alp metas (bind_binder sigma id [(Name id',Explicit,None,t1)])
       (mkGApp Loc.ghost b1 (GVar (Loc.ghost,id'))) b2

  | (GRec _ | GEvar _), _
  | _,_ -> raise No_match

and match_in u = match_ true u

and match_hd u = match_ false u

and match_binders u alp metas na1 na2 sigma b1 b2 =
  let (alp,sigma) = match_names metas (alp,sigma) na1 na2 in
  match_in u alp metas sigma b1 b2

and match_equations u alp metas sigma (_,_,patl1,rhs1) (patl2,rhs2) =
  (* patl1 and patl2 have the same length because they respectively
     correspond to some tml1 and tml2 that have the same length *)
  let (alp,sigma) =
    List.fold_left2 (match_cases_pattern_binders metas)
      (alp,sigma) patl1 patl2 in
  match_in u alp metas sigma rhs1 rhs2

let match_notation_constr u c (metas,pat) =
  let test (_, (_, x)) = match x with NtnTypeBinderList -> false | _ -> true in
  let vars = List.partition test metas in
  let vars = (List.map fst (fst vars), List.map fst (snd vars)) in
  let terms,termlists,binders = match_ false u [] vars ([],[],[]) c pat in
  (* Reorder canonically the substitution *)
  let find x =
    try Id.List.assoc x terms
    with Not_found ->
      (* Happens for binders bound to Anonymous *)
      (* Find a better way to propagate Anonymous... *)
      GVar (Loc.ghost,x) in
  List.fold_right (fun (x,(scl,typ)) (terms',termlists',binders') ->
    match typ with
    | NtnTypeConstr ->
       ((find x, scl)::terms',termlists',binders')
    | NtnTypeConstrList ->
       (terms',(Id.List.assoc x termlists,scl)::termlists',binders')
    | NtnTypeBinderList ->
       (terms',termlists',(Id.List.assoc x binders,scl)::binders'))
    metas ([],[],[])

(* Matching cases pattern *)
let add_patterns_for_params ind l =
  let mib,_ = Global.lookup_inductive ind in
  let nparams = mib.Declarations.mind_nparams in
    Util.List.addn nparams (PatVar (Loc.ghost,Anonymous)) l

let bind_env_cases_pattern (sigma,sigmalist,x as fullsigma) var v =
  try
    let vvar = Id.List.assoc var sigma in
    if cases_pattern_eq v vvar then fullsigma else raise No_match
  with Not_found ->
    (* TODO: handle the case of multiple occs in different scopes *)
    (var,v)::sigma,sigmalist,x

let rec match_cases_pattern metas sigma a1 a2 =
 match (a1,a2) with
  | r1, NVar id2 when Id.List.mem id2 metas -> (bind_env_cases_pattern sigma id2 r1),(0,[])
  | PatVar (_,Anonymous), NHole _ -> sigma,(0,[])
  | PatCstr (loc,(ind,_ as r1),largs,_), NRef (ConstructRef r2) when eq_constructor r1 r2 ->
      sigma,(0,add_patterns_for_params (fst r1) largs)
  | PatCstr (loc,(ind,_ as r1),args1,_), NApp (NRef (ConstructRef r2),l2)
      when eq_constructor r1 r2 ->
      let l1 = add_patterns_for_params (fst r1) args1 in
      let le2 = List.length l2 in
      if Int.equal le2 0 (* Special case of a notation for a @Cstr *) || le2 > List.length l1
      then
	raise No_match
      else
	let l1',more_args = Util.List.chop le2 l1 in
	(List.fold_left2 (match_cases_pattern_no_more_args metas) sigma l1' l2),(le2,more_args)
  | r1, NList (x,_,iter,termin,lassoc) ->
      (match_alist (fun (metas,_) -> match_cases_pattern_no_more_args metas)
	(metas,[]) (pi1 sigma,pi2 sigma,()) r1 x iter termin lassoc),(0,[])
  | _ -> raise No_match

and match_cases_pattern_no_more_args metas sigma a1 a2 =
    match match_cases_pattern metas sigma a1 a2 with
      |out,(_,[]) -> out
      |_ -> raise No_match

let match_ind_pattern metas sigma ind pats a2 =
  match a2 with
  | NRef (IndRef r2) when eq_ind ind r2 ->
      sigma,(0,pats)
  | NApp (NRef (IndRef r2),l2)
      when eq_ind ind r2 ->
      let le2 = List.length l2 in
      if Int.equal le2 0 (* Special case of a notation for a @Cstr *) || le2 > List.length pats
      then
	raise No_match
      else
	let l1',more_args = Util.List.chop le2 pats in
	(List.fold_left2 (match_cases_pattern_no_more_args metas) sigma l1' l2),(le2,more_args)
  |_ -> raise No_match

let reorder_canonically_substitution terms termlists metas =
  List.fold_right (fun (x,(scl,typ)) (terms',termlists') ->
    match typ with
      | NtnTypeConstr -> ((Id.List.assoc x terms, scl)::terms',termlists')
      | NtnTypeConstrList -> (terms',(Id.List.assoc x termlists,scl)::termlists')
      | NtnTypeBinderList -> assert false)
    metas ([],[])

let match_notation_constr_cases_pattern c (metas,pat) =
  let vars = List.map fst metas in
  let (terms,termlists,()),more_args = match_cases_pattern vars ([],[],()) c pat in
  reorder_canonically_substitution terms termlists metas, more_args

let match_notation_constr_ind_pattern ind args (metas,pat) =
  let vars = List.map fst metas in
  let (terms,termlists,()),more_args = match_ind_pattern vars ([],[],()) ind args pat in
  reorder_canonically_substitution terms termlists metas, more_args
