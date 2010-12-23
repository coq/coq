(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Pp
open Util
open Names
open Nameops
open Libnames
open Rawterm
open Term
open Mod_subst
(*i*)

(**********************************************************************)
(* This is the subtype of glob_constr allowed in syntactic extensions *)

(* For AList: first constr is iterator, second is terminator;
   first id is where each argument of the list has to be substituted
   in iterator and snd id is alternative name just for printing;
   boolean is associativity *)

type aconstr =
  (* Part common to glob_constr and cases_pattern *)
  | ARef of global_reference
  | AVar of identifier
  | AApp of aconstr * aconstr list
  | AList of identifier * identifier * aconstr * aconstr * bool
  (* Part only in glob_constr *)
  | ALambda of name * aconstr * aconstr
  | AProd of name * aconstr * aconstr
  | ABinderList of identifier * identifier * aconstr * aconstr
  | ALetIn of name * aconstr * aconstr
  | ACases of case_style * aconstr option *
      (aconstr * (name * (inductive * int * name list) option)) list *
      (cases_pattern list * aconstr) list
  | ALetTuple of name list * (name * aconstr option) * aconstr * aconstr
  | AIf of aconstr * (name * aconstr option) * aconstr * aconstr
  | ARec of fix_kind * identifier array *
      (name * aconstr option * aconstr) list array * aconstr array *
      aconstr array
  | ASort of rawsort
  | AHole of Evd.hole_kind
  | APatVar of patvar
  | ACast of aconstr * aconstr cast_type

type scope_name = string

type tmp_scope_name = scope_name

type subscopes = tmp_scope_name option * scope_name list

type notation_var_instance_type =
  | NtnTypeConstr | NtnTypeConstrList | NtnTypeBinderList

type notation_var_internalization_type =
  | NtnInternTypeConstr | NtnInternTypeBinder | NtnInternTypeIdent

type interpretation =
    (identifier * (subscopes * notation_var_instance_type)) list * aconstr

(**********************************************************************)
(* Re-interpret a notation as a glob_constr, taking care of binders     *)

let name_to_ident = function
  | Anonymous -> error "This expression should be a simple identifier."
  | Name id -> id

let to_id g e id = let e,na = g e (Name id) in e,name_to_ident na

let rec cases_pattern_fold_map loc g e = function
  | PatVar (_,na) ->
      let e',na' = g e na in e', PatVar (loc,na')
  | PatCstr (_,cstr,patl,na) ->
      let e',na' = g e na in
      let e',patl' = list_fold_map (cases_pattern_fold_map loc g) e patl in
      e', PatCstr (loc,cstr,patl',na')

let rec subst_glob_vars l = function
  | GVar (_,id) as r -> (try List.assoc id l with Not_found -> r)
  | GProd (loc,Name id,bk,t,c) ->
      let id =
	try match List.assoc id l with GVar(_,id') -> id' | _ -> id
	with Not_found -> id in
      GProd (loc,Name id,bk,subst_glob_vars l t,subst_glob_vars l c)
  | GLambda (loc,Name id,bk,t,c) ->
      let id =
	try match List.assoc id l with GVar(_,id') -> id' | _ -> id
	with Not_found -> id in
      GLambda (loc,Name id,bk,subst_glob_vars l t,subst_glob_vars l c)
  | r -> map_glob_constr (subst_glob_vars l) r (* assume: id is not binding *)

let ldots_var = id_of_string ".."

let glob_constr_of_aconstr_with_binders loc g f e = function
  | AVar id -> GVar (loc,id)
  | AApp (a,args) -> GApp (loc,f e a, List.map (f e) args)
  | AList (x,y,iter,tail,swap) ->
      let t = f e tail in let it = f e iter in
      let innerl = (ldots_var,t)::(if swap then [] else [x,GVar(loc,y)]) in
      let inner = GApp (loc,GVar (loc,ldots_var),[subst_glob_vars innerl it]) in
      let outerl = (ldots_var,inner)::(if swap then [x,GVar(loc,y)] else []) in
      subst_glob_vars outerl it
  | ABinderList (x,y,iter,tail) ->
      let t = f e tail in let it = f e iter in
      let innerl = [(ldots_var,t);(x,GVar(loc,y))] in
      let inner = GApp (loc,GVar (loc,ldots_var),[subst_glob_vars innerl it]) in
      let outerl = [(ldots_var,inner)] in
      subst_glob_vars outerl it
  | ALambda (na,ty,c) ->
      let e',na = g e na in GLambda (loc,na,Explicit,f e ty,f e' c)
  | AProd (na,ty,c) ->
      let e',na = g e na in GProd (loc,na,Explicit,f e ty,f e' c)
  | ALetIn (na,b,c) ->
      let e',na = g e na in GLetIn (loc,na,f e b,f e' c)
  | ACases (sty,rtntypopt,tml,eqnl) ->
      let e',tml' = List.fold_right (fun (tm,(na,t)) (e',tml') ->
	let e',t' = match t with
	| None -> e',None
	| Some (ind,npar,nal) ->
	  let e',nal' = List.fold_right (fun na (e',nal) ->
	      let e',na' = g e' na in e',na'::nal) nal (e',[]) in
	  e',Some (loc,ind,npar,nal') in
	let e',na' = g e' na in
	(e',(f e tm,(na',t'))::tml')) tml (e,[]) in
      let fold (idl,e) na = let (e,na) = g e na in ((name_cons na idl,e),na) in
      let eqnl' = List.map (fun (patl,rhs) ->
	let ((idl,e),patl) =
	  list_fold_map (cases_pattern_fold_map loc fold) ([],e) patl in
	(loc,idl,patl,f e rhs)) eqnl in
      GCases (loc,sty,Option.map (f e') rtntypopt,tml',eqnl')
  | ALetTuple (nal,(na,po),b,c) ->
      let e',nal = list_fold_map g e nal in
      let e'',na = g e na in
      GLetTuple (loc,nal,(na,Option.map (f e'') po),f e b,f e' c)
  | AIf (c,(na,po),b1,b2) ->
      let e',na = g e na in
      GIf (loc,f e c,(na,Option.map (f e') po),f e b1,f e b2)
  | ARec (fk,idl,dll,tl,bl) ->
      let e,dll = array_fold_map (list_fold_map (fun e (na,oc,b) ->
	  let e,na = g e na in
	  (e,(na,Explicit,Option.map (f e) oc,f e b)))) e dll in
      let e',idl = array_fold_map (to_id g) e idl in
      GRec (loc,fk,idl,dll,Array.map (f e) tl,Array.map (f e') bl)
  | ACast (c,k) -> GCast (loc,f e c,
			  match k with
			    | CastConv (k,t) -> CastConv (k,f e t)
			    | CastCoerce -> CastCoerce)
  | ASort x -> GSort (loc,x)
  | AHole x  -> GHole (loc,x)
  | APatVar n -> GPatVar (loc,(false,n))
  | ARef x -> GRef (loc,x)

let rec glob_constr_of_aconstr loc x =
  let rec aux () x =
    glob_constr_of_aconstr_with_binders loc (fun () id -> ((),id)) aux () x
  in aux () x

(****************************************************************************)
(* Translating a glob_constr into a notation, interpreting recursive patterns *)

let add_id r id = r := (id :: pi1 !r, pi2 !r, pi3 !r)
let add_name r = function Anonymous -> () | Name id -> add_id r id

let split_at_recursive_part c =
  let sub = ref None in
  let rec aux = function
  | GApp (loc0,GVar(loc,v),c::l) when v = ldots_var ->
      if !sub <> None then
	(* Not narrowed enough to find only one recursive part *)
	raise Not_found
      else
	(sub := Some c;
	 if l = [] then GVar (loc,ldots_var)
	 else GApp (loc0,GVar (loc,ldots_var),l))
  | c -> map_glob_constr aux c in
  let outer_iterator = aux c in
  match !sub with
  | None -> (* No recursive pattern found *) raise Not_found
  | Some c ->
  match outer_iterator with
  | GVar (_,v) when v = ldots_var -> (* Not enough context *) raise Not_found
  | _ -> outer_iterator, c

let on_true_do b f c = if b then (f c; b) else b

let compare_glob_constr f add t1 t2 = match t1,t2 with
  | GRef (_,r1), GRef (_,r2) -> eq_gr r1 r2
  | GVar (_,v1), GVar (_,v2) -> on_true_do (v1 = v2) add (Name v1)
  | GApp (_,f1,l1), GApp (_,f2,l2) -> f f1 f2 & list_for_all2eq f l1 l2
  | GLambda (_,na1,bk1,ty1,c1), GLambda (_,na2,bk2,ty2,c2) when na1 = na2 && bk1 = bk2 -> on_true_do (f ty1 ty2 & f c1 c2) add na1
  | GProd (_,na1,bk1,ty1,c1), GProd (_,na2,bk2,ty2,c2) when na1 = na2 && bk1 = bk2 ->
      on_true_do (f ty1 ty2 & f c1 c2) add na1
  | GHole _, GHole _ -> true
  | GSort (_,s1), GSort (_,s2) -> s1 = s2
  | GLetIn (_,na1,b1,c1), GLetIn (_,na2,b2,c2) when na1 = na2 ->
      on_true_do (f b1 b2 & f c1 c2) add na1
  | (GCases _ | GRec _ | GDynamic _
    | GPatVar _ | GEvar _ | GLetTuple _ | GIf _ | GCast _),_
  | _,(GCases _ | GRec _ | GDynamic _
      | GPatVar _ | GEvar _ | GLetTuple _ | GIf _ | GCast _)
      -> error "Unsupported construction in recursive notations."
  | (GRef _ | GVar _ | GApp _ | GLambda _ | GProd _
    | GHole _ | GSort _ | GLetIn _), _
      -> false

let rec eq_glob_constr t1 t2 = compare_glob_constr eq_glob_constr (fun _ -> ()) t1 t2

let subtract_loc loc1 loc2 = make_loc (fst (unloc loc1),fst (unloc loc2)-1)

let check_is_hole id = function GHole _ -> () | t ->
  user_err_loc (loc_of_glob_constr t,"",
    strbrk "In recursive notation with binders, " ++ pr_id id ++
    strbrk " is expected to come without type.")

let compare_recursive_parts found f (iterator,subc) =
  let diff = ref None in
  let terminator = ref None in
  let rec aux c1 c2 = match c1,c2 with
  | GVar(_,v), term when v = ldots_var ->
      (* We found the pattern *)
      assert (!terminator = None); terminator := Some term;
      true
  | GApp (_,GVar(_,v),l1), GApp (_,term,l2) when v = ldots_var ->
      (* We found the pattern, but there are extra arguments *)
      (* (this allows e.g. alternative (recursive) notation of application) *)
      assert (!terminator = None); terminator := Some term;
      list_for_all2eq aux l1 l2
  | GVar (_,x), GVar (_,y) when x<>y ->
      (* We found the position where it differs *)
      let lassoc = (!terminator <> None) in
      let x,y = if lassoc then y,x else x,y in
      !diff = None && (diff := Some (x,y,Some lassoc); true)
  | GLambda (_,Name x,_,t_x,c), GLambda (_,Name y,_,t_y,term)
  | GProd (_,Name x,_,t_x,c), GProd (_,Name y,_,t_y,term) ->
      (* We found a binding position where it differs *)
      check_is_hole y t_x;
      check_is_hole y t_y;
      !diff = None && (diff := Some (x,y,None); aux c term)
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
	  f (if lassoc then subst_glob_vars [y,GVar(dummy_loc,x)] iterator
	  else iterator) in
	(* found have been collected by compare_constr *)
	found := newfound;
	AList (x,y,iterator,f (Option.get !terminator),lassoc)
    | Some (x,y,None) ->
	let newfound = (pi1 !found, pi2 !found, (x,y) :: pi3 !found) in
	let iterator = f iterator in
	(* found have been collected by compare_constr *)
	found := newfound;
	ABinderList (x,y,iterator,f (Option.get !terminator))
  else
    raise Not_found

let aconstr_and_vars_of_glob_constr a =
  let found = ref ([],[],[]) in
  let rec aux c =
    let keepfound = !found in
    (* n^2 complexity but small and done only once per notation *)
    try compare_recursive_parts found aux' (split_at_recursive_part c)
    with Not_found ->
    found := keepfound;
    match c with
    | GApp (_,GVar (loc,f),[c]) when f = ldots_var ->
	(* Fall on the second part of the recursive pattern w/o having
	   found the first part *)
	user_err_loc (loc,"",
	str "Cannot find where the recursive pattern starts.")
    | c ->
	aux' c
  and aux' = function
  | GVar (_,id) -> add_id found id; AVar id
  | GApp (_,g,args) -> AApp (aux g, List.map aux args)
  | GLambda (_,na,bk,ty,c) -> add_name found na; ALambda (na,aux ty,aux c)
  | GProd (_,na,bk,ty,c) -> add_name found na; AProd (na,aux ty,aux c)
  | GLetIn (_,na,b,c) -> add_name found na; ALetIn (na,aux b,aux c)
  | GCases (_,sty,rtntypopt,tml,eqnl) ->
      let f (_,idl,pat,rhs) = List.iter (add_id found) idl; (pat,aux rhs) in
      ACases (sty,Option.map aux rtntypopt,
        List.map (fun (tm,(na,x)) ->
	  add_name found na;
	  Option.iter
	    (fun (_,_,_,nl) -> List.iter (add_name found) nl) x;
          (aux tm,(na,Option.map (fun (_,ind,n,nal) -> (ind,n,nal)) x))) tml,
        List.map f eqnl)
  | GLetTuple (loc,nal,(na,po),b,c) ->
      add_name found na;
      List.iter (add_name found) nal;
      ALetTuple (nal,(na,Option.map aux po),aux b,aux c)
  | GIf (loc,c,(na,po),b1,b2) ->
      add_name found na;
      AIf (aux c,(na,Option.map aux po),aux b1,aux b2)
  | GRec (_,fk,idl,dll,tl,bl) ->
      Array.iter (add_id found) idl;
      let dll = Array.map (List.map (fun (na,bk,oc,b) ->
	 if bk <> Explicit then
	   error "Binders marked as implicit not allowed in notations.";
	 add_name found na; (na,Option.map aux oc,aux b))) dll in
      ARec (fk,idl,dll,Array.map aux tl,Array.map aux bl)
  | GCast (_,c,k) -> ACast (aux c,
			    match k with CastConv (k,t) -> CastConv (k,aux t)
			      | CastCoerce -> CastCoerce)
  | GSort (_,s) -> ASort s
  | GHole (_,w) -> AHole w
  | GRef (_,r) -> ARef r
  | GPatVar (_,(_,n)) -> APatVar n
  | GDynamic _ | GEvar _ ->
      error "Existential variables not allowed in notations."

  in
  let t = aux a in
  (* Side effect *)
  t, !found

let rec list_rev_mem_assoc x = function
  | [] -> false
  | (_,x')::l -> x = x' || list_rev_mem_assoc x l

let check_variables vars recvars (found,foundrec,foundrecbinding) =
  let useless_vars = List.map snd recvars in
  let vars = List.filter (fun (y,_) -> not (List.mem y useless_vars)) vars in
  let check_recvar x =
    if List.mem x found then
      errorlabstrm "" (pr_id x ++
	strbrk " should only be used in the recursive part of a pattern.") in
  List.iter (fun (x,y) -> check_recvar x; check_recvar y)
    (foundrec@foundrecbinding);
  let check_bound x =
    if not (List.mem x found) then
      if List.mem_assoc x foundrec or List.mem_assoc x foundrecbinding
	or list_rev_mem_assoc x foundrec or list_rev_mem_assoc x foundrecbinding
      then
	error ((string_of_id x)^" should not be bound in a recursive pattern of the right-hand side.")
      else
	error ((string_of_id x)^" is unbound in the right-hand side.") in
  let check_pair s x y where =
    if not (List.mem (x,y) where) then
      errorlabstrm "" (strbrk "in the right-hand side, " ++ pr_id x ++
	str " and " ++ pr_id y ++ strbrk " should appear in " ++ str s ++
	str " position as part of a recursive pattern.") in
  let check_type (x,typ) =
    match typ with
    | NtnInternTypeConstr ->
	begin
	  try check_pair "term" x (List.assoc x recvars) foundrec
	  with Not_found -> check_bound x
	end
    | NtnInternTypeBinder ->
	begin
	  try check_pair "binding" x (List.assoc x recvars) foundrecbinding
	  with Not_found -> check_bound x
	end
    | NtnInternTypeIdent -> check_bound x in
  List.iter check_type vars

let aconstr_of_glob_constr vars recvars a =
  let a,found = aconstr_and_vars_of_glob_constr a in
  check_variables vars recvars found;
  a

(* Substitution of kernel names, avoiding a list of bound identifiers *)

let aconstr_of_constr avoiding t =
 aconstr_of_glob_constr [] [] (Detyping.detype false avoiding [] t)

let rec subst_pat subst pat =
  match pat with
  | PatVar _ -> pat
  | PatCstr (loc,((kn,i),j),cpl,n) ->
      let kn' = subst_ind subst kn
      and cpl' = list_smartmap (subst_pat subst) cpl in
        if kn' == kn && cpl' == cpl then pat else
          PatCstr (loc,((kn',i),j),cpl',n)

let rec subst_aconstr subst bound raw =
  match raw with
  | ARef ref ->
      let ref',t = subst_global subst ref in
	if ref' == ref then raw else
	  aconstr_of_constr bound t

  | AVar _ -> raw

  | AApp (r,rl) ->
      let r' = subst_aconstr subst bound r
      and rl' = list_smartmap (subst_aconstr subst bound) rl in
	if r' == r && rl' == rl then raw else
	  AApp(r',rl')

  | AList (id1,id2,r1,r2,b) ->
      let r1' = subst_aconstr subst bound r1
      and r2' = subst_aconstr subst bound r2 in
	if r1' == r1 && r2' == r2 then raw else
	  AList (id1,id2,r1',r2',b)

  | ALambda (n,r1,r2) ->
      let r1' = subst_aconstr subst bound r1
      and r2' = subst_aconstr subst bound r2 in
	if r1' == r1 && r2' == r2 then raw else
	  ALambda (n,r1',r2')

  | AProd (n,r1,r2) ->
      let r1' = subst_aconstr subst bound r1
      and r2' = subst_aconstr subst bound r2 in
	if r1' == r1 && r2' == r2 then raw else
	  AProd (n,r1',r2')

  | ABinderList (id1,id2,r1,r2) ->
      let r1' = subst_aconstr subst bound r1
      and r2' = subst_aconstr subst bound r2 in
	if r1' == r1 && r2' == r2 then raw else
	  ABinderList (id1,id2,r1',r2')

  | ALetIn (n,r1,r2) ->
      let r1' = subst_aconstr subst bound r1
      and r2' = subst_aconstr subst bound r2 in
	if r1' == r1 && r2' == r2 then raw else
	  ALetIn (n,r1',r2')

  | ACases (sty,rtntypopt,rl,branches) ->
      let rtntypopt' = Option.smartmap (subst_aconstr subst bound) rtntypopt
      and rl' = list_smartmap
        (fun (a,(n,signopt) as x) ->
	  let a' = subst_aconstr subst bound a in
	  let signopt' = Option.map (fun ((indkn,i),n,nal as z) ->
	    let indkn' = subst_ind subst indkn in
	    if indkn == indkn' then z else ((indkn',i),n,nal)) signopt in
	  if a' == a && signopt' == signopt then x else (a',(n,signopt')))
        rl
      and branches' = list_smartmap
                        (fun (cpl,r as branch) ->
                           let cpl' = list_smartmap (subst_pat subst) cpl
                           and r' = subst_aconstr subst bound r in
                             if cpl' == cpl && r' == r then branch else
                               (cpl',r'))
                        branches
      in
        if rtntypopt' == rtntypopt && rtntypopt == rtntypopt' &
          rl' == rl && branches' == branches then raw else
          ACases (sty,rtntypopt',rl',branches')

  | ALetTuple (nal,(na,po),b,c) ->
      let po' = Option.smartmap (subst_aconstr subst bound) po
      and b' = subst_aconstr subst bound b
      and c' = subst_aconstr subst bound c in
	if po' == po && b' == b && c' == c then raw else
	  ALetTuple (nal,(na,po'),b',c')

  | AIf (c,(na,po),b1,b2) ->
      let po' = Option.smartmap (subst_aconstr subst bound) po
      and b1' = subst_aconstr subst bound b1
      and b2' = subst_aconstr subst bound b2
      and c' = subst_aconstr subst bound c in
	if po' == po && b1' == b1 && b2' == b2 && c' == c then raw else
	  AIf (c',(na,po'),b1',b2')

  | ARec (fk,idl,dll,tl,bl) ->
      let dll' =
	array_smartmap (list_smartmap (fun (na,oc,b as x) ->
	  let oc' =  Option.smartmap (subst_aconstr subst bound) oc in
	  let b' =  subst_aconstr subst bound b in
	  if oc' == oc && b' == b then x else (na,oc',b'))) dll in
      let tl' = array_smartmap (subst_aconstr subst bound) tl in
      let bl' = array_smartmap (subst_aconstr subst bound) bl in
      if dll' == dll && tl' == tl && bl' == bl then raw else
	  ARec (fk,idl,dll',tl',bl')

  | APatVar _ | ASort _ -> raw

  | AHole (Evd.ImplicitArg (ref,i,b)) ->
      let ref',t = subst_global subst ref in
	if ref' == ref then raw else
	  AHole (Evd.InternalHole)
  | AHole (Evd.BinderType _ | Evd.QuestionMark _ | Evd.CasesType
    | Evd.InternalHole | Evd.TomatchTypeParameter _ | Evd.GoalEvar
    | Evd.ImpossibleCase | Evd.MatchingVar _) -> raw

  | ACast (r1,k) ->
      match k with
	  CastConv (k, r2) ->
	    let r1' = subst_aconstr subst bound r1
	    and r2' = subst_aconstr subst bound r2 in
	      if r1' == r1 && r2' == r2 then raw else
		ACast (r1',CastConv (k,r2'))
	| CastCoerce ->
	    let r1' = subst_aconstr subst bound r1 in
	      if r1' == r1 then raw else
		ACast (r1',CastCoerce)

let subst_interpretation subst (metas,pat) =
  let bound = List.map fst metas in
  (metas,subst_aconstr subst bound pat)

(* Pattern-matching glob_constr and aconstr *)

let abstract_return_type_context pi mklam tml rtno =
  Option.map (fun rtn ->
    let nal =
      List.flatten (List.map (fun (_,(na,t)) ->
	match t with Some x -> (pi x)@[na] | None -> [na]) tml) in
    List.fold_right mklam nal rtn)
    rtno

let abstract_return_type_context_glob_constr =
  abstract_return_type_context (fun (_,_,_,nal) -> nal)
    (fun na c -> GLambda(dummy_loc,na,Explicit,GHole(dummy_loc,Evd.InternalHole),c))

let abstract_return_type_context_aconstr =
  abstract_return_type_context pi3
    (fun na c -> ALambda(na,AHole Evd.InternalHole,c))

exception No_match

let rec alpha_var id1 id2 = function
  | (i1,i2)::_ when i1=id1 -> i2 = id2
  | (i1,i2)::_ when i2=id2 -> i1 = id1
  | _::idl -> alpha_var id1 id2 idl
  | [] -> id1 = id2

let alpha_eq_val (x,y) = x = y

let bind_env alp (sigma,sigmalist,sigmabinders as fullsigma) var v =
  try
    let vvar = List.assoc var sigma in
    if alpha_eq_val (v,vvar) then fullsigma
    else raise No_match
  with Not_found ->
    (* Check that no capture of binding variables occur *)
    if List.exists (fun (id,_) ->occur_glob_constr id v) alp then raise No_match;
    (* TODO: handle the case of multiple occs in different scopes *)
    ((var,v)::sigma,sigmalist,sigmabinders)

let bind_binder (sigma,sigmalist,sigmabinders) x bl =
  (sigma,sigmalist,(x,List.rev bl)::sigmabinders)

let match_fix_kind fk1 fk2 =
  match (fk1,fk2) with
  | RCoFix n1, RCoFix n2 -> n1 = n2
  | RFix (nl1,n1), RFix (nl2,n2) ->
      n1 = n2 &&
      array_for_all2 (fun (n1,_) (n2,_) -> n2 = None || n1 = n2) nl1 nl2
  | _ -> false

let match_opt f sigma t1 t2 = match (t1,t2) with
  | None, None -> sigma
  | Some t1, Some t2 -> f sigma t1 t2
  | _ -> raise No_match

let match_names metas (alp,sigma) na1 na2 = match (na1,na2) with
  | (Name id1,Name id2) when List.mem id2 (fst metas) ->
      alp, bind_env alp sigma id2 (GVar (dummy_loc,id1))
  | (Name id1,Name id2) -> (id1,id2)::alp,sigma
  | (Anonymous,Anonymous) -> alp,sigma
  | _ -> raise No_match

let rec match_cases_pattern_binders metas acc pat1 pat2 =
  match (pat1,pat2) with
  | PatVar (_,na1), PatVar (_,na2) -> match_names metas acc na1 na2
  | PatCstr (_,c1,patl1,na1), PatCstr (_,c2,patl2,na2)
      when c1 = c2 & List.length patl1 = List.length patl2 ->
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
	((na,Explicit (*?*), Some c,GHole(loc,Evd.BinderType na))::decls) b
  | b -> (decls,b)

let remove_sigma x (sigmavar,sigmalist,sigmabinders) =
  (List.remove_assoc x sigmavar,sigmalist,sigmabinders)

let rec match_abinderlist_with_app match_fun metas sigma rest x iter termin =
  let rec aux sigma acc rest =
    try
      let sigma = match_fun (ldots_var::fst metas,snd metas) sigma rest iter in
      let rest = List.assoc ldots_var (pi1 sigma) in
      let b = match List.assoc x (pi3 sigma) with [b] -> b | _ ->assert false in
      let sigma = remove_sigma x (remove_sigma ldots_var sigma) in
      aux sigma (b::acc) rest
    with No_match when acc <> [] ->
      acc, match_fun metas sigma rest termin in
  let bl,sigma = aux sigma [] rest in
  bind_binder sigma x bl

let match_alist match_fun metas sigma rest x iter termin lassoc =
  let rec aux sigma acc rest =
    try
      let sigma = match_fun (ldots_var::fst metas,snd metas) sigma rest iter in
      let rest = List.assoc ldots_var (pi1 sigma) in
      let t = List.assoc x (pi1 sigma) in
      let sigma = remove_sigma x (remove_sigma ldots_var sigma) in
      aux sigma (t::acc) rest
    with No_match when acc <> [] ->
      acc, match_fun metas sigma rest termin in
  let l,sigma = aux sigma [] rest in
  (pi1 sigma, (x,if lassoc then l else List.rev l)::pi2 sigma, pi3 sigma)

let rec match_ alp (tmetas,blmetas as metas) sigma a1 a2 = match (a1,a2) with

  (* Matching notation variable *)
  | r1, AVar id2 when List.mem id2 tmetas -> bind_env alp sigma id2 r1

  (* Matching recursive notations for terms *)
  | r1, AList (x,_,iter,termin,lassoc) ->
      match_alist (match_ alp) metas sigma r1 x iter termin lassoc

  (* Matching recursive notations for binders: ad hoc cases supporting let-in *)
  | GLambda (_,na1,bk,t1,b1), ABinderList (x,_,ALambda (Name id2,_,b2),termin)->
      let (decls,b) = match_iterated_binders true [(na1,bk,None,t1)] b1 in
      (* TODO: address the possibility that termin is a Lambda itself *)
      match_ alp metas (bind_binder sigma x decls) b termin
  | GProd (_,na1,bk,t1,b1), ABinderList (x,_,AProd (Name id2,_,b2),termin)
      when na1 <> Anonymous ->
      let (decls,b) = match_iterated_binders false [(na1,bk,None,t1)] b1 in
      (* TODO: address the possibility that termin is a Prod itself *)
      match_ alp metas (bind_binder sigma x decls) b termin
  (* Matching recursive notations for binders: general case *)
  | r, ABinderList (x,_,iter,termin) ->
      match_abinderlist_with_app (match_ alp) metas sigma r x iter termin

  (* Matching individual binders as part of a recursive pattern *)
  | GLambda (_,na,bk,t,b1), ALambda (Name id,_,b2) when List.mem id blmetas ->
      match_ alp metas (bind_binder sigma id [(na,bk,None,t)]) b1 b2
  | GProd (_,na,bk,t,b1), AProd (Name id,_,b2)
      when List.mem id blmetas & na <> Anonymous ->
      match_ alp metas (bind_binder sigma id [(na,bk,None,t)]) b1 b2

  (* Matching compositionally *)
  | GVar (_,id1), AVar id2 when alpha_var id1 id2 alp -> sigma
  | GRef (_,r1), ARef r2 when (eq_gr r1 r2) -> sigma
  | GPatVar (_,(_,n1)), APatVar n2 when n1=n2 -> sigma
  | GApp (loc,f1,l1), AApp (f2,l2) ->
      let n1 = List.length l1 and n2 = List.length l2 in
      let f1,l1,f2,l2 =
	if n1 < n2 then
	  let l21,l22 = list_chop (n2-n1) l2 in f1,l1, AApp (f2,l21), l22
	else if n1 > n2 then
	  let l11,l12 = list_chop (n1-n2) l1 in GApp (loc,f1,l11),l12, f2,l2
	else f1,l1, f2, l2 in
      List.fold_left2 (match_ alp metas) (match_ alp metas sigma f1 f2) l1 l2
  | GLambda (_,na1,_,t1,b1), ALambda (na2,t2,b2) ->
     match_binders alp metas na1 na2 (match_ alp metas sigma t1 t2) b1 b2
  | GProd (_,na1,_,t1,b1), AProd (na2,t2,b2) ->
     match_binders alp metas na1 na2 (match_ alp metas sigma t1 t2) b1 b2
  | GLetIn (_,na1,t1,b1), ALetIn (na2,t2,b2) ->
     match_binders alp metas na1 na2 (match_ alp metas sigma t1 t2) b1 b2
  | GCases (_,sty1,rtno1,tml1,eqnl1), ACases (sty2,rtno2,tml2,eqnl2)
      when sty1 = sty2
	 & List.length tml1 = List.length tml2
	 & List.length eqnl1 = List.length eqnl2 ->
      let rtno1' = abstract_return_type_context_glob_constr tml1 rtno1 in
      let rtno2' = abstract_return_type_context_aconstr tml2 rtno2 in
      let sigma =
	try Option.fold_left2 (match_ alp metas) sigma rtno1' rtno2'
	with Option.Heterogeneous -> raise No_match
      in
      let sigma = List.fold_left2
      (fun s (tm1,_) (tm2,_) -> match_ alp metas s tm1 tm2) sigma tml1 tml2 in
      List.fold_left2 (match_equations alp metas) sigma eqnl1 eqnl2
  | GLetTuple (_,nal1,(na1,to1),b1,c1), ALetTuple (nal2,(na2,to2),b2,c2)
      when List.length nal1 = List.length nal2 ->
      let sigma = match_opt (match_binders alp metas na1 na2) sigma to1 to2 in
      let sigma = match_ alp metas sigma b1 b2 in
      let (alp,sigma) =
	List.fold_left2 (match_names metas) (alp,sigma) nal1 nal2 in
      match_ alp metas sigma c1 c2
  | GIf (_,a1,(na1,to1),b1,c1), AIf (a2,(na2,to2),b2,c2) ->
      let sigma = match_opt (match_binders alp metas na1 na2) sigma to1 to2 in
      List.fold_left2 (match_ alp metas) sigma [a1;b1;c1] [a2;b2;c2]
  | GRec (_,fk1,idl1,dll1,tl1,bl1), ARec (fk2,idl2,dll2,tl2,bl2)
      when match_fix_kind fk1 fk2 & Array.length idl1 =  Array.length idl2 &
	array_for_all2 (fun l1 l2 -> List.length l1 = List.length l2) dll1 dll2
	->
      let alp,sigma = array_fold_left2
	(List.fold_left2 (fun (alp,sigma) (na1,_,oc1,b1) (na2,oc2,b2) ->
	  let sigma =
	    match_ alp metas (match_opt (match_ alp metas) sigma oc1 oc2) b1 b2
	  in match_names metas (alp,sigma) na1 na2)) (alp,sigma) dll1 dll2 in
      let sigma = array_fold_left2 (match_ alp metas) sigma tl1 tl2 in
      let alp,sigma = array_fold_right2 (fun id1 id2 alsig ->
	match_names metas alsig (Name id1) (Name id2)) idl1 idl2 (alp,sigma) in
      array_fold_left2 (match_ alp metas) sigma bl1 bl2
  | GCast(_,c1, CastConv(_,t1)), ACast(c2, CastConv (_,t2)) ->
      match_ alp metas (match_ alp metas sigma c1 c2) t1 t2
  | GCast(_,c1, CastCoerce), ACast(c2, CastCoerce) ->
      match_ alp metas sigma c1 c2
  | GSort (_,s1), ASort s2 when s1 = s2 -> sigma
  | GPatVar _, AHole _ -> (*Don't hide Metas, they bind in ltac*) raise No_match
  | a, AHole _ -> sigma
  | (GDynamic _ | GRec _ | GEvar _), _
  | _,_ -> raise No_match

and match_binders alp metas na1 na2 sigma b1 b2 =
  let (alp,sigma) = match_names metas (alp,sigma) na1 na2 in
  match_ alp metas sigma b1 b2

and match_equations alp metas sigma (_,_,patl1,rhs1) (patl2,rhs2) =
  (* patl1 and patl2 have the same length because they respectively
     correspond to some tml1 and tml2 that have the same length *)
  let (alp,sigma) =
    List.fold_left2 (match_cases_pattern_binders metas)
      (alp,sigma) patl1 patl2 in
  match_ alp metas sigma rhs1 rhs2

let match_aconstr c (metas,pat) =
  let vars = list_split_by (fun (_,(_,x)) -> x <> NtnTypeBinderList) metas in
  let vars = (List.map fst (fst vars), List.map fst (snd vars)) in
  let terms,termlists,binders = match_ [] vars ([],[],[]) c pat in
  (* Reorder canonically the substitution *)
  let find x =
    try List.assoc x terms
    with Not_found ->
      (* Happens for binders bound to Anonymous *)
      (* Find a better way to propagate Anonymous... *)
      GVar (dummy_loc,x) in
  List.fold_right (fun (x,(scl,typ)) (terms',termlists',binders') ->
    match typ with
    | NtnTypeConstr ->
       ((find x, scl)::terms',termlists',binders')
    | NtnTypeConstrList ->
       (terms',(List.assoc x termlists,scl)::termlists',binders')
    | NtnTypeBinderList ->
       (terms',termlists',(List.assoc x binders,scl)::binders'))
    metas ([],[],[])

(* Matching cases pattern *)

let bind_env_cases_pattern (sigma,sigmalist,x as fullsigma) var v =
  try
    let vvar = List.assoc var sigma in
    if v=vvar then fullsigma else raise No_match
  with Not_found ->
    (* TODO: handle the case of multiple occs in different scopes *)
    (var,v)::sigma,sigmalist,x

let rec match_cases_pattern metas sigma a1 a2 = match (a1,a2) with
  | r1, AVar id2 when List.mem id2 metas -> bind_env_cases_pattern sigma id2 r1
  | PatVar (_,Anonymous), AHole _ -> sigma
  | PatCstr (loc,(ind,_ as r1),[],_), ARef (ConstructRef r2) when r1 = r2 ->
      sigma
  | PatCstr (loc,(ind,_ as r1),args1,_), AApp (ARef (ConstructRef r2),l2)
      when r1 = r2 ->
      let nparams = Inductive.inductive_params (Global.lookup_inductive ind) in
      if List.length l2 <> nparams + List.length args1
      then
	(* TODO: revert partially applied notations of the form
           "Notation P := (@pair)." *)
	raise No_match
      else
        let (p2,args2) = list_chop nparams l2 in
        (* All parameters must be _ *)
        List.iter (function AHole _ -> () | _ -> raise No_match) p2;
	List.fold_left2 (match_cases_pattern metas) sigma args1 args2
  | r1, AList (x,_,iter,termin,lassoc) ->
      match_alist (fun (metas,_) -> match_cases_pattern metas)
	(metas,[]) (pi1 sigma,pi2 sigma,()) r1 x iter termin lassoc
  | _ -> raise No_match

let match_aconstr_cases_pattern c (metas,pat) =
  let vars = List.map fst metas in
  let terms,termlists,() = match_cases_pattern vars ([],[],()) c pat in
  (* Reorder canonically the substitution *)
  List.fold_right (fun (x,(scl,typ)) (terms',termlists') ->
    match typ with
    | NtnTypeConstr -> ((List.assoc x terms, scl)::terms',termlists')
    | NtnTypeConstrList -> (terms',(List.assoc x termlists,scl)::termlists')
    | NtnTypeBinderList -> assert false)
    metas ([],[])

(**********************************************************************)
(*s Concrete syntax for terms *)

type notation = string

type explicitation = ExplByPos of int * identifier option | ExplByName of identifier

type binder_kind = Default of binding_kind | Generalized of binding_kind * binding_kind * bool

type abstraction_kind = AbsLambda | AbsPi

type proj_flag = int option (* [Some n] = proj of the n-th visible argument *)

type prim_token = Numeral of Bigint.bigint | String of string

type cases_pattern_expr =
  | CPatAlias of loc * cases_pattern_expr * identifier
  | CPatCstr of loc * reference * cases_pattern_expr list
  | CPatAtom of loc * reference option
  | CPatOr of loc * cases_pattern_expr list
  | CPatNotation of loc * notation * cases_pattern_notation_substitution
  | CPatPrim of loc * prim_token
  | CPatRecord of Util.loc * (reference * cases_pattern_expr) list
  | CPatDelimiters of loc * string * cases_pattern_expr

and cases_pattern_notation_substitution =
    cases_pattern_expr list *     (** for constr subterms *)
    cases_pattern_expr list list  (** for recursive notations *)

type constr_expr =
  | CRef of reference
  | CFix of loc * identifier located * fix_expr list
  | CCoFix of loc * identifier located * cofix_expr list
  | CArrow of loc * constr_expr * constr_expr
  | CProdN of loc * (name located list * binder_kind * constr_expr) list * constr_expr
  | CLambdaN of loc * (name located list * binder_kind * constr_expr) list * constr_expr
  | CLetIn of loc * name located * constr_expr * constr_expr
  | CAppExpl of loc * (proj_flag * reference) * constr_expr list
  | CApp of loc * (proj_flag * constr_expr) *
      (constr_expr * explicitation located option) list
  | CRecord of loc * constr_expr option * (reference * constr_expr) list
  | CCases of loc * case_style * constr_expr option *
      (constr_expr * (name located option * constr_expr option)) list *
      (loc * cases_pattern_expr list located list * constr_expr) list
  | CLetTuple of loc * name located list * (name located option * constr_expr option) *
      constr_expr * constr_expr
  | CIf of loc * constr_expr * (name located option * constr_expr option)
      * constr_expr * constr_expr
  | CHole of loc * Evd.hole_kind option
  | CPatVar of loc * (bool * patvar)
  | CEvar of loc * existential_key * constr_expr list option
  | CSort of loc * rawsort
  | CCast of loc * constr_expr * constr_expr cast_type
  | CNotation of loc * notation * constr_notation_substitution
  | CGeneralization of loc * binding_kind * abstraction_kind option * constr_expr
  | CPrim of loc * prim_token
  | CDelimiters of loc * string * constr_expr
  | CDynamic of loc * Dyn.t

and fix_expr =
    identifier located * (identifier located option * recursion_order_expr) * local_binder list * constr_expr * constr_expr

and cofix_expr =
    identifier located * local_binder list * constr_expr * constr_expr

and recursion_order_expr =
  | CStructRec
  | CWfRec of constr_expr
  | CMeasureRec of constr_expr * constr_expr option (* measure, relation *)

and local_binder =
  | LocalRawDef of name located * constr_expr
  | LocalRawAssum of name located list * binder_kind * constr_expr

and constr_notation_substitution =
    constr_expr list *      (* for constr subterms *)
    constr_expr list list * (* for recursive notations *)
    local_binder list list      (* for binders subexpressions *)

type typeclass_constraint = name located * binding_kind * constr_expr

and typeclass_context = typeclass_constraint list

type constr_pattern_expr = constr_expr

(***********************)
(* For binders parsing *)

let default_binder_kind = Default Explicit

let names_of_local_assums bl =
  List.flatten (List.map (function LocalRawAssum(l,_,_)->l|_->[]) bl)

let names_of_local_binders bl =
  List.flatten (List.map (function LocalRawAssum(l,_,_)->l|LocalRawDef(l,_)->[l]) bl)

(**********************************************************************)
(* Functions on constr_expr *)

let constr_loc = function
  | CRef (Ident (loc,_)) -> loc
  | CRef (Qualid (loc,_)) -> loc
  | CFix (loc,_,_) -> loc
  | CCoFix (loc,_,_) -> loc
  | CArrow (loc,_,_) -> loc
  | CProdN (loc,_,_) -> loc
  | CLambdaN (loc,_,_) -> loc
  | CLetIn (loc,_,_,_) -> loc
  | CAppExpl (loc,_,_) -> loc
  | CApp (loc,_,_) -> loc
  | CRecord (loc,_,_) -> loc
  | CCases (loc,_,_,_,_) -> loc
  | CLetTuple (loc,_,_,_,_) -> loc
  | CIf (loc,_,_,_,_) -> loc
  | CHole (loc, _) -> loc
  | CPatVar (loc,_) -> loc
  | CEvar (loc,_,_) -> loc
  | CSort (loc,_) -> loc
  | CCast (loc,_,_) -> loc
  | CNotation (loc,_,_) -> loc
  | CGeneralization (loc,_,_,_) -> loc
  | CPrim (loc,_) -> loc
  | CDelimiters (loc,_,_) -> loc
  | CDynamic _ -> dummy_loc

let cases_pattern_expr_loc = function
  | CPatAlias (loc,_,_) -> loc
  | CPatCstr (loc,_,_) -> loc
  | CPatAtom (loc,_) -> loc
  | CPatOr (loc,_) -> loc
  | CPatNotation (loc,_,_) -> loc
  | CPatRecord (loc, _) -> loc
  | CPatPrim (loc,_) -> loc
  | CPatDelimiters (loc,_,_) -> loc

let local_binder_loc = function
  | LocalRawAssum ((loc,_)::_,_,t)
  | LocalRawDef ((loc,_),t) -> join_loc loc (constr_loc t)
  | LocalRawAssum ([],_,_) -> assert false

let local_binders_loc bll =
  if bll = [] then dummy_loc else
  join_loc (local_binder_loc (List.hd bll)) (local_binder_loc (list_last bll))

let ids_of_cases_indtype =
  let add_var ids = function CRef (Ident (_,id)) -> id::ids | _ -> ids in
  let rec vars_of = function
    (* We deal only with the regular cases *)
    | CApp (_,_,l) -> List.fold_left add_var [] (List.map fst l)
    | CNotation (_,_,(l,[],[]))
    (* assume the ntn is applicative and does not instantiate the head !! *)
    | CAppExpl (_,_,l) -> List.fold_left add_var [] l
    | CDelimiters(_,_,c) -> vars_of c
    | _ -> [] in
  vars_of

let ids_of_cases_tomatch tms =
  List.fold_right
    (fun (_,(ona,indnal)) l ->
      Option.fold_right (fun t -> (@) (ids_of_cases_indtype t))
      indnal (Option.fold_right (down_located name_cons) ona l))
    tms []

let is_constructor id =
  try ignore (Nametab.locate_extended (qualid_of_ident id)); true
  with Not_found -> true

let rec cases_pattern_fold_names f a = function
  | CPatRecord (_, l) ->
      List.fold_left (fun acc (r, cp) -> cases_pattern_fold_names f acc cp) a l
  | CPatAlias (_,pat,id) -> f id a
  | CPatCstr (_,_,patl) | CPatOr (_,patl) ->
      List.fold_left (cases_pattern_fold_names f) a patl
  | CPatNotation (_,_,(patl,patll)) ->
      List.fold_left (cases_pattern_fold_names f) a (patl@List.flatten patll)
  | CPatDelimiters (_,_,pat) -> cases_pattern_fold_names f a pat
  | CPatAtom (_,Some (Ident (_,id))) when not (is_constructor id) -> f id a
  | CPatPrim _ | CPatAtom _ -> a

let ids_of_pattern_list =
  List.fold_left
    (located_fold_left
      (List.fold_left (cases_pattern_fold_names Idset.add)))
    Idset.empty

let rec fold_constr_expr_binders g f n acc b = function
  | (nal,bk,t)::l ->
      let nal = snd (List.split nal) in
      let n' = List.fold_right (name_fold g) nal n in
      f n (fold_constr_expr_binders g f n' acc b l) t
  | [] ->
      f n acc b

let rec fold_local_binders g f n acc b = function
  | LocalRawAssum (nal,bk,t)::l ->
      let nal = snd (List.split nal) in
      let n' = List.fold_right (name_fold g) nal n in
      f n (fold_local_binders g f n' acc b l) t
  | LocalRawDef ((_,na),t)::l ->
      f n (fold_local_binders g f (name_fold g na n) acc b l) t
  | [] ->
      f n acc b

let fold_constr_expr_with_binders g f n acc = function
  | CArrow (loc,a,b) -> f n (f n acc a) b
  | CAppExpl (loc,(_,_),l) -> List.fold_left (f n) acc l
  | CApp (loc,(_,t),l) -> List.fold_left (f n) (f n acc t) (List.map fst l)
  | CProdN (_,l,b) | CLambdaN (_,l,b) -> fold_constr_expr_binders g f n acc b l
  | CLetIn (_,na,a,b) -> fold_constr_expr_binders g f n acc b [[na],default_binder_kind,a]
  | CCast (loc,a,CastConv(_,b)) -> f n (f n acc a) b
  | CCast (loc,a,CastCoerce) -> f n acc a
  | CNotation (_,_,(l,ll,bll)) ->
      (* The following is an approximation: we don't know exactly if
         an ident is binding nor to which subterms bindings apply *)
      let acc = List.fold_left (f n) acc (l@List.flatten ll) in
      List.fold_left (fun acc bl -> fold_local_binders g f n acc (CHole (dummy_loc,None)) bl) acc bll
  | CGeneralization (_,_,_,c) -> f n acc c
  | CDelimiters (loc,_,a) -> f n acc a
  | CHole _ | CEvar _ | CPatVar _ | CSort _ | CPrim _ | CDynamic _  | CRef _ ->
      acc
  | CRecord (loc,_,l) -> List.fold_left (fun acc (id, c) -> f n acc c) acc l
  | CCases (loc,sty,rtnpo,al,bl) ->
      let ids = ids_of_cases_tomatch al in
      let acc = Option.fold_left (f (List.fold_right g ids n)) acc rtnpo in
      let acc = List.fold_left (f n) acc (List.map fst al) in
      List.fold_right (fun (loc,patl,rhs) acc ->
	let ids = ids_of_pattern_list patl in
	f (Idset.fold g ids n) acc rhs) bl acc
  | CLetTuple (loc,nal,(ona,po),b,c) ->
      let n' = List.fold_right (down_located (name_fold g)) nal n in
      f (Option.fold_right (down_located (name_fold g)) ona n') (f n acc b) c
  | CIf (_,c,(ona,po),b1,b2) ->
      let acc = f n (f n (f n acc b1) b2) c in
      Option.fold_left
	(f (Option.fold_right (down_located (name_fold g)) ona n)) acc po
  | CFix (loc,_,l) ->
      let n' = List.fold_right (fun ((_,id),_,_,_,_) -> g id) l n in
      List.fold_right (fun (_,(_,o),lb,t,c) acc ->
	fold_local_binders g f n'
	  (fold_local_binders g f n acc t lb) c lb) l acc
  | CCoFix (loc,_,_) ->
      Pp.warning "Capture check in multiple binders not done"; acc

let free_vars_of_constr_expr c =
  let rec aux bdvars l = function
  | CRef (Ident (_,id)) -> if List.mem id bdvars then l else Idset.add id l
  | c -> fold_constr_expr_with_binders (fun a l -> a::l) aux bdvars l c
  in aux [] Idset.empty c

let occur_var_constr_expr id c = Idset.mem id (free_vars_of_constr_expr c)

let mkIdentC id  = CRef (Ident (dummy_loc, id))
let mkRefC r     = CRef r
let mkCastC (a,k)  = CCast (dummy_loc,a,k)
let mkLambdaC (idl,bk,a,b) = CLambdaN (dummy_loc,[idl,bk,a],b)
let mkLetInC (id,a,b)   = CLetIn (dummy_loc,id,a,b)
let mkProdC (idl,bk,a,b)   = CProdN (dummy_loc,[idl,bk,a],b)

let mkAppC (f,l) =
  let l = List.map (fun x -> (x,None)) l in
  match f with
  | CApp (_,g,l') -> CApp (dummy_loc, g, l' @ l)
  | _ -> CApp (dummy_loc, (None, f), l)

let rec mkCProdN loc bll c =
  match bll with
  | LocalRawAssum ((loc1,_)::_ as idl,bk,t) :: bll ->
      CProdN (loc,[idl,bk,t],mkCProdN (join_loc loc1 loc) bll c)
  | LocalRawDef ((loc1,_) as id,b) :: bll ->
      CLetIn (loc,id,b,mkCProdN (join_loc loc1 loc) bll c)
  | [] -> c
  | LocalRawAssum ([],_,_) :: bll -> mkCProdN loc bll c

let rec mkCLambdaN loc bll c =
  match bll with
  | LocalRawAssum ((loc1,_)::_ as idl,bk,t) :: bll ->
      CLambdaN (loc,[idl,bk,t],mkCLambdaN (join_loc loc1 loc) bll c)
  | LocalRawDef ((loc1,_) as id,b) :: bll ->
      CLetIn (loc,id,b,mkCLambdaN (join_loc loc1 loc) bll c)
  | [] -> c
  | LocalRawAssum ([],_,_) :: bll -> mkCLambdaN loc bll c

let rec abstract_constr_expr c = function
  | [] -> c
  | LocalRawDef (x,b)::bl -> mkLetInC(x,b,abstract_constr_expr c bl)
  | LocalRawAssum (idl,bk,t)::bl ->
      List.fold_right (fun x b -> mkLambdaC([x],bk,t,b)) idl
      (abstract_constr_expr c bl)

let rec prod_constr_expr c = function
  | [] -> c
  | LocalRawDef (x,b)::bl -> mkLetInC(x,b,prod_constr_expr c bl)
  | LocalRawAssum (idl,bk,t)::bl ->
      List.fold_right (fun x b -> mkProdC([x],bk,t,b)) idl
      (prod_constr_expr c bl)

let coerce_reference_to_id = function
  | Ident (_,id) -> id
  | Qualid (loc,_) ->
      user_err_loc (loc, "coerce_reference_to_id",
        str "This expression should be a simple identifier.")

let coerce_to_id = function
  | CRef (Ident (loc,id)) -> (loc,id)
  | a -> user_err_loc
        (constr_loc a,"coerce_to_id",
         str "This expression should be a simple identifier.")

let coerce_to_name = function
  | CRef (Ident (loc,id)) -> (loc,Name id)
  | CHole (loc,_) -> (loc,Anonymous)
  | a -> user_err_loc
        (constr_loc a,"coerce_to_name",
         str "This expression should be a name.")

(* Interpret the index of a recursion order annotation *)

let split_at_annot bl na =
  let names = List.map snd (names_of_local_assums bl) in
  match na with
  | None ->
      if names = [] then error "A fixpoint needs at least one parameter."
      else [], bl
  | Some (loc, id) ->
      let rec aux acc = function
	| LocalRawAssum (bls, k, t) as x :: rest ->
	    let l, r = list_split_when (fun (loc, na) -> na = Name id) bls in
	      if r = [] then aux (x :: acc) rest
	      else
		(List.rev (if l = [] then acc else LocalRawAssum (l, k, t) :: acc),
		 LocalRawAssum (r, k, t) :: rest)
	| LocalRawDef _ as x :: rest -> aux (x :: acc) rest
	| [] ->
            user_err_loc(loc,"",
			 str "No parameter named " ++ Nameops.pr_id id ++ str".")
      in aux [] bl

(* Used in correctness and interface *)

let map_binder g e nal = List.fold_right (down_located (name_fold g)) nal e

let map_binders f g e bl =
  (* TODO: avoid variable capture in [t] by some [na] in [List.tl nal] *)
  let h (e,bl) (nal,bk,t) = (map_binder g e nal,(nal,bk,f e t)::bl) in
  let (e,rbl) = List.fold_left h (e,[]) bl in
  (e, List.rev rbl)

let map_local_binders f g e bl =
  (* TODO: avoid variable capture in [t] by some [na] in [List.tl nal] *)
  let h (e,bl) = function
      LocalRawAssum(nal,k,ty) ->
        (map_binder g e nal, LocalRawAssum(nal,k,f e ty)::bl)
    | LocalRawDef((loc,na),ty) ->
        (name_fold g na e, LocalRawDef((loc,na),f e ty)::bl) in
  let (e,rbl) = List.fold_left h (e,[]) bl in
  (e, List.rev rbl)

let map_constr_expr_with_binders g f e = function
  | CArrow (loc,a,b) -> CArrow (loc,f e a,f e b)
  | CAppExpl (loc,r,l) -> CAppExpl (loc,r,List.map (f e) l)
  | CApp (loc,(p,a),l) ->
      CApp (loc,(p,f e a),List.map (fun (a,i) -> (f e a,i)) l)
  | CProdN (loc,bl,b) ->
      let (e,bl) = map_binders f g e bl in CProdN (loc,bl,f e b)
  | CLambdaN (loc,bl,b) ->
      let (e,bl) = map_binders f g e bl in CLambdaN (loc,bl,f e b)
  | CLetIn (loc,na,a,b) -> CLetIn (loc,na,f e a,f (name_fold g (snd na) e) b)
  | CCast (loc,a,CastConv (k,b)) -> CCast (loc,f e a,CastConv(k, f e b))
  | CCast (loc,a,CastCoerce) -> CCast (loc,f e a,CastCoerce)
  | CNotation (loc,n,(l,ll,bll)) ->
      (* This is an approximation because we don't know what binds what *)
      CNotation (loc,n,(List.map (f e) l,List.map (List.map (f e)) ll,
                     List.map (fun bl -> snd (map_local_binders f g e bl)) bll))
  | CGeneralization (loc,b,a,c) -> CGeneralization (loc,b,a,f e c)
  | CDelimiters (loc,s,a) -> CDelimiters (loc,s,f e a)
  | CHole _ | CEvar _ | CPatVar _ | CSort _
  | CPrim _ | CDynamic _ | CRef _ as x -> x
  | CRecord (loc,p,l) -> CRecord (loc,p,List.map (fun (id, c) -> (id, f e c)) l)
  | CCases (loc,sty,rtnpo,a,bl) ->
      (* TODO: apply g on the binding variables in pat... *)
      let bl = List.map (fun (loc,pat,rhs) -> (loc,pat,f e rhs)) bl in
      let ids = ids_of_cases_tomatch a in
      let po = Option.map (f (List.fold_right g ids e)) rtnpo in
      CCases (loc, sty, po, List.map (fun (tm,x) -> (f e tm,x)) a,bl)
  | CLetTuple (loc,nal,(ona,po),b,c) ->
      let e' = List.fold_right (down_located (name_fold g)) nal e in
      let e'' = Option.fold_right (down_located (name_fold g)) ona e in
      CLetTuple (loc,nal,(ona,Option.map (f e'') po),f e b,f e' c)
  | CIf (loc,c,(ona,po),b1,b2) ->
      let e' = Option.fold_right (down_located (name_fold g)) ona e in
      CIf (loc,f e c,(ona,Option.map (f e') po),f e b1,f e b2)
  | CFix (loc,id,dl) ->
      CFix (loc,id,List.map (fun (id,n,bl,t,d) ->
        let (e',bl') = map_local_binders f g e bl in
        let t' = f e' t in
        (* Note: fix names should be inserted before the arguments... *)
        let e'' = List.fold_left (fun e ((_,id),_,_,_,_) -> g id e) e' dl in
        let d' = f e'' d in
        (id,n,bl',t',d')) dl)
  | CCoFix (loc,id,dl) ->
      CCoFix (loc,id,List.map (fun (id,bl,t,d) ->
        let (e',bl') = map_local_binders f g e bl in
        let t' = f e' t in
        let e'' = List.fold_left (fun e ((_,id),_,_,_) -> g id e) e' dl in
        let d' = f e'' d in
        (id,bl',t',d')) dl)

(* Used in constrintern *)
let rec replace_vars_constr_expr l = function
  | CRef (Ident (loc,id)) as x ->
      (try CRef (Ident (loc,List.assoc id l)) with Not_found -> x)
  | c -> map_constr_expr_with_binders List.remove_assoc
           replace_vars_constr_expr l c

(**********************************************************************)
(* Concrete syntax for modules and modules types *)

type with_declaration_ast =
  | CWith_Module of identifier list located * qualid located
  | CWith_Definition of identifier list located * constr_expr

type module_ast =
  | CMident of qualid located
  | CMapply of module_ast * module_ast
  | CMwith of module_ast * with_declaration_ast

type module_ast_inl = module_ast * bool (* honor the inline annotations or not *)

type 'a module_signature =
  | Enforce of 'a (* ... : T *)
  | Check of 'a list (* ... <: T1 <: T2, possibly empty *)

(* Returns the ranges of locs of the notation that are not occupied by args  *)
(* and which are then occupied by proper symbols of the notation (or spaces) *)

let locs_of_notation loc locs ntn =
  let (bl,el) = Util.unloc loc in
  let locs =  List.map Util.unloc locs in
  let rec aux pos = function
    | [] -> if pos = el then [] else [(pos,el-1)]
    | (ba,ea)::l ->if pos = ba then aux ea l else (pos,ba-1)::aux ea l
  in aux bl (Sort.list (fun l1 l2 -> fst l1 < fst l2) locs)

let ntn_loc loc (args,argslist,binderslist) =
  locs_of_notation loc
    (List.map constr_loc (args@List.flatten argslist)@
     List.map local_binders_loc binderslist)

let patntn_loc loc (args,argslist) =
  locs_of_notation loc
    (List.map cases_pattern_expr_loc (args@List.flatten argslist))
