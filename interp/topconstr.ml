(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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
(* This is the subtype of rawconstr allowed in syntactic extensions *)

(* For AList: first constr is iterator, second is terminator;
   first id is where each argument of the list has to be substituted
   in iterator and snd id is alternative name just for printing;
   boolean is associativity *)

type aconstr =
  (* Part common to rawconstr and cases_pattern *)
  | ARef of global_reference
  | AVar of identifier
  | AApp of aconstr * aconstr list
  | AList of identifier * identifier * aconstr * aconstr * bool
  (* Part only in rawconstr *)
  | ALambda of name * aconstr * aconstr
  | AProd of name * aconstr * aconstr
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

(**********************************************************************)
(* Re-interpret a notation as a rawconstr, taking care of binders     *)

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

let rec subst_rawvars l = function
  | RVar (_,id) as r -> (try List.assoc id l with Not_found -> r)
  | r -> map_rawconstr (subst_rawvars l) r (* assume: id is not binding *)

let ldots_var = id_of_string ".."

let rawconstr_of_aconstr_with_binders loc g f e = function
  | AVar id -> RVar (loc,id)
  | AApp (a,args) -> RApp (loc,f e a, List.map (f e) args)
  | AList (x,y,iter,tail,swap) ->
      let t = f e tail in let it = f e iter in
      let innerl = (ldots_var,t)::(if swap then [] else [x,RVar(loc,y)]) in
      let inner = RApp (loc,RVar (loc,ldots_var),[subst_rawvars innerl it]) in
      let outerl = (ldots_var,inner)::(if swap then [x,RVar(loc,y)] else []) in
      subst_rawvars outerl it
  | ALambda (na,ty,c) ->
      let e,na = g e na in RLambda (loc,na,Explicit,f e ty,f e c)
  | AProd (na,ty,c) ->
      let e,na = g e na in RProd (loc,na,Explicit,f e ty,f e c)
  | ALetIn (na,b,c) ->
      let e,na = g e na in RLetIn (loc,na,f e b,f e c)
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
      RCases (loc,sty,Option.map (f e') rtntypopt,tml',eqnl')
  | ALetTuple (nal,(na,po),b,c) ->
      let e,nal = list_fold_map g e nal in
      let e,na = g e na in
      RLetTuple (loc,nal,(na,Option.map (f e) po),f e b,f e c)
  | AIf (c,(na,po),b1,b2) ->
      let e,na = g e na in
      RIf (loc,f e c,(na,Option.map (f e) po),f e b1,f e b2)
  | ARec (fk,idl,dll,tl,bl) ->
      let e,idl = array_fold_map (to_id g) e idl in
      let e,dll = array_fold_map (list_fold_map (fun e (na,oc,b) ->
	  let e,na = g e na in
	  (e,(na,Explicit,Option.map (f e) oc,f e b)))) e dll in
      RRec (loc,fk,idl,dll,Array.map (f e) tl,Array.map (f e) bl)
  | ACast (c,k) -> RCast (loc,f e c,
			  match k with
			    | CastConv (k,t) -> CastConv (k,f e t)
			    | CastCoerce -> CastCoerce)
  | ASort x -> RSort (loc,x)
  | AHole x  -> RHole (loc,x)
  | APatVar n -> RPatVar (loc,(false,n))
  | ARef x -> RRef (loc,x)

let rec rawconstr_of_aconstr loc x =
  let rec aux () x =
    rawconstr_of_aconstr_with_binders loc (fun () id -> ((),id)) aux () x
  in aux () x

(****************************************************************************)
(* Translating a rawconstr into a notation, interpreting recursive patterns *)

let add_name r = function
  | Anonymous -> ()
  | Name id -> r := id :: !r

let has_ldots =
  List.exists
    (function RApp (_,RVar(_,v),_) when v = ldots_var -> true | _ -> false)

let compare_rawconstr f t1 t2 = match t1,t2 with
  | RRef (_,r1), RRef (_,r2) -> eq_gr r1 r2 
  | RVar (_,v1), RVar (_,v2) -> v1 = v2
  | RApp (_,f1,l1), RApp (_,f2,l2) -> f f1 f2 & List.for_all2 f l1 l2
  | RLambda (_,na1,bk1,ty1,c1), RLambda (_,na2,bk2,ty2,c2) when na1 = na2 && bk1 = bk2 ->
      f ty1 ty2 & f c1 c2
  | RProd (_,na1,bk1,ty1,c1), RProd (_,na2,bk2,ty2,c2) when na1 = na2 && bk1 = bk2 ->
      f ty1 ty2 & f c1 c2
  | RHole _, RHole _ -> true
  | RSort (_,s1), RSort (_,s2) -> s1 = s2
  | (RLetIn _ | RCases _ | RRec _ | RDynamic _
    | RPatVar _ | REvar _ | RLetTuple _ | RIf _ | RCast _),_
  | _,(RLetIn _ | RCases _ | RRec _ | RDynamic _
      | RPatVar _ | REvar _ | RLetTuple _ | RIf _ | RCast _)
      -> error "Unsupported construction in recursive notations."
  | (RRef _ | RVar _ | RApp _ | RLambda _ | RProd _ | RHole _ | RSort _), _
      -> false

let rec eq_rawconstr t1 t2 = compare_rawconstr eq_rawconstr t1 t2

let discriminate_patterns foundvars nl l1 l2 =
  let diff = ref None in
  let rec aux n c1 c2 = match c1,c2 with
  | RVar (_,v1), RVar (_,v2) when v1<>v2 ->
      if !diff = None then (diff := Some (v1,v2,(n>=nl)); true)
      else
        !diff = Some (v1,v2,(n>=nl)) or !diff = Some (v2,v1,(n<nl))
        or (error
          "Both ends of the recursive pattern differ in more than one place")
  | _ -> compare_rawconstr (aux (n+1)) c1 c2 in
  let l = list_map2_i aux 0 l1 l2 in
  if not (List.for_all ((=) true) l) then
    error "Both ends of the recursive pattern differ.";
  match !diff with
    | None ->  error "Both ends of the recursive pattern are the same."
    | Some (x,y,_ as discr) ->
	List.iter (fun id ->
          if List.mem id !foundvars
          then errorlabstrm "" (strbrk "Variables used in the recursive part of a pattern are not allowed to occur outside of the recursive part.");
          foundvars := id::!foundvars) [x;y];
	discr

let aconstr_and_vars_of_rawconstr a =
  let found = ref [] in
  let rec aux = function
  | RVar (_,id) -> found := id::!found; AVar id
  | RApp (_,f,args) when has_ldots args -> make_aconstr_list f args
  | RApp (_,RVar (_,f),[RApp (_,t,[c]);d]) when f = ldots_var ->
      (* Special case for alternative (recursive) notation of application *)
      let x,y,lassoc = discriminate_patterns found 0 [c] [d] in
      found := ldots_var :: !found; assert lassoc;
      AList (x,y,AApp (AVar ldots_var,[AVar x]),aux t,lassoc)
  | RApp (_,g,args) -> AApp (aux g, List.map aux args)
  | RLambda (_,na,bk,ty,c) -> add_name found na; ALambda (na,aux ty,aux c)
  | RProd (_,na,bk,ty,c) -> add_name found na; AProd (na,aux ty,aux c)
  | RLetIn (_,na,b,c) -> add_name found na; ALetIn (na,aux b,aux c)
  | RCases (_,sty,rtntypopt,tml,eqnl) ->
      let f (_,idl,pat,rhs) = found := idl@(!found); (pat,aux rhs) in
      ACases (sty,Option.map aux rtntypopt,
        List.map (fun (tm,(na,x)) ->
	  add_name found na;
	  Option.iter
	    (fun (_,_,_,nl) -> List.iter (add_name found) nl) x;
          (aux tm,(na,Option.map (fun (_,ind,n,nal) -> (ind,n,nal)) x))) tml,
        List.map f eqnl)
  | RLetTuple (loc,nal,(na,po),b,c) ->
      add_name found na;
      List.iter (add_name found) nal;
      ALetTuple (nal,(na,Option.map aux po),aux b,aux c)
  | RIf (loc,c,(na,po),b1,b2) ->
      add_name found na;
      AIf (aux c,(na,Option.map aux po),aux b1,aux b2)
  | RRec (_,fk,idl,dll,tl,bl) ->
      Array.iter (fun id -> found := id::!found) idl;
      let dll = Array.map (List.map (fun (na,bk,oc,b) ->
	 if bk <> Explicit then
	   error "Binders marked as implicit not allowed in notations.";
	 add_name found na; (na,Option.map aux oc,aux b))) dll in
      ARec (fk,idl,dll,Array.map aux tl,Array.map aux bl)
  | RCast (_,c,k) -> ACast (aux c,
			    match k with CastConv (k,t) -> CastConv (k,aux t)
			      | CastCoerce -> CastCoerce)
  | RSort (_,s) -> ASort s
  | RHole (_,w) -> AHole w
  | RRef (_,r) -> ARef r
  | RPatVar (_,(_,n)) -> APatVar n
  | RDynamic _ | REvar _ ->
      error "Existential variables not allowed in notations."

  (* Recognizing recursive notations *)
  and terminator_of_pat f1 ll1 lr1 = function
  | RApp (loc,f2,l2) ->
      if not (eq_rawconstr f1 f2) then errorlabstrm ""
	(strbrk "Cannot recognize the same head to both ends of the recursive pattern.");
      let nl = List.length ll1 in
      let nr = List.length lr1 in
      if List.length l2 <> nl + nr + 1 then
	error "Both ends of the recursive pattern have different lengths.";
      let ll2,l2' = list_chop nl l2 in
      let t = List.hd l2' and lr2 = List.tl l2' in
      let x,y,order = discriminate_patterns found nl (ll1@lr1) (ll2@lr2) in
      let iter =
        if order then RApp (loc,f2,ll2@RVar (loc,ldots_var)::lr2)
        else RApp (loc,f1,ll1@RVar (loc,ldots_var)::lr1) in
      (if order then y else x),(if order then x else y), aux iter, aux t, order
  | _ -> error "One end of the recursive pattern is not an application."

  and make_aconstr_list f args =
    let rec find_patterns acc = function
      | RApp(_,RVar (_,a),[c]) :: l when a = ldots_var ->
          (* We've found the recursive part *)
	  let x,y,iter,term,lassoc = terminator_of_pat f (List.rev acc) l c in
	  AList (x,y,iter,term,lassoc)
      | a::l -> find_patterns (a::acc) l
      | [] -> error "Ill-formed recursive notation."
    in find_patterns [] args

  in
  let t = aux a in
  (* Side effect *)
  t, !found

let aconstr_of_rawconstr vars a =
  let a,foundvars = aconstr_and_vars_of_rawconstr a in
  let check_type x =
    if not (List.mem x foundvars) then
      error ((string_of_id x)^" is unbound in the right-hand-side.") in
  List.iter check_type vars;
  a

(* Substitution of kernel names, avoiding a list of bound identifiers *)

let aconstr_of_constr avoiding t =
 aconstr_of_rawconstr [] (Detyping.detype false avoiding [] t)

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
  let bound = List.map fst (fst metas @ snd metas) in
  (metas,subst_aconstr subst bound pat)

let encode_list_value l = RApp (dummy_loc,RVar (dummy_loc,ldots_var),l)

(* Pattern-matching rawconstr and aconstr *)

let abstract_return_type_context pi mklam tml rtno =
  Option.map (fun rtn ->
    let nal =
      List.flatten (List.map (fun (_,(na,t)) ->
	match t with Some x -> (pi x)@[na] | None -> [na]) tml) in
    List.fold_right mklam nal rtn)
    rtno

let abstract_return_type_context_rawconstr =
  abstract_return_type_context (fun (_,_,_,nal) -> nal)
    (fun na c -> RLambda(dummy_loc,na,Explicit,RHole(dummy_loc,Evd.InternalHole),c))

let abstract_return_type_context_aconstr =
  abstract_return_type_context pi3
    (fun na c -> ALambda(na,AHole Evd.InternalHole,c))

let rec adjust_scopes = function
  | _,[] -> []
  | [],a::args -> (None,a) :: adjust_scopes ([],args)
  | sc::scopes,a::args -> (sc,a) :: adjust_scopes (scopes,args)

exception No_match

let rec alpha_var id1 id2 = function
  | (i1,i2)::_ when i1=id1 -> i2 = id2
  | (i1,i2)::_ when i2=id2 -> i1 = id1
  | _::idl -> alpha_var id1 id2 idl
  | [] -> id1 = id2

let alpha_eq_val (x,y) = x = y

let bind_env alp (sigma,sigmalist as fullsigma) var v =
  try
    let vvar = List.assoc var sigma in
    if alpha_eq_val (v,vvar) then fullsigma
    else raise No_match
  with Not_found ->
    (* Check that no capture of binding variables occur *)
    if List.exists (fun (id,_) ->occur_rawconstr id v) alp then raise No_match;
    (* TODO: handle the case of multiple occs in different scopes *)
    ((var,v)::sigma,sigmalist)

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

let rawconstr_of_name = function
  | Anonymous -> RHole (dummy_loc,Evd.InternalHole)
  | Name id -> RVar (dummy_loc,id)

let match_names metas (alp,sigma) na1 na2 = match (na1,na2) with
  | (na,Name id2) when List.mem id2 metas ->
      alp, bind_env alp sigma id2 (rawconstr_of_name na)
  | (Name id1,Name id2) -> (id1,id2)::alp,sigma
  | (Anonymous,Anonymous) -> alp,sigma
  | _ -> raise No_match

let rec match_cases_pattern metas acc pat1 pat2 =
  match (pat1,pat2) with
  | PatVar (_,na1), PatVar (_,na2) -> match_names metas acc na1 na2
  | PatCstr (_,c1,patl1,na1), PatCstr (_,c2,patl2,na2)
      when c1 = c2 & List.length patl1 = List.length patl2 ->
      List.fold_left2 (match_cases_pattern metas)
	(match_names metas acc na1 na2) patl1 patl2
  | _ -> raise No_match

let adjust_application_n n loc f l =
  let l1,l2 = list_chop (List.length l - n) l in
  if l1 = [] then f,l else RApp (loc,f,l1), l2

let rec match_ alp metas sigma a1 a2 = match (a1,a2) with
  | r1, AVar id2 when List.mem id2 metas -> bind_env alp sigma id2 r1
  | RVar (_,id1), AVar id2 when alpha_var id1 id2 alp -> sigma
  | RRef (_,r1), ARef r2 when (eq_gr r1 r2) -> sigma 
  | RPatVar (_,(_,n1)), APatVar n2 when n1=n2 -> sigma
  | RApp (loc,f1,l1), AApp (f2,l2) ->
      let n1 = List.length l1 and n2 = List.length l2 in
      let f1,l1,f2,l2 =
	if n1 < n2 then
	  let l21,l22 = list_chop (n2-n1) l2 in f1,l1, AApp (f2,l21), l22
	else if n1 > n2 then
	  let l11,l12 = list_chop (n1-n2) l1 in RApp (loc,f1,l11),l12, f2,l2
	else f1,l1, f2, l2 in
      List.fold_left2 (match_ alp metas) (match_ alp metas sigma f1 f2) l1 l2
  | RApp (loc,f1,l1), AList (x,_,(AApp (f2,l2) as iter),termin,lassoc)
      when List.length l1 >= List.length l2 ->
      let f1,l1 = adjust_application_n (List.length l2) loc f1 l1 in
      match_alist alp metas sigma (f1::l1) (f2::l2) x iter termin lassoc
  | RLambda (_,na1,_,t1,b1), ALambda (na2,t2,b2) ->
     match_binders alp metas na1 na2 (match_ alp metas sigma t1 t2) b1 b2
  | RProd (_,na1,_,t1,b1), AProd (na2,t2,b2) ->
     match_binders alp metas na1 na2 (match_ alp metas sigma t1 t2) b1 b2
  | RLetIn (_,na1,t1,b1), ALetIn (na2,t2,b2) ->
     match_binders alp metas na1 na2 (match_ alp metas sigma t1 t2) b1 b2
  | RCases (_,sty1,rtno1,tml1,eqnl1), ACases (sty2,rtno2,tml2,eqnl2)
      when sty1 = sty2
	 & List.length tml1 = List.length tml2
	 & List.length eqnl1 = List.length eqnl2 ->
      let rtno1' = abstract_return_type_context_rawconstr tml1 rtno1 in
      let rtno2' = abstract_return_type_context_aconstr tml2 rtno2 in
      let sigma =
	try Option.fold_left2 (match_ alp metas) sigma rtno1' rtno2'
	with Option.Heterogeneous -> raise No_match
      in
      let sigma = List.fold_left2
      (fun s (tm1,_) (tm2,_) -> match_ alp metas s tm1 tm2) sigma tml1 tml2 in
      List.fold_left2 (match_equations alp metas) sigma eqnl1 eqnl2
  | RLetTuple (_,nal1,(na1,to1),b1,c1), ALetTuple (nal2,(na2,to2),b2,c2)
      when List.length nal1 = List.length nal2 ->
      let sigma = match_opt (match_binders alp metas na1 na2) sigma to1 to2 in
      let sigma = match_ alp metas sigma b1 b2 in
      let (alp,sigma) =
	List.fold_left2 (match_names metas) (alp,sigma) nal1 nal2 in
      match_ alp metas sigma c1 c2
  | RIf (_,a1,(na1,to1),b1,c1), AIf (a2,(na2,to2),b2,c2) ->
      let sigma = match_opt (match_binders alp metas na1 na2) sigma to1 to2 in
      List.fold_left2 (match_ alp metas) sigma [a1;b1;c1] [a2;b2;c2]
  | RRec (_,fk1,idl1,dll1,tl1,bl1), ARec (fk2,idl2,dll2,tl2,bl2)
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
  | RCast(_,c1, CastConv(_,t1)), ACast(c2, CastConv (_,t2)) ->
      match_ alp metas (match_ alp metas sigma c1 c2) t1 t2
  | RCast(_,c1, CastCoerce), ACast(c2, CastCoerce) ->
      match_ alp metas sigma c1 c2
  | RSort (_,s1), ASort s2 when s1 = s2 -> sigma
  | RPatVar _, AHole _ -> (*Don't hide Metas, they bind in ltac*) raise No_match
  | a, AHole _ -> sigma
  | (RDynamic _ | RRec _ | REvar _), _
  | _,_ -> raise No_match

and match_alist alp metas sigma l1 l2 x iter termin lassoc =
  (* match the iterator at least once *)
  let sigmavar,sigmalist =
    List.fold_left2 (match_ alp (ldots_var::metas)) sigma l1 l2 in
  (* Recover the recursive position *)
  let rest = List.assoc ldots_var sigmavar in
  (* Recover the first element *)
  let t1 = List.assoc x sigmavar in
  let sigmavar = List.remove_assoc x (List.remove_assoc ldots_var sigmavar) in
  (* try to find the remaining elements or the terminator *)
  let rec match_alist_tail alp metas sigma acc rest =
    try
      let sigmavar,sigmalist = match_ alp (ldots_var::metas) sigma rest iter in
      let rest = List.assoc ldots_var sigmavar in
      let t = List.assoc x sigmavar in
      let sigmavar =
	List.remove_assoc x (List.remove_assoc ldots_var sigmavar) in
      match_alist_tail alp metas (sigmavar,sigmalist) (t::acc) rest
    with No_match ->
      List.rev acc, match_ alp metas (sigmavar,sigmalist) rest termin in
  let tl,(sigmavar,sigmalist) = match_alist_tail alp metas sigma [t1] rest in
  (sigmavar, (x,if lassoc then List.rev tl else tl)::sigmalist)

and match_binders alp metas na1 na2 sigma b1 b2 =
  let (alp,sigma) = match_names metas (alp,sigma) na1 na2 in
  match_ alp metas sigma b1 b2

and match_equations alp metas sigma (_,_,patl1,rhs1) (patl2,rhs2) =
  (* patl1 and patl2 have the same length because they respectively
     correspond to some tml1 and tml2 that have the same length *)
  let (alp,sigma) =
    List.fold_left2 (match_cases_pattern metas) (alp,sigma) patl1 patl2 in
  match_ alp metas sigma rhs1 rhs2

type scope_name = string

type tmp_scope_name = scope_name

type subscopes = tmp_scope_name option * scope_name list

type interpretation =
    (* regular vars of notation    / recursive parts of notation    / body *)
    ((identifier * subscopes) list * (identifier * subscopes) list) * aconstr

let match_aconstr c ((metas_scl,metaslist_scl),pat) =
  let vars = List.map fst metas_scl @ List.map fst metaslist_scl in
  let subst,substlist = match_ [] vars ([],[]) c pat in
  (* Reorder canonically the substitution *)
  let find x =
    try List.assoc x subst
    with Not_found ->
      (* Happens for binders bound to Anonymous *)
      (* Find a better way to propagate Anonymous... *)
      RVar (dummy_loc,x) in
  List.map (fun (x,scl) -> (find x,scl)) metas_scl,
  List.map (fun (x,scl) -> (List.assoc x substlist,scl)) metaslist_scl

(**********************************************************************)
(*s Concrete syntax for terms *)

type notation = string

type explicitation = ExplByPos of int * identifier option | ExplByName of identifier

type binder_kind = Default of binding_kind | Generalized of binding_kind * binding_kind * bool

type abstraction_kind = AbsLambda | AbsPi

type proj_flag = int option (* [Some n] = proj of the n-th visible argument *)

type prim_token = Numeral of Bigint.bigint | String of string

type 'a notation_substitution =
    'a list * (* for recursive notations: *) 'a list list

type cases_pattern_expr =
  | CPatAlias of loc * cases_pattern_expr * identifier
  | CPatCstr of loc * reference * cases_pattern_expr list
  | CPatAtom of loc * reference option
  | CPatOr of loc * cases_pattern_expr list
  | CPatNotation of loc * notation * cases_pattern_expr notation_substitution
  | CPatPrim of loc * prim_token
  | CPatRecord of loc * (reference * cases_pattern_expr) list
  | CPatDelimiters of loc * string * cases_pattern_expr

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
      (constr_expr * (name option * constr_expr option)) list *
      (loc * cases_pattern_expr list located list * constr_expr) list
  | CLetTuple of loc * name list * (name option * constr_expr option) *
      constr_expr * constr_expr
  | CIf of loc * constr_expr * (name option * constr_expr option)
      * constr_expr * constr_expr
  | CHole of loc * Evd.hole_kind option
  | CPatVar of loc * (bool * patvar)
  | CEvar of loc * existential_key * constr_expr list option
  | CSort of loc * rawsort
  | CCast of loc * constr_expr * constr_expr cast_type
  | CNotation of loc * notation * constr_expr notation_substitution
  | CGeneralization of loc * binding_kind * abstraction_kind option * constr_expr
  | CPrim of loc * prim_token
  | CDelimiters of loc * string * constr_expr
  | CDynamic of loc * Dyn.t

and fix_expr =
    identifier located * (identifier located option * recursion_order_expr) * local_binder list * constr_expr * constr_expr

and local_binder =
  | LocalRawDef of name located * constr_expr
  | LocalRawAssum of name located list * binder_kind * constr_expr

and typeclass_constraint = name located * binding_kind * constr_expr

and typeclass_context = typeclass_constraint list

and cofix_expr =
    identifier located * local_binder list * constr_expr * constr_expr

and recursion_order_expr =
  | CStructRec
  | CWfRec of constr_expr
  | CMeasureRec of constr_expr * constr_expr option (* measure, relation *)

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

let occur_var_constr_ref id = function
  | Ident (loc,id') -> id = id'
  | Qualid _ -> false

let ids_of_cases_indtype =
  let add_var ids = function CRef (Ident (_,id)) -> id::ids | _ -> ids in
  let rec vars_of = function
    (* We deal only with the regular cases *)
    | CApp (_,_,l) -> List.fold_left add_var [] (List.map fst l)
    | CNotation (_,_,(l,[]))
    (* assume the ntn is applicative and does not instantiate the head !! *)
    | CAppExpl (_,_,l) -> List.fold_left add_var [] l
    | CDelimiters(_,_,c) -> vars_of c
    | _ -> [] in
  vars_of

let ids_of_cases_tomatch tms =
  List.fold_right
    (fun (_,(ona,indnal)) l ->
      Option.fold_right (fun t -> (@) (ids_of_cases_indtype t))
      indnal (Option.fold_right name_cons ona l))
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
  | _ ->
      f n acc b

let fold_constr_expr_with_binders g f n acc = function
  | CArrow (loc,a,b) -> f n (f n acc a) b
  | CAppExpl (loc,(_,_),l) -> List.fold_left (f n) acc l
  | CApp (loc,(_,t),l) -> List.fold_left (f n) (f n acc t) (List.map fst l)
  | CProdN (_,l,b) | CLambdaN (_,l,b) -> fold_constr_expr_binders g f n acc b l
  | CLetIn (_,na,a,b) -> fold_constr_expr_binders g f n acc b [[na],default_binder_kind,a]
  | CCast (loc,a,CastConv(_,b)) -> f n (f n acc a) b
  | CCast (loc,a,CastCoerce) -> f n acc a
  | CNotation (_,_,(l,ll)) -> List.fold_left (f n) acc (l@List.flatten ll)
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
      let n' = List.fold_right (name_fold g) nal n in
      f (Option.fold_right (name_fold g) ona n') (f n acc b) c
  | CIf (_,c,(ona,po),b1,b2) ->
      let acc = f n (f n (f n acc b1) b2) c in
      Option.fold_left (f (Option.fold_right (name_fold g) ona n)) acc po
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

let index_of_annot bl na =
  let names = List.map snd (names_of_local_assums bl) in
  match na with
  | None ->
      if names = [] then error "A fixpoint needs at least one parameter." 
      else None
  | Some (loc, id) ->
      try Some (list_index0 (Name id) names)
      with Not_found ->
        user_err_loc(loc,"",
        str "No parameter named " ++ Nameops.pr_id id ++ str".")

(* Used in correctness and interface *)

let map_binder g e nal = List.fold_right (fun (_,na) -> name_fold g na) nal e

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
  | CNotation (loc,n,(l,ll)) ->
      CNotation (loc,n,(List.map (f e) l,List.map (List.map (f e)) ll))
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
      let e' = List.fold_right (name_fold g) nal e in
      let e'' = Option.fold_right (name_fold g) ona e in
      CLetTuple (loc,nal,(ona,Option.map (f e'') po),f e b,f e' c)
  | CIf (loc,c,(ona,po),b1,b2) ->
      let e' = Option.fold_right (name_fold g) ona e in
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
(* and which are them occupied by proper symbols of the notation (or spaces) *)

let locs_of_notation f loc (args,argslist) ntn =
  let (bl,el) = Util.unloc loc in
  let rec aux pos = function
    | [] -> if pos = el then [] else [(pos,el-1)]
    | a::l ->
	let ba,ea = Util.unloc (f a) in
	if pos = ba then aux ea l else (pos,ba-1)::aux ea l
  in aux bl (args@List.flatten argslist)

let ntn_loc = locs_of_notation constr_loc
let patntn_loc = locs_of_notation cases_pattern_expr_loc
