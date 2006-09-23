(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(*i*)
open Pp
open Util
open Names
open Nameops
open Libnames
open Rawterm
open Term
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
  | ACases of aconstr option * aconstr option *
      (aconstr * (name * (inductive * name list) option)) list *
      (identifier list * cases_pattern list * aconstr) list
  | AOrderedCase of case_style * aconstr option * aconstr * aconstr array
  | ALetTuple of name list * (name * aconstr option) * aconstr * aconstr
  | AIf of aconstr * (name * aconstr option) * aconstr * aconstr
  | ASort of rawsort
  | AHole of hole_kind
  | APatVar of patvar
  | ACast of aconstr * aconstr
  
let name_app f e = function
  | Name id -> let (id, e) = f id e in (Name id, e)
  | Anonymous -> Anonymous, e

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
      let na,e = name_app g e na in RLambda (loc,na,f e ty,f e c)
  | AProd (na,ty,c) ->
      let na,e = name_app g e na in RProd (loc,na,f e ty,f e c)
  | ALetIn (na,b,c) ->
      let na,e = name_app g e na in RLetIn (loc,na,f e b,f e c)
  | ACases (tyopt,rtntypopt,tml,eqnl) ->
      let cases_predicate_names tml =
	List.flatten (List.map (function
	  | (tm,(na,None)) -> [na]
	  | (tm,(na,Some (_,nal))) -> na::nal) tml) in
      (* TODO: apply g to na (in fact not used) *)
      let e' = List.fold_right
	(fun na e -> snd (name_app g e na)) (cases_predicate_names tml) e in
      let fold id (idl,e) = let (id,e) = g id e in (id::idl,e) in
      let eqnl = List.map (fun (idl,pat,rhs) ->
        let (idl,e) = List.fold_right fold idl ([],e) in (loc,idl,pat,f e rhs)) eqnl in
      RCases (loc,(option_app (f e) tyopt, ref (option_app (f e') rtntypopt)),
        List.map (fun (tm,(na,x)) -> 
	  (f e tm,ref (na,option_app (fun (x,y) -> (loc,x,y)) x))) tml,eqnl)
  | AOrderedCase (b,tyopt,tm,bv) ->
      ROrderedCase (loc,b,option_app (f e) tyopt,f e tm,Array.map (f e) bv,ref None)
  | ALetTuple (nal,(na,po),b,c) ->
      let e,nal = list_fold_map (fun e na -> let (na,e) = name_app g e na in e,na) e nal in 
      let na,e = name_app g e na in
      RLetTuple (loc,nal,(na,option_app (f e) po),f e b,f e c)
  | AIf (c,(na,po),b1,b2) ->
      let na,e = name_app g e na in
      RIf (loc,f e c,(na,option_app (f e) po),f e b1,f e b2)
  | ACast (c,t) -> RCast (loc,f e c,f e t)
  | ASort x -> RSort (loc,x)
  | AHole x  -> RHole (loc,x)
  | APatVar n -> RPatVar (loc,(false,n))
  | ARef x -> RRef (loc,x)

let rec subst_pat subst pat = 
  match pat with
  | PatVar _ -> pat
  | PatCstr (loc,((kn,i),j),cpl,n) -> 
      let kn' = subst_kn subst kn 
      and cpl' = list_smartmap (subst_pat subst) cpl in
        if kn' == kn && cpl' == cpl then pat else
          PatCstr (loc,((kn',i),j),cpl',n)

let rec subst_aconstr subst raw =
  match raw with
  | ARef ref -> 
      let ref' = subst_global subst ref in 
	if ref' == ref then raw else
	  ARef ref'

  | AVar _ -> raw

  | AApp (r,rl) -> 
      let r' = subst_aconstr subst r 
      and rl' = list_smartmap (subst_aconstr subst) rl in
	if r' == r && rl' == rl then raw else
	  AApp(r',rl')

  | AList (id1,id2,r1,r2,b) -> 
      let r1' = subst_aconstr subst r1 and r2' = subst_aconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  AList (id1,id2,r1',r2',b)

  | ALambda (n,r1,r2) -> 
      let r1' = subst_aconstr subst r1 and r2' = subst_aconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  ALambda (n,r1',r2')

  | AProd (n,r1,r2) -> 
      let r1' = subst_aconstr subst r1 and r2' = subst_aconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  AProd (n,r1',r2')

  | ALetIn (n,r1,r2) -> 
      let r1' = subst_aconstr subst r1 and r2' = subst_aconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  ALetIn (n,r1',r2')

  | ACases (ro,rtntypopt,rl,branches) -> 
      let ro' = option_smartmap (subst_aconstr subst) ro 
      and rtntypopt' = option_smartmap (subst_aconstr subst) rtntypopt
      and rl' = list_smartmap
        (fun (a,(n,signopt) as x) -> 
	  let a' = subst_aconstr subst a in
	  let signopt' = option_app (fun ((indkn,i),nal as z) ->
	    let indkn' = subst_kn subst indkn in
	    if indkn == indkn' then z else ((indkn',i),nal)) signopt in
	  if a' == a && signopt' == signopt then x else (a',(n,signopt')))
        rl
      and branches' = list_smartmap 
                        (fun (idl,cpl,r as branch) ->
                           let cpl' = list_smartmap (subst_pat subst) cpl
                           and r' = subst_aconstr subst r in
                             if cpl' == cpl && r' == r then branch else
                               (idl,cpl',r'))
                        branches
      in
        if ro' == ro && rtntypopt == rtntypopt' &
          rl' == rl && branches' == branches then raw else
          ACases (ro',rtntypopt',rl',branches')

  | AOrderedCase (b,ro,r,ra) -> 
      let ro' = option_smartmap (subst_aconstr subst) ro
      and r' = subst_aconstr subst r 
      and ra' = array_smartmap (subst_aconstr subst) ra in
	if ro' == ro && r' == r && ra' == ra then raw else
	  AOrderedCase (b,ro',r',ra')

  | ALetTuple (nal,(na,po),b,c) ->
      let po' = option_smartmap (subst_aconstr subst) po
      and b' = subst_aconstr subst b 
      and c' = subst_aconstr subst c in
	if po' == po && b' == b && c' == c then raw else
	  ALetTuple (nal,(na,po'),b',c')

  | AIf (c,(na,po),b1,b2) ->
      let po' = option_smartmap (subst_aconstr subst) po
      and b1' = subst_aconstr subst b1
      and b2' = subst_aconstr subst b2 
      and c' = subst_aconstr subst c in
	if po' == po && b1' == b1 && b2' == b2 && c' == c then raw else
	  AIf (c',(na,po'),b1',b2')

  | APatVar _ | ASort _ -> raw

  | AHole (ImplicitArg (ref,i)) ->
      let ref' = subst_global subst ref in 
	if ref' == ref then raw else
	  AHole (ImplicitArg (ref',i))
  | AHole (BinderType _ | QuestionMark | CasesType |
      InternalHole | TomatchTypeParameter _) -> raw

  | ACast (r1,r2) -> 
      let r1' = subst_aconstr subst r1 and r2' = subst_aconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  ACast (r1',r2')

let add_name r = function
  | Anonymous -> ()
  | Name id -> r := id :: !r

let has_ldots =
  List.exists
    (function RApp (_,RVar(_,v),_) when v = ldots_var -> true | _ -> false)

let compare_rawconstr f t1 t2 = match t1,t2 with
  | RRef (_,r1), RRef (_,r2) -> r1 = r2
  | RVar (_,v1), RVar (_,v2) -> v1 = v2
  | RApp (_,f1,l1), RApp (_,f2,l2) -> f f1 f2 & List.for_all2 f l1 l2
  | RLambda (_,na1,ty1,c1), RLambda (_,na2,ty2,c2) when na1 = na2 ->
      f ty1 ty2 & f c1 c2
  | RProd (_,na1,ty1,c1), RProd (_,na2,ty2,c2) when na1 = na2 ->
      f ty1 ty2 & f c1 c2
  | RHole _, RHole _ -> true
  | RSort (_,s1), RSort (_,s2) -> s1 = s2
  | (RLetIn _ | RCases _ | ROrderedCase _ | RRec _ | RDynamic _
    | RPatVar _ | REvar _ | RLetTuple _ | RIf _ | RCast _),_
  | _,(RLetIn _ | RCases _ | ROrderedCase _ | RRec _ | RDynamic _
      | RPatVar _ | REvar _ | RLetTuple _ | RIf _ | RCast _)
      -> error "Unsupported construction in recursive notations"
  | (RRef _ | RVar _ | RApp _ | RLambda _ | RProd _ | RHole _ | RSort _), _
      -> false

let rec eq_rawconstr t1 t2 = compare_rawconstr eq_rawconstr t1 t2

let discriminate_patterns nl l1 l2 =
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
    error "Both ends of the recursive pattern differ";
  !diff

let aconstr_and_vars_of_rawconstr a =
  let found = ref [] in
  let bound_binders = ref [] in
  let rec aux = function
  | RVar (_,id) -> 
      if not (List.mem id !bound_binders) then found := id::!found;
      AVar id
  | RApp (_,f,args) when has_ldots args -> make_aconstr_list f args 
  | RApp (_,g,args) -> AApp (aux g, List.map aux args)
  | RLambda (_,na,ty,c) -> add_name bound_binders na; ALambda (na,aux ty,aux c)
  | RProd (_,na,ty,c) -> add_name bound_binders na; AProd (na,aux ty,aux c)
  | RLetIn (_,na,b,c) -> add_name bound_binders na; ALetIn (na,aux b,aux c)
  | RCases (_,(tyopt,rtntypopt),tml,eqnl) ->
      let f (_,idl,pat,rhs) =
        bound_binders := idl@(!bound_binders);
        (idl,pat,aux rhs) in
      ACases (option_app aux tyopt,
        option_app aux !rtntypopt,
        List.map (fun (tm,{contents = (na,x)}) ->
	  add_name bound_binders na;
	  option_iter
	    (fun (_,_,nl) -> List.iter (add_name bound_binders) nl) x;
          (aux tm,(na,option_app (fun (_,ind,nal) -> (ind,nal)) x))) tml,
        List.map f eqnl)
  | ROrderedCase (_,b,tyopt,tm,bv,_) ->
      AOrderedCase (b,option_app aux tyopt,aux tm, Array.map aux bv)
  | RLetTuple (loc,nal,(na,po),b,c) ->
      add_name bound_binders na;
      List.iter (add_name bound_binders) nal;
      ALetTuple (nal,(na,option_app aux po),aux b,aux c)
  | RIf (loc,c,(na,po),b1,b2) ->
      add_name bound_binders na;
      AIf (aux c,(na,option_app aux po),aux b1,aux b2)
  | RCast (_,c,t) -> ACast (aux c,aux t)
  | RSort (_,s) -> ASort s
  | RHole (_,w) -> AHole w
  | RRef (_,r) -> ARef r
  | RPatVar (_,(_,n)) -> APatVar n
  | RDynamic _ | RRec _ | REvar _ ->
      error "Fixpoints, cofixpoints, existential variables and pattern-matching  not \
allowed in abbreviatable expressions"

  (* Recognizing recursive notations *)
  and terminator_of_pat f1 ll1 lr1 = function
  | RApp (loc,f2,l2) ->
      if not (eq_rawconstr f1 f2) then error
	"Cannot recognize the same head to both ends of the recursive pattern";
      let nl = List.length ll1 in
      let nr = List.length lr1 in
      if List.length l2 <> nl + nr + 1 then
	error "Both ends of the recursive pattern have different lengths";
      let ll2,l2' = list_chop nl l2 in
      let t = List.hd l2' and lr2 = List.tl l2' in
      let discr = discriminate_patterns nl (ll1@lr1) (ll2@lr2) in
      let x,y,order = match discr with Some z -> z | None -> 
	error "Both ends of the recursive pattern are the same" in
      List.iter (fun id ->
        if List.mem id !bound_binders or List.mem id !found 
        then error "Variables used in the recursive part of a pattern are not allowed to occur outside of the recursive part";
        found := id::!found) [x;y];
      let iter =
        if order then RApp (loc,f2,ll2@RVar (loc,ldots_var)::lr2)
        else RApp (loc,f1,ll1@RVar (loc,ldots_var)::lr1) in
      (if order then y else x),(if order then x else y), aux iter, aux t, order
  | _ -> error "One end of the recursive pattern is not an application"
    
  and make_aconstr_list f args =
    let rec find_patterns acc = function
      | RApp(_,RVar (_,a),[c]) :: l when a = ldots_var ->
          (* We've found the recursive part *)
	  let x,y,iter,term,lassoc = terminator_of_pat f (List.rev acc) l c in
	  AList (x,y,iter,term,lassoc)
      | a::l -> find_patterns (a::acc) l
      | [] -> error "Ill-formed recursive notation"
    in find_patterns [] args

  in
  let t = aux a in
  (* Side effect *)
  t, !found, !bound_binders

let aconstr_of_rawconstr vars a =
  let a,notbindingvars,binders = aconstr_and_vars_of_rawconstr a in
  let check_type x =
    if not (List.mem x notbindingvars or List.mem x binders) then
      error ((string_of_id x)^" is unbound in the right-hand-side") in
  List.iter check_type vars;
  a

let encode_list_value l = RApp (dummy_loc,RVar (dummy_loc,ldots_var),l)

(* Pattern-matching rawconstr and aconstr *)

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

let bind_env alp sigma var v =
  try
    let vvar = List.assoc var sigma in
    if alpha_eq_val (v,vvar) then sigma
    else raise No_match
  with Not_found ->
    (* Check that no capture of binding variables occur *)
    if List.exists (fun (id,_) ->occur_rawconstr id v) alp then raise No_match;
    (* TODO: handle the case of multiple occs in different scopes *)
    (var,v)::sigma

let match_names metas (alp,sigma) na1 na2 = match (na1,na2) with
  | (Name id1,Name id2) when List.mem id2 metas ->
      alp, bind_env alp sigma id2 (RVar (dummy_loc,id1))
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

let rec match_ alp metas sigma a1 a2 = match (a1,a2) with
  | r1, AVar id2 when List.mem id2 metas -> bind_env alp sigma id2 r1
  | RVar (_,id1), AVar id2 when alpha_var id1 id2 alp -> sigma
  | RRef (_,r1), ARef r2 when r1 = r2 -> sigma
  | RPatVar (_,(_,n1)), APatVar n2 when n1=n2 -> sigma
  | RApp (_,f1,l1), AApp (f2,l2) when List.length l1 = List.length l2 ->
      List.fold_left2 (match_ alp metas) (match_ alp metas sigma f1 f2) l1 l2
  | RApp (_,f1,l1), AList (x,_,(AApp (f2,l2) as iter),termin,lassoc) 
      when List.length l1 = List.length l2 ->
      match_alist alp metas sigma (f1::l1) (f2::l2) x iter termin lassoc
  | RLambda (_,na1,t1,b1), ALambda (na2,t2,b2) ->
     match_binders alp metas (match_ alp metas sigma t1 t2) b1 b2 na1 na2
  | RProd (_,na1,t1,b1), AProd (na2,t2,b2) ->
     match_binders alp metas (match_ alp metas sigma t1 t2) b1 b2 na1 na2
  | RLetIn (_,na1,t1,b1), ALetIn (na2,t2,b2) ->
     match_binders alp metas (match_ alp metas sigma t1 t2) b1 b2 na1 na2
  | RCases (_,(po1,rtno1),tml1,eqnl1), ACases (po2,rtno2,tml2,eqnl2) 
      when List.length tml1 = List.length tml2
	 & List.length eqnl1 = List.length eqnl2 ->
     let sigma = option_fold_left2 (match_ alp metas) sigma po1 po2 in
     (* TODO: match rtno' with their contexts *)
     let sigma = List.fold_left2 
       (fun s (tm1,_) (tm2,_) -> match_ alp metas s tm1 tm2) sigma tml1 tml2 in
     List.fold_left2 (match_equations alp metas) sigma eqnl1 eqnl2
  | ROrderedCase (_,st,po1,c1,bl1,_), AOrderedCase (st2,po2,c2,bl2) 
      when Array.length bl1 = Array.length bl2 ->
     let sigma = option_fold_left2 (match_ alp metas) sigma po1 po2 in
     array_fold_left2 (match_ alp metas) (match_ alp metas sigma c1 c2) bl1 bl2
  | RCast(_,c1,t1), ACast(c2,t2) ->
      match_ alp metas (match_ alp metas sigma c1 c2) t1 t2
  | RSort (_,s1), ASort s2 when s1 = s2 -> sigma
  | RPatVar _, AHole _ -> (*Don't hide Metas, they bind in ltac*) raise No_match
  | a, AHole _ when not(Options.do_translate()) -> sigma
  | RHole _, AHole _ -> sigma
  | (RDynamic _ | RRec _ | REvar _), _ 
  | _,_ -> raise No_match

and match_alist alp metas sigma l1 l2 x iter termin lassoc =
  (* match the iterator at least once *)
  let sigma = List.fold_left2 (match_ alp (ldots_var::metas)) sigma l1 l2 in
  (* Recover the recursive position *)
  let rest = List.assoc ldots_var sigma in
  (* Recover the first element *)
  let t1 = List.assoc x sigma in
  let sigma = List.remove_assoc x (List.remove_assoc ldots_var sigma) in
  (* try to find the remaining elements or the terminator *)
  let rec match_alist_tail alp metas sigma acc rest =
    try 
      let sigma = match_ alp (ldots_var::metas) sigma rest iter in
      let rest = List.assoc ldots_var sigma in
      let t = List.assoc x sigma in
      let sigma = List.remove_assoc x (List.remove_assoc ldots_var sigma) in
      match_alist_tail alp metas sigma (t::acc) rest
    with No_match ->
      List.rev acc, match_ alp metas sigma rest termin in
  let tl,sigma = match_alist_tail alp metas sigma [t1] rest in
  (x,encode_list_value (if lassoc then List.rev tl else tl))::sigma

and match_binders alp metas sigma b1 b2 na1 na2 =
  let (alp,sigma) = match_names metas (alp,sigma) na1 na2 in
  match_ alp metas sigma b1 b2

and match_equations alp metas sigma (_,_,patl1,rhs1) (_,patl2,rhs2) =
  (* patl1 and patl2 have the same length because they respectively
     correspond to some tml1 and tml2 that have the same length *)
  let (alp,sigma) = 
    List.fold_left2 (match_cases_pattern metas) (alp,sigma) patl1 patl2 in
  match_ alp metas sigma rhs1 rhs2

type scope_name = string

type interpretation = 
    (identifier * (scope_name option * scope_name list)) list * aconstr

let match_aconstr c (metas_scl,pat) =
  let subst = match_ [] (List.map fst metas_scl) [] c pat in
  (* Reorder canonically the substitution *)
  let find x subst =
    try List.assoc x subst
    with Not_found ->
      (* Happens for binders bound to Anonymous *)
      (* Find a better way to propagate Anonymous... *)
      RVar (dummy_loc,x) in
  List.map (fun (x,scl) -> (find x subst,scl)) metas_scl

(**********************************************************************)
(*s Concrete syntax for terms *)

type notation = string

type explicitation = ExplByPos of int | ExplByName of identifier

type proj_flag = int option (* [Some n] = proj of the n-th visible argument *)

type cases_pattern_expr =
  | CPatAlias of loc * cases_pattern_expr * identifier
  | CPatCstr of loc * reference * cases_pattern_expr list
  | CPatAtom of loc * reference option
  | CPatNotation of loc * notation * cases_pattern_expr list
  | CPatNumeral of loc * Bignat.bigint
  | CPatDelimiters of loc * string * cases_pattern_expr

type constr_expr =
  | CRef of reference
  | CFix of loc * identifier located * fixpoint_expr list
  | CCoFix of loc * identifier located * cofixpoint_expr list
  | CArrow of loc * constr_expr * constr_expr
  | CProdN of loc * (name located list * constr_expr) list * constr_expr
  | CLambdaN of loc * (name located list * constr_expr) list * constr_expr
  | CLetIn of loc * name located * constr_expr * constr_expr
  | CAppExpl of loc * (proj_flag * reference) * constr_expr list
  | CApp of loc * (proj_flag * constr_expr) * 
      (constr_expr * explicitation located option) list
  | CCases of loc * (constr_expr option * constr_expr option) *
      (constr_expr * (name option * constr_expr option)) list *
      (loc * cases_pattern_expr list * constr_expr) list
  | COrderedCase of loc * case_style * constr_expr option * constr_expr
      * constr_expr list
  | CLetTuple of loc * name list * (name option * constr_expr option) *
      constr_expr * constr_expr
  | CIf of loc * constr_expr * (name option * constr_expr option)
      * constr_expr * constr_expr
  | CHole of loc
  | CPatVar of loc * (bool * patvar)
  | CEvar of loc * existential_key
  | CSort of loc * rawsort
  | CCast of loc * constr_expr * constr_expr
  | CNotation of loc * notation * constr_expr list
  | CNumeral of loc * Bignat.bigint
  | CDelimiters of loc * string * constr_expr
  | CDynamic of loc * Dyn.t

and fixpoint_expr =
    identifier * int * local_binder list * constr_expr * constr_expr

and local_binder =
  | LocalRawDef of name located * constr_expr
  | LocalRawAssum of name located list * constr_expr

and cofixpoint_expr =
    identifier * local_binder list * constr_expr * constr_expr

(***********************)
(* For binders parsing *)

let rec local_binders_length = function
  | [] -> 0
  | LocalRawDef _::bl -> 1 + local_binders_length bl
  | LocalRawAssum (idl,_)::bl -> List.length idl + local_binders_length bl

let names_of_local_assums bl =
  List.flatten (List.map (function LocalRawAssum(l,_)->l|_->[]) bl)

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
  | CCases (loc,_,_,_) -> loc
  | COrderedCase (loc,_,_,_,_) -> loc
  | CLetTuple (loc,_,_,_,_) -> loc
  | CIf (loc,_,_,_,_) -> loc
  | CHole loc -> loc
  | CPatVar (loc,_) -> loc
  | CEvar (loc,_) -> loc
  | CSort (loc,_) -> loc
  | CCast (loc,_,_) -> loc
  | CNotation (loc,_,_) -> loc
  | CNumeral (loc,_) -> loc
  | CDelimiters (loc,_,_) -> loc
  | CDynamic _ -> dummy_loc

let cases_pattern_loc = function
  | CPatAlias (loc,_,_) -> loc
  | CPatCstr (loc,_,_) -> loc
  | CPatAtom (loc,_) -> loc
  | CPatNotation (loc,_,_) -> loc
  | CPatNumeral (loc,_) -> loc
  | CPatDelimiters (loc,_,_) -> loc

let occur_var_constr_ref id = function
  | Ident (loc,id') -> id = id'
  | Qualid _ -> false

let rec occur_var_constr_expr id = function
  | CRef r -> occur_var_constr_ref id r
  | CArrow (loc,a,b) -> occur_var_constr_expr id a or occur_var_constr_expr id b
  | CAppExpl (loc,(_,r),l) ->
      occur_var_constr_ref id r or List.exists (occur_var_constr_expr id) l
  | CApp (loc,(_,f),l) ->
      occur_var_constr_expr id f or
      List.exists (fun (a,_) -> occur_var_constr_expr id a) l
  | CProdN (_,l,b) -> occur_var_binders id b l
  | CLambdaN (_,l,b) -> occur_var_binders id b l
  | CLetIn (_,na,a,b) -> occur_var_binders id b [[na],a]
  | CCast (loc,a,b) -> occur_var_constr_expr id a or occur_var_constr_expr id b
  | CNotation (_,_,l) -> List.exists (occur_var_constr_expr id) l
  | CDelimiters (loc,_,a) -> occur_var_constr_expr id a
  | CHole _ | CEvar _ | CPatVar _ | CSort _ | CNumeral _ | CDynamic _ -> false
  | CCases (loc,_,_,_) 
  | COrderedCase (loc,_,_,_,_) 
  | CLetTuple (loc,_,_,_,_) 
  | CIf (loc,_,_,_,_) 
  | CFix (loc,_,_) 
  | CCoFix (loc,_,_) -> 
      Pp.warning "Capture check in multiple binders not done"; false

and occur_var_binders id b = function
  | (idl,a)::l -> 
      occur_var_constr_expr id a or
      (not (List.mem (Name id) (snd (List.split idl)))
      & occur_var_binders id b l)
  | [] -> occur_var_constr_expr id b

let mkIdentC id  = CRef (Ident (dummy_loc, id))
let mkRefC r     = CRef r
let mkAppC (f,l) = CApp (dummy_loc, (None,f), List.map (fun x -> (x,None)) l)
let mkCastC (a,b)  = CCast (dummy_loc,a,b)
let mkLambdaC (idl,a,b) = CLambdaN (dummy_loc,[idl,a],b)
let mkLetInC (id,a,b)   = CLetIn (dummy_loc,id,a,b)
let mkProdC (idl,a,b)   = CProdN (dummy_loc,[idl,a],b)

(* Used in correctness and interface *)


let names_of_cases_indtype =
  let rec vars_of ids t =
    match t with
      (* We deal only with the regular cases *)
      | CApp (_,_,l) -> List.fold_left (fun ids (a,_) -> vars_of ids a) [] l
      | CRef (Ident (_,id)) -> id::ids
      | CNotation (_,_,l)
      (* assume the ntn is applicative and does not instantiate the head !! *)
      | CAppExpl (_,_,l) -> List.fold_left vars_of [] l
      | CDelimiters(_,_,c) -> vars_of ids c
      | _ -> ids in
  vars_of []

let map_binder g e nal = List.fold_right (fun (_,na) -> name_fold g na) nal e

let map_binders f g e bl =
  (* TODO: avoid variable capture in [t] by some [na] in [List.tl nal] *)
  let h (e,bl) (nal,t) = (map_binder g e nal,(nal,f e t)::bl) in
  let (e,rbl) = List.fold_left h (e,[]) bl in
  (e, List.rev rbl)

let map_local_binders f g e bl =
  (* TODO: avoid variable capture in [t] by some [na] in [List.tl nal] *)
  let h (e,bl) = function
      LocalRawAssum(nal,ty) ->
        (map_binder g e nal, LocalRawAssum(nal,f e ty)::bl)
    | LocalRawDef((loc,na),ty) ->
        (name_fold g na e, LocalRawDef((loc,na),f e ty)::bl) in
  let (e,rbl) = List.fold_left h (e,[]) bl in
  (e, List.rev rbl)

let map_constr_expr_with_binders f g e = function
  | CArrow (loc,a,b) -> CArrow (loc,f e a,f e b)
  | CAppExpl (loc,r,l) -> CAppExpl (loc,r,List.map (f e) l) 
  | CApp (loc,(p,a),l) -> 
      CApp (loc,(p,f e a),List.map (fun (a,i) -> (f e a,i)) l)
  | CProdN (loc,bl,b) ->
      let (e,bl) = map_binders f g e bl in CProdN (loc,bl,f e b)
  | CLambdaN (loc,bl,b) ->
      let (e,bl) = map_binders f g e bl in CLambdaN (loc,bl,f e b)
  | CLetIn (loc,na,a,b) -> CLetIn (loc,na,f e a,f (name_fold g (snd na) e) b)
  | CCast (loc,a,b) -> CCast (loc,f e a,f e b)
  | CNotation (loc,n,l) -> CNotation (loc,n,List.map (f e) l)
  | CDelimiters (loc,s,a) -> CDelimiters (loc,s,f e a)
  | CHole _ | CEvar _ | CPatVar _ | CSort _ 
  | CNumeral _ | CDynamic _ | CRef _ as x -> x
  | CCases (loc,(po,rtnpo),a,bl) ->
      (* TODO: apply g on the binding variables in pat... *)
      let bl = List.map (fun (loc,pat,rhs) -> (loc,pat,f e rhs)) bl in
      let e' = 
	List.fold_right
	  (fun (tm,(na,indnal)) e ->
	    option_fold_right
	      (fun t ->
		let ids = names_of_cases_indtype t in
		List.fold_right g ids)
            indnal (option_fold_right (name_fold g) na e))
	  a e
      in
      CCases (loc,(option_app (f e) po, option_app (f e') rtnpo),
         List.map (fun (tm,x) -> (f e tm,x)) a,bl)
  | COrderedCase (loc,s,po,a,bl) ->
      COrderedCase (loc,s,option_app (f e) po,f e a,List.map (f e) bl)
  | CLetTuple (loc,nal,(ona,po),b,c) ->
      let e' = List.fold_right (name_fold g) nal e in
      let e'' = option_fold_right (name_fold g) ona e in
      CLetTuple (loc,nal,(ona,option_app (f e'') po),f e b,f e' c)
  | CIf (loc,c,(ona,po),b1,b2) ->
      let e' = option_fold_right (name_fold g) ona e in
      CIf (loc,f e c,(ona,option_app (f e') po),f e b1,f e b2)
  | CFix (loc,id,dl) ->
      CFix (loc,id,List.map (fun (id,n,bl,t,d) -> 
        let (e',bl') = map_local_binders f g e bl in
        let t' = f e' t in
        (* Note: fix names should be inserted before the arguments... *)
        let e'' = List.fold_left (fun e (id,_,_,_,_) -> g id e) e' dl in
        let d' = f e'' d in
        (id,n,bl',t',d')) dl)
  | CCoFix (loc,id,dl) ->
      CCoFix (loc,id,List.map (fun (id,bl,t,d) ->
        let (e',bl') = map_local_binders f g e bl in
        let t' = f e' t in
        let e'' = List.fold_left (fun e (id,_,_,_) -> g id e) e' dl in
        let d' = f e'' d in
        (id,bl',t',d')) dl)

(* Used in constrintern *)
let rec replace_vars_constr_expr l = function
  | CRef (Ident (loc,id)) as x ->
      (try CRef (Ident (loc,List.assoc id l)) with Not_found -> x)
  | c -> map_constr_expr_with_binders replace_vars_constr_expr 
      (fun id l -> List.remove_assoc id l) l c

(**********************************************************************)
(* Concrete syntax for modules and modules types *)

type with_declaration_ast = 
  | CWith_Module of identifier located * qualid located
  | CWith_Definition of identifier located * constr_expr

type module_type_ast = 
  | CMTEident of qualid located
  | CMTEwith of module_type_ast * with_declaration_ast

type module_ast = 
  | CMEident of qualid located
  | CMEapply of module_ast * module_ast
