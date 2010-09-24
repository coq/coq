(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Libnames
open Nameops
open Term
open Rawterm
open Environ
open Nametab
open Pp
open Mod_subst

(* Metavariables *)

type constr_under_binders = identifier list * constr

type patvar_map = (patvar * constr) list
type extended_patvar_map = (patvar * constr_under_binders) list

(* Patterns *)

type constr_pattern =
  | PRef of global_reference
  | PVar of identifier
  | PEvar of existential_key * constr_pattern array
  | PRel of int
  | PApp of constr_pattern * constr_pattern array
  | PSoApp of patvar * constr_pattern list
  | PLambda of name * constr_pattern * constr_pattern
  | PProd of name * constr_pattern * constr_pattern
  | PLetIn of name * constr_pattern * constr_pattern
  | PSort of rawsort
  | PMeta of patvar option
  | PIf of constr_pattern * constr_pattern * constr_pattern
  | PCase of (case_style * int array * inductive option * (int * int) option)
      * constr_pattern * constr_pattern * constr_pattern array
  | PFix of fixpoint
  | PCoFix of cofixpoint

let rec occur_meta_pattern = function
  | PApp (f,args) ->
      (occur_meta_pattern f) or (array_exists occur_meta_pattern args)
  | PLambda (na,t,c)  -> (occur_meta_pattern t) or (occur_meta_pattern c)
  | PProd (na,t,c)  -> (occur_meta_pattern t) or (occur_meta_pattern c)
  | PLetIn (na,t,c)  -> (occur_meta_pattern t) or (occur_meta_pattern c)
  | PIf (c,c1,c2)  ->
      (occur_meta_pattern c) or
      (occur_meta_pattern c1) or (occur_meta_pattern c2)
  | PCase(_,p,c,br) ->
      (occur_meta_pattern p) or
      (occur_meta_pattern c) or (array_exists occur_meta_pattern br)
  | PMeta _ | PSoApp _ -> true
  | PEvar _ | PVar _ | PRef _ | PRel _ | PSort _ | PFix _ | PCoFix _ -> false

exception BoundPattern;;

let rec head_pattern_bound t =
  match t with
    | PProd (_,_,b)  -> head_pattern_bound b
    | PLetIn (_,_,b) -> head_pattern_bound b
    | PApp (c,args)  -> head_pattern_bound c
    | PIf (c,_,_)  -> head_pattern_bound c
    | PCase (_,p,c,br) -> head_pattern_bound c
    | PRef r         -> r
    | PVar id        -> VarRef id
    | PEvar _ | PRel _ | PMeta _ | PSoApp _  | PSort _ | PFix _
	-> raise BoundPattern
    (* Perhaps they were arguments, but we don't beta-reduce *)
    | PLambda _ -> raise BoundPattern
    | PCoFix _ -> anomaly "head_pattern_bound: not a type"

let head_of_constr_reference c = match kind_of_term c with
  | Const sp -> ConstRef sp
  | Construct sp -> ConstructRef sp
  | Ind sp -> IndRef sp
  | Var id -> VarRef id
  | _ -> anomaly "Not a rigid reference"

open Evd

let pattern_of_constr sigma t =
  let ctx = ref [] in
  let rec pattern_of_constr t =
  match kind_of_term t with
    | Rel n  -> PRel n
    | Meta n -> PMeta (Some (id_of_string ("META" ^ string_of_int n)))
    | Var id -> PVar id
    | Sort (Prop c) -> PSort (RProp c)
    | Sort (Type _) -> PSort (RType None)
    | Cast (c,_,_)      -> pattern_of_constr c
    | LetIn (na,c,_,b) -> PLetIn (na,pattern_of_constr c,pattern_of_constr b)
    | Prod (na,c,b)   -> PProd (na,pattern_of_constr c,pattern_of_constr b)
    | Lambda (na,c,b) -> PLambda (na,pattern_of_constr c,pattern_of_constr b)
    | App (f,a) ->
        (match 
          match kind_of_term f with
            Evar (evk,args as ev) ->
              (match snd (Evd.evar_source evk sigma) with
                  MatchingVar (true,id) ->
                    ctx := (id,None,existential_type sigma ev)::!ctx;
                    Some id
                | _ -> None)
            | _ -> None
          with
            | Some n -> PSoApp (n,Array.to_list (Array.map pattern_of_constr a))
            | None -> PApp (pattern_of_constr f,Array.map (pattern_of_constr) a))
    | Const sp         -> PRef (ConstRef (constant_of_kn(canonical_con sp)))
    | Ind sp        -> PRef (canonical_gr (IndRef sp))
    | Construct sp -> PRef (canonical_gr (ConstructRef sp))
    | Evar (evk,ctxt as ev) ->
        (match snd (Evd.evar_source evk sigma) with
          | MatchingVar (b,id) ->
              ctx := (id,None,existential_type sigma ev)::!ctx;
              assert (not b); PMeta (Some id)
          | GoalEvar -> PEvar (evk,Array.map pattern_of_constr ctxt)
          | _ -> PMeta None)
    | Case (ci,p,a,br) ->
	let cip = ci.ci_pp_info in
	let no = Some (ci.ci_npar,cip.ind_nargs) in
	PCase ((cip.style,ci.ci_cstr_ndecls,Some ci.ci_ind,no),
	       pattern_of_constr p,pattern_of_constr a,
	       Array.map pattern_of_constr br)
    | Fix f -> PFix f
    | CoFix f -> PCoFix f in
  let p = pattern_of_constr t in
  (* side-effect *)
  (* Warning: the order of dependencies in ctx is not ensured *)
  (!ctx,p)

(* To process patterns, we need a translation without typing at all. *)

let map_pattern_with_binders g f l = function
  | PApp (p,pl) -> PApp (f l p, Array.map (f l) pl)
  | PSoApp (n,pl) -> PSoApp (n, List.map (f l) pl)
  | PLambda (n,a,b) -> PLambda (n,f l a,f (g n l) b)
  | PProd (n,a,b) -> PProd (n,f l a,f (g n l) b)
  | PLetIn (n,a,b) -> PLetIn (n,f l a,f (g n l) b)
  | PIf (c,b1,b2) -> PIf (f l c,f l b1,f l b2)
  | PCase (ci,po,p,pl) -> PCase (ci,f l po,f l p,Array.map (f l) pl)
  (* Non recursive *)
  | (PVar _ | PEvar _ | PRel _ | PRef _  | PSort _  | PMeta _
  (* Bound to terms *)
  | PFix _ | PCoFix _ as x) -> x

let error_instantiate_pattern id l =
  let is = if List.length l = 1 then "is" else "are" in
  errorlabstrm "" (str "Cannot substitute the term bound to " ++ pr_id id
    ++ strbrk " in pattern because the term refers to " ++ pr_enum pr_id l
    ++ strbrk " which " ++ str is ++ strbrk " not bound in the pattern.")

let instantiate_pattern sigma lvar c =
  let rec aux vars = function
  | PVar id as x ->
      (try
	let ctx,c = List.assoc id lvar in
	try
	  let inst =
	    List.map (fun id -> mkRel (list_index (Name id) vars)) ctx in
	  let c = substl inst c in
	  snd (pattern_of_constr sigma c)
	with Not_found (* list_index failed *) ->
	  let vars =
	    list_map_filter (function Name id -> Some id | _ -> None) vars in
	  error_instantiate_pattern id (list_subtract ctx vars)
       with Not_found (* List.assoc failed *) ->
	 x)
  | (PFix _ | PCoFix _) -> error ("Non instantiable pattern.")
  | c ->
      map_pattern_with_binders (fun id vars -> id::vars) aux vars c in
  aux [] c

let rec liftn_pattern k n = function
  | PRel i as x -> if i >= n then PRel (i+k) else x
  | PFix x -> PFix (destFix (liftn k n (mkFix x)))
  | PCoFix x -> PCoFix (destCoFix (liftn k n (mkCoFix x)))
  | c -> map_pattern_with_binders (fun _ -> succ) (liftn_pattern k) n c

let lift_pattern k = liftn_pattern k 1

let rec subst_pattern subst pat =
  match pat with
  | PRef ref ->
      let ref',t = subst_global subst ref in
	if ref' == ref then pat else
	 snd (pattern_of_constr Evd.empty t)
  | PVar _
  | PEvar _
  | PRel _ -> pat
  | PApp (f,args) ->
      let f' = subst_pattern subst f in
      let args' = array_smartmap (subst_pattern subst) args in
	if f' == f && args' == args then pat else
	  PApp (f',args')
  | PSoApp (i,args) ->
      let args' = list_smartmap (subst_pattern subst) args in
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
  | PLetIn (name,c1,c2) ->
      let c1' = subst_pattern subst c1 in
      let c2' = subst_pattern subst c2 in
	if c1' == c1 && c2' == c2 then pat else
	  PLetIn (name,c1',c2')
  | PSort _
  | PMeta _ -> pat
  | PIf (c,c1,c2) ->
      let c' = subst_pattern subst c in
      let c1' = subst_pattern subst c1 in
      let c2' = subst_pattern subst c2 in
	if c' == c && c1' == c1 && c2' == c2 then pat else
	  PIf (c',c1',c2')
  | PCase ((a,b,ind,n as cs),typ,c,branches) ->
      let ind' = Option.smartmap (Inductiveops.subst_inductive subst) ind in
      let typ' = subst_pattern subst typ in
      let c' = subst_pattern subst c in
      let branches' = array_smartmap (subst_pattern subst) branches in
      let cs' = if ind == ind' then cs else (a,b,ind',n) in
	if typ' == typ && c' == c && branches' == branches then pat else
	  PCase(cs',typ', c', branches')
  | PFix fixpoint ->
      let cstr = mkFix fixpoint in
      let fixpoint' = destFix (subst_mps subst cstr) in
	if fixpoint' == fixpoint then pat else
	  PFix fixpoint'
  | PCoFix cofixpoint ->
      let cstr = mkCoFix cofixpoint in
      let cofixpoint' = destCoFix (subst_mps subst cstr) in
	if cofixpoint' == cofixpoint then pat else
	  PCoFix cofixpoint'

let mkPLambda na b = PLambda(na,PMeta None,b)
let rev_it_mkPLambda = List.fold_right mkPLambda

let rec pat_of_raw metas vars = function
  | RVar (_,id) ->
      (try PRel (list_index (Name id) vars)
       with Not_found -> PVar id)
  | RPatVar (_,(false,n)) ->
      metas := n::!metas; PMeta (Some n)
  | RRef (_,gr) ->
      PRef (canonical_gr gr)
  (* Hack pour ne pas réécrire une interprétation complète des patterns*)
  | RApp (_, RPatVar (_,(true,n)), cl) ->
      metas := n::!metas; PSoApp (n, List.map (pat_of_raw metas vars) cl)
  | RApp (_,c,cl) ->
      PApp (pat_of_raw metas vars c,
	    Array.of_list (List.map (pat_of_raw metas vars) cl))
  | RLambda (_,na,bk,c1,c2) ->
      name_iter (fun n -> metas := n::!metas) na;
      PLambda (na, pat_of_raw metas vars c1,
	       pat_of_raw metas (na::vars) c2)
  | RProd (_,na,bk,c1,c2) ->
      name_iter (fun n -> metas := n::!metas) na;
      PProd (na, pat_of_raw metas vars c1,
	       pat_of_raw metas (na::vars) c2)
  | RLetIn (_,na,c1,c2) ->
      name_iter (fun n -> metas := n::!metas) na;
      PLetIn (na, pat_of_raw metas vars c1,
	       pat_of_raw metas (na::vars) c2)
  | RSort (_,s) ->
      PSort s
  | RHole _ ->
      PMeta None
  | RCast (_,c,_) ->
      Flags.if_verbose
        Pp.warning "Cast not taken into account in constr pattern";
      pat_of_raw metas vars c
  | RIf (_,c,(_,None),b1,b2) ->
      PIf (pat_of_raw metas vars c,
           pat_of_raw metas vars b1,pat_of_raw metas vars b2)
  | RLetTuple (loc,nal,(_,None),b,c) ->
      let mkRLambda c na = RLambda (loc,na,Explicit,RHole (loc,Evd.InternalHole),c) in
      let c = List.fold_left mkRLambda c nal in
      PCase ((LetStyle,[|1|],None,None),PMeta None,pat_of_raw metas vars b,
             [|pat_of_raw metas vars c|])
  | RCases (loc,sty,p,[c,(na,indnames)],brs) ->
      let pred,ind_nargs, ind = match p,indnames with
	| Some p, Some (_,ind,n,nal) ->
	    rev_it_mkPLambda nal (mkPLambda na (pat_of_raw metas vars p)),
	    Some (n,List.length nal),Some ind
	| _ -> PMeta None, None, None in
      let ind = match ind with Some _ -> ind | None ->
	match brs with
	  | (_,_,[PatCstr(_,(ind,_),_,_)],_)::_ -> Some ind
	  | _ -> None in
      let cbrs =
	Array.init (List.length brs) (pat_of_raw_branch loc metas vars ind brs)
      in
      let cstr_nargs,brs = (Array.map fst cbrs, Array.map snd cbrs) in
      PCase ((sty,cstr_nargs,ind,ind_nargs), pred,
             pat_of_raw metas vars c, brs)

  | r ->
      let loc = loc_of_rawconstr r in
      user_err_loc (loc,"pattern_of_rawconstr", Pp.str"Non supported pattern.")

and pat_of_raw_branch loc metas vars ind brs i =
  let bri = List.filter
    (function
        (_,_,[PatCstr(_,c,lv,Anonymous)],_) -> snd c = i+1
      | (loc,_,_,_) ->
          user_err_loc (loc,"pattern_of_rawconstr",
                        Pp.str "Non supported pattern.")) brs in
  match bri with
    | [(_,_,[PatCstr(_,(indsp,_),lv,_)],br)] ->
	if ind <> None & ind <> Some indsp then
          user_err_loc (loc,"pattern_of_rawconstr",
            Pp.str "All constructors must be in the same inductive type.");
        let lna =
          List.map
            (function PatVar(_,na) -> na
              | PatCstr(loc,_,_,_) ->
                  user_err_loc (loc,"pattern_of_rawconstr",
                                Pp.str "Non supported pattern.")) lv in
        let vars' = List.rev lna @ vars in
	List.length lv, rev_it_mkPLambda lna (pat_of_raw metas vars' br)
    | _ -> user_err_loc (loc,"pattern_of_rawconstr",
                         str "No unique branch for " ++ int (i+1) ++
                         str"-th constructor.")

let pattern_of_rawconstr c =
  let metas = ref [] in
  let p = pat_of_raw metas [] c in	
  (!metas,p)
