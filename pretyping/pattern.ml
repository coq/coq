(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Names
open Libnames
open Nameops
open Term
open Rawterm
open Environ
open Nametab
open Pp

(* Metavariables *)

type patvar_map = (patvar * constr) list
let patvar_of_int n =
  let p = if !Options.v7 & not (Options.do_translate ()) then "?" else "X"
  in
  Names.id_of_string (p ^ string_of_int n)
let pr_patvar = pr_id

let patvar_of_int_v7 n = Names.id_of_string ("?" ^ string_of_int n)

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
  | PCase of (inductive option * case_style)
      * constr_pattern option * constr_pattern * constr_pattern array
  | PFix of fixpoint
  | PCoFix of cofixpoint

let rec occur_meta_pattern = function
  | PApp (f,args) ->
      (occur_meta_pattern f) or (array_exists occur_meta_pattern args)
  | PLambda (na,t,c)  -> (occur_meta_pattern t) or (occur_meta_pattern c)
  | PProd (na,t,c)  -> (occur_meta_pattern t) or (occur_meta_pattern c)
  | PLetIn (na,t,c)  -> (occur_meta_pattern t) or (occur_meta_pattern c)
  | PCase(_,None,c,br)   ->
      (occur_meta_pattern c) or (array_exists occur_meta_pattern br)
  | PCase(_,Some p,c,br) ->
      (occur_meta_pattern p) or
      (occur_meta_pattern c) or (array_exists occur_meta_pattern br)
  | PMeta _ | PSoApp _ -> true
  | PEvar _ | PVar _ | PRef _ | PRel _ | PSort _ | PFix _ | PCoFix _ -> false

let rec subst_pattern subst pat = match pat with
  | PRef ref ->
      let ref' = subst_global subst ref in
	if ref' == ref then pat else 
	  PRef ref'
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
  | PCase (cs,typ, c, branches) -> 
      let typ' = option_smartmap (subst_pattern subst) typ in 
      let c' = subst_pattern subst c in
      let branches' = array_smartmap (subst_pattern subst) branches in
	if typ' == typ && c' == c && branches' == branches then pat else
	  PCase(cs,typ', c', branches') 
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

type constr_label =
  | ConstNode of constant
  | IndNode of inductive
  | CstrNode of constructor
  | VarNode of identifier

exception BoundPattern;;

let label_of_ref = function
  | ConstRef sp     -> ConstNode sp
  | IndRef sp       -> IndNode sp
  | ConstructRef sp -> CstrNode sp
  | VarRef id       -> VarNode id

let ref_of_label = function
  | ConstNode sp     -> ConstRef sp
  | IndNode sp       -> IndRef sp
  | CstrNode sp      -> ConstructRef sp
  | VarNode id       -> VarRef id

let subst_label subst cstl = 
  let ref = ref_of_label cstl in
  let ref' = subst_global subst ref in
    if ref' == ref then cstl else
      label_of_ref ref'
      
  
let rec head_pattern_bound t =
  match t with
    | PProd (_,_,b)  -> head_pattern_bound b 
    | PLetIn (_,_,b) -> head_pattern_bound b 
    | PApp (c,args)  -> head_pattern_bound c
    | PCase (_,p,c,br) -> head_pattern_bound c
    | PRef r         -> label_of_ref r
    | PVar id        -> VarNode id
    | PEvar _ | PRel _ | PMeta _ | PSoApp _  | PSort _ | PFix _
	-> raise BoundPattern
    (* Perhaps they were arguments, but we don't beta-reduce *)
    | PLambda _ -> raise BoundPattern
    | PCoFix _ -> anomaly "head_pattern_bound: not a type"

let head_of_constr_reference c = match kind_of_term c with
  | Const sp -> ConstNode sp
  | Construct sp -> CstrNode sp
  | Ind sp -> IndNode sp
  | Var id -> VarNode id
  | _ -> anomaly "Not a rigid reference"

let rec pattern_of_constr t =
  match kind_of_term t with
    | Rel n  -> PRel n
    | Meta n -> PMeta (Some (id_of_string (string_of_int n)))
    | Var id -> PVar id
    | Sort (Prop c) -> PSort (RProp c)
    | Sort (Type _) -> PSort (RType None)
    | Cast (c,_)      -> pattern_of_constr c
    | LetIn (na,c,_,b) -> PLetIn (na,pattern_of_constr c,pattern_of_constr b)
    | Prod (na,c,b)   -> PProd (na,pattern_of_constr c,pattern_of_constr b)
    | Lambda (na,c,b) -> PLambda (na,pattern_of_constr c,pattern_of_constr b)
    | App (f,a) -> PApp (pattern_of_constr f,Array.map pattern_of_constr a)
    | Const sp         -> PRef (ConstRef sp)
    | Ind sp        -> PRef (IndRef sp)
    | Construct sp -> PRef (ConstructRef sp)
    | Evar (n,ctxt) -> PEvar (n,Array.map pattern_of_constr ctxt)
    | Case (ci,p,a,br) ->
	PCase ((Some ci.ci_ind,ci.ci_pp_info.style),
	       Some (pattern_of_constr p),pattern_of_constr a,
	       Array.map pattern_of_constr br)
    | Fix f -> PFix f
    | CoFix f -> PCoFix f

(* To process patterns, we need a translation without typing at all. *)

let rec inst lvar = function
  | PVar id as x -> (try List.assoc id lvar with Not_found -> x)
  | PApp (p,pl) -> PApp (inst lvar p, Array.map (inst lvar) pl)
  | PSoApp (n,pl) -> PSoApp (n, List.map (inst lvar) pl)
  | PLambda (n,a,b) -> PLambda (n,inst lvar a,inst lvar b)
  | PProd (n,a,b) -> PProd (n,inst lvar a,inst lvar b)
  | PLetIn (n,a,b) -> PLetIn (n,inst lvar a,inst lvar b)
  | PCase (ci,po,p,pl) ->
      PCase (ci,option_app (inst lvar) po,inst lvar p,Array.map (inst lvar) pl)
  (* Non recursive *)
  | (PEvar _ | PRel _ | PRef _  | PSort _  | PMeta _ as x) -> x 
  (* Bound to terms *)
  | (PFix _ | PCoFix _ as r) ->
      error ("Not instantiable pattern")

let instantiate_pattern = inst

let rec pat_of_raw metas vars = function
  | RVar (_,id) ->
      (try PRel (list_index (Name id) vars)
       with Not_found -> PVar id)
  | RPatVar (_,(false,n)) ->
      metas := n::!metas; PMeta (Some n)
  | RRef (_,r) ->
      PRef r
  (* Hack pour ne pas réécrire une interprétation complète des patterns*)
  | RApp (_, RPatVar (_,(true,n)), cl) ->
      PSoApp (n, List.map (pat_of_raw metas vars) cl)
  | RApp (_,c,cl) -> 
      PApp (pat_of_raw metas vars c,
	    Array.of_list (List.map (pat_of_raw metas vars) cl))
  | RLambda (_,na,c1,c2) ->
      PLambda (na, pat_of_raw metas vars c1,
	       pat_of_raw metas (na::vars) c2)
  | RProd (_,na,c1,c2) ->
      PProd (na, pat_of_raw metas vars c1,
	       pat_of_raw metas (na::vars) c2)
  | RLetIn (_,na,c1,c2) ->
      PLetIn (na, pat_of_raw metas vars c1,
	       pat_of_raw metas (na::vars) c2)
  | RSort (_,s) ->
      PSort s
  | RHole _ ->
      PMeta None
  | RCast (_,c,t) ->
      Options.if_verbose
        Pp.warning "Cast not taken into account in constr pattern";
      pat_of_raw metas vars c
  | ROrderedCase (_,st,po,c,br,_) ->
      PCase ((None,st),option_app (pat_of_raw metas vars) po,
             pat_of_raw metas vars c,
             Array.map (pat_of_raw metas vars) br)
  | RIf (_,c,(_,None),b1,b2) ->
      PCase ((None,IfStyle),None, pat_of_raw metas vars c,
             [|pat_of_raw metas vars b1; pat_of_raw metas vars b2|])
  | RCases (loc,(po,_),[c,_],brs) ->
      let sp =
	match brs with
	  | (_,_,[PatCstr(_,(ind,_),_,_)],_)::_ -> Some ind
	  | _ -> None in
      (* When po disappears: switch to rtn type *)
      PCase ((sp,Term.RegularStyle),option_app (pat_of_raw metas vars) po,
             pat_of_raw metas vars c,
             Array.init (List.length brs)
	       (pat_of_raw_branch loc metas vars sp brs))
  | r ->
      let loc = loc_of_rawconstr r in
      user_err_loc (loc,"pattern_of_rawconstr", Pp.str "Not supported pattern")

and pat_of_raw_branch loc metas vars ind brs i =
  let bri = List.filter
    (function
        (_,_,[PatCstr(_,c,lv,_)],_) -> snd c = i+1
      | (loc,_,_,_) ->
          user_err_loc (loc,"pattern_of_rawconstr",
                        Pp.str "Not supported pattern")) brs in
  match bri with
      [(_,_,[PatCstr(_,(indsp,_),lv,_)],br)] ->
	if ind <> None & ind <> Some indsp then
          user_err_loc (loc,"pattern_of_rawconstr",
            Pp.str "All constructors must be in the same inductive type");
        let lna =
          List.map
            (function PatVar(_,na) -> na
              | PatCstr(loc,_,_,_) ->
                  user_err_loc (loc,"pattern_of_rawconstr",
                                Pp.str "Not supported pattern")) lv in
        let vars' = List.rev lna @ vars in 
        List.fold_right (fun na b -> PLambda(na,PMeta None,b)) lna
          (pat_of_raw metas vars' br)
    | _ -> user_err_loc (loc,"pattern_of_rawconstr",
                         str "No unique branch for " ++ int (i+1) ++
                         str"-th constructor")

let pattern_of_rawconstr c =
  let metas = ref [] in
  let p = pat_of_raw metas [] c in
  (!metas,p)
