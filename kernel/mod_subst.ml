(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Term

type substitution_domain = MSI of mod_self_id | MBI of mod_bound_id

let string_of_subst_domain = function
   MSI msid -> debug_string_of_msid msid
 | MBI mbid -> debug_string_of_mbid mbid

module Umap = Map.Make(struct 
			 type t = substitution_domain
			 let compare = Pervasives.compare
		       end)

(* this is correct under the condition that bound and struct
   identifiers can never be identical (i.e. get the same stamp)! *) 

type substitution = module_path Umap.t

let empty_subst = Umap.empty

let add_msid sid = Umap.add (MSI sid)
let add_mbid bid = Umap.add (MBI bid)

let map_msid msid mp = add_msid msid mp empty_subst
let map_mbid mbid mp = add_mbid mbid mp empty_subst

let list_contents sub = 
  let one_pair uid mp l =
    (string_of_subst_domain uid, string_of_mp mp)::l
  in
    Umap.fold one_pair sub []

let debug_string_of_subst sub = 
  let l = List.map (fun (s1,s2) -> s1^"|->"^s2) (list_contents sub) in
    "{" ^ String.concat "; " l ^ "}"

let debug_pr_subst sub = 
  let l = list_contents sub in
  let f (s1,s2) = hov 2 (str s1 ++ spc () ++ str "|-> " ++ str s2) 
  in
    str "{" ++ hov 2 (prlist_with_sep pr_coma f l) ++ str "}" 

let rec subst_mp sub mp = (* 's like subst *)
  match mp with
    | MPself sid -> 
	(try Umap.find (MSI sid) sub with Not_found -> mp)
    | MPbound bid ->
	(try Umap.find (MBI bid) sub with Not_found -> mp)
    | MPdot (mp1,l) -> 
	let mp1' = subst_mp sub mp1 in
	  if mp1==mp1' then 
	    mp
	  else
	    MPdot (mp1',l)
    | _ -> mp

let join subst1 subst2 = 
  let subst = Umap.map (subst_mp subst2) subst1 in
  Umap.fold Umap.add subst2 subst

let rec occur_in_path uid path =
 match uid,path with
  | MSI sid,MPself sid' -> sid = sid'
  | MBI bid,MPbound bid' -> bid = bid'
  | _,MPdot (mp1,_) -> occur_in_path uid mp1
  | _ -> false
    
let occur_uid uid sub = 
  let check_one uid' mp =
    if uid = uid' || occur_in_path uid mp then raise Exit
  in
    try 
      Umap.iter check_one sub;
      false
    with Exit -> true

let occur_msid uid = occur_uid (MSI uid)
let occur_mbid uid = occur_uid (MBI uid)
    
type 'a lazy_subst =
  | LSval of 'a
  | LSlazy of substitution * 'a
	
type 'a substituted = 'a lazy_subst ref
      
let from_val a = ref (LSval a)
    
let force fsubst r = 
  match !r with
  | LSval a -> a
  | LSlazy(s,a) -> 
      let a' = fsubst s a in
      r := LSval a';
      a' 

let subst_substituted s r =
  match !r with
  | LSval a -> ref (LSlazy(s,a))
  | LSlazy(s',a) ->
      let s'' = join s' s in
      ref (LSlazy(s'',a))

let subst_kn sub kn =
 let mp,dir,l = repr_kn kn in
  let mp' = subst_mp sub mp in
    if mp==mp' then kn else make_kn mp' dir l

let subst_con sub con =
 let mp,dir,l = repr_con con in
  let mp' = subst_mp sub mp in
    if mp==mp' then con else make_con mp' dir l

let subst_evaluable_reference subst = function
  | EvalVarRef id -> EvalVarRef id
  | EvalConstRef kn -> EvalConstRef (subst_con subst kn)

(* 
map_kn : (kernel_name -> kernel_name) -> constr -> constr

This should be rewritten to prevent duplication of constr's when not
necessary.
For now, it uses map_constr and is rather ineffective
*)

let rec map_kn f f_con c = 
  let func = map_kn f f_con in
    match kind_of_term c with
      | Const kn -> 
	  mkConst (f_con kn)
      | Ind (kn,i) -> 
	  mkInd (f kn,i)
      | Construct ((kn,i),j) -> 
	  mkConstruct ((f kn,i),j)
      | Case (ci,p,c,l) ->
	  let ci' = { ci with ci_ind = let (kn,i) = ci.ci_ind in f kn, i } in
	  mkCase (ci', func p, func c, array_smartmap func l) 
      | _ -> map_constr func c

let subst_mps sub = 
  map_kn (subst_kn sub) (subst_con sub)
