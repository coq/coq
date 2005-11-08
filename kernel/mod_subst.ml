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

(* WARNING: not every constant in the associative list domain used to exist
   in the environment. This allows a simple implementation of the join
   operation. However, iterating over the associative list becomes a non-sense
*)
type resolver = (constant * constr option) list

let make_resolver resolve = resolve

let apply_opt_resolver resolve kn =
 match resolve with
    None -> None
  | Some resolve ->
     try List.assoc kn resolve with Not_found -> assert false

type substitution_domain = MSI of mod_self_id | MBI of mod_bound_id

let string_of_subst_domain = function
   MSI msid -> debug_string_of_msid msid
 | MBI mbid -> debug_string_of_mbid mbid

module Umap = Map.Make(struct 
			 type t = substitution_domain
			 let compare = Pervasives.compare
		       end)

type substitution = (module_path * resolver option) Umap.t

let empty_subst = Umap.empty

let add_msid msid mp =
  Umap.add (MSI msid) (mp,None)
let add_mbid mbid mp resolve =
  Umap.add (MBI mbid) (mp,resolve)

let map_msid msid mp = add_msid msid mp empty_subst
let map_mbid mbid mp resolve = add_mbid mbid mp resolve empty_subst

let list_contents sub = 
  let one_pair uid (mp,_) l =
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

let subst_mp0 sub mp = (* 's like subst *)
 let rec aux mp =
  match mp with
    | MPself sid -> 
        let mp',resolve = Umap.find (MSI sid) sub in
         mp',resolve
    | MPbound bid ->
        let mp',resolve = Umap.find (MBI bid) sub in
         mp',resolve
    | MPdot (mp1,l) -> 
	let mp1',resolve = aux mp1 in
	 MPdot (mp1',l),resolve
    | _ -> raise Not_found
 in
  try Some (aux mp) with Not_found -> None

let subst_mp sub mp =
 match subst_mp0 sub mp with
    None -> mp
  | Some (mp',_) -> mp'


let subst_kn0 sub kn =
 let mp,dir,l = repr_kn kn in
  match subst_mp0 sub mp with
     Some (mp',_) ->
      Some (make_kn mp' dir l)
   | None -> None

let subst_kn sub kn =
 match subst_kn0 sub kn with
    None -> kn
  | Some kn' -> kn'

let subst_con sub con =
 let mp,dir,l = repr_con con in
  match subst_mp0 sub mp with
     None -> con,mkConst con
   | Some (mp',resolve) ->
      let con' = make_con mp' dir l in
       match apply_opt_resolver resolve con with
          None -> con',mkConst con'
        | Some t -> con',t

(* Here the semantics is completely unclear.
   What does "Hint Unfold t" means when "t" is a parameter?
   Does the user mean "Unfold X.t" or does she mean "Unfold y"
   where X.t is later on instantiated with y? I choose the first
   interpretation (i.e. an evaluable reference is never expanded). *)
let subst_evaluable_reference subst = function
  | EvalVarRef id -> EvalVarRef id
  | EvalConstRef kn -> EvalConstRef (fst (subst_con subst kn))

(* 
This should be rewritten to prevent duplication of constr's when not
necessary.
For now, it uses map_constr and is rather ineffective
*)

let rec map_kn f f' c = 
  let func = map_kn f f' in
    match kind_of_term c with
      | Const kn -> f' kn
      | Ind (kn,i) -> 
         (match f kn with
             None -> c
           | Some kn' ->
	      mkInd (kn',i))
      | Construct ((kn,i),j) -> 
         (match f kn with
             None -> c
           | Some kn' ->
	      mkConstruct ((kn',i),j))
      | Case (ci,p,c,l) ->
	  let ci' =
           { ci with
              ci_ind =
               let (kn,i) = ci.ci_ind in
                match f kn with None -> ci.ci_ind | Some kn' -> kn',i } in
	  mkCase (ci', func p, func c, array_smartmap func l) 
      | _ -> map_constr func c

let subst_mps sub = 
  map_kn (subst_kn0 sub) (fun con -> snd (subst_con sub con))

let rec replace_mp_in_mp mpfrom mpto mp =
  match mp with
    | _ when mp = mpfrom -> mpto
    | MPdot (mp1,l) -> 
	let mp1' = replace_mp_in_mp mpfrom mpto mp1 in
	  if mp1==mp1' then mp
	  else MPdot (mp1',l)
    | _ -> mp

let replace_mp_in_con mpfrom mpto kn =
 let mp,dir,l = repr_con kn in
  let mp'' = replace_mp_in_mp mpfrom mpto mp in
    if mp==mp'' then kn
    else make_con mp'' dir l

exception BothSubstitutionsAreIdentitySubstitutions
exception ChangeDomain of resolver

let join (subst1 : substitution) (subst2 : substitution) = 
  let apply_subst (sub : substitution) key (mp,resolve) =
   let mp',resolve' =
    match subst_mp0 sub mp with
       None -> mp, None
     | Some (mp',resolve') -> mp',resolve' in
   let resolve'' : resolver option =
    try
     let res =
      match resolve with
         Some res -> res
       | None ->
          match resolve' with
             None -> raise BothSubstitutionsAreIdentitySubstitutions
           | Some res -> raise (ChangeDomain res)
     in
      Some
       (List.map
         (fun (kn,topt) ->
           kn,
           match topt with
              None ->
               (match key with
                   MSI msid ->
                    let kn' = replace_mp_in_con (MPself msid) mp kn in
                     apply_opt_resolver resolve' kn'
                 | MBI mbid ->
                    let kn' = replace_mp_in_con (MPbound mbid) mp kn in
                     apply_opt_resolver resolve' kn')
            | Some t -> Some (subst_mps sub t)) res)
    with
       BothSubstitutionsAreIdentitySubstitutions -> None
     | ChangeDomain res ->
        Some
         ((List.map
            (fun (kn,topt) ->
              let key' =
               match key with
                  MSI msid -> MPself msid
                | MBI mbid -> MPbound mbid in
              (* let's replace mp with key in kn *)
              let kn' = replace_mp_in_con mp key' kn in
               kn',topt)) res)
   in
    mp',resolve'' in
  let subst = Umap.mapi (apply_subst subst2) subst1 in
  Umap.fold Umap.add subst2 subst

let rec occur_in_path uid path =
 match uid,path with
  | MSI sid,MPself sid' -> sid = sid'
  | MBI bid,MPbound bid' -> bid = bid'
  | _,MPdot (mp1,_) -> occur_in_path uid mp1
  | _ -> false
    
let occur_uid uid sub = 
  let check_one uid' (mp,_) =
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
