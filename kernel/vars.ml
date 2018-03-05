(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Esubst

module RelDecl = Context.Rel.Declaration

(*********************)
(*     Occurring     *)
(*********************)

exception LocalOccur

(* (closedn n M) raises FreeVar if a variable of height greater than n
   occurs in M, returns () otherwise *)

let closedn n c =
  let rec closed_rec n c = match Constr.kind c with
    | Constr.Rel m -> if m>n then raise LocalOccur
    | _ -> Constr.iter_with_binders succ closed_rec n c
  in
  try closed_rec n c; true with LocalOccur -> false

(* [closed0 M] is true iff [M] is a (de Bruijn) closed term *)

let closed0 c = closedn 0 c

(* (noccurn n M) returns true iff (Rel n) does NOT occur in term M  *)

let noccurn n term =
  let rec occur_rec n c = match Constr.kind c with
    | Constr.Rel m -> if Int.equal m n then raise LocalOccur
    | _ -> Constr.iter_with_binders succ occur_rec n c
  in
  try occur_rec n term; true with LocalOccur -> false

(* (noccur_between n m M) returns true iff (Rel p) does NOT occur in term M
  for n <= p < n+m *)

let noccur_between n m term =
  let rec occur_rec n c = match Constr.kind c with
    | Constr.Rel p -> if n<=p && p<n+m then raise LocalOccur
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
    | Constr.Rel p -> if n<=p && p<n+m then raise LocalOccur
    | Constr.App(f,cl) ->
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

(* The generic lifting function *)
let rec exliftn el c = match Constr.kind c with
  | Constr.Rel i -> Constr.mkRel(reloc_rel i el)
  | _ -> Constr.map_with_binders el_lift exliftn el c

(* Lifting the binding depth across k bindings *)

let liftn n k c =
  match el_liftn (pred k) (el_shft n el_id) with
    | ELID -> c
    | el -> exliftn el c

let lift n = liftn n 1

(*********************)
(*   Substituting    *)
(*********************)

(* (subst1 M c) substitutes M for Rel(1) in c
   we generalise it to (substl [M1,...,Mn] c) which substitutes in parallel
   M1,...,Mn for respectively Rel(1),...,Rel(n) in c *)

(* 1st : general case *)

type info = Closed | Open | Unknown
type 'a substituend = { mutable sinfo: info; sit: 'a }

let lift_substituend depth s =
  match s.sinfo with
    | Closed -> s.sit
    | Open -> lift depth s.sit
    | Unknown ->
      let sit = s.sit in
      if closed0 sit then
        let () = s.sinfo <- Closed in
        sit
      else
        let () = s.sinfo <- Open in
        lift depth sit

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

(*
let substkey = CProfile.declare_profile "substn_many";;
let substn_many lamv n c = CProfile.profile3 substkey substn_many lamv n c;;
*)

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

(* Build a substitution from an instance, inserting missing let-ins *)

let subst_of_rel_context_instance sign l =
  let rec aux subst sign l =
    let open RelDecl in
    match sign, l with
    | LocalAssum _ :: sign', a::args' -> aux (a::subst) sign' args'
    | LocalDef (_,c,_)::sign', args' ->
	aux (substl subst c :: subst) sign' args'
    | [], [] -> subst
    | _ -> CErrors.anomaly (Pp.str "Instance and signature do not match.")
  in aux [] (List.rev sign) l

let adjust_subst_to_rel_context sign l =
  List.rev (subst_of_rel_context_instance sign l)

let adjust_rel_to_rel_context sign n =
  let rec aux sign =
    let open RelDecl in
    match sign with
    | LocalAssum _ :: sign' -> let (n',p) = aux sign' in (n'+1,p)
    | LocalDef (_,c,_)::sign' -> let (n',p) = aux sign' in (n'+1,if n'<n then p+1 else p)
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

let rec find_var id = function
| [] -> raise Not_found
| (idc, c) :: subst ->
  if Id.equal id idc then c
  else find_var id subst

(* (replace_vars sigma M) applies substitution sigma to term M *)
let replace_vars var_alist x =
  let var_alist = thin_val var_alist in
  match var_alist with
  | [] -> x
  | _ ->
    let rec substrec n c = match Constr.kind c with
    | Constr.Var x ->
      (try lift_substituend n (find_var x var_alist)
      with Not_found -> c)
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

(** Universe substitutions *)
open Constr

let subst_univs_level_constr subst c =
  if Univ.is_empty_level_subst subst then c
  else 
    let f = Univ.Instance.subst_fn (Univ.subst_univs_level_level subst) in
    let changed = ref false in
    let rec aux t = 
      match kind t with
      | Const (c, u) -> 
	if Univ.Instance.is_empty u then t
	else 
          let u' = f u in 
	    if u' == u then t
	    else (changed := true; mkConstU (c, u'))
      | Ind (i, u) ->
	if Univ.Instance.is_empty u then t
	else 
	  let u' = f u in 
	    if u' == u then t
	    else (changed := true; mkIndU (i, u'))
      | Construct (c, u) ->
	if Univ.Instance.is_empty u then t
	else 
          let u' = f u in 
	    if u' == u then t
	    else (changed := true; mkConstructU (c, u'))
      | Sort (Sorts.Type u) -> 
         let u' = Univ.subst_univs_level_universe subst u in
	   if u' == u then t else 
	     (changed := true; mkSort (Sorts.sort_of_univ u'))
      | _ -> Constr.map aux t
    in
    let c' = aux c in
      if !changed then c' else c

let subst_univs_level_context s = 
  Context.Rel.map (subst_univs_level_constr s)
      
let subst_instance_constr subst c =
  if Univ.Instance.is_empty subst then c
  else
    let f u = Univ.subst_instance_instance subst u in
    let rec aux t =
      match kind t with
      | Const (c, u) ->
       if Univ.Instance.is_empty u then t
       else
          let u' = f u in
           if u' == u then t
           else (mkConstU (c, u'))
      | Ind (i, u) ->
       if Univ.Instance.is_empty u then t
       else
         let u' = f u in
           if u' == u then t
           else (mkIndU (i, u'))
      | Construct (c, u) ->
       if Univ.Instance.is_empty u then t
       else
          let u' = f u in
           if u' == u then t
           else (mkConstructU (c, u'))
      | Sort (Sorts.Type u) ->
         let u' = Univ.subst_instance_universe subst u in
          if u' == u then t else
            (mkSort (Sorts.sort_of_univ u'))
      | _ -> Constr.map aux t
    in
    aux c

(* let substkey = CProfile.declare_profile "subst_instance_constr";; *)
(* let subst_instance_constr inst c = CProfile.profile2 substkey subst_instance_constr inst c;; *)

let subst_instance_context s ctx = 
  if Univ.Instance.is_empty s then ctx
  else Context.Rel.map (fun x -> subst_instance_constr s x) ctx
