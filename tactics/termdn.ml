
(* $Id$ *)

open Util
(*i open Generic i*)
open Names
open Term
open Pattern

(* Discrimination nets of terms.
   See the module dn.ml for further explanations.
   Eduardo (5/8/97) *)

type 'a t = (constr_label,constr_pattern,'a) Dn.t

(*If we have: f a b c ..., decomp gives: (f,[a;b;c;...])*)

let decomp = 
  let rec decrec acc c = match kind_of_term c with
    | IsAppL (f,l) -> decrec (l@acc) f
    | IsCast (c1,_) -> decrec acc c1
    | _ -> (c,acc)
  in 
  decrec []

let decomp_pat = 
  let rec decrec acc = function
    | PApp (f,args) -> decrec (Array.to_list args @ acc) f
    | c -> (c,acc)
  in 
  decrec []   

let constr_pat_discr t =
  if not (occur_meta_pattern t) then 
    None
  else
    match decomp_pat t with
      | PRef (RInd (ind_sp,_)), args -> Some(IndNode ind_sp,args)
      | PRef (RConstruct (cstr_sp,_)), args -> Some(CstrNode cstr_sp,args)
      | PRef (RVar id), args -> Some(VarNode id,args)
      | _ -> None

let constr_val_discr t =
  let c, l = decomp t in
  match kind_of_term c with
    (* IsConst _,_) -> Some(TERM c,l) *)
    | IsMutInd (ind_sp,_) -> Some(IndNode ind_sp,l)
    | IsMutConstruct (cstr_sp,_) -> Some(CstrNode cstr_sp,l)
    | IsVar id -> Some(VarNode id,l)
    | _ -> None

(* Les deux fonctions suivantes ecrasaient les precedentes, 
   ajout d'un suffixe _nil CP 16/08 *) 

let constr_pat_discr_nil t =
  match constr_pat_discr t with
    | None -> None
    | Some (c,_) -> Some(c,[])

let constr_val_discr_nil t =
  match constr_val_discr t with
    | None -> None
    | Some (c,_) -> Some(c,[])

let create = Dn.create 

let add dn = Dn.add dn constr_pat_discr

let rmv dn = Dn.rmv dn constr_pat_discr

let lookup dn t = Dn.lookup dn constr_val_discr t

let app f dn = Dn.app f dn
