
(* $Id$ *)

open Util
open Generic
open Names
open Term
open Rawterm

(* Discrimination nets of terms.
   See the module dn.ml for further explanations.
   Eduardo (5/8/97) *)

type 'a t = (constr_label,constr_pattern,'a) Dn.t

(*If we have: f a b c ..., decomp gives: (f,[a;b;c;...])*)

let decomp = 
  let rec decrec acc = function
    | DOPN(AppL,cl) -> decrec (array_app_tl cl acc) (array_hd cl)
    | DOP2(Cast,c1,_) -> decrec acc c1
    | c -> (c,acc)
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
  match decomp t with
    (* DOPN(Const _,_) as c,l -> Some(TERM c,l) *)
    | DOPN(MutInd ind_sp,_) as c,l -> Some(IndNode ind_sp,l)
    | DOPN(MutConstruct cstr_sp,_) as c,l -> Some(CstrNode cstr_sp,l)
    | VAR id as c,l -> Some(VarNode id,l)
    | c -> None

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
