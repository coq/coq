(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Names
open Nameops
open Term
open Pattern
open Rawterm
open Libnames
open Nametab

(* Discrimination nets of terms.
   See the module dn.ml for further explanations.
   Eduardo (5/8/97) *)

type 'a t = (constr_label,constr_pattern,'a) Dn.t

(*If we have: f a b c ..., decomp gives: (f,[a;b;c;...])*)

let decomp = 
  let rec decrec acc c = match kind_of_term c with
    | App (f,l) -> decrec (Array.fold_right (fun a l -> a::l) l acc) f
    | Cast (c1,_) -> decrec acc c1
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
      | PRef (IndRef sp), args -> Some(IndNode sp,args)
      | PRef (ConstructRef sp), args -> Some(CstrNode sp,args)
      | PRef (VarRef id), args -> Some(VarNode id,args)
      | _ -> None

let constr_val_discr t =
  let c, l = decomp t in
  match kind_of_term c with
    (* Const _,_) -> Some(TERM c,l) *)
    | Ind ind_sp -> Some(IndNode ind_sp,l)
    | Construct cstr_sp -> Some(CstrNode cstr_sp,l)
    (* Ici, comment distinguer SectionVarNode de VarNode ?? *)
    | Var id -> Some(VarNode id,l)
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
