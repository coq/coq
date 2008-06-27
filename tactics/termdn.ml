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
open Nameops
open Term
open Pattern
open Rawterm
open Libnames
open Nametab

(* Discrimination nets of terms.
   See the module dn.ml for further explanations.
   Eduardo (5/8/97) *)

type 'a t = (global_reference,constr_pattern,'a) Dn.t

(*If we have: f a b c ..., decomp gives: (f,[a;b;c;...])*)

let decomp = 
  let rec decrec acc c = match kind_of_term c with
    | App (f,l) -> decrec (Array.fold_right (fun a l -> a::l) l acc) f
    | Cast (c1,_,_) -> decrec acc c1
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
    | PRef ((IndRef _) as ref), args
    | PRef ((ConstructRef _ ) as ref), args -> Some (ref,args)
    | PRef ((VarRef v) as ref), args -> Some(ref,args)
    | _ -> None

let constr_pat_discr_st (idpred,cpred) t =
  match decomp_pat t with
  | PRef ((IndRef _) as ref), args
  | PRef ((ConstructRef _ ) as ref), args -> Some (ref,args)
  | PRef ((VarRef v) as ref), args when not (Idpred.mem v idpred) -> 
      Some(ref,args)
  | PVar v, args when not (Idpred.mem v idpred) ->
      Some(VarRef v,args)
  | PRef ((ConstRef c) as ref), args when not (Cpred.mem c cpred) ->
      Some (ref, args)
  | _ -> None

open Dn

let constr_val_discr t =  
  let c, l = decomp t in
    match kind_of_term c with
    | Ind ind_sp -> Label(IndRef ind_sp,l)
    | Construct cstr_sp -> Label((ConstructRef cstr_sp),l)
    | Var id -> Label(VarRef id,l)
    | _ -> Nothing
	
let constr_val_discr_st (idpred,cpred) t =  
  let c, l = decomp t in
    match kind_of_term c with
    | Const c -> if Cpred.mem c cpred then Everything else Label(ConstRef c,l)
    | Ind ind_sp -> Label(IndRef ind_sp,l)
    | Construct cstr_sp -> Label((ConstructRef cstr_sp),l)
    | Var id when not (Idpred.mem id idpred) -> Label(VarRef id,l)
    | Evar _ -> Everything
    | _ -> Nothing

let create = Dn.create 

let add dn st = Dn.add dn (constr_pat_discr_st st)

let rmv dn st = Dn.rmv dn (constr_pat_discr_st st)

let lookup dn st t = Dn.lookup dn (constr_val_discr_st st) t
  
let app f dn = Dn.app f dn
