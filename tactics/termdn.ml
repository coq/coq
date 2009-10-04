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

type term_label =
  | GRLabel of global_reference
  | ProdLabel
  | LambdaLabel
  | SortLabel of sorts option

type 'a t = (term_label,constr_pattern,'a) Dn.t

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
    | PRef ((ConstructRef _ ) as ref), args -> Some (GRLabel ref,args)
    | PRef ((VarRef v) as ref), args -> Some(GRLabel ref,args)
    | _ -> None

let constr_pat_discr_st (idpred,cpred) t =
  match decomp_pat t with
  | PRef ((IndRef _) as ref), args
  | PRef ((ConstructRef _ ) as ref), args -> Some (GRLabel ref,args)
  | PRef ((VarRef v) as ref), args when not (Idpred.mem v idpred) ->
      Some(GRLabel ref,args)
  | PVar v, args when not (Idpred.mem v idpred) ->
      Some(GRLabel (VarRef v),args)
  | PRef ((ConstRef c) as ref), args when not (Cpred.mem c cpred) ->
      Some (GRLabel ref, args)
  | PProd (_, d, c), [] -> Some (ProdLabel, [d ; c])
  | PLambda (_, d, c), l -> Some (LambdaLabel, [d ; c] @ l)
  | PSort s, [] ->
      let s' = match s with
	| RProp c -> Some (Prop c)
	| RType (Some c) -> Some (Type c)
	| RType None -> None
      in Some (SortLabel s', [])
  | _ -> None

open Dn

let constr_val_discr t =
  let c, l = decomp t in
    match kind_of_term c with
    | Ind ind_sp -> Label(GRLabel (IndRef ind_sp),l)
    | Construct cstr_sp -> Label(GRLabel (ConstructRef cstr_sp),l)
    | Var id -> Label(GRLabel (VarRef id),l)
    | Const _ -> Everything
    | _ -> Nothing

let constr_val_discr_st (idpred,cpred) t =
  let c, l = decomp t in
    match kind_of_term c with
    | Const c -> if Cpred.mem c cpred then Everything else Label(GRLabel (ConstRef c),l)
    | Ind ind_sp -> Label(GRLabel (IndRef ind_sp),l)
    | Construct cstr_sp -> Label(GRLabel (ConstructRef cstr_sp),l)
    | Var id when not (Idpred.mem id idpred) -> Label(GRLabel (VarRef id),l)
    | Prod (n, d, c) -> Label(ProdLabel, [d; c])
    | Lambda (n, d, c) -> Label(LambdaLabel, [d; c] @ l)
    | Sort s -> Label(SortLabel (Some s), [])
    | Evar _ -> Everything
    | _ -> Nothing

let create = Dn.create

let add dn st = Dn.add dn (constr_pat_discr_st st)

let rmv dn st = Dn.rmv dn (constr_pat_discr_st st)

let lookup dn st t = Dn.lookup dn (constr_val_discr_st st) t

let app f dn = Dn.app f dn
