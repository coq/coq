(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Term
open Names
open Termdn
open Pattern
open Libnames

(* Discrimination nets with bounded depth.
   See the module dn.ml for further explanations.
   Eduardo (5/8/97). *)

let dnet_depth = ref 8


module Make =
  functor (Z : Map.OrderedType) ->
struct
  module Term_dn = Termdn.Make(Z)

  module X = struct
    type t = constr_pattern*int
    let compare = Pervasives.compare 
  end

 module Y = struct 
     type t = Term_dn.term_label
     let compare x y = 
       let make_name n =
	 match n with
	 | Term_dn.GRLabel(ConstRef con) -> 
	     Term_dn.GRLabel(ConstRef(constant_of_kn(canonical_con con)))
	 | Term_dn.GRLabel(IndRef (kn,i)) ->
	     Term_dn.GRLabel(IndRef(mind_of_kn(canonical_mind kn),i))
	 | Term_dn.GRLabel(ConstructRef ((kn,i),j ))->
	     Term_dn.GRLabel(ConstructRef((mind_of_kn(canonical_mind kn),i),j))
	 | k -> k
       in
	 Pervasives.compare (make_name x) (make_name y)
 end
 
 module Dn = Dn.Make(X)(Y)(Z)
  
 type t = Dn.t

  let create = Dn.create

  let decomp = 
    let rec decrec acc c = match kind_of_term c with
      | App (f,l) -> decrec (Array.fold_right (fun a l -> a::l) l acc) f
      | Cast (c1,_,_) -> decrec acc c1
      | _ -> (c,acc)
    in 
      decrec []

  let constr_val_discr t =
    let c, l = decomp t in
      match kind_of_term c with
      | Ind ind_sp -> Dn.Label(Term_dn.GRLabel (IndRef ind_sp),l)
      | Construct cstr_sp -> Dn.Label(Term_dn.GRLabel (ConstructRef cstr_sp),l)
      | Var id -> Dn.Label(Term_dn.GRLabel (VarRef id),l)
      | Const _ -> Dn.Everything
      | _ -> Dn.Nothing
	
  let constr_val_discr_st (idpred,cpred) t =
    let c, l = decomp t in
      match kind_of_term c with
      | Const c -> if Cpred.mem c cpred then Dn.Everything else Dn.Label(Term_dn.GRLabel (ConstRef c),l)
      | Ind ind_sp -> Dn.Label(Term_dn.GRLabel (IndRef ind_sp),l)
      | Construct cstr_sp -> Dn.Label(Term_dn.GRLabel (ConstructRef cstr_sp),l)
      | Var id when not (Idpred.mem id idpred) -> Dn.Label(Term_dn.GRLabel (VarRef id),l)
      | Prod (n, d, c) -> Dn.Label(Term_dn.ProdLabel, [d; c])
      | Lambda (n, d, c) -> Dn.Label(Term_dn.LambdaLabel, [d; c] @ l)
      | Sort s when is_small s -> Dn.Label(Term_dn.SortLabel (Some s), [])
      | Sort _ -> Dn.Label(Term_dn.SortLabel None, [])
      | Evar _ -> Dn.Everything
      | _ -> Dn.Nothing

  let bounded_constr_pat_discr_st st (t,depth) =
    if depth = 0 then 
      None 
    else
      match Term_dn.constr_pat_discr_st st t with
	| None -> None
	| Some (c,l) -> Some(c,List.map (fun c -> (c,depth-1)) l)
	    
  let bounded_constr_val_discr_st st (t,depth) =
    if depth = 0 then 
      Dn.Nothing 
    else
      match constr_val_discr_st st t with
	| Dn.Label (c,l) -> Dn.Label(c,List.map (fun c -> (c,depth-1)) l)
	| Dn.Nothing -> Dn.Nothing
	| Dn.Everything -> Dn.Everything

  let bounded_constr_pat_discr (t,depth) =
    if depth = 0 then 
      None 
    else
      match Term_dn.constr_pat_discr t with
	| None -> None
	| Some (c,l) -> Some(c,List.map (fun c -> (c,depth-1)) l)
	    
  let bounded_constr_val_discr (t,depth) =
    if depth = 0 then 
      Dn.Nothing 
    else
      match constr_val_discr t with
	| Dn.Label (c,l) -> Dn.Label(c,List.map (fun c -> (c,depth-1)) l)
	| Dn.Nothing -> Dn.Nothing
	| Dn.Everything -> Dn.Everything
	    
	    
  let add = function
    | None -> 
	(fun dn (c,v) -> 
	   Dn.add dn bounded_constr_pat_discr ((c,!dnet_depth),v))
    | Some st -> 
	(fun dn (c,v) -> 
	   Dn.add dn (bounded_constr_pat_discr_st st) ((c,!dnet_depth),v))
	  
  let rmv = function
    | None -> 
	(fun dn (c,v) -> 
	   Dn.rmv dn bounded_constr_pat_discr ((c,!dnet_depth),v))
    | Some st -> 
	(fun dn (c,v) -> 
	 Dn.rmv dn (bounded_constr_pat_discr_st st) ((c,!dnet_depth),v))
	  
  let lookup = function
    | None -> 
	(fun dn t ->
	   List.map 
	     (fun ((c,_),v) -> (c,v)) 
	     (Dn.lookup dn bounded_constr_val_discr (t,!dnet_depth)))
    | Some st -> 
	(fun dn t ->
	   List.map 
	     (fun ((c,_),v) -> (c,v)) 
	     (Dn.lookup dn (bounded_constr_val_discr_st st) (t,!dnet_depth)))
	  
  let app f dn = Dn.app (fun ((c,_),v) -> f(c,v)) dn
    
end
    
