(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Term
open Names
open Pattern
open Globnames

(* Discrimination nets with bounded depth.
   See the module dn.ml for further explanations.
   Eduardo (5/8/97). *)

let dnet_depth = ref 8


module Make =
  functor (Z : Map.OrderedType) ->
struct
  open Termdn

  module X = struct
    type t = constr_pattern*int
    let compare = Pervasives.compare (** FIXME *)
  end

 module Y = struct
    type t = term_label
    let compare = compare_term_label
 end

 type 'res lookup_res = 'res Dn.lookup_res = Label of 'res | Nothing | Everything

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
      | Var id when not (Id.Pred.mem id idpred) -> Label(GRLabel (VarRef id),l)
      | Prod (n, d, c) -> Label(ProdLabel, [d; c])
      | Lambda (n, d, c) -> Label(LambdaLabel, [d; c] @ l)
      | Sort _ -> Label(SortLabel, [])
      | Evar _ -> Everything
      | _ -> Nothing

  let bounded_constr_pat_discr_st st (t,depth) =
    if Int.equal depth 0 then
      None
    else
      match constr_pat_discr_st st t with
	| None -> None
	| Some (c,l) -> Some(c,List.map (fun c -> (c,depth-1)) l)

  let bounded_constr_val_discr_st st (t,depth) =
    if Int.equal depth 0 then
      Nothing
    else
      match constr_val_discr_st st t with
	| Label (c,l) -> Label(c,List.map (fun c -> (c,depth-1)) l)
	| Nothing -> Nothing
	| Everything -> Everything

  let bounded_constr_pat_discr (t,depth) =
    if Int.equal depth 0 then
      None
    else
      match constr_pat_discr t with
	| None -> None
	| Some (c,l) -> Some(c,List.map (fun c -> (c,depth-1)) l)

  let bounded_constr_val_discr (t,depth) =
    if Int.equal depth 0 then
      Nothing
    else
      match constr_val_discr t with
	| Label (c,l) -> Label(c,List.map (fun c -> (c,depth-1)) l)
	| Nothing -> Nothing
	| Everything -> Everything


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

