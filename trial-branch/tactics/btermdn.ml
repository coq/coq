(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Term
open Termdn
open Pattern
open Libnames

(* Discrimination nets with bounded depth.
   See the module dn.ml for further explanations.
   Eduardo (5/8/97). *)

let dnet_depth = ref 8
		   
let bounded_constr_pat_discr (t,depth) =
  if depth = 0 then 
    None 
  else
    match constr_pat_discr t with
      | None -> None
      | Some (c,l) -> Some(c,List.map (fun c -> (c,depth-1)) l)
	    
let bounded_constr_val_discr (t,depth) =
  if depth = 0 then 
    None 
  else
    match constr_val_discr t with
      | None -> None
      | Some (c,l) -> Some(c,List.map (fun c -> (c,depth-1)) l)

type 'a t = (global_reference,constr_pattern * int,'a) Dn.t

let create = Dn.create

let add dn (c,v) = Dn.add dn bounded_constr_pat_discr ((c,!dnet_depth),v)

let rmv dn (c,v) = Dn.rmv dn bounded_constr_pat_discr ((c,!dnet_depth),v)

let lookup dn t =
  List.map 
    (fun ((c,_),v) -> (c,v)) 
    (Dn.lookup dn bounded_constr_val_discr (t,!dnet_depth))

let app f dn = Dn.app (fun ((c,_),v) -> f(c,v)) dn

