
(* $Id$ *)

open Term
open Termdn

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

type 'a t = (lbl,constr * int,'a) Dn.under_t

let newdn () = Dn.create bounded_constr_pat_discr

let ex_termdn = newdn()

let inDN tdn = { 
  Dn.args = ex_termdn.Dn.args;
  Dn.tm = tdn }

let outDN dn = dn.Dn.tm

let create () = outDN (newdn())

let add dn (c,v) = outDN (Dn.add (inDN dn) ((c,!dnet_depth),v))

let rmv dn (c,v) = outDN (Dn.rmv (inDN dn) ((c,!dnet_depth),v))

let lookup dn t = 
  List.map 
    (fun ((c,_),v) -> (c,v)) 
    (Dn.lookup (inDN dn) bounded_constr_val_discr (t,!dnet_depth))

let app f dn = Dn.app (fun ((c,_),v) -> f(c,v)) (inDN dn)
