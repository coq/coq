
(* $Id$ *)

open Util
open Names
open Term
open Sign

(* The type of mappings for existential variables *)

type evar = int

let new_evar =
  let evar_ctr = ref 0 in
  fun () -> incr evar_ctr; !evar_ctr

type evar_body =
  | Evar_empty 
  | Evar_defined of constr

type evar_info = {
  evar_concl : typed_type;           (* the type of the evar ...          *)
  evar_hyps  : typed_type signature; (* ... under a certain signature     *)
  evar_body  : evar_body }           (* any other necessary information   *)

type evar_map = evar_info Intmap.t

let mt_evd = Intmap.empty

let to_list evc = Intmap.fold (fun sp x acc -> (sp,x)::acc) evc []
let dom evc = Intmap.fold (fun sp _ acc -> sp::acc) evc []
let map evc k = Intmap.find k evc
let rmv evc k = Intmap.remove k evc
let remap evc k i = Intmap.add k i evc
let in_dom evc k = Intmap.mem k evc

let add_with_info evd sp newinfo = 
  Intmap.add sp newinfo evd

let add_noinfo evd sp sign typ = 
  let newinfo = 
    { evar_concl = typ;
      evar_hyps  = sign;
      evar_body  = Evar_empty }
  in 
  Intmap.add sp newinfo evd

let define evd sp body = 
  let oldinfo = map evd sp in
  let newinfo =
    { evar_concl = oldinfo.evar_concl;
      evar_hyps  = oldinfo.evar_hyps;
      evar_body  = Evar_defined body } 
  in
  match oldinfo.evar_body with
    | Evar_empty -> Intmap.add sp newinfo evd
    | _ -> anomaly "cannot define an isevar twice"

(* The list of non-instantiated existential declarations *)

let non_instantiated sigma = 
  let listsp = to_list sigma in
  List.fold_left 
    (fun l ((sp,evd) as d) -> 
       if evd.evar_body = Evar_empty then (d::l) else l)
    [] listsp
    
let is_evar sigma sp = in_dom sigma sp

let is_defined sigma sp =
  let info = map sigma sp in not (info.evar_body = Evar_empty)
