
(* $Id$ *)

open Util
open Names
open Term
open Sign

(* The type of mappings for existential variables *)

type evar_body =
  | EVAR_EMPTY 
  | EVAR_DEFINED of constr

type 'a evar_info = {
  evar_concl : typed_type;           (* the type of the evar ...          *)
  evar_hyps  : typed_type signature; (* ... under a certain signature     *)
  evar_body  : evar_body;            (* its definition                    *) 
  evar_info  : 'a option }           (* any other necessary information   *)

type 'a evar_map = 'a evar_info Spmap.t

let mt_evd = Spmap.empty

let toList evc = Spmap.fold (fun sp x acc -> (sp,x)::acc) evc []
let dom evc = Spmap.fold (fun sp _ acc -> sp::acc) evc []
let map evc k = Spmap.find k evc
let rmv evc k = Spmap.remove k evc
let remap evc k i = Spmap.add k i evc
let in_dom evc k = Spmap.mem k evc

let add_with_info evd sp newinfo = 
  Spmap.add sp newinfo evd

let add_noinfo evd sp sign typ = 
  let newinfo = 
    { evar_concl = typ;
      evar_hyps  = sign;
      evar_body  = EVAR_EMPTY;
      evar_info  = None}
  in 
  Spmap.add sp newinfo evd

let define evd sp body = 
  let oldinfo = map evd sp in
  let newinfo =
    { evar_concl = oldinfo.evar_concl;
      evar_hyps  = oldinfo.evar_hyps;
      evar_body  = EVAR_DEFINED body;
      evar_info  = oldinfo.evar_info} 
  in
  match oldinfo.evar_body with
    | EVAR_EMPTY -> Spmap.add sp newinfo evd
    | _ -> anomaly "cannot define an isevar twice"

(* The list of non-instantiated existential declarations *)

let non_instantiated sigma = 
  let listsp = toList sigma in
  List.fold_left 
    (fun l ((sp,evd) as d) -> 
       if evd.evar_body = EVAR_EMPTY then (d::l) else l)
    [] listsp
    
let is_evar sigma sp = in_dom sigma sp

let is_defined sigma sp =
  let info = map sigma sp in not (info.evar_body = EVAR_EMPTY)
