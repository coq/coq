
(* $Id$ *)

open Util
open Names
open Term
open Sign

(* The type of mappings for existential variables *)

type evar_body =
    EVAR_EMPTY | EVAR_DEFINED of constr

type 'a evar_info = {
  concl : constr;            (* the type of the evar ...          *)
  hyps  : context;           (* ... under a certain signature     *)
  body  : evar_body;         (* its definition                    *) 
  info  : 'a option          (* any other necessary information   *)
}         

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
    { concl = typ;
      hyps  = sign;
      body  = EVAR_EMPTY;
      info  = None}
  in 
  Spmap.add sp newinfo evd

let define evd sp body = 
 let oldinfo = map evd sp in
 let newinfo =
   { concl = oldinfo.concl;
     hyps  = oldinfo.hyps;
     body  = EVAR_DEFINED body;
     info  = oldinfo.info} 
 in
 match oldinfo.body with
   | EVAR_EMPTY -> Spmap.add sp newinfo evd
   | _ -> anomaly "cannot define an isevar twice"

(* The list of non-instantiated existential declarations *)

let non_instantiated sigma = 
    let listsp = toList sigma in
    List.fold_left 
        (fun l ((sp,evd) as d) -> if evd.body = EVAR_EMPTY then (d::l) else l)
        [] listsp

let is_evar sigma sp = in_dom sigma sp
