
(* $Id$ *)

open Util
open Names
open Term
open Sign
open Environ

(* The type of mappings for existential variables *)

type evar = int

let new_evar =
  let evar_ctr = ref 0 in
  fun () -> incr evar_ctr; !evar_ctr

type evar_body =
  | Evar_empty 
  | Evar_defined of constr

type 'a evar_info = {
  evar_concl : typed_type;
  evar_env : unsafe_env;
  evar_body : evar_body;
  evar_info : 'a }

type 'a evar_map = 'a evar_info Intmap.t

let empty = Intmap.empty

let to_list evc = Intmap.fold (fun ev x acc -> (ev,x)::acc) evc []
let dom evc = Intmap.fold (fun ev _ acc -> ev::acc) evc []
let map evc k = Intmap.find k evc
let rmv evc k = Intmap.remove k evc
let remap evc k i = Intmap.add k i evc
let in_dom evc k = Intmap.mem k evc

let add evd ev newinfo =  Intmap.add ev newinfo evd

let define evd ev body = 
  let oldinfo = map evd ev in
  let newinfo =
    { evar_concl = oldinfo.evar_concl;
      evar_env = oldinfo.evar_env;
      evar_body = Evar_defined body;
      evar_info = oldinfo.evar_info } 
  in
  match oldinfo.evar_body with
    | Evar_empty -> Intmap.add ev newinfo evd
    | _ -> anomaly "cannot define an isevar twice"

(* The list of non-instantiated existential declarations *)

let non_instantiated sigma = 
  let listev = to_list sigma in
  List.fold_left 
    (fun l ((ev,evd) as d) -> 
       if evd.evar_body = Evar_empty then (d::l) else l)
    [] listev
    
let is_evar sigma ev = in_dom sigma ev

let is_defined sigma ev =
  let info = map sigma ev in 
  not (info.evar_body = Evar_empty)

let metamap sigma = failwith "metamap : NOT YET IMPLEMENTED"

let evar_hyps ev = get_globals (context ev.evar_env)
