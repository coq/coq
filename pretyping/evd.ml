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
open Term
open Sign

(* The type of mappings for existential variables *)

type evar = existential_key

type evar_body =
  | Evar_empty 
  | Evar_defined of constr

type evar_info = {
  evar_concl : constr;
  evar_hyps : named_context;
  evar_body : evar_body}

module Evarmap = Intmap

type evar_map = evar_info Evarmap.t

let empty = Evarmap.empty

let to_list evc = Evarmap.fold (fun ev x acc -> (ev,x)::acc) evc []
let dom evc = Evarmap.fold (fun ev _ acc -> ev::acc) evc []
let map evc k = Evarmap.find k evc
let rmv evc k = Evarmap.remove k evc
let remap evc k i = Evarmap.add k i evc
let in_dom evc k = Evarmap.mem k evc

let add evd ev newinfo =  Evarmap.add ev newinfo evd

let define evd ev body = 
  let oldinfo = map evd ev in
  let newinfo =
    { evar_concl = oldinfo.evar_concl;
      evar_hyps = oldinfo.evar_hyps;
      evar_body = Evar_defined body} 
  in
  match oldinfo.evar_body with
    | Evar_empty -> Evarmap.add ev newinfo evd
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

let evar_body ev = ev.evar_body

let string_of_existential ev = "?" ^ string_of_int ev

let existential_of_int ev = ev
