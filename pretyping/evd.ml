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
open Environ

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
    
let is_evar sigma ev = in_dom sigma ev

let is_defined sigma ev =
  let info = map sigma ev in 
  not (info.evar_body = Evar_empty)

let evar_body ev = ev.evar_body

let string_of_existential ev = "?" ^ string_of_int ev

let existential_of_int ev = ev

(*******************************************************************)
(* Formerly Instantiate module *)

let is_id_inst inst =
  let is_id (id,c) = match kind_of_term c with
    | Var id' -> id = id'
    | _ -> false
  in
  List.for_all is_id inst

(* Vérifier que les instances des let-in sont compatibles ?? *)
let instantiate_sign_including_let sign args =
  let rec instrec = function
    | ((id,b,_) :: sign, c::args) -> (id,c) :: (instrec (sign,args))
    | ([],[])                        -> []
    | ([],_) | (_,[]) ->
    anomaly "Signature and its instance do not match"
  in 
  instrec (sign,args)

let instantiate_evar sign c args =
  let inst = instantiate_sign_including_let sign args in
  if is_id_inst inst then
    c
  else
    replace_vars inst c

(* Existentials. *)

let existential_type sigma (n,args) =
  let info =
    try map sigma n
    with Not_found ->
      anomaly ("Evar "^(string_of_existential n)^" was not declared") in
  let hyps = info.evar_hyps in
  instantiate_evar hyps info.evar_concl (Array.to_list args)

exception NotInstantiatedEvar

let existential_value sigma (n,args) =
  let info = map sigma n in
  let hyps = info.evar_hyps in
  match evar_body info with
    | Evar_defined c ->
	instantiate_evar hyps c (Array.to_list args)
    | Evar_empty ->
	raise NotInstantiatedEvar

let existential_opt_value sigma ev =
  try Some (existential_value sigma ev)
  with NotInstantiatedEvar -> None

(*******************************************************************)
(* The type constructor ['a sigma] adds an evar map to an object of
  type ['a] *)
type 'a sigma = {
  it : 'a ;
  sigma : evar_map}
 
let sig_it x = x.it
let sig_sig x = x.sigma
 
(*******************************************************************)
(* Metamaps *)

(*******************************************************************)
(*            Constraints for existential variables                *)
(*******************************************************************)

type 'a freelisted = {
  rebus : 'a;
  freemetas : Intset.t }

(* Collects all metavars appearing in a constr *)
let metavars_of c =
  let rec collrec acc c =
    match kind_of_term c with
      | Meta mv -> Intset.add mv acc
      | _         -> fold_constr collrec acc c
  in
  collrec Intset.empty c

let mk_freelisted c =
  { rebus = c; freemetas = metavars_of c }


(* Clausal environments *)

type clbinding =
  | Cltyp of constr freelisted
  | Clval of constr freelisted * constr freelisted

let map_fl f cfl = { cfl with rebus=f cfl.rebus }

let map_clb f = function
  | Cltyp cfl -> Cltyp (map_fl f cfl)
  | Clval (cfl1,cfl2) -> Clval (map_fl f cfl1,map_fl f cfl2)

(***********************)
                                                                               
module Metaset = Intset
                                                                               
let meta_exists p s = Metaset.fold (fun x b -> (p x) || b) s false

module Metamap = Intmap

let metamap_in_dom x m =
  try let _ = Metamap.find x m in true with Not_found -> false

                                                                               
let metamap_to_list m =
  Metamap.fold (fun n v l -> (n,v)::l) m []
 
let metamap_inv m b =
  Metamap.fold (fun n v l -> if v = b then n::l else l) m []
 
type meta_map = clbinding Metamap.t
 
let meta_defined env mv =
  match Metamap.find mv env with
    | Clval _ -> true
    | Cltyp _ -> false
 
let meta_fvalue env mv =
  match Metamap.find mv env with
    | Clval(b,_) -> b
    | Cltyp _ -> anomaly "meta_fvalue: meta has no value"
           
let meta_ftype env mv =
  match Metamap.find mv env with
    | Cltyp b -> b
    | Clval(_,b) -> b
 
let meta_declare mv v menv =
  Metamap.add mv (Cltyp(mk_freelisted v)) menv
  
let meta_assign mv v menv =
  Metamap.add mv (Clval(mk_freelisted v, meta_ftype menv mv)) menv
