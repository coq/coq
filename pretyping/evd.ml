(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Sign
open Environ
open Libnames
open Mod_subst

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
let fold = Evarmap.fold

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
let evar_env evd = Global.env_of_context evd.evar_hyps

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
type open_constr = evar_map * constr

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

let map_fl f cfl = { cfl with rebus=f cfl.rebus }


(* Clausal environments *)

type clbinding =
  | Cltyp of name * constr freelisted
  | Clval of name * constr freelisted * constr freelisted

let map_clb f = function
  | Cltyp (na,cfl) -> Cltyp (na,map_fl f cfl)
  | Clval (na,cfl1,cfl2) -> Clval (na,map_fl f cfl1,map_fl f cfl2)

(* name of defined is erased (but it is pretty-printed) *)
let clb_name = function
    Cltyp(na,_) -> (na,false)
  | Clval (na,_,_) -> (na,true)

(***********************)
                                                                               
module Metaset = Intset
                                                                               
let meta_exists p s = Metaset.fold (fun x b -> b || (p x)) s false

module Metamap = Intmap

let metamap_to_list m =
  Metamap.fold (fun n v l -> (n,v)::l) m []
 
(*************************)
(* Unification state *)

type hole_kind =
  | ImplicitArg of global_reference * (int * identifier option)
  | BinderType of name
  | QuestionMark
  | CasesType
  | InternalHole
  | TomatchTypeParameter of inductive * int

type conv_pb = Reduction.conv_pb
type evar_constraint = conv_pb * constr * constr
type evar_defs =
    { evars : evar_map;
      conv_pbs : evar_constraint list;
      history : (existential_key * (loc * hole_kind)) list;
      metas : clbinding Metamap.t }

let subst_evar_defs sub evd =
  { evd with
    conv_pbs =
      List.map (fun (k,t1,t2) ->(k,subst_mps sub t1,subst_mps sub t2))
        evd.conv_pbs;
    metas = Metamap.map (map_clb (subst_mps sub)) evd.metas }

let create_evar_defs sigma =
  { evars=sigma; conv_pbs=[]; history=[]; metas=Metamap.empty }
let evars_of d = d.evars
let evars_reset_evd evd d = {d with evars = evd}
let reset_evd (sigma,mmap) d = {d with evars = sigma; metas=mmap}
let add_conv_pb pb d = {d with conv_pbs = pb::d.conv_pbs}
let evar_source ev d =
  try List.assoc ev d.history
  with Not_found -> (dummy_loc, InternalHole)

(* define the existential of section path sp as the constr body *)
let evar_define sp body isevars =
  (* needed only if an inferred type *)
  let body = refresh_universes body in
  {isevars with evars = define isevars.evars sp body}


let evar_declare hyps evn ty ?(src=(dummy_loc,InternalHole)) evd =
  { evd with
    evars = add evd.evars evn
      {evar_hyps=hyps; evar_concl=ty; evar_body=Evar_empty};
    history = (evn,src)::evd.history }

let is_defined_evar isevars (n,_) = is_defined isevars.evars n

(* Does k corresponds to an (un)defined existential ? *)
let is_undefined_evar isevars c = match kind_of_term c with
  | Evar ev -> not (is_defined_evar isevars ev)
  | _ -> false


(* extracts conversion problems that satisfy predicate p *)
(* Note: conv_pbs not satisying p are stored back in reverse order *)
let get_conv_pbs isevars p =
  let (pbs,pbs1) = 
    List.fold_left
      (fun (pbs,pbs1) pb ->
    	 if p pb then 
	   (pb::pbs,pbs1)
         else 
	   (pbs,pb::pbs1))
      ([],[])
      isevars.conv_pbs
  in
  {isevars with conv_pbs = pbs1},
  pbs

(**********************************************************)
(* Accessing metas *)

let meta_list evd = metamap_to_list evd.metas

let meta_defined evd mv =
  match Metamap.find mv evd.metas with
    | Clval _ -> true
    | Cltyp _ -> false
 
let meta_fvalue evd mv =
  match Metamap.find mv evd.metas with
    | Clval(_,b,_) -> b
    | Cltyp _ -> anomaly "meta_fvalue: meta has no value"
           
let meta_ftype evd mv =
  match Metamap.find mv evd.metas with
    | Cltyp (_,b) -> b
    | Clval(_,_,b) -> b
 
let meta_declare mv v ?(name=Anonymous) evd =
  { evd with metas = Metamap.add mv (Cltyp(name,mk_freelisted v)) evd.metas }
  
let meta_assign mv v evd =
  match Metamap.find mv evd.metas with
      Cltyp(na,ty) ->
        { evd with
          metas = Metamap.add mv (Clval(na,mk_freelisted v, ty)) evd.metas }
    | _ -> anomaly "meta_assign: already defined"

(* If the meta is defined then forget its name *)
let meta_name evd mv =
  try
    let (na,def) = clb_name (Metamap.find mv evd.metas) in
    if def then Anonymous else na
  with Not_found -> Anonymous

let meta_with_name evd id =
  let na = Name id in
  let (mvl,mvnodef) =
    Metamap.fold
      (fun n clb (l1,l2 as l) ->
        let (na',def) = clb_name clb in
        if na = na' then if def then (n::l1,l2) else (n::l1,n::l2)
        else l)
      evd.metas ([],[]) in
  match mvnodef, mvl with
    | _,[]  -> 
	errorlabstrm "Evd.meta_with_name"
          (str"No such bound variable " ++ pr_id id)
    | ([n],_|_,[n]) -> 
	n
    | _  -> 
	errorlabstrm "Evd.meta_with_name"
          (str "Binder name \"" ++ pr_id id ++
           str"\" occurs more than once in clause")


let meta_merge evd1 evd2 =
  {evd2 with
    metas = List.fold_left (fun m (n,v) -> Metamap.add n v m) 
      evd2.metas (metamap_to_list evd1.metas) }


(**********************************************************)
(* Pretty-printing *)

let pr_meta_map mmap =
  let pr_name = function
      Name id -> str"[" ++ pr_id id ++ str"]"
    | _ -> mt() in
  let pr_meta_binding = function
    | (mv,Cltyp (na,b)) ->
      	hov 0 
	  (pr_meta mv ++ pr_name na ++ str " : " ++
           print_constr b.rebus ++ fnl ())
    | (mv,Clval(na,b,_)) ->
      	hov 0 
	  (pr_meta mv ++ pr_name na ++ str " := " ++
           print_constr b.rebus ++ fnl ())
  in
  prlist pr_meta_binding (metamap_to_list mmap)

let pr_idl idl = prlist_with_sep pr_spc pr_id idl

let pr_evar_info evi =
  let phyps = pr_idl (List.rev (ids_of_named_context evi.evar_hyps)) in
  let pty = print_constr evi.evar_concl in
  let pb =
    match evi.evar_body with
      | Evar_empty -> mt ()
      | Evar_defined c -> spc() ++ str"=> "  ++ print_constr c
  in
  hov 2 (str"["  ++ phyps ++ spc () ++ str"|- "  ++ pty ++ pb ++ str"]")

let pr_evar_map sigma =
  h 0 
    (prlist_with_sep pr_fnl
      (fun (ev,evi) ->
        h 0 (str(string_of_existential ev)++str"=="++ pr_evar_info evi))
      (to_list sigma))

let pr_evar_defs evd =
  let pp_evm =
    if evd.evars = empty then mt() else
      str"EVARS:"++brk(0,1)++pr_evar_map evd.evars++fnl() in
  let n = List.length evd.conv_pbs in
  let cstrs =
    if n=0 then mt() else
      str"=> " ++ int n ++ str" constraints" ++ fnl() ++ fnl() in
  let pp_met =
    if evd.metas = Metamap.empty then mt() else
      str"METAS:"++brk(0,1)++pr_meta_map evd.metas in
  v 0 (pp_evm ++ cstrs ++ pp_met)
