(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Names
open Term
open Termops
open Nametab
open Constrintern

open Ptype
open Past
open Penv

let cci_global id =
  try
    global_reference id
  with
    _ -> raise Not_found

let lookup_var ids locop id =
  if List.mem id ids then
    None
  else begin
    try Some (cci_global id)
    with Not_found -> Perror.unbound_variable id locop
  end

let check_ref idl loc id =
  if (not (List.mem id idl)) & (not (Penv.is_global id)) then
    Perror.unbound_reference id loc

(* db types : only check the references for the moment *)

let rec check_type_v refs = function
  | Ref v -> 
      check_type_v refs v
  | Array (c,v) -> 
      check_type_v refs v
  | Arrow (bl,c) -> 
      check_binder refs c bl
  | TypePure _ -> 
      ()

and check_type_c refs ((_,v),e,_,_) =
  check_type_v refs v;
  List.iter (check_ref refs None) (Peffect.get_reads e);
  List.iter (check_ref refs None) (Peffect.get_writes e)
  (* TODO: check_condition on p and q *)

and check_binder refs c = function
  | [] -> 
      check_type_c refs c
  | (id, BindType (Ref _ | Array _ as v)) :: bl -> 
      check_type_v refs v;
      check_binder (id :: refs) c bl
  | (_, BindType v) :: bl ->
      check_type_v refs v;
      check_binder refs c bl
  | _ :: bl -> 
      check_binder refs c bl

(* db binders *)

let rec db_binders ((tids,pids,refs) as idl) = function
  | [] -> 
      idl, []
  | (id, BindType (Ref _ | Array _ as v)) as b :: rem ->
      check_type_v refs v;
      let idl',rem' = db_binders (tids,pids,id::refs) rem in
      idl', b :: rem'
  | (id, BindType v) as b :: rem ->
      check_type_v refs v;
      let idl',rem' = db_binders (tids,id::pids,refs) rem in
      idl', b :: rem'
  | ((id, BindSet) as t) :: rem ->
      let idl',rem' = db_binders (id::tids,pids,refs) rem in
      idl', t :: rem'
  | a :: rem ->
      let idl',rem' = db_binders idl rem in idl', a :: rem'


(* db programs *)
  
let db_prog e =
  (* tids = type identifiers, ids = variables, refs = references and arrays *)
  let rec db_desc ((tids,ids,refs) as idl) = function
    | (Variable x) as t ->
	(match lookup_var ids (Some e.loc) x with
	     None -> t
	   | Some c -> Expression c)
    | (Acc x) as t ->
	check_ref refs (Some e.loc) x;
	t
    | Aff (x,e1) ->
	check_ref refs (Some e.loc) x;
	Aff (x, db idl e1)
    | TabAcc (b,x,e1) ->
	check_ref refs (Some e.loc) x;
	TabAcc(b,x,db idl e1)
    | TabAff (b,x,e1,e2) ->
	check_ref refs (Some e.loc) x;
	TabAff (b,x, db idl e1, db idl e2)
    | Seq bl ->
	Seq (List.map (function
			   Statement p -> Statement (db idl p)
			 | x -> x) bl)
    | If (e1,e2,e3) ->
	If (db idl e1, db idl e2, db idl e3)
    | While (b,inv,var,bl) ->
	let bl' = List.map (function
				Statement p -> Statement (db idl p)
			      | x -> x) bl in
	While (db idl b, inv, var, bl')
	  
    | Lam (bl,e) ->
	let idl',bl' = db_binders idl bl in Lam(bl', db idl' e)
    | Apply (e1,l) ->
	Apply (db idl e1, List.map (db_arg idl) l)
    | SApp (dl,l) ->
	SApp (dl, List.map (db idl) l)
    | LetRef (x,e1,e2) ->
	LetRef (x, db idl e1, db (tids,ids,x::refs) e2)
    | Let (x,e1,e2) ->
	Let (x, db idl e1, db (tids,x::ids,refs) e2)
	  
    | LetRec (f,bl,v,var,e) ->
	let (tids',ids',refs'),bl' = db_binders idl bl in
	check_type_v refs' v;
	LetRec (f, bl, v, var, db (tids',f::ids',refs') e)
	  
    | Debug (s,e1) ->
	Debug (s, db idl e1)
	  
    | Expression _ as x -> x
    | PPoint (s,d) -> PPoint (s, db_desc idl d)
	  
  and db_arg ((tids,_,refs) as idl) = function
    | Term ({ desc = Variable id } as t) -> 
	if List.mem id refs then Refarg id else Term (db idl t)
    | Term t -> Term (db idl t)
    | Type v as ty -> check_type_v refs v; ty
    | Refarg _ -> assert false

  and db idl e =
    { desc = db_desc idl e.desc ;
      pre = e.pre; post = e.post;
      loc = e.loc; info = e.info }

  in
  let ids = Termops.ids_of_named_context (Global.named_context ()) in
            (* TODO: separer X:Set et x:V:Set
                     virer le reste (axiomes, etc.) *)
  let vars,refs = all_vars (), all_refs () in
  db ([],vars@ids,refs) e
;;

