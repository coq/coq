(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Names
open Term

open Ptype
open Past
open Penv

let cci_global id =
  try
    Declare.global_reference CCI id
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
    Perror.unbound_reference id (Some loc)

(* db types  : just do nothing for the moment ! *)

let rec db_type_v ids = function
  | Ref v -> Ref (db_type_v ids v)
  | Array (c,v) -> Array (c,db_type_v ids v)
  | Arrow (bl,c) -> Arrow (List.map (db_binder ids) bl, db_type_c ids c)
  | TypePure _ as v -> v
and db_type_c ids ((id,v),e,p,q) =
  (id,db_type_v ids v), e, p, q
  (* TODO: db_condition ? *)
and db_binder ids = function
    (n, BindType v) -> (n, BindType (db_type_v ids v))
  | b -> b

(* db binders *)

let rec db_binders ((tids,pids,refs) as idl) = function
    [] -> idl, []
  | (id, BindType (Ref _ | Array _ as v)) :: rem ->
      let idl',rem' = db_binders (tids,pids,id::refs) rem in
      idl', (id, BindType (db_type_v tids v)) :: rem'
  | (id, BindType v) :: rem ->
      let idl',rem' = db_binders (tids,id::pids,refs) rem in
      idl', (id, BindType (db_type_v tids v)) :: rem'
  | ((id, BindSet) as t) :: rem ->
      let idl',rem' = db_binders (id::tids,pids,refs) rem in
      idl', t :: rem'
  | a :: rem ->
      let idl',rem' = db_binders idl rem in idl', a :: rem'


(* db patterns *)

let rec db_pattern = function
  | (PatVar id) as t ->
      (try 
	 (match Nametab.sp_of_id CCI id with
	    | ConstructRef (x,y) -> [], PatConstruct (id,(x,y))
	    | _                  -> [id],t)
       with Not_found -> [id],t)
  | PatAlias (p,id) ->
      let ids,p' = db_pattern p in ids,PatAlias (p',id)
  | PatPair (p1,p2) ->
      let ids1,p1' = db_pattern p1 in
      let ids2,p2' = db_pattern p2 in
      	ids1@ids2, PatPair (p1',p2')
  | PatApp pl ->
      let ids,pl' =
	List.fold_right
	  (fun p (ids,pl) ->
	     let ids',p' = db_pattern p in ids'@ids,p'::pl) pl ([],[]) in
  	ids,PatApp pl'
  | PatConstruct _ ->
      failwith "constructor in a pattern after parsing !"


(* db programs *)
  
let db_prog e =
  (* tids = type identifiers, ids = variables, refs = references and arrays *)
  let rec db_desc ((tids,ids,refs) as idl) = function
      (Var x) as t ->
	(match lookup_var ids (Some e.loc) x with
	     None -> t
	   | Some c -> Expression c)
    | (Acc x) as t ->
	check_ref refs e.loc x;
	t
    | Aff (x,e1) ->
	check_ref refs e.loc x;
	Aff (x, db idl e1)
    | TabAcc (b,x,e1) ->
	check_ref refs e.loc x;
	TabAcc(b,x,db idl e1)
    | TabAff (b,x,e1,e2) ->
	check_ref refs e.loc x;
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
    | App (e1,l) ->
	App (db idl e1, List.map (db_arg idl) l)
    | SApp (dl,l) ->
	SApp (dl, List.map (db idl) l)
    | LetRef (x,e1,e2) ->
	LetRef (x, db idl e1, db (tids,ids,x::refs) e2)
    | LetIn (x,e1,e2) ->
	LetIn (x, db idl e1, db (tids,x::ids,refs) e2)
	  
    | LetRec (f,bl,v,var,e) ->
	let (tids',ids',refs'),bl' = db_binders idl bl in
	LetRec (f, bl, db_type_v tids' v, var, db (tids',f::ids',refs') e)
	  
    | Debug (s,e1) ->
	Debug (s, db idl e1)
	  
    | Expression _ as x -> x
    | PPoint (s,d) -> PPoint (s, db_desc idl d)
	  
  and db_arg ((tids,_,refs) as idl) = function
      Term ({ desc = Var id } as t) -> 
	if List.mem id refs then Refarg id else Term (db idl t)
    | Term t -> Term (db idl t)
    | Type v -> Type (db_type_v tids v)
    | Refarg _ -> assert false

  and db idl e =
    { desc = db_desc idl e.desc ;
      pre = e.pre; post = e.post;
      loc = e.loc; info = e.info }

  in
  let ids = Sign.ids_of_named_context (Global.named_context ()) in
            (* TODO: separer X:Set et x:V:Set
                     virer le reste (axiomes, etc.) *)
  let vars,refs = all_vars (), all_refs () in
  db ([],vars@ids,refs) e
;;

