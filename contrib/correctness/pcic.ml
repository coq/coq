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
open Declarations

open Pmisc
open Past


(* Here we translate intermediates terms (cc_term) into CCI terms (constr) *)

let make_hole c = mkCast (isevar, c)

(* Tuples are defined in file Tuples.v 
 * and their constructors are called Build_tuple_n or exists_n,
 * wether they are dependant (last element only) or not. 
 * If necessary, tuples are generated ``on the fly''. *)

let tuple_exists id =
  try let _ = Nametab.sp_of_id CCI id in true with Not_found -> false

let ast_set = Ast.ope ("PROP", [ Ast.ide "Pos" ])

let tuple_n n =
  let name = "tuple_" ^ string_of_int n in
  let id = id_of_string name in
  let l1n = Util.interval 1 n in
  let params = 
    List.map 
      (fun i -> let id = id_of_string ("T" ^ string_of_int i) in (id, ast_set))
      l1n
  in
  let fields = 
    List.map
      (fun i -> 
	 let id = id_of_string 
		    ("proj_" ^ string_of_int n ^ "_" ^ string_of_int i) in
	 (false, (id, true, Ast.nvar ("T" ^ string_of_int i))))
      l1n 
  in
  let cons = id_of_string ("Build_tuple_" ^ string_of_int n) in
  Record.definition_structure (false, id, params, fields, cons, mk_Set)

(*s [(sig_n n)] generates the inductive
    \begin{verbatim}
    Inductive sig_n [T1,...,Tn:Set; P:T1->...->Tn->Prop] : Set :=
      exist_n : (x1:T1)...(xn:Tn)(P x1 ... xn) -> (sig_n T1 ... Tn P).
    \end{verbatim} *)

let sig_n n =
  let name = "sig_" ^ string_of_int n in
  let id = id_of_string name in
  let l1n = Util.interval 1 n in
  let lT = List.map (fun i -> id_of_string ("T" ^ string_of_int i)) l1n in
  let lx = List.map (fun i -> id_of_string ("x" ^ string_of_int i)) l1n in
  let idp = id_of_string "P" in
  let params =
    let typ = List.fold_right (fun _ c -> mkArrow (mkRel n) c) lT mkProp in
    (idp, LocalAssum typ) :: 
    (List.rev_map (fun id -> (id, LocalAssum mkSet)) lT)
  in
  let lc = 
    let app_sig = mkAppA (Array.init (n+2) (fun i -> mkRel (2*n+3-i))) in
    let app_p = mkAppA (Array.init (n+1) (fun i -> mkRel (n+1-i))) in
    let c = mkArrow app_p app_sig in
    List.fold_right (fun id c -> mkProd (Name id, mkRel (n+1), c)) lx c
  in
  let cname = id_of_string ("exist_" ^ string_of_int n) in
  Declare.declare_mind 
    { mind_entry_finite = true;
      mind_entry_inds = 
	[ { mind_entry_nparams = succ n;
	    mind_entry_params = params;
	    mind_entry_typename = id;
	    mind_entry_arity = mkSet;
	    mind_entry_consnames = [ cname ];
	    mind_entry_lc = [ lc ] } ] }
	
let tuple_name dep n =
  if n = 2 & not dep then
    "pair"
  else
    let n = n - (if dep then 1 else 0) in
    if dep then
      if n = 1 then 
	"exist" 
      else begin
	let name = Printf.sprintf "exist_%d" n in
	if not (tuple_exists (id_of_string name)) then ignore (sig_n n);
	name
      end
    else begin
      let name = Printf.sprintf "Build_tuple_%d" n in
      if not (tuple_exists (id_of_string name)) then tuple_n n;
      name
    end

(* Binders. *)

let trad_binding bl =
  List.map (function
		(id,CC_untyped_binder) -> (id,isevar)
	      | (id,CC_typed_binder ty) -> (id,ty)) bl

let lambda_of_bl bl c =
  let b = trad_binding bl in n_lambda c (List.rev b)

(* The translation itself is quite easy.
   letin are translated into Cases construtions *)

let constr_of_prog p =
  let rec trad = function
    | CC_var id -> mkVar id

    (* optimisation : let x = <constr> in e2  =>  e2[x<-constr] *)
    | CC_letin (_,_,[id,_],(CC_expr c,_),e2) ->
	real_subst_in_constr [id,c] (trad e2)

    | CC_letin (_,_,([_] as b),(e1,_),e2) ->
      	let c = trad e1 and c2 = trad e2 in
	Term.applist (lambda_of_bl b c2, [c])

    | CC_letin (dep,ty,bl,(e,info),e1) ->
	let c1 = trad e1
	and c = trad e in
	let l = [| lambda_of_bl bl c1 |] in
	Term.mkMutCase (info, ty, c, l)

    | CC_lam (bl,e) ->
	let c = trad e in lambda_of_bl bl c

    | CC_app (f,args) ->
	let c = trad f
	and cargs = List.map trad args in
	Term.applist (c,cargs)

    | CC_tuple (_,_,[e]) -> trad e
	
    | CC_tuple (false,_,[e1;e2]) ->
	let c1 = trad e1 
	and c2 = trad e2 in
	Term.applist (constant "pair", [isevar;isevar;c1;c2])

    | CC_tuple (dep,tyl,l) ->
      	let n = List.length l in
      	let cl = List.map trad l in
      	let name = tuple_name dep n in
      	let args = tyl @ cl in
	Term.applist (constant name,args)

    | CC_case (ty,(b,info),el) ->
	let c = trad b in
	let cl = List.map trad el in
	mkMutCase (info, ty, c, Array.of_list cl)

    | CC_expr c -> c

    | CC_hole c -> make_hole c

  in
  trad p
