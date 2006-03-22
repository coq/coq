open Global
open Pp
open Util
open Names
open Sign
open Evd
open Term
open Termops
open Reductionops
open Environ
open Type_errors
open Typeops
open Libnames
open Classops
open List
open Recordops 
open Evarutil
open Pretype_errors
open Rawterm
open Evarconv
open Pattern
open Dyn
open Topconstr

open Subtac_coercion
open Subtac_utils
open Coqlib
open Printer
open Subtac_errors
open Context
open Eterm


let mkAppExplC (f, args) = CAppExpl (dummy_loc, (None, f), args)

let mkSubset name typ prop = 
  mkAppExplC (sig_ref,
	      [ typ; mkLambdaC ([name], typ, prop) ])
	      
let mkProj1 u p x = 
  mkAppExplC (proj1_sig_ref, [ u; p; x ])

let mkProj2 u p x = 
  mkAppExplC (proj2_sig_ref, [ u; p; x ])

let list_of_local_binders l = 
  let rec aux acc = function
      Topconstr.LocalRawDef (n, c) :: tl -> aux ((n, c) :: acc) tl
    | Topconstr.LocalRawAssum (nl, c) :: tl -> 
	aux (List.fold_left (fun acc n -> (n, c) :: acc) acc nl) tl
    | [] -> List.rev acc
  in aux [] l
       
let abstract_constr_expr_bl c bl =
  List.fold_right (fun (n, t) c -> mkLambdaC ([n], t, c)) bl c

let pr_binder_list b = 
  List.fold_right (fun ((loc, name), t) acc -> Nameops.pr_name name ++ str " : " ++
		     Ppconstr.pr_constr_expr t ++ spc () ++ acc) b (mt ()) 


let rec rewrite_rec_calls l c = c

let rewrite_fixpoint env l (f, decl) = 
  let (id, (n, ro), bl, typ, body) = f in
  let body = rewrite_rec_calls l body in
    match ro with
	CStructRec -> ((id, (n, ro), bl, typ, body), decl)
      | CWfRec wfrel -> 
	  let bls = list_of_local_binders bl in
	  let _ = trace (str "Rewriting fixpoint: " ++ Ppconstr.pr_id id ++ 
			 Ppconstr.pr_binders bl ++ str " : " ++ 
			 Ppconstr.pr_constr_expr typ ++ str " := " ++ spc () ++
			 Ppconstr.pr_constr_expr body)
	  in
	  let after, before = list_chop n bls in
	  let _ = trace (str "Binders before the recursion arg: " ++ spc () ++
			 pr_binder_list before ++ str "; after the recursion arg: " ++
			 pr_binder_list after)
	  in
	  let ((locn, name), ntyp), before = match before with
	      hd :: tl -> hd, tl
	    | _ -> assert(false) (* Rec arg must be in before *)
	  in
	  let nid = match name with
	      Name id -> id
	    | Anonymous -> assert(false) (* Rec arg _must_ be named *)
	  in
	  let _wfproof = 
	    let _wf_rel = mkAppExplC (well_founded_ref, [ntyp; wfrel]) in
	      (*make_existential_expr dummy_loc before wf_rel*)
	      mkRefC lt_wf_ref
	  in
	  let nid', accproofid = 
	    let nid = string_of_id nid in
	      id_of_string (nid ^ "'"), id_of_string ("Acc_" ^ nid)
	  in
	  let lnid', laccproofid = (dummy_loc, Name nid'), (dummy_loc, Name accproofid) in
	  let coqP = abstract_constr_expr_bl typ after in
	  let body' =
	    let prop = (mkAppC (wfrel, [ mkIdentC nid'; mkIdentC nid ])) in
	    let lamprop = mkLambdaC ([lnid'], ntyp, prop) in
	    let typnid' = mkSubset lnid' ntyp prop in
	    let body' = (* body abstracted by rec call *)
	      mkLambdaC ([(dummy_loc, Name id)], 
			 mkProdC ([lnid'], typnid', coqP),
			 body)
	    in
	      mkAppC (body',
		      [mkLambdaC 
			 ([lnid'], typnid',
			  mkAppC (mkIdentC id, 
				  [mkProj1 ntyp lamprop (mkIdentC nid');
				   (mkAppExplC (acc_inv_ref,
						[ ntyp; wfrel;
						  mkIdentC nid;
						  mkIdentC accproofid;
						  mkProj1 ntyp lamprop (mkIdentC nid');
						  mkProj2 ntyp lamprop (mkIdentC nid') ])) ]))])
	  in
	  let acctyp = mkAppExplC (acc_ref, [ ntyp; wfrel; mkIdentC nid ]) in
	  let bl' = 
	    let rec aux acc = function
		Topconstr.LocalRawDef _ as x :: tl -> 
		  aux (x :: acc) tl
	      | Topconstr.LocalRawAssum (bl, typ) as assum :: tl ->
		  let rec aux' bl' = function
		      ((loc, name') as x) :: tl ->
			if name' = name then
			  LocalRawAssum (List.rev (x :: bl'), typ) ::
			    LocalRawAssum ([(dummy_loc, Name accproofid)], acctyp) ::
			    if tl = [] then [] else [LocalRawAssum (tl, typ)]
			else aux' (x :: bl') tl
		    | [] -> [assum]
		  in aux (acc @ List.rev (aux' [] bl)) tl
	      | [] -> List.rev acc
	    in aux [] bl
	  in
	  let _ = trace (str "Rewrote fixpoint: " ++ Ppconstr.pr_id id ++ 
			 Ppconstr.pr_binders bl' ++ str " : " ++ 
			 Ppconstr.pr_constr_expr typ ++ str " := " ++ spc () ++
			 Ppconstr.pr_constr_expr body')
	  in (id, (succ n, ro), bl', typ, body'), decl

let list_mapi f = 
  let rec aux i = function 
      hd :: tl -> f i hd :: aux (succ i) tl 
    | [] -> []
  in aux 0

let rewrite_cases_aux (loc, po, tml, eqns) =
  let tml = list_mapi (fun i (c, (n, opt)) -> c, 
		       ((match n with
			    Name id -> (match c with
					  | RVar (_, id') when id = id' ->
					      Name (id_of_string (string_of_id id ^ "'"))
					  | _ -> n)
			  | Anonymous -> Name (id_of_string ("x" ^ string_of_int i))),
			opt)) tml 
  in
  let mkHole = RHole (dummy_loc, InternalHole) in
  let mkeq c n = RApp (dummy_loc, RRef (dummy_loc, (Lazy.force eqind_ref)),
		       [mkHole; c; n])
  in
  let eqs_types = 
    List.map
      (fun (c, (n, _)) ->
	 let id = match n with Name id -> id | _ -> assert false in
	 let heqid = id_of_string ("Heq" ^ string_of_id id) in
	   Name heqid, mkeq c (RVar (dummy_loc, id)))
      tml
  in
  let po = 
    List.fold_right
      (fun (n,t) acc ->
	 RProd (dummy_loc, n, t, acc))
      eqs_types (match po with 
		     Some e -> e
		   | None -> mkHole)
  in
  let eqns =   
    List.map (fun (loc, idl, cpl, c) ->
		let c' = 
		  List.fold_left 
		    (fun acc (n, t) ->
		       RLambda (dummy_loc, n, t, acc))
		    c eqs_types
		in (loc, idl, cpl, c'))
      eqns
  in
  let mk_refl_equal c = RApp (dummy_loc, RRef (dummy_loc, Lazy.force refl_equal_ref),
			      [mkHole; c])
  in
  let refls = List.map (fun (c, _) -> mk_refl_equal c) tml in
  let case = RCases (loc,Some po,tml,eqns) in
  let app = RApp (dummy_loc, case, refls) in
    app

let rec rewrite_cases c = 
  match c with 
      RCases _ -> let c' = map_rawconstr rewrite_cases c in
	(match c' with 
	   | RCases (x, y, z, w) -> rewrite_cases_aux (x,y,z,w)
	   | _ -> assert(false))
    | _ -> map_rawconstr rewrite_cases c
	  
