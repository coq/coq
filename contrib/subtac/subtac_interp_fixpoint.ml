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
       
let abstract_constr_expr_bl abs c bl =
  List.fold_right (fun (n, t) c -> abs ([n], t, c)) bl c

let pr_binder_list b = 
  List.fold_right (fun ((loc, name), t) acc -> Nameops.pr_name name ++ str " : " ++
		     Ppconstr.pr_constr_expr t ++ spc () ++ acc) b (mt ()) 


let rec rewrite_rec_calls l c = c
(*
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
	  let before, after = list_chop n bls in
	  let _ = trace (str "Binders before the recursion arg: " ++ spc () ++
			 pr_binder_list before ++ str "; after the recursion arg: " ++
			 pr_binder_list after)
	  in
	  let ((locn, name) as lnid, ntyp), after = match after with
	      hd :: tl -> hd, tl
	    | _ -> assert(false) (* Rec arg must be in after *)
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
	  let wf_prop = (mkAppC (wfrel, [ mkIdentC nid'; mkIdentC nid ])) in
	  let lam_wf_prop = mkLambdaC ([lnid'], ntyp, wf_prop) in
	  let typnid' = mkSubset lnid' ntyp wf_prop in
	  let internal_type = 
	    abstract_constr_expr_bl mkProdC 
	      (mkProdC ([lnid'], typnid', 
			mkLetInC (lnid, mkProj1 ntyp lam_wf_prop (mkIdentC nid'), 
				  abstract_constr_expr_bl mkProdC typ after)))
	      before
	  in
	  let body' =
	    let body =
	      (* cast or we will loose some info at pretyping time as body
		 is a function *)
	      CCast (dummy_loc, body,  CastConv DEFAULTcast, typ) 
	    in
	    let body' = (* body abstracted by rec call *)
	      mkLambdaC ([(dummy_loc, Name id)], internal_type, body)
	    in
	      mkAppC (body',
		      [mkLambdaC 
			 ([lnid'], typnid',
			  mkAppC (mkIdentC id, 
				  [mkProj1 ntyp lam_wf_prop (mkIdentC nid');
				   (mkAppExplC (acc_inv_ref,
						[ ntyp; wfrel;
						  mkIdentC nid;
						  mkIdentC accproofid;
						  mkProj1 ntyp lam_wf_prop (mkIdentC nid');
						  mkProj2 ntyp lam_wf_prop (mkIdentC nid') ])) ]))])
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
			  (if tl = [] then [] else [LocalRawAssum (tl, typ)]) @
			  LocalRawAssum ([(dummy_loc, Name accproofid)], acctyp) ::
			    [LocalRawAssum (List.rev (x :: bl'), typ)]
			else aux' (x :: bl') tl
		    | [] -> [assum]
		  in aux (aux' [] bl @ acc) tl
	      | [] -> List.rev acc
	    in aux [] bl
	  in
	  let _ = trace (str "Rewrote fixpoint: " ++ Ppconstr.pr_id id ++ 
			 Ppconstr.pr_binders bl' ++ str " : " ++ 
			 Ppconstr.pr_constr_expr typ ++ str " := " ++ spc () ++
			 Ppconstr.pr_constr_expr body')
	  in (id, (succ n, ro), bl', typ, body'), decl

*)
