(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Term
open Declarations
open Environ
open Reduction
open Inductive
open Modops
(*i*)

(* This local type is used to subtype a constant with a constructor or
   an inductive type. It can also be useful to allow reorderings in
   inductive types *)

type namedobject = 
  | Constant of constant_body
  | Mind of mutual_inductive_body
  | IndType of inductive * mutual_inductive_body
  | IndConstr of constructor * mutual_inductive_body
  | Module of module_specification_body
  | Modtype of module_type_body

(* adds above information about one mutual inductive: all types and
   constructors *)

let add_nameobjects_of_mib ln mib map = 
  let add_nameobjects_of_one j oib map =
    let ip = (ln,j) in
    let map = 
      array_fold_right_i 
	(fun i id map -> Idmap.add id (IndConstr ((ip,i), mib)) map)
	oib.mind_consnames
	map
    in
      Idmap.add oib.mind_typename (IndType (ip, mib)) map
  in
    array_fold_right_i add_nameobjects_of_one mib.mind_packets map

(* creates namedobject map for the whole signature *)

let make_label_map msid list = 
  let add_one (l,e) map = 
    let obj = 
      match e with
	| SPBconst cb -> Constant cb
	| SPBmind mib -> Mind mib
	| SPBmodule mb -> Module mb
	| SPBmodtype mtb -> Modtype mtb
    in
(*    let map = match obj with
      | Mind mib -> 
	  add_nameobjects_of_mib (make_ln (MPself msid) l) mib map
      | _ -> map
    in *)
      Labmap.add l obj map
  in
    List.fold_right add_one list Labmap.empty

let check_conv_error error f env a1 a2 =
  try
    f env a1 a2
  with
      NotConvertible -> error ()

(* for now we do not allow reorderings *)
let check_inductive env msid1 l info1 mib2 spec2 = 
  let kn = make_kn (MPself msid1) empty_dirpath l in
  let error () = error_not_match l spec2 in
  let check_conv f = check_conv_error error f in
  let mib1 = 
    match info1 with
      | Mind mib -> mib
    (*  | IndType (_,mib) -> mib   we will enable this later*)
      | _ -> error ()
  in
  let check_packet p1 p2 =
    let check f = if f p1 <> f p2 then error () in
      check (fun p -> p.mind_consnames);
      check (fun p -> p.mind_typename);
      (* nf_lc later *)
      (* nf_arity later *)
      (* user_lc ignored *)
      (* user_arity ignored *)
      check_conv conv_sort env p1.mind_sort p2.mind_sort;
      check (fun p -> p.mind_nrealargs);
      (* kelim ignored *)
      (* listrec ignored *)
      (* finite done *)
      (* nparams done *)
      (* params_ctxt done *)
      check_conv conv env p1.mind_nf_arity p2.mind_nf_arity;
      ()
  in
    (* this function uses mis_something and the others do not.
       Perhaps we should uniformize it at some point... *)
  let check_cons_types i p1 p2 =
    array_fold_left2 
      (fun _ t1 t2 -> check_conv conv env t1 t2; ()) 
      ()
      (arities_of_specif kn (mib1,p1))
      (arities_of_specif kn (mib2,p2))
  in
  let check f = if f mib1 <> f mib2 then error () in
    check (fun mib -> mib.mind_finite);
    check (fun mib -> mib.mind_ntypes);
    assert (mib1.mind_hyps=[] && mib2.mind_hyps=[]);
    assert (Array.length mib1.mind_packets >= 1 
	    && Array.length mib2.mind_packets >= 1);
    check (fun mib -> mib.mind_packets.(0).mind_nparams);
    check (fun mib -> mib.mind_packets.(0).mind_params_ctxt); 
         (* TODO: we should allow renaming of parameters at least ! *)
    match mib1.mind_singl, mib2.mind_singl with
	None, None -> ()
      | Some c1, Some c2 -> check_conv conv env c1 c2; ()
      | _ -> error () ;
    (* we first check simple things *)
    for i=0 to mib1.mind_ntypes-1 do 
      check_packet mib1.mind_packets.(i) mib2.mind_packets.(i)
    done;
    (* and constructor types in the end *)
    for i=0 to mib1.mind_ntypes-1 do 
      check_cons_types i mib1.mind_packets.(i) mib2.mind_packets.(i)
    done
    
    (* TODO: constraints ? *)

let check_constant env msid1 l info1 cb2 spec2 = 
  let error () = error_not_match l spec2 in
  let check_conv f = check_conv_error error f in
  let cb1 = 
    match info1 with
      | Constant cb -> cb
      | _ -> error ()
  in 
    assert (cb1.const_hyps=[] && cb2.const_hyps=[]) ;
      (* TODO: we should think about universes!!!! *)
    check_conv conv env cb1.const_type cb2.const_type;
    match cb1.const_body, cb2.const_body with
      | None, None -> ()
      | Some _, None -> ()
      | Some c1, Some c2 -> 
	  check_conv conv env c1 c2; ()
      | None, Some c2 ->
	  check_conv 
	    conv 
	    env 
	    (mkConst (make_kn (MPself msid1) empty_dirpath l)) 
	    c2; 
	  ()

let rec check_modules env msid1 l msb1 msb2 =
  check_modtypes env (fst msb1) (fst msb2) false;
  match (snd msb1), (snd msb2) with
    | _, None -> ()
    | None, Some mp2 -> 
	check_modpath_equiv env (MPdot(MPself msid1,l)) mp2
    | Some mp1, Some mp2 ->
	check_modpath_equiv env mp1 mp2

and check_signatures env' (msid1,sig1) (msid2,sig2') = 
  let mp1 = MPself msid1 in
  let env = add_signature mp1 sig1 env' in 
  let sig2 = subst_signature_msid msid2 mp1 sig2' in
  let map1 = make_label_map msid1 sig1 in
  let check_one_body (l,spec2) = 
    let info1 = 
      try 
	Labmap.find l map1 
      with 
	  Not_found -> error_no_such_label l 
    in
      match spec2 with
	| SPBconst cb2 ->
	    check_constant env msid1 l info1 cb2 spec2
	| SPBmind mib2 -> 
	    check_inductive env msid1 l info1 mib2 spec2
	| SPBmodule msb2 -> 
	    let msb1 = 
	      match info1 with
		| Module msb -> msb
		| _ -> error_not_match l spec2
	    in
	      check_modules env msid1 l msb1 msb2
	| SPBmodtype mtb2 ->
	    let mtb1 = 
	      match info1 with
		| Modtype mtb -> mtb
		| _ -> error_not_match l spec2
	    in
	      check_modtypes env mtb1 mtb2 true
  in
    List.iter check_one_body sig2
    
and check_modtypes env mtb1 mtb2 equiv = 
  if mtb1==mtb2 then (); (* just in case  :) *)
  let mtb1' = scrape_modtype env mtb1 in
  let mtb2' = scrape_modtype env mtb2 in
    if mtb1'==mtb2' then ();
    match mtb1', mtb2' with
      | MTBsig (msid1,list1), 
	MTBsig (msid2,list2) -> 
	  check_signatures env (msid1,list1) (msid2,list2);
	  if equiv then
	    check_signatures env (msid2,list2) (msid1,list1) 
      | MTBfunsig (arg_id1,arg_t1,body_t1), 
	MTBfunsig (arg_id2,arg_t2,body_t2) ->
	  check_modtypes env arg_t2 arg_t1 equiv; (* contravariant *)
	  let env' = 
	    add_module (MPbound arg_id2) (module_body_of_type arg_t2) env 
	  in
	  let body_t1' = 
	    subst_modtype 
	      (map_mbid arg_id1 (MPbound arg_id2)) 
	      body_t1
	  in
	  check_modtypes env' body_t1' body_t2 equiv
      | MTBident _ , _ -> anomaly "Subtyping: scrape failed"
      | _ , MTBident _ -> anomaly "Subtyping: scrape failed"
      | _ , _ -> error_incompatible_modtypes mtb1 mtb2
	  
let check_subtypes env sup super = 
  check_modtypes env sup super false

