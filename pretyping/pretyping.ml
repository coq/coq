
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Sign
open Evd
open Term
open Reduction
open Environ
open Type_errors
open Typeops
open Classops
open List
open Recordops 
open Evarutil
open Pretype_errors
open Rawterm
open Evarconv
open Coercion

let ctxt_of_ids ids =
  Array.of_list (List.map (function id -> VAR id) ids)

let mt_evd = Evd.empty

let vect_lift_type = Array.mapi (fun i t -> typed_app (lift i) t)

let j_nf_ise env sigma {uj_val=v;uj_type=t;uj_kind=k} =
  {uj_val=nf_ise1 env sigma v;uj_type=nf_ise1 env sigma t;uj_kind=k}

let jv_nf_ise env sigma = Array.map (j_nf_ise env sigma)

let evar_type_fixpoint env isevars lna lar vdefj =
  let lt = Array.length vdefj in 
    if Array.length lar = lt then 
      for i = 0 to lt-1 do 
        if not (the_conv_x_leq env isevars
		  (vdefj.(i)).uj_type (lift lt (body_of_type lar.(i)))) then
          error_ill_typed_rec_body CCI env i lna 
	    (jv_nf_ise env !isevars vdefj) 
	    (Array.map (typed_app (nf_ise1 env !isevars)) lar)
      done


(* Inutile ?
let cast_rel isevars env cj tj =
    if the_conv_x_leq isevars env cj.uj_type tj.uj_val then
        {uj_val=j_val_only cj;
         uj_type=tj.uj_val;
         uj_kind = hnf_constr !isevars tj.uj_type}
   else error_actual_type CCI env (j_nf_ise !isevars cj) (j_nf_ise !isevars tj)

*)
let let_path = make_path ["Core"] (id_of_string "let") CCI

let wrong_number_of_cases_message loc env isevars (c,ct) expn = 
  let c = nf_ise1 env !isevars c and ct = nf_ise1 env !isevars ct in
  error_number_branches_loc loc env c ct expn

let check_branches_message loc env isevars (c,ct) (explft,lft) = 
  let n = Array.length explft and expn = Array.length lft in
  if n<>expn then wrong_number_of_cases_message loc env isevars (c,ct) expn;
  for i = 0 to n-1 do
    if not (the_conv_x_leq env isevars lft.(i) explft.(i)) then 
      let c = nf_ise1 env !isevars c
      and ct = nf_ise1 env !isevars ct 
      and lfi = nf_betaiota env !isevars (nf_ise1 env !isevars lft.(i)) in
      error_ill_formed_branch_loc loc CCI env c i lfi (nf_betaiota env !isevars explft.(i))
  done

(*
let evar_type_case isevars env ct pt lft p c =
  let (mind,bty,rslty) = type_case_branches env !isevars ct pt p c
  in check_branches_message isevars env (c,ct) (bty,lft); (mind,rslty)
*)


let trad_metamap = ref []
let trad_nocheck = ref false

let pretype_ref loc isevars env = function
| RMeta n ->
    let metaty =
      try List.assoc n !trad_metamap
      with Not_found ->
	Ast.user_err_loc 
	  (loc,"pretype",
	   [< 'sTR "Metavariable "; 'iNT n; 'sTR "remains non instanciated" >])
	  in
    (match kind_of_term metaty with
      IsCast (typ,kind) -> {uj_val=DOP0 (Meta n); uj_type=typ; uj_kind=kind}
    | _ ->
        {uj_val=DOP0 (Meta n);
          uj_type=metaty;
          uj_kind=failwith "should be casted"})
	   (* hnf_constr !isevars (exemeta_hack metaty).uj_type}) *)

| RVar id ->
    let {body=typ;typ=s} = snd(lookup_glob id (context env)) in
    {uj_val=VAR id; uj_type=typ; uj_kind = DOP0 (Sort s)}

| RConst (sp,ids) ->
    let cstr = mkConst sp (ctxt_of_ids ids) in
    make_judge cstr (type_of_constant env !isevars cstr)
(*
| RAbst sp ->
  if sp = let_path then
      (match Array.to_list cl with
       [m;DLAM(na,b)] ->
       let mj = pretype mt_tycon isevars env m in
	 (try 
	    let mj = inh_ass_of_j isevars env mj in
	    let mb = body_of_type mj in
	    let bj =
	     pretype mt_tycon isevars (add_rel (na,mj) env) b in
	   {uj_val = DOPN(Abst sp,[|mb;DLAM(na,bj.uj_val)|]);
            uj_type = sAPP (DLAM(na,bj.uj_type)) mb;
            uj_kind = pop bj.uj_kind }
	 with UserError _ -> 
	   pretype vtcon isevars env (abst_value cstr)) 
      | _ -> errorlabstrm "Trad.constr_of_com" [< 'sTR"Malformed ``let''" >])
   else if evaluable_abst cstr then
     pretype vtcon isevars env (abst_value cstr)
   else error "Cannot typecheck an unevaluable abstraction"
*)

| REVar (sp,ids) ->
    let cstr = mkConst sp (ctxt_of_ids ids) in
    make_judge cstr (type_of_existential env !isevars cstr)

| RInd ((sp,i),ids) ->
    let cstr = mkMutInd sp i (ctxt_of_ids ids) in
    make_judge cstr (type_of_inductive env !isevars cstr)
 
| RConstruct (((sp,i),j),ids) ->
    let cstr = mkMutConstruct sp i j (ctxt_of_ids ids) in
    let (typ,kind) = destCast (type_of_constructor env !isevars cstr) in
    {uj_val=cstr; uj_type=typ; uj_kind=kind}

(* pretype vtcon isevars env constr tries to solve the *)
(* existential variables in constr in environment env with the *)
(* constraint vtcon (see Tradevar). *)
(* Invariant : Prod and Lambda types are casted !! *)
let rec pretype vtcon env isevars cstr =
match cstr with   (* Où teste-t-on que le résultat doit satisfaire tycon ? *)


| RRef (loc,ref) -> 
    pretype_ref loc isevars env ref

| RRel (loc,n) -> relative env n

| RHole loc ->
  if !compter then nbimpl:=!nbimpl+1;
  (match vtcon with
    (true,(Some v, _)) ->
      let (valc,typc) = destCast v in
      {uj_val=valc; uj_type=typc; uj_kind=dummy_sort}
  | (false,(None,Some ty)) ->
      let (c,ty) = new_isevar env isevars ty CCI in
      {uj_val=c;uj_type=ty;uj_kind = dummy_sort}
  | (true,(None,None)) ->
      let (c,ty) = new_isevar env isevars (mkCast dummy_sort dummy_sort) CCI in
      {uj_val=c;uj_type=ty;uj_kind = dummy_sort}
  | (false,(None,None)) ->
      (match loc with
	  None -> anomaly "There is an implicit argument I cannot solve"
	| Some loc -> 
	    Ast.user_err_loc
	      (loc,"pretype",
	       [< 'sTR "Cannot infer a term for this placeholder" >]))
  | _ -> anomaly "tycon")


| RRec (loc,fixkind,lfi,lar,vdef) ->
  let larj = Array.map (pretype def_vty_con env isevars) lar in
  let lara = Array.map (assumption_of_judgment env !isevars) larj in
  let nbfix = Array.length lfi in
  let lfi = List.map (fun id -> Name id) (Array.to_list lfi) in
  let newenv =
    array_fold_left2 (fun env id ar -> (push_rel (id,ar) env))
      env (Array.of_list (List.rev lfi)) (vect_lift_type lara) in
  let vdefj =
    Array.mapi 
      (fun i def -> (* we lift nbfix times the type in tycon, because of
                     * the nbfix variables pushed to newenv *)
        pretype (mk_tycon (lift nbfix (larj.(i).uj_val))) newenv isevars def)
      vdef in
  (evar_type_fixpoint env isevars lfi lara vdefj;
  match fixkind with
    | RFix(vn,i) ->
      let fix = mkFix vn i lara (List.rev lfi) (Array.map j_val_only vdefj) in
	check_fix env !isevars fix;
	make_judge fix lara.(i)
    | RCofix i -> 
      let cofix = mkCoFix i lara (List.rev lfi) (Array.map j_val_only vdefj) in
	check_cofix env !isevars cofix;
	make_judge cofix lara.(i))

| RSort (loc,RProp c) -> make_judge_of_prop_contents c

| RSort (loc,RType) -> 
    { uj_val = dummy_sort; uj_type = dummy_sort; uj_kind = dummy_sort }

| RApp (loc,f,args) -> 
    let j = pretype mt_tycon env isevars f in
    let j = inh_app_fun env isevars j in
    let apply_one_arg (tycon,jl) c =
      let cj = pretype (app_dom_tycon isevars tycon) env isevars c in
      let rtc = app_rng_tycon isevars cj.uj_val tycon in
      (rtc,cj::jl)  in
    let jl = List.rev (snd (List.fold_left apply_one_arg
			      (mk_tycon j.uj_type,[]) args)) in
    inh_apply_rel_list !trad_nocheck env isevars jl j vtcon

| RBinder(loc,BLambda,name,c1,c2)      ->
    let j = pretype (abs_dom_valcon isevars vtcon) env isevars c1 in
    let assum = inh_ass_of_j env isevars j in
    let var = (name,assum) in
    let j' =
      pretype (abs_rng_tycon isevars vtcon) isevars
 	(add_rel var env) c2 in 
    abs_rel !isevars name assum j'

| RBinder(loc,BProd,name,c1,c2)        ->
    let j = pretype def_vty_con env isevars c1 in
    let assum = inh_ass_of_j env isevars j in
    let var = (name,assum) in
    let j' = pretype def_vty_con isevars (add_rel var env) c2 in
    let j'' = inh_tosort env isevars j' in
    gen_rel !isevars CCI env name assum j''

| ROldCase (loc,isrec,po,c,lf) ->
  let cj = pretype mt_tycon env isevars c in
  let (mind,_) =
    try find_mrectype !isevars cj.uj_type
    with Induc -> error_case_not_inductive CCI env
	(nf_ise1 !isevars cj.uj_val) (nf_ise1 !isevars cj.uj_type) in
  let pj = match po with
    | Some p -> pretype mt_tycon env isevars p
    | None -> 
	try match vtcon with
	    (_,(_,Some pred)) -> 
	      let (predc,predt) = destCast pred in
	      let predj = {uj_val=predc;uj_type=predt;uj_kind=dummy_sort} in
	      inh_tosort env isevars predj
	  | _ -> error "notype"
	with UserError _ -> (* get type information from type of branches *)
	  let rec findtype i =
	    if i > Array.length lf
	    then error_cant_find_case_type loc env cj.uj_val
	    else
	      try
		let expti = Indrec.branch_scheme !isevars isrec i cj.uj_type in
		let fj = pretype (mk_tycon expti) env isevars lf.(i-1) in
		let efjt = nf_ise1 !isevars fj.uj_type in 
		let pred = 
		  Indrec.pred_case_ml_onebranch env !isevars isrec 
		    (cj.uj_val,cj.uj_type) (i,fj.uj_val,efjt) in
		if has_ise pred then findtype (i+1)
		else 
		  let pty = Mach.newtype_of env !isevars pred in
		    {uj_val=pred;uj_type=pty;uj_kind=Mach.newtype_of env !isevars pty}
	      with UserError _ -> findtype (i+1) in
	    findtype 1 in

  let evalct = nf_ise1 !isevars cj.uj_type
  and evalPt = nf_ise1 !isevars pj.uj_type in

  let (mind,bty,rsty) =
    Indrec.type_rec_branches isrec env !isevars evalct evalPt pj.uj_val cj.uj_val in
  if Array.length bty <> Array.length lf then
    wrong_number_of_cases_message loc env isevars (cj.uj_val,evalct)
      (Array.length bty)
  else
    let lfj =
      map2_vect
        (fun tyc f -> pretype (mk_tycon tyc) env isevars f) bty lf in
    let lft = (Array.map (fun j -> j.uj_type) lfj) in
    check_branches_message loc env isevars (cj.uj_val,evalct) (bty,lft);
    let v =
      if isrec
      then 
	let rEC = Array.append [|(j_val pj); (j_val cj)|]
		    (Array.map j_val lfj) in
	Indrec.transform_rec loc env !isevars rEC (evalct,evalPt)
      else let ci = ci_of_mind mind in
	mkMutCaseA ci (j_val pj) (j_val cj) (Array.map j_val lfj) in

      {uj_val = v;
       uj_type = rsty;
       uj_kind = sort_of_arity !isevars evalPt}

| RCases (loc,prinfo,po,tml,eqns) ->
    Multcase.compile_multcase
      ((fun vtyc -> pretype vtyc isevars),isevars)
      vtcon env (po,tml,eqns)
(*
| DOP2(Cast,c,t) ->
  let tj = pretype def_vty_con env isevars t in
  let tj = inh_tosort_force env isevars tj in
  let cj =
    pretype (mk_tycon2 vtcon (assumption_of_judgement env !isevars tj).body)
      env isevars c in
  inh_cast_rel env isevars cj tj
*)
(* Maintenant, tout s'exécute... 
  | _ -> error_cant_execute CCI env (nf_ise1 !isevars cstr)
*)


let unsafe_fmachine vtcon nocheck isevars metamap env constr = 
  trad_metamap := metamap;
  trad_nocheck := nocheck;
  reset_problems ();
  pretype vtcon env isevars constr


(* [fail_evar] says how to process unresolved evars:
 *   true -> raise an error message
 *   false -> convert them into new Metas (casted with their type)
 *)
let process_evars fail_evar sigma =
  (if fail_evar then whd_ise sigma else whd_ise1_metas sigma)


let j_apply f j = 
  { uj_val=strong (under_outer_cast f) j.uj_val;
    uj_type=strong f j.uj_type;
    uj_kind=strong f j.uj_kind}

(* TODO: comment faire remonter l'information si le typage a resolu des
       variables du sigma original. il faudrait que la fonction de typage
       retourne aussi le nouveau sigma...
*)
let ise_resolve fail_evar sigma metamap env c =
  let isevars = ref sigma in
  let j = unsafe_fmachine mt_tycon false isevars metamap env c in
  j_apply (process_evars fail_evar !isevars) j


let ise_resolve_type fail_evar sigma metamap env c =
  let isevars = ref sigma in
  let j = unsafe_fmachine def_vty_con false isevars metamap env c in
  let tj = inh_ass_of_j env isevars j in
  type_app (strong (process_evars fail_evar !isevars)) tj


let ise_resolve_nocheck sigma metamap env c =
  let isevars = ref sigma in
  let j = unsafe_fmachine mt_tycon true isevars metamap env c in
  j_apply (process_evars true !isevars) j


let ise_resolve1 is_ass sigma env c =
  if is_ass then body_of_type (ise_resolve_type true sigma [] env c)
  else (ise_resolve true sigma [] env c).uj_val
