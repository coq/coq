
(* $Id$ *)

open Pp
open Generic
open Term
open Constant
open Inductive
open Reduction
open Tacred
open Declare
open Names
open Coqast
open Ast
open Library
open Libobject
open Astterm

let mkCastC(c,t) = ope("CAST",[c;t])
let mkLambdaC(x,a,b) = ope("LAMBDA",[a;slam(Some (string_of_id x),b)])
let mkLambdaCit = List.fold_right (fun (x,a) b -> mkLambdaC(x,a,b))
let mkProdC (x,a,b) = ope("PROD",[a;slam(Some (string_of_id x),b)])
let mkProdCit = List.fold_right (fun (x,a) b -> mkProdC(x,a,b))

(* Commands of the interface *)

(* 1| Constant definitions *)

let constant_entry_of_com com =
  let sigma = Evd.empty in
  let env = Global.env() in
  match com with
    | Node(_,"CAST",[_;t]) ->
        { const_entry_body = constr_of_com sigma env com;
	  const_entry_type = Some (constr_of_com1 true sigma env t) }
    | _ -> 
	{ const_entry_body = constr_of_com sigma env com;
	  const_entry_type = None }

let definition_body ident n com = 
  let ce = constant_entry_of_com com in
  declare_constant ident (ce,n,false)

let red_constant_entry ce = function
  | None -> ce
  | Some red -> 
      { const_entry_body = 
	  reduction_of_redexp red (Global.env()) Evd.empty ce.const_entry_body;
	const_entry_type = 
	  ce.const_entry_type }

let definition_body_red ident n com red_option = 
  let ce = constant_entry_of_com com in
  let ce' = red_constant_entry ce red_option in
  declare_constant ident (ce',n,false)

let syntax_definition ident com =
  let c = constr_of_com Evd.empty (Global.env()) com in 
  declare_syntax_constant ident c

let abstraction_definition ident arity com =
  let c = raw_constr_of_compattern Evd.empty (Global.env()) com in 
  machine_abstraction ident arity c


(* 2| Variable definitions *)

let parameter_def_var ident c =
  let (sigma,(sign,fsign)) = initial_sigma_assumptions() in 
  machine_parameter (sign,fsign)
    (id_of_string ident, constr_of_com1 true sigma sign c)
    
let hypothesis_def_var is_refining ident n c = 
  let (sigma,(sign,fsign)) = initial_sigma_assumptions() in
  match n with
    | NeverDischarge -> parameter_def_var ident c
    | DischargeAt disch_sp ->
        if is_section_p disch_sp then
          (machine_variable (sign,fsign)
             (id_of_string ident,n,false,
              constr_of_com1 true sigma sign c);
           if is_refining then 
             (mSGERRNL [< 'sTR"Warning: Variable " ; 'sTR ident ; 
                          'sTR" is not visible from current goals" >]))
        else (mSGERRNL [< 'sTR"Warning: Declaring " ; 'sTR ident ; 
                          'sTR" as a parameter rather than a variable " ;
                          'sTR" because it is at a global level" >];
              parameter_def_var ident c)
	  
(* 3| Mutual Inductive definitions *)

let minductive_message = function 
  | []  -> anomaly "no inductive definition"
  | [x] -> [< print_id x; 'sTR " is defined">]
  | l   -> hOV 0  [< prlist_with_sep pr_coma print_id l;
		     'sPC; 'sTR "are defined">]

let recursive_message = function 
  | []  -> anomaly "no recursive definition"
  | [x] -> [< print_id x; 'sTR " is recursively defined">]
  | l   -> hOV 0 [< prlist_with_sep pr_coma print_id l;
		    'sPC; 'sTR "are recursively defined">]

let corecursive_message = function 
  | []  -> anomaly "no corecursive definition"
  | [x] -> [< print_id x; 'sTR " is corecursively defined">]
  | l   -> hOV 0 [< prlist_with_sep pr_coma print_id l;
                    'sPC; 'sTR "are corecursively defined">]

let build_mutual lparams lnamearconstrs finite =
  let lrecnames = List.map (fun (x,_,_)->x)  lnamearconstrs
  and nparams = List.length lparams
  and (sigma,(sign0,fsign0)) = initial_sigma_assumptions() in
  let x = Vartab.freeze() in
  let mispecvec =
    try
      let (ind_sign,arityl) =
    	List.fold_left 
	  (fun (sign,arl) (recname,arityc,_) -> 
             let arity = 
	       fconstruct_type sigma sign0 (mkProdCit lparams arityc) in
             (Vartab.push recname false (arity,None) NeverDischarge 
           	(if is_implicit_args() then IMPL_AUTO (poly_args_type arity)
		 else NO_IMPL);
              (add_sign (recname,arity) sign, (arity::arl))))
	  (sign0,[]) lnamearconstrs 
      in
      Array.of_list 
      	(List.map2
           (fun ar (name,_,lname_constr) -> 
              let consconstrl =
              	List.map 
                  (fun (_,constr) -> constr_of_com sigma ind_sign
                       (mkProdCit lparams constr))
                  lname_constr 
	      in
              (name,Anonymous,ar,
               put_DLAMSV_subst (List.rev lrecnames)
                 (Array.of_list consconstrl),
                 Array.of_list (List.map fst lname_constr)))
           (List.rev arityl) lnamearconstrs)

(* Expérimental
let (full_env,lpar) =
    List.fold_left
      (fun (env,lp) (n,t) ->
	 let tj = type_from_com_env env t in
	   (add_rel (n,tj) env, (n,tj)::lp))
      (gLOB ind_sign) lparams in  (* On triche: les ind n'ont pas le droit de
                                    figurer dans les par, mais on sait par le
				    calcul de arityl qu'ils ne figurent pas *)

  let lrecnames' = List.rev lrecnames in
    (Array.of_list 
      (List.map2
         (fun ar (name,_,lname_constr) ->
            let lc =
              List.map 
                (fun (_,c) ->
		   it_list_i (fun i c id -> subst_varn id i c)
		     (nparams+1)
		     (constr_of_com_env sigma env c)
		     lrecnames')
                lname_constr in
              (name, Anonymous, ar, (lpar,lc),
	       Array.of_list (List.map fst lname_constr)))
         (List.rev arityl) lnamearconstrs))
*)
  with e -> (Vartab.unfreeze x; raise e) 

in let _ = Vartab.unfreeze x

  in machine_minductive (sign0,fsign0) nparams mispecvec finite;
    pPNL(minductive_message lrecnames)


(* try to find non recursive definitions *)
let collect_non_rec  = 
  let rec searchrec lnonrec lnamerec ldefrec larrec nrec = 
    try
      let i = 
        try_find_i
          (fun i f ->
             if List.for_all (fun def -> not (occur_var f def)) ldefrec
             then i else failwith "try_find_i")
          0 lnamerec in

      let (lf1,f::lf2) = chop_list i lnamerec 
      and (ldef1,def::ldef2) = chop_list i ldefrec 
      and (lar1,ar::lar2) = chop_list i larrec
      and newlnv = (try (match chop_list i nrec with 
                             (lnv1,_::lnv2) -> (lnv1@lnv2)
			   | _ -> [])
                     (* nrec=[] for cofixpoints *)
                    with Failure "chop_list" -> [])
      in searchrec ((f,DOP2(Cast,def,body_of_type ar))::lnonrec) 
           (lf1@lf2) (ldef1@ldef2) (lar1@lar2) newlnv
    with Failure "try_find_i" -> (lnonrec, (lnamerec,ldefrec,larrec,nrec))
  in searchrec [] 



let build_recursive lnameargsardef = 

  let lrecnames = List.map (fun (f,_,_,_) -> f) lnameargsardef
  and (sigma,(sign0,_ as env)) = initial_sigma_assumptions()
  and nv = Array.of_list (List.map (fun (_,la,_,_) -> (List.length la) -1)
                            lnameargsardef) in

  let x = Vartab.freeze() in
  let (rec_sign,arityl) = 
    try (List.fold_left 
           (fun (sign,arl) (recname,lparams,arityc,_) -> 
              let arity =
                fconstruct_type sigma sign0 (mkProdCit lparams arityc) in
                (Vartab.push recname false (arity,None) NeverDischarge 
                   (if is_implicit_args() then IMPL_AUTO (poly_args_type arity)
                    else NO_IMPL);
                 (add_sign (recname,arity) sign, (arity::arl))))
           (sign0,[]) lnameargsardef)
    with e -> (Vartab.unfreeze x; raise e)  in 

  let recdef = 
    try (List.map (fun (_,lparams,arityc,def) -> 
                     constr_of_com sigma rec_sign 
                       (mkLambdaCit lparams (mkCastC(def,arityc))))
           lnameargsardef)
    with e -> (Vartab.unfreeze x; raise e) in

  let _ = Vartab.unfreeze x in

  let (lnonrec,(lnamerec,ldefrec,larrec,nvrec)) = 
    collect_non_rec lrecnames recdef (List.rev arityl) (Array.to_list nv) in
  let n = NeverDischarge in 
    if lnamerec <> [] then
      (let recvec = [|put_DLAMSV_subst (List.rev lnamerec)
                          (Array.of_list ldefrec)|] in
       let varrec = Array.of_list larrec in
       let rec declare i = function 
           (fi::lf) ->
	     machine_constant env 
               ((fi,false,n), mkFixDlam (Array.of_list nvrec) i varrec recvec);
             declare (i+1) lf
         | _        -> () in 
       (* declare the recursive definitions *)
         declare 0 lnamerec; pPNL(recursive_message lnamerec));
         (* The others are declared as normal definitions *)
  let var_subst id =
    (id,make_substituend (Machops.search_reference (gLOB sign0) id)) in
  let _ = List.fold_left
      (fun subst (f,def) ->
	machine_constant env ((f,false,n),Generic.replace_vars subst def);
      	warning ((string_of_id f)^" is non-recursively defined");
      	(var_subst f) :: subst)
      
      (List.map var_subst lnamerec)
      lnonrec in
  ()



let build_corecursive lnameardef = 

  let lrecnames = List.map (fun (f,_,_) -> f) lnameardef
  and (sigma,(sign0,_ as env)) = initial_sigma_assumptions() in

  let x = Vartab.freeze() in
  let (rec_sign,arityl) = 
    try (List.fold_left 
           (fun (sign,arl) (recname,arityc,_) -> 
              let arity = fconstruct_type sigma sign0 arityc in
                (Vartab.push recname false (arity,None) NeverDischarge 
                   (if is_implicit_args() then IMPL_AUTO (poly_args_type arity)
                    else NO_IMPL);
                 (add_sign (recname,arity) sign, (arity::arl))))
           (sign0,[]) lnameardef)
    with e -> (Vartab.unfreeze x; raise e)  in 

  let recdef =
    try (List.map (fun (_,arityc,def) -> 
                     constr_of_com sigma rec_sign
                       (mkCastC(def,arityc)))
           lnameardef)
    with e -> (Vartab.unfreeze x; raise e) in

  let _ = Vartab.unfreeze x in

  let (lnonrec,(lnamerec,ldefrec,larrec,_)) = 
    collect_non_rec lrecnames recdef (List.rev arityl) [] in

  let n = NeverDischarge in 

    if lnamerec <> [] then 
      (let recvec = if lnamerec = [] then [||] 
       else 
         [|put_DLAMSV_subst (List.rev lnamerec) (Array.of_list ldefrec)|] in

       let rec declare i = function 
           (fi::lf) ->
             machine_constant env 
	       ((fi,false,n), mkCoFixDlam i (Array.of_list larrec) recvec);
             declare (i+1) lf
         | _        -> () in 

         declare 0 lnamerec; pPNL(corecursive_message lnamerec));
  let var_subst id =
    (id,make_substituend (Machops.search_reference (gLOB sign0) id)) in
  let _ = List.fold_left
      (fun subst (f,def) ->
	machine_constant env ((f,false,n),Generic.replace_vars subst def);
      	warning ((string_of_id f)^" is non-recursively defined");
      	(var_subst f) :: subst)
      (List.map var_subst lnamerec)
      lnonrec in
  ()


let build_scheme lnamedepindsort = 
  let lrecnames = List.map (fun (f,_,_,_) -> f) lnamedepindsort
  and (sigma,(sign0,fsign0)) = initial_sigma_assumptions() in
  let lrecspec =
    List.map (fun (_,dep,ind,sort) -> 
                let indc = constr_of_com sigma sign0 ind
                and s = destSort (constr_of_com sigma sign0 sort) in
                  (indc,dep,s)) lnamedepindsort
  and n = NeverDischarge in 
  let listdecl = Indrec.build_indrec sigma lrecspec in 
  let rec declare i = function 
      (fi::lf) -> machine_constant (sign0,fsign0) ((fi,false,n),listdecl.(i));
        declare (i+1) lf
    | _        -> ()
  in 
    declare 0 lrecnames; pPNL(recursive_message lrecnames)
