
(* $Id$ *)

open Pp
open Util
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
  let c = raw_constr_of_com Evd.empty (Global.context()) com in 
  Syntax_def.declare_syntactic_definition ident c

(***TODO
let abstraction_definition ident arity com =
  let c = raw_constr_of_compattern Evd.empty (Global.env()) com in 
  machine_abstraction ident arity c
***)

(* 2| Variable definitions *)

let parameter_def_var ident c =
  let c = constr_of_com1 true Evd.empty (Global.env()) c in
  declare_parameter (id_of_string ident) c
    
let hypothesis_def_var is_refining ident n c =
  match n with
    | NeverDischarge -> parameter_def_var ident c
    | DischargeAt disch_sp ->
        if Lib.is_section_p disch_sp then begin
          declare_variable (id_of_string ident)
             (constr_of_com1 true Evd.empty (Global.env()) c,n,false);
          if is_refining then 
            mSGERRNL [< 'sTR"Warning: Variable " ; 'sTR ident ; 
                        'sTR" is not visible from current goals" >]
        end else begin
	  mSGERRNL [< 'sTR"Warning: Declaring " ; 'sTR ident ; 
                      'sTR" as a parameter rather than a variable " ;
                      'sTR" because it is at a global level" >];
          parameter_def_var ident c
	end
	  
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
  and sigma = Evd.empty 
  and env0 = Global.env() in
  let fs = States.freeze() in
  try
    let mispecvec =
      let (ind_sign,arityl) =
      	List.fold_left 
	  (fun (env,arl) (recname,arityc,_) -> 
             let arity = type_of_com env (mkProdCit lparams arityc) in
	     let env' = Environ.push_var (recname,arity) env in
	     declare_variable recname (arity.body,NeverDischarge,false);
	     (env', (arity::arl)))
	  (env0,[]) lnamearconstrs 
      in
      List.map2
        (fun ar (name,_,lname_constr) -> 
           let consconstrl =
             List.map 
               (fun (_,constr) -> constr_of_com sigma ind_sign
                    (mkProdCit lparams constr))
               lname_constr 
	   in
           (name, ar.body, List.map fst lname_constr,
            put_DLAMSV_subst (List.rev lrecnames) (Array.of_list consconstrl)))
        (List.rev arityl) lnamearconstrs
    in 
    let mie = { 
      mind_entry_nparams = nparams;
      mind_entry_finite = finite;
      mind_entry_inds = mispecvec }
    in
    declare_mind mie;
    States.unfreeze fs;
    pPNL(minductive_message lrecnames)
  with e ->
    States.unfreeze fs; raise e


(* try to find non recursive definitions *)

let list_chop_hd i l = match list_chop i l with
  | (l1,x::l2) -> (l1,x,l2)
  | _ -> assert false

let collect_non_rec  = 
  let rec searchrec lnonrec lnamerec ldefrec larrec nrec = 
    try
      let i = 
        list_try_find_i
          (fun i f ->
             if List.for_all (fun def -> not (occur_var f def)) ldefrec
             then i else failwith "try_find_i")
          0 lnamerec 
      in
      let (lf1,f,lf2) = list_chop_hd i lnamerec in
      let (ldef1,def,ldef2) = list_chop_hd i ldefrec in
      let (lar1,ar,lar2) = list_chop_hd i larrec in
      let newlnv = 
	try 
	  match list_chop i nrec with 
            | (lnv1,_::lnv2) -> (lnv1@lnv2)
	    | _ -> [] (* nrec=[] for cofixpoints *)
        with Failure "list_chop" -> []
      in 
      searchrec ((f,DOP2(Cast,def,body_of_type ar))::lnonrec) 
        (lf1@lf2) (ldef1@ldef2) (lar1@lar2) newlnv
    with Failure "try_find_i" -> 
      (lnonrec, (lnamerec,ldefrec,larrec,nrec))
  in 
  searchrec [] 

let build_recursive lnameargsardef = 
  let lrecnames = List.map (fun (f,_,_,_) -> f) lnameargsardef
  and sigma = Evd.empty
  and env0 = Global.env()
  and nv = Array.of_list (List.map (fun (_,la,_,_) -> (List.length la) -1)
                            lnameargsardef) 
  in
  let fs = States.freeze() in
  let (rec_sign,arityl) = 
    try 
      List.fold_left 
        (fun (env,arl) (recname,lparams,arityc,_) -> 
           let arity = type_of_com env (mkProdCit lparams arityc) in
           declare_variable recname (arity.body,NeverDischarge,false);
           (Environ.push_var (recname,arity) env, (arity::arl)))
        (env0,[]) lnameargsardef
    with e ->
      States.unfreeze fs; raise e
  in 
  let recdef = 
    try 
      List.map (fun (_,lparams,arityc,def) -> 
                  constr_of_com sigma rec_sign 
                    (mkLambdaCit lparams (mkCastC(def,arityc))))
        lnameargsardef
    with e -> 
      States.unfreeze fs; raise e
  in
  States.unfreeze fs;
  let (lnonrec,(lnamerec,ldefrec,larrec,nvrec)) = 
    collect_non_rec lrecnames recdef (List.rev arityl) (Array.to_list nv) in
  let n = NeverDischarge in 
  if lnamerec <> [] then begin
    let recvec = [|put_DLAMSV_subst (List.rev lnamerec)
                       (Array.of_list ldefrec)|] in
    let varrec = Array.of_list larrec in
    let rec declare i = function 
      | fi::lf ->
	  let ce = { const_entry_body = 
		       mkFixDlam (Array.of_list nvrec) i varrec recvec;
		     const_entry_type = None } in
	  declare_constant fi (ce, n, false);
          declare (i+1) lf
      | _ -> () 
    in 
    (* declare the recursive definitions *)
    declare 0 lnamerec; 
    pPNL(recursive_message lnamerec)
  end;
  (* The others are declared as normal definitions *)
  let var_subst id = (id,make_substituend (global_reference CCI id)) in
  let _ = 
    List.fold_left
      (fun subst (f,def) ->
	 let ce = { const_entry_body = Generic.replace_vars subst def;
		    const_entry_type = None } in
	 declare_constant f (ce,n,false);
      	 warning ((string_of_id f)^" is non-recursively defined");
      	 (var_subst f) :: subst)
      (List.map var_subst lnamerec)
      lnonrec 
  in
  ()

let build_corecursive lnameardef = 
  let lrecnames = List.map (fun (f,_,_) -> f) lnameardef
  and sigma = Evd.empty
  and env0 = Global.env() in
  let fs = States.freeze() in
  let (rec_sign,arityl) = 
    try 
      List.fold_left 
        (fun (env,arl) (recname,arityc,_) -> 
           let arity = type_of_com env0 arityc in
           declare_variable recname (arity.body,NeverDischarge,false);
           (Environ.push_var (recname,arity) env, (arity::arl)))
        (env0,[]) lnameardef
    with e -> 
      States.unfreeze fs; raise e
  in 
  let recdef =
    try 
      List.map (fun (_,arityc,def) -> 
                  constr_of_com sigma rec_sign
                    (mkCastC(def,arityc)))
        lnameardef
    with e -> 
      States.unfreeze fs; raise e 
  in
  States.unfreeze fs;
  let (lnonrec,(lnamerec,ldefrec,larrec,_)) = 
    collect_non_rec lrecnames recdef (List.rev arityl) [] in
  let n = NeverDischarge in 
  if lnamerec <> [] then begin
    let recvec = 
      if lnamerec = [] then 
	[||] 
      else 
	[|put_DLAMSV_subst (List.rev lnamerec) (Array.of_list ldefrec)|] 
    in
    let rec declare i = function 
      | fi::lf ->
	  let ce = { const_entry_body = 
		       mkCoFixDlam i (Array.of_list larrec) recvec;
		     const_entry_type = None } in
          declare_constant fi (ce,n,false);
          declare (i+1) lf
      | _        -> () 
    in 
    declare 0 lnamerec; 
    pPNL(corecursive_message lnamerec)
  end;
  let var_subst id =
    (id,make_substituend (global_reference CCI id)) in
  let _ = 
    List.fold_left
      (fun subst (f,def) ->
	 let ce = { const_entry_body = Generic.replace_vars subst def;
		    const_entry_type = None } in
	 declare_constant f (ce,n,false);
      	 warning ((string_of_id f)^" is non-recursively defined");
      	 (var_subst f) :: subst)
      (List.map var_subst lnamerec)
      lnonrec 
  in
  ()

let build_scheme lnamedepindsort = 
  let lrecnames = List.map (fun (f,_,_,_) -> f) lnamedepindsort
  and sigma = Evd.empty
  and env0 = Global.env() in
  let lrecspec =
    List.map (fun (_,dep,ind,sort) -> 
                let indc = constr_of_com sigma env0 ind
                and s = destSort (constr_of_com sigma env0 sort) in
                (indc,dep,s)) lnamedepindsort
  in
  let n = NeverDischarge in 
  let listdecl = Indrec.build_indrec env0 sigma lrecspec in 
  let rec declare i = function 
    | fi::lf -> 
	let ce = 
	  { const_entry_body = listdecl.(i); const_entry_type = None } in
	declare_constant fi (ce,n,false);
        declare (i+1) lf
    | _        -> ()
  in 
  declare 0 lrecnames; pPNL(recursive_message lrecnames)
