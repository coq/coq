
(* $Id$ *)

open Pp
open Util
open Options
open Term
open Declarations
open Inductive
open Environ
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

let constant_entry_of_com (com,comtypopt) =
  let sigma = Evd.empty in
  let env = Global.env() in
  match comtypopt with
      None -> 
	{ const_entry_body = interp_constr sigma env com;
	  const_entry_type = None }
    | Some comtyp ->
	let typ = interp_type sigma env comtyp in
	{ const_entry_body = interp_casted_constr sigma env com typ;
	  const_entry_type = Some typ }

let red_constant_entry ce = function
  | None -> ce
  | Some red ->
      let body = ce.const_entry_body in
      { const_entry_body = 
	  reduction_of_redexp red (Global.env()) Evd.empty body; 
	const_entry_type = 
	  ce.const_entry_type }

let definition_body_red ident n com comtypeopt red_option = 
  let ce = constant_entry_of_com (com,comtypeopt) in
  let ce' = red_constant_entry ce red_option in
  declare_constant ident (ConstantEntry ce',n);
  if is_verbose() then message ((string_of_id ident) ^ " is defined")

let definition_body ident n com typ = definition_body_red ident n com typ None

let syntax_definition ident com =
  let c = interp_rawconstr Evd.empty (Global.env()) com in 
  Syntax_def.declare_syntactic_definition ident c;
  if is_verbose() then 
    message ((string_of_id ident) ^ " is now a syntax macro")

(* 2| Variable definitions *)

let parameter_def_var ident c =
  let c = interp_type Evd.empty (Global.env()) c in
  declare_parameter (id_of_string ident) c;
  if is_verbose() then message (ident ^ " is assumed")
    
let hypothesis_def_var is_refining ident n c =
  let warning () = 
    mSGERRNL [< 'sTR"Warning: "; 'sTR ident; 
                'sTR" is declared as a parameter";
                'sTR" because it is at a global level" >]
  in
  match n with
    | NeverDischarge -> 
	warning();
	parameter_def_var ident c
    | DischargeAt disch_sp ->
        if Lib.is_section_p disch_sp then begin
	  let t = interp_type Evd.empty (Global.env()) c in
          declare_variable (id_of_string ident)
             (SectionLocalDecl t,n,false);
	  if is_verbose() then message (ident ^ " is assumed");
          if is_refining then 
            mSGERRNL [< 'sTR"Warning: Variable "; 'sTR ident; 
                        'sTR" is not visible from current goals" >]
        end else begin
	  warning();
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
  let allnames = 
    List.fold_left 
      (fun acc (id,_,l) -> id::(List.map fst l)@acc) [] lnamearconstrs in
  if not (list_distinct allnames) then
    error "Two inductive objects have the same name";
  let lrecnames = List.map (fun (x,_,_) -> x)  lnamearconstrs
  and nparams = List.length lparams
  and sigma = Evd.empty 
  and env0 = Global.env() in
  let mispecvec =
    let (ind_env,arityl) =
      List.fold_left 
	(fun (env,arl) (recname,arityc,_) -> 
           let raw_arity = mkProdCit lparams arityc in
           let arj = type_judgment_of_rawconstr Evd.empty env raw_arity in
	   let arity = arj.utj_val in
	   let env' = Environ.push_rel_assum (Name recname,arity) env in
	   (env', (arity::arl)))
	(env0,[]) lnamearconstrs 
    in
    List.map2
      (fun ar (name,_,lname_constr) -> 
         let consconstrl =
           List.map 
             (fun (_,constr) -> interp_constr sigma ind_env
                  (mkProdCit lparams constr))
             lname_constr 
	 in
         (name, (body_of_type ar), List.map fst lname_constr, consconstrl))
      (List.rev arityl) lnamearconstrs
  in
  let mie = { 
    mind_entry_nparams = nparams;
    mind_entry_finite = finite;
    mind_entry_inds = mispecvec }
  in
  let sp = declare_mind mie in
  if is_verbose() then pPNL(minductive_message lrecnames);
  if finite then
    for i = 0 to List.length mispecvec - 1 do
      declare_eliminations sp i
    done

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
      searchrec ((f,mkCast (def,body_of_type ar))::lnonrec) 
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
           let raw_arity = mkProdCit lparams arityc in
           let arj = type_judgment_of_rawconstr Evd.empty env raw_arity in
	   let arity = arj.utj_val in
           declare_variable recname
	     (SectionLocalDecl arj.utj_val,NeverDischarge,false);
           (Environ.push_named_assum (recname,arity) env, (arity::arl)))
        (env0,[]) lnameargsardef
    with e ->
      States.unfreeze fs; raise e
  in 
  let recdef = (* TODO: remplacer mkCast par un appel à interp_casted_constr *)
    try 
      List.map (fun (_,lparams,arityc,def) -> 
                  interp_constr sigma rec_sign 
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
    let recvec = 
      Array.map (subst_vars (List.rev lnamerec)) (Array.of_list ldefrec) in
    let varrec = Array.of_list larrec in
    let rec declare i = function 
      | fi::lf ->
	  let ce = 
	    { const_entry_body =
		mkFix ((Array.of_list nvrec,i),
		       (varrec,List.map (fun id -> Name id) lnamerec,
			recvec));
	      const_entry_type = None } 
	  in
	  declare_constant fi (ConstantEntry ce, n);
          declare (i+1) lf
      | _ -> () 
    in 
    (* declare the recursive definitions *)
    declare 0 lnamerec; 
    if is_verbose() then pPNL(recursive_message lnamerec)
  end;
  (* The others are declared as normal definitions *)
  let var_subst id = (id, global_reference CCI id) in
  let _ = 
    List.fold_left
      (fun subst (f,def) ->
	 let ce = { const_entry_body = replace_vars subst def;
		    const_entry_type = None } in
	 declare_constant f (ConstantEntry ce,n);
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
           let arj = type_judgment_of_rawconstr Evd.empty env0 arityc in
	   let arity = arj.utj_val in
           declare_variable recname
	     (SectionLocalDecl arj.utj_val,NeverDischarge,false);
           (Environ.push_named_assum (recname,arity) env, (arity::arl)))
        (env0,[]) lnameardef
    with e -> 
      States.unfreeze fs; raise e
  in 
  let recdef =
    try 
      List.map (fun (_,arityc,def) -> 
                  interp_constr sigma rec_sign
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
	Array.map (subst_vars (List.rev lnamerec)) (Array.of_list ldefrec) in
    let varrec = Array.of_list larrec in
    let rec declare i = function 
      | fi::lf ->
	  let ce = 
	    { const_entry_body =
		mkCoFix (i, (varrec,List.map (fun id -> Name id) lnamerec,
			     recvec));
	      const_entry_type = None } 
	  in
          declare_constant fi (ConstantEntry ce,n);
          declare (i+1) lf
      | _        -> () 
    in 
    declare 0 lnamerec; 
    if is_verbose() then pPNL(corecursive_message lnamerec)
  end;
  let var_subst id = (id, global_reference CCI id) in
  let _ = 
    List.fold_left
      (fun subst (f,def) ->
	 let ce = { const_entry_body = replace_vars subst def;
		    const_entry_type = None } in
	 declare_constant f (ConstantEntry ce,n);
      	 warning ((string_of_id f)^" is non-recursively defined");
      	 (var_subst f) :: subst)
      (List.map var_subst lnamerec)
      lnonrec 
  in
  ()

let inductive_of_ident id =
  let c =
    try global_reference CCI id
    with Not_found ->
      errorlabstrm "inductive_of_ident"
	[< 'sTR ((string_of_id id) ^ " not found") >]
  in
  match kind_of_term (global_reference CCI id) with
    | IsMutInd ind -> ind
    | _ -> errorlabstrm "inductive_of_ident"
	[< 'sTR (string_of_id id); 'sPC; 'sTR "is not an inductive type" >]

let build_scheme lnamedepindsort = 
  let lrecnames = List.map (fun (f,_,_,_) -> f) lnamedepindsort
  and sigma = Evd.empty
  and env0 = Global.env() in
  let lrecspec =
    List.map (fun (_,dep,indid,sort) -> 
                let s = destSort (interp_constr sigma env0 sort) in
                (inductive_of_ident indid,dep,s)) lnamedepindsort
  in
  let n = NeverDischarge in 
  let listdecl = Indrec.build_mutual_indrec env0 sigma lrecspec in 
  let rec declare decl fi =
    let ce = { const_entry_body = decl; const_entry_type = None } 
    in declare_constant fi (ConstantEntry ce,n)
  in 
  List.iter2 declare listdecl lrecnames; 
  if is_verbose() then pPNL(recursive_message lrecnames)

let start_proof_com sopt stre com =
  let env = Global.env () in
  let sign = Global.named_context () in
  let id = match sopt with
    | Some id -> id
    | None ->
	next_ident_away (id_of_string "Unnamed_thm")
	  (Pfedit.get_all_proof_names ())
  in
  Pfedit.start_proof id stre sign (interp_type Evd.empty env com)

let save_named opacity =
  let id,(const,strength) = Pfedit.cook_proof () in
  declare_constant id (ConstantEntry const,strength);
  Pfedit.delete_current_proof ();
  if Options.is_verbose() then message ((string_of_id id) ^ " is defined")

let save_anonymous opacity save_ident strength =
  let id,(const,_) = Pfedit.cook_proof () in
  if atompart_of_id id <> "Unnamed_thm" then
    message("Overriding name "^(string_of_id id)^" and using "^save_ident);
  declare_constant (id_of_string save_ident) (ConstantEntry const,strength);
  Pfedit.delete_current_proof ();
  if Options.is_verbose() then message (save_ident ^ " is defined")

let save_anonymous_thm opacity id =
  save_anonymous opacity id NeverDischarge

let save_anonymous_remark opacity id =
  let path = try List.tl (List.tl (Lib.cwd())) with Failure _ -> [] in
  save_anonymous opacity id (make_strength path)

let get_current_context () =
  try Pfedit.get_current_goal_context ()
  with e when Logic.catchable_exception e -> 
    (Evd.empty, Global.env())
