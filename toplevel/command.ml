(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Options
open Term
open Termops
open Declarations
open Inductive
open Environ
open Reduction
open Tacred
open Declare
open Nametab
open Names
open Libnames
open Nameops
open Coqast
open Ast
open Library
open Libobject
open Astterm
open Proof_type
open Tacmach
open Safe_typing
open Nametab
open Typeops
open Indtypes

let mkCastC(a,b) = ope("CAST",[a;b])
let mkLambdaC(x,a,b) = ope("LAMBDA",[a;slam(Some x,b)])
let mkLambdaCit = List.fold_right (fun (x,a) b -> mkLambdaC(x,a,b))
let mkProdC (x,a,b) = ope("PROD",[a;slam(Some x,b)])
let mkProdCit = List.fold_right (fun (x,a) b -> mkProdC(x,a,b))

(* Commands of the interface *)

(* 1| Constant definitions *)

let constant_entry_of_com (com,comtypopt,opacity) =
  let sigma = Evd.empty in
  let env = Global.env() in
  match comtypopt with
      None -> 
	{ const_entry_body = interp_constr sigma env com;
	  const_entry_type = None;
          const_entry_opaque = opacity }
    | Some comtyp ->
	(* We use a cast to avoid troubles with evars in comtyp *)
	(* that can only be resolved knowing com *)
	let b = mkCastC (com,comtyp) in
	let (body,typ) = destCast (interp_constr sigma env b) in
	{ const_entry_body = body;
	  const_entry_type = Some typ;
          const_entry_opaque = opacity }

let red_constant_entry ce = function
  | None -> ce
  | Some red ->
      let body = ce.const_entry_body in
      { ce with const_entry_body = 
	  reduction_of_redexp red (Global.env()) Evd.empty body }

let declare_global_definition ident ce n local =
  let sp = declare_constant ident (ConstantEntry ce,n) in
  if local then
    msg_warning (pr_id ident ++ str" is declared as a global definition");
  if_verbose message ((string_of_id ident) ^ " is defined");
  ConstRef sp

let declare_definition red_option ident (local,n) c typopt = 
  let ce = constant_entry_of_com (c,typopt,false) in
  let ce' = red_constant_entry ce red_option in
  match n with
    | NeverDischarge -> declare_global_definition ident ce' n local
    | DischargeAt (disch_sp,_) ->
        if Lib.is_section_p disch_sp then begin
	  let c = SectionLocalDef(ce'.const_entry_body,ce'.const_entry_type) in
          let sp = declare_variable ident (Lib.cwd(), c, n) in
	  if_verbose message ((string_of_id ident) ^ " is defined");
          if Pfedit.refining () then 
            msgerrnl (str"Warning: Local definition " ++ pr_id ident ++ 
                      str" is not visible from current goals");
	  VarRef ident
        end
	else
	  declare_global_definition ident ce' n true
    | NotDeclare ->
      anomalylabstrm "Command.definition_body_red"
        (str "Strength NotDeclare not for Definition, only for Let")

let syntax_definition ident c =
  let c = interp_rawconstr Evd.empty (Global.env()) c in 
  Syntax_def.declare_syntactic_definition ident c;
  if_verbose message ((string_of_id ident) ^ " is now a syntax macro")

(* 2| Variable/Hypothesis/Parameter/Axiom declarations *)

let assumption_message id =
  if_verbose message ((string_of_id id) ^ " is assumed")

let declare_assumption ident n c =
  let c = interp_type Evd.empty (Global.env()) c in
  match n with
    | NeverDischarge ->
	let _ = declare_constant ident (ParameterEntry c, NeverDischarge) in
	assumption_message ident
    | DischargeAt (disch_sp,_) ->
        if Lib.is_section_p disch_sp then begin
          let _ = declare_variable ident (Lib.cwd(),SectionLocalAssum c,n) in
	  assumption_message ident;
          if is_verbose () & Pfedit.refining () then 
            msgerrnl (str"Warning: Variable " ++ pr_id ident ++ 
                      str" is not visible from current goals")
        end
	else
	  let _ = declare_constant ident (ParameterEntry c, NeverDischarge) in
	  assumption_message ident;
	  if_verbose
	    msg_warning (pr_id ident ++ str" is declared as a parameter" ++
               str" because it is at a global level");
    | NotDeclare ->
      anomalylabstrm "Command.hypothesis_def_var"
        (str "Strength NotDeclare not for Variable, only for Let")

(* 3| Mutual Inductive definitions *)

let minductive_message = function 
  | []  -> error "no inductive definition"
  | [x] -> (pr_id x ++ str " is defined")
  | l   -> hov 0  (prlist_with_sep pr_coma pr_id l ++
		     spc () ++ str "are defined")

let recursive_message v =
  match Array.length v with
    | 0 -> error "no recursive definition"
    | 1 -> (Printer.pr_global v.(0) ++ str " is recursively defined")
    | _ -> hov 0 (prvect_with_sep pr_coma Printer.pr_global v ++
		    spc () ++ str "are recursively defined")

let corecursive_message v =
  match Array.length v with
    | 0 -> error "no corecursive definition"
    | 1 -> (Printer.pr_global v.(0) ++ str " is corecursively defined")
    | _ -> hov 0 (prvect_with_sep pr_coma Printer.pr_global v ++
                    spc () ++ str "are corecursively defined")

let interp_mutual lparams lnamearconstrs finite = 
  let allnames = 
    List.fold_left 
      (fun acc (id,_,l) -> id::(List.map fst l)@acc) [] lnamearconstrs in
  if not (list_distinct allnames) then
    error "Two inductive objects have the same name";
  let nparams = List.length lparams
  and sigma = Evd.empty 
  and env0 = Global.env() in
  let env_params, params =
    List.fold_left
      (fun (env, params) (id,t) ->
	 let p = interp_type sigma env t in
	 (Termops.push_rel_assum (Name id,p) env, (Name id,None,p)::params))
      (env0,[]) lparams
  in
  (* Pour permettre à terme les let-in dans les params *)
  let params' =
    List.map (fun (na,_,p) ->
		let id = match na with
		  | Name id -> id
		  | Anonymous -> anomaly "Unnamed inductive variable"
		in (id, LocalAssum p)) params
  in
  let (ind_env,ind_impls,arityl) =
    List.fold_left
      (fun (env, ind_impls, arl) (recname, arityc,_) ->
         let arity = interp_type sigma env_params arityc in
	 let fullarity =
           prod_it arity (List.map (fun (id,_,ty) -> (id,ty)) params) in
	 let env' = Termops.push_rel_assum (Name recname,fullarity) env in
	 let impls = 
	   if Impargs.is_implicit_args()
	   then Impargs.compute_implicits env_params fullarity
	   else [] in
	 (env', (recname,impls)::ind_impls, (arity::arl)))
      (env0, [], []) lnamearconstrs
  in
  let ind_env_params = push_rel_context params ind_env in
  let mispecvec = 
    List.map2
      (fun ar (name,_,lname_constr) ->
	 let constrnames, bodies = List.split lname_constr in
         let constrs =
	   List.map 
	     (interp_type_with_implicits sigma ind_env_params ind_impls) bodies
	 in
	 { mind_entry_params = params';
	   mind_entry_typename = name;
	   mind_entry_arity = ar;
	   mind_entry_consnames = constrnames;
	   mind_entry_lc = constrs })
      (List.rev arityl) lnamearconstrs
  in
  { mind_entry_finite = finite; mind_entry_inds = mispecvec }

let declare_mutual_with_eliminations mie =
  let lrecnames =
    List.map (fun e -> e.mind_entry_typename) mie.mind_entry_inds in
  let sp = declare_mind mie in
  if_verbose ppnl (minductive_message lrecnames);
  Indrec.declare_eliminations sp;
  sp

let eq_la (id,ast) (id',ast') = id = id' & alpha_eq(ast,ast')

let extract_coe lc =
  List.fold_right
    (fun (id,addcoe,t) (l1,l2) ->
      ((if addcoe then id::l1 else l1), (id,t)::l2)) lc ([],[])

let extract_coe_la_lc = function
  | []            -> anomaly "Vernacentries: empty list of inductive types"
  | (id,la,ar,lc)::rest ->
      let rec check = function 
	| []             -> [],[]
  	| (id,la',ar,lc)::rest ->
            if (List.length la = List.length la') && 
               (List.for_all2 eq_la la la')
	    then
	      let mcoes, mspec = check rest in
	      let coes, lc' = extract_coe lc in
	      (coes::mcoes,(id,ar,lc')::mspec)
	    else 
	      error ("Parameters should be syntactically the same "^
		     "for each inductive type")
      in
      let mcoes, mspec = check rest in
      let coes, lc' = extract_coe lc in
      (coes,la,(id,ar,lc'):: mspec)

let build_mutual lind finite =
  let (coes,lparams,lnamearconstructs) = extract_coe_la_lc lind in
  let mie = interp_mutual lparams lnamearconstructs finite in
  let _ = declare_mutual_with_eliminations mie in
  List.iter
    (fun id -> 
      Class.try_add_new_coercion
        (locate (make_short_qualid id)) NeverDischarge) coes

(* try to find non recursive definitions *)

let list_chop_hd i l = match list_chop i l with
  | (l1,x::l2) -> (l1,x,l2)
  | _ -> assert false

let collect_non_rec env = 
  let rec searchrec lnonrec lnamerec ldefrec larrec nrec = 
    try
      let i = 
        list_try_find_i
          (fun i f ->
             if List.for_all (fun def -> not (occur_var env f def)) ldefrec
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
      searchrec ((f,def,ar)::lnonrec) 
	(lf1@lf2) (ldef1@ldef2) (lar1@lar2) newlnv
    with Failure "try_find_i" -> 
      (List.rev lnonrec,
       (Array.of_list lnamerec, Array.of_list ldefrec,
        Array.of_list larrec, Array.of_list nrec))
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
           let arity = interp_type sigma env0 raw_arity in
           let _ = declare_variable recname
	     (Lib.cwd(),SectionLocalAssum arity, NeverDischarge) in
           (Environ.push_named (recname,None,arity) env, (arity::arl)))
        (env0,[]) lnameargsardef
    with e ->
      States.unfreeze fs; raise e in
  let arityl = List.rev arityl in
  let recdef =
    try 
      List.map2
	(fun (_,lparams,_,def) arity ->
           interp_casted_constr sigma rec_sign (mkLambdaCit lparams def) arity)
        lnameargsardef arityl
    with e ->
      States.unfreeze fs; raise e
  in
  States.unfreeze fs;
  let (lnonrec,(namerec,defrec,arrec,nvrec)) = 
    collect_non_rec env0 lrecnames recdef arityl (Array.to_list nv) in
  let n = NeverDischarge in 
  let recvec = 
    Array.map (subst_vars (List.rev (Array.to_list namerec))) defrec in
  let rec declare i fi =
    let ce = 
      { const_entry_body =
	  mkFix ((nvrec,i),
	         (Array.map (fun id -> Name id) namerec,
                  arrec,
		  recvec));
        const_entry_type = None;
        const_entry_opaque = false } in
    let sp = declare_constant fi (ConstantEntry ce, n) in
    (ConstRef sp)
  in 
  (* declare the recursive definitions *)
  let lrefrec = Array.mapi declare namerec in
  if_verbose ppnl (recursive_message lrefrec);
  (* The others are declared as normal definitions *)
  let var_subst id = (id, global_reference id) in
  let _ = 
    List.fold_left
      (fun subst (f,def,t) ->
	 let ce = { const_entry_body = replace_vars subst def;
		    const_entry_type = Some t;
                    const_entry_opaque = false } in
	 let _ = declare_constant f (ConstantEntry ce,n) in
      	 warning ((string_of_id f)^" is non-recursively defined");
      	 (var_subst f) :: subst)
      (List.map var_subst (Array.to_list namerec))
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
           let _ = declare_variable recname
	     (Lib.cwd(),SectionLocalAssum arj.utj_val,NeverDischarge) in
           (Environ.push_named (recname,None,arity) env, (arity::arl)))
        (env0,[]) lnameardef
    with e -> 
      States.unfreeze fs; raise e in 
  let arityl = List.rev arityl in
  let recdef =
    try 
      List.map (fun (_,arityc,def) ->
		  let arity = interp_constr sigma rec_sign arityc in
                  interp_casted_constr sigma rec_sign def arity)
        lnameardef
    with e -> 
      States.unfreeze fs; raise e 
  in
  States.unfreeze fs;
  let (lnonrec,(namerec,defrec,arrec,_)) = 
    collect_non_rec env0 lrecnames recdef arityl [] in
  let n = NeverDischarge in 
  let recvec = 
    Array.map (subst_vars (List.rev (Array.to_list namerec))) defrec in
  let rec declare i fi =
    let ce = 
      { const_entry_body =
	  mkCoFix (i, (Array.map (fun id -> Name id) namerec,
                       arrec,
		       recvec));
        const_entry_type = None;
        const_entry_opaque = false } 
    in
    let sp = declare_constant fi (ConstantEntry ce,n) in
    (ConstRef sp)
  in 
  let lrefrec = Array.mapi declare namerec in
  if_verbose ppnl (corecursive_message lrefrec);
  let var_subst id = (id, global_reference id) in
  let _ = 
    List.fold_left
      (fun subst (f,def,t) ->
	 let ce = { const_entry_body = replace_vars subst def;
		    const_entry_type = Some t;
                    const_entry_opaque = false } in
	 let _ = declare_constant f (ConstantEntry ce,n) in
      	 warning ((string_of_id f)^" is non-recursively defined");
      	 (var_subst f) :: subst)
      (List.map var_subst (Array.to_list namerec))
      lnonrec 
  in
  ()

let build_scheme lnamedepindsort = 
  let lrecnames = List.map (fun (f,_,_,_) -> f) lnamedepindsort
  and sigma = Evd.empty
  and env0 = Global.env() in
  let lrecspec =
    List.map
      (fun (_,dep,indid,sort) ->
        let ind = Nametab.global_inductive indid in
        let (mib,mip) = Global.lookup_inductive ind in
         (ind,mib,mip,dep,interp_elimination_sort sort)) 
      lnamedepindsort
  in
  let n = NeverDischarge in 
  let listdecl = Indrec.build_mutual_indrec env0 sigma lrecspec in 
  let rec declare decl fi lrecref =
    let ce = { const_entry_body = decl;
               const_entry_type = None;
               const_entry_opaque = false } in
    let sp = declare_constant fi (ConstantEntry ce,n) in
    ConstRef sp :: lrecref
  in 
  let lrecref = List.fold_right2 declare listdecl lrecnames [] in
  if_verbose ppnl (recursive_message (Array.of_list lrecref))

let start_proof_com sopt (local,stre) com hook =
  let env = Global.env () in
  let sign = Global.named_context () in
  let id = match sopt with
    | Some id ->
        (* We check existence here: it's a bit late at Qed time *)
        if Nametab.exists_cci (Lib.make_path id) then
          errorlabstrm "start_proof" (pr_id id ++ str " already exists");
        id
    | None ->
	next_ident_away (id_of_string "Unnamed_thm")
	  (Pfedit.get_all_proof_names ())
  in
  let c = interp_type Evd.empty env com in
  let _ = Typeops.infer_type env c in
  Pfedit.start_proof id (local,stre) sign c hook

let apply_tac_not_declare id pft = function
  | None -> error "Type of Let missing"
  | Some typ ->
    let cutt = Hiddentac.h_cut typ
    and exat = Hiddentac.h_exact pft in
    Pfedit.delete_current_proof ();
    Pfedit.by (Refiner.tclTHENSV cutt [|introduction id;exat|])

let save id const strength hook =
  let {const_entry_body = pft;
       const_entry_type = tpo;
       const_entry_opaque = opacity } = const in
  begin match strength with
    | DischargeAt (disch_sp,_) when Lib.is_section_p disch_sp && not opacity ->
	let c = SectionLocalDef (pft, tpo) in
	let _ = declare_variable id (Lib.cwd(), c, strength) in
	hook strength (VarRef id)
    | NeverDischarge | DischargeAt _ ->
        let ref = ConstRef (declare_constant id (ConstantEntry const,strength)) in
	hook strength ref
    | NotDeclare -> apply_tac_not_declare id pft tpo
  end;
  if not (strength = NotDeclare) then
  begin
    Pfedit.delete_current_proof ();
    if_verbose message ((string_of_id id) ^ " is defined")
  end

let save_named opacity =
  let id,(const,(local,strength),hook) = Pfedit.cook_proof () in
  let const = { const with const_entry_opaque = opacity } in
  save id const strength hook

let check_anonymity id save_ident =
  if atompart_of_id id <> "Unnamed_thm" then
    error "This command can only be used for unnamed theorem"
(*
    message("Overriding name "^(string_of_id id)^" and using "^save_ident)
*)

let save_anonymous opacity save_ident =
  let id,(const,(local,strength),hook) = Pfedit.cook_proof () in
  let const = { const with const_entry_opaque = opacity } in
  check_anonymity id save_ident;
  save save_ident const strength hook

let save_anonymous_with_strength strength opacity save_ident =
  let id,(const,_,hook) = Pfedit.cook_proof () in
  let const = { const with const_entry_opaque = opacity } in
  check_anonymity id save_ident;
  save save_ident const strength hook

let get_current_context () =
  try Pfedit.get_current_goal_context ()
  with e when Logic.catchable_exception e -> 
    (Evd.empty, Global.env())
