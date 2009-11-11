open Closure
open RedFlags
open Declarations
open Entries
open Libobject
open Pattern
open Matching
open Pp
open Rawterm
open Sign
open Tacred
open Util
open Names
open Nameops
open Libnames
open Nametab
open Pfedit
open Proof_type
open Refiner
open Tacmach
open Tactic_debug
open Topconstr
open Term
open Termops
open Tacexpr
open Safe_typing
open Typing
open Hiddentac
open Genarg
open Decl_kinds
open Mod_subst
open Printer
open Inductiveops
open Syntax_def
open Environ
open Tactics
open Tacticals
open Tacinterp
open Vernacexpr
open Notation
open Evd
open Evarutil

module SPretyping = Subtac_pretyping.Pretyping
open Subtac_utils
open Pretyping
open Subtac_obligations

(*********************************************************************)
(* Functions to parse and interpret constructions *)

let evar_nf isevars c =
  Evarutil.nf_isevar !isevars c

let get_undefined_evars evd =
  Evd.fold (fun ev evi evd' ->
    if evi.evar_body = Evar_empty then
      Evd.add evd' ev (nf_evar_info evd evi)
    else evd') evd Evd.empty

let interp_gen kind isevars env
               ?(impls=([],[])) ?(allow_patvar=false) ?(ltacvars=([],[]))
               c =
  let c' = Constrintern.intern_gen (kind=IsType) ~impls ~allow_patvar ~ltacvars ( !isevars) env c in
  let c' = SPretyping.understand_tcc_evars isevars env kind c' in
    evar_nf isevars c'

let interp_constr isevars env c =
  interp_gen (OfType None) isevars env c

let interp_type_evars isevars env ?(impls=([],[])) c =
  interp_gen IsType isevars env ~impls c

let interp_casted_constr isevars env ?(impls=([],[])) c typ =
  interp_gen (OfType (Some typ)) isevars env ~impls c

let interp_casted_constr_evars isevars env ?(impls=([],[])) c typ =
  interp_gen (OfType (Some typ)) isevars env ~impls c

let interp_open_constr isevars env c =
    msgnl (str "Pretyping " ++ my_print_constr_expr c);
  let c = Constrintern.intern_constr ( !isevars) env c in
  let c' = SPretyping.understand_tcc_evars isevars env (OfType None) c in
    evar_nf isevars c'

let interp_constr_judgment isevars env c =
  let j =
    SPretyping.understand_judgment_tcc isevars env
      (Constrintern.intern_constr ( !isevars) env c)
  in
    { uj_val = evar_nf isevars j.uj_val; uj_type = evar_nf isevars j.uj_type }

let locate_if_isevar loc na = function
  | RHole _ ->
      (try match na with
	| Name id ->  Reserve.find_reserved_type id
	| Anonymous -> raise Not_found
      with Not_found -> RHole (loc, Evd.BinderType na))
  | x -> x

let interp_binder sigma env na t =
  let t = Constrintern.intern_gen true ( !sigma) env t in
    SPretyping.understand_tcc_evars sigma env IsType (locate_if_isevar (loc_of_rawconstr t) na t)

let interp_context_evars evdref env params =
  let bl = Constrintern.intern_context false ( !evdref) env params in
  let (env, par, _, impls) =
    List.fold_left
      (fun (env,params,n,impls) (na, k, b, t) ->
	match b with
	    None ->
	      let t' = locate_if_isevar (loc_of_rawconstr t) na t in
	      let t = SPretyping.understand_tcc_evars evdref env IsType t' in
	      let d = (na,None,t) in
	      let impls =
		if k = Implicit then
		  let na = match na with Name n -> Some n | Anonymous -> None in
		    (ExplByPos (n, na), (true, true, true)) :: impls
		else impls
	      in
		(push_rel d env, d::params, succ n, impls)
	  | Some b ->
	      let c = SPretyping.understand_judgment_tcc evdref env b in
	      let d = (na, Some c.uj_val, c.uj_type) in
		(push_rel d env,d::params, succ n, impls))
      (env,[],1,[]) (List.rev bl)
  in (env, par), impls

(* try to find non recursive definitions *)

let list_chop_hd i l = match list_chop i l with
  | (l1,x::l2) -> (l1,x,l2)
  | (x :: [], l2) -> ([], x, [])
  | _ -> assert(false)

let collect_non_rec env =
  let rec searchrec lnonrec lnamerec ldefrec larrec nrec =
    try
      let i =
        list_try_find_i
          (fun i f ->
             if List.for_all (fun (_, def) -> not (occur_var env f def)) ldefrec
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

let list_of_local_binders l =
  let rec aux acc = function
      Topconstr.LocalRawDef (n, c) :: tl -> aux ((n, Some c, None) :: acc) tl
    | Topconstr.LocalRawAssum (nl, k, c) :: tl ->
	aux (List.fold_left (fun acc n -> (n, None, Some c) :: acc) acc nl) tl
    | [] -> List.rev acc
  in aux [] l

let lift_binders k n l =
  let rec aux n = function
    | (id, t, c) :: tl -> (id, Option.map (liftn k n) t, liftn k n c) :: aux (pred n) tl
    | [] -> []
  in aux n l

let rec gen_rels = function
    0 -> []
  | n -> mkRel n :: gen_rels (pred n)

let split_args n rel = match list_chop ((List.length rel) - n) rel with
    (l1, x :: l2) -> l1, x, l2
  | _ -> assert(false)

open Coqlib

let sigT = Lazy.lazy_from_fun build_sigma_type
let sigT_info = lazy
  { ci_ind       = destInd (Lazy.force sigT).typ;
    ci_npar      = 2;
    ci_cstr_nargs = [|2|];
    ci_pp_info   =  { ind_nargs = 0; style = LetStyle }
  }

let telescope = function
  | [] -> assert false
  | [(n, None, t)] -> t, [n, Some (mkRel 1), t], mkRel 1
  | (n, None, t) :: tl ->
      let ty, tys, (k, constr) =
	List.fold_left
	  (fun (ty, tys, (k, constr)) (n, b, t) ->
	    let pred = mkLambda (n, t, ty) in
	    let sigty = mkApp ((Lazy.force sigT).typ, [|t; pred|]) in
	    let intro = mkApp ((Lazy.force sigT).intro, [|lift k t; lift k pred; mkRel k; constr|]) in
	      (sigty, pred :: tys, (succ k, intro)))
	  (t, [], (2, mkRel 1)) tl
      in
      let (last, subst) = List.fold_right2
	(fun pred (n, b, t) (prev, subst) ->
	  let proj1 = applistc (Lazy.force sigT).proj1 [t; pred; prev] in
	  let proj2 = applistc (Lazy.force sigT).proj2 [t; pred; prev] in
	    (lift 1 proj2, (n, Some proj1, t) :: subst))
	(List.rev tys) tl (mkRel 1, [])
      in ty, ((n, Some last, t) :: subst), constr

  | _ -> raise (Invalid_argument "telescope")

let build_wellfounded (recname,n,bl,arityc,body) r measure notation boxed =
  Coqlib.check_required_library ["Coq";"Program";"Wf"];
  let sigma = Evd.empty in
  let isevars = ref (Evd.create_evar_defs sigma) in
  let env = Global.env() in
  let _pr c = my_print_constr env c in
  let _prr = Printer.pr_rel_context env in
  let _prn = Printer.pr_named_context env in
  let _pr_rel env = Printer.pr_rel_context env in
  let (env', binders_rel), impls = interp_context_evars isevars env bl in
  let len = List.length binders_rel in
  let top_env = push_rel_context binders_rel env in
  let top_arity = interp_type_evars isevars top_env arityc in
  let full_arity = it_mkProd_or_LetIn top_arity binders_rel in
  let argtyp, letbinders, make = telescope binders_rel in
  let argname = id_of_string "recarg" in
  let arg = (Name argname, None, argtyp) in
  let binders = letbinders @ [arg] in
  let binders_env = push_rel_context binders_rel env in
  let rel = interp_constr isevars env r in
  let relty = type_of env !isevars rel in
  let relargty =
    let ctx, ar = Reductionops.splay_prod_n env !isevars 2 relty in
      match ctx, kind_of_term ar with
      | [(_, None, t); (_, None, u)], Sort (Prop Null)
	  when Reductionops.is_conv env !isevars t u -> t
      | _, _ ->
	  user_err_loc (constr_loc r,
		       "Subtac_command.build_wellfounded",
		       my_print_constr env rel ++ str " is not an homogeneous binary relation.")
  in
  let measure = interp_casted_constr isevars binders_env measure relargty in
  let wf_rel, wf_rel_fun, measure_fn =
    let measure_body, measure =
      it_mkLambda_or_LetIn measure letbinders,
      it_mkLambda_or_LetIn measure binders
    in
    let comb = constr_of_global (Lazy.force measure_on_R_ref) in
    let wf_rel = mkApp (comb, [| argtyp; relargty; rel; measure |]) in
    let wf_rel_fun x y =
      mkApp (rel, [| subst1 x measure_body;
 		     subst1 y measure_body |])
    in wf_rel, wf_rel_fun, measure
  in
  let wf_proof = mkApp (Lazy.force well_founded, [| argtyp ; wf_rel |]) in
  let argid' = id_of_string (string_of_id argname ^ "'") in
  let wfarg len = (Name argid', None,
  		  mkSubset (Name argid') argtyp
		    (wf_rel_fun (mkRel 1) (mkRel (len + 1))))
  in
  let intern_bl = wfarg 1 :: [arg] in
  let _intern_env = push_rel_context intern_bl env in
  let proj = (Lazy.force sig_).Coqlib.proj1 in
  let wfargpred = mkLambda (Name argid', argtyp, wf_rel_fun (mkRel 1) (mkRel 3)) in
  let projection = (* in wfarg :: arg :: before *)
    mkApp (proj, [| argtyp ; wfargpred ; mkRel 1 |])
  in
  let top_arity_let = it_mkLambda_or_LetIn top_arity letbinders in
  let intern_arity = substl [projection] top_arity_let in
  (* substitute the projection of wfarg for something,
     now intern_arity is in wfarg :: arg *)
  let intern_fun_arity_prod = it_mkProd_or_LetIn intern_arity [wfarg 1] in
  let intern_fun_binder = (Name (add_suffix recname "'"), None, intern_fun_arity_prod) in
  let curry_fun =
    let wfpred = mkLambda (Name argid', argtyp, wf_rel_fun (mkRel 1) (mkRel (2 * len + 4))) in
    let arg = mkApp ((Lazy.force sig_).intro, [| argtyp; wfpred; lift 1 make; mkRel 1 |]) in
    let app = mkApp (mkRel (2 * len + 2 (* recproof + orig binders + current binders *)), [| arg |]) in
    let rcurry = mkApp (rel, [| measure; lift len measure |]) in
    let lam = (Name (id_of_string "recproof"), None, rcurry) in
    let body = it_mkLambda_or_LetIn app (lam :: binders_rel) in
    let ty = it_mkProd_or_LetIn (lift 1 top_arity) (lam :: binders_rel) in
      (Name recname, Some body, ty)
  in
  let fun_bl = intern_fun_binder :: [arg] in
  let lift_lets = Termops.lift_rel_context 1 letbinders in
  let intern_body =
    let ctx = (Name recname, None, pi3 curry_fun) :: binders_rel in
    let (r, l, impls, scopes) = Constrintern.compute_internalization_data env Constrintern.Recursive full_arity impls in
    let newimpls = [(recname, (r, l, impls @ [Some (id_of_string "recproof", Impargs.Manual, (true, false))], scopes @ [None]))] in
    let newimpls = Constrintern.set_internalization_env_params newimpls [] in
    interp_casted_constr isevars ~impls:newimpls
      (push_rel_context ctx env) body (lift 1 top_arity)
  in
  let intern_body_lam = it_mkLambda_or_LetIn intern_body (curry_fun :: lift_lets @ fun_bl) in
  let prop = mkLambda (Name argname, argtyp, top_arity_let) in
  let def =
    mkApp (constr_of_global (Lazy.force fix_sub_ref),
	  [| argtyp ; wf_rel ;
	     make_existential dummy_loc ~opaque:(Define false) env isevars wf_proof ;
	     prop ; intern_body_lam |])
  in
  let hook, recname, typ = 
    if List.length binders_rel > 1 then
      let name = add_suffix recname "_func" in
      let hook l gr = 
	let body = it_mkLambda_or_LetIn (mkApp (constr_of_global gr, [|make|])) binders_rel in
	let ty = it_mkProd_or_LetIn top_arity binders_rel in
	let ce =
	  { const_entry_body = body;
	    const_entry_type = Some ty;
	    const_entry_opaque = false;
	    const_entry_boxed = false} 
	in 
	let c = Declare.declare_constant recname (DefinitionEntry ce, IsDefinition Definition) in
	let gr = ConstRef c in
	  if Impargs.is_implicit_args () || impls <> [] then
	    Impargs.declare_manual_implicits false gr impls
      in
      let typ = it_mkProd_or_LetIn top_arity binders in
	hook, name, typ
    else 
      let typ = it_mkProd_or_LetIn top_arity binders_rel in
      let hook l gr = 
	if Impargs.is_implicit_args () || impls <> [] then
	  Impargs.declare_manual_implicits false gr impls
      in hook, recname, typ
  in
  let _ = isevars := Evarutil.nf_evar_defs !isevars in
  let fullcoqc = Evarutil.nf_isevar !isevars def in
  let fullctyp = Evarutil.nf_isevar !isevars typ in
  let evm = evars_of_term !isevars Evd.empty fullctyp in
  let evm = evars_of_term !isevars evm fullcoqc in
  let evm = non_instanciated_map env isevars evm in
  let evars, _, evars_def, evars_typ = Eterm.eterm_obligations env recname !isevars evm 0 fullcoqc fullctyp in
    Subtac_obligations.add_definition recname ~term:evars_def evars_typ evars ~hook

let nf_evar_context isevars ctx =
  List.map (fun (n, b, t) ->
    (n, Option.map (Evarutil.nf_isevar isevars) b, Evarutil.nf_isevar isevars t)) ctx

let interp_fix_context evdref env fix =
  interp_context_evars evdref env fix.Command.fix_binders

let interp_fix_ccl evdref (env,_) fix =
  interp_type_evars evdref env fix.Command.fix_type

let interp_fix_body evdref env_rec impls (_,ctx) fix ccl =
  let env = push_rel_context ctx env_rec in
  let body = interp_casted_constr_evars evdref env ~impls fix.Command.fix_body ccl in
  it_mkLambda_or_LetIn body ctx

let build_fix_type (_,ctx) ccl = it_mkProd_or_LetIn ccl ctx

let prepare_recursive_declaration fixnames fixtypes fixdefs =
  let defs = List.map (subst_vars (List.rev fixnames)) fixdefs in
  let names = List.map (fun id -> Name id) fixnames in
  (Array.of_list names, Array.of_list fixtypes, Array.of_list defs)

let rel_index n ctx =
  list_index0 (Name n) (List.rev_map pi1 (List.filter (fun x -> pi2 x = None) ctx))

let rec unfold f b =
  match f b with
    | Some (x, b') -> x :: unfold f b'
    | None -> []

let compute_possible_guardness_evidences (n,_) (_, fixctx) fixtype =
  match n with
  | Some (loc, n) -> [rel_index n fixctx]
  | None ->
      (* If recursive argument was not given by user, we try all args.
	 An earlier approach was to look only for inductive arguments,
	 but doing it properly involves delta-reduction, and it finally
         doesn't seem to worth the effort (except for huge mutual
	 fixpoints ?) *)
      let len = List.length fixctx in
	unfold (function x when x = len -> None
	  | n -> Some (n, succ n)) 0

let push_named_context = List.fold_right push_named

let check_evars env initial_sigma evd c =
  let sigma =  evd in
  let c = nf_evar sigma c in
  let rec proc_rec c =
    match kind_of_term c with
      | Evar (evk,args) ->
          assert (Evd.mem sigma evk);
	  if not (Evd.mem initial_sigma evk) then
            let (loc,k) = evar_source evk evd in
	      (match k with
	      | QuestionMark _
	      | ImplicitArg (_, _, false) -> ()
	      | _ ->
		  let evi = nf_evar_info sigma (Evd.find sigma evk) in
		    Pretype_errors.error_unsolvable_implicit loc env sigma evi k None)
      | _ -> iter_constr proc_rec c
  in proc_rec c

let interp_recursive fixkind l boxed =
  let env = Global.env() in
  let fixl, ntnl = List.split l in
  let kind = fixkind <> IsCoFixpoint in
  let fixnames = List.map (fun fix -> fix.Command.fix_name) fixl in

  (* Interp arities allowing for unresolved types *)
  let evdref = ref Evd.empty in
  let fixctxs, fiximps = List.split (List.map (interp_fix_context evdref env) fixl) in
  let fixccls = List.map2 (interp_fix_ccl evdref) fixctxs fixl in
  let fixtypes = List.map2 build_fix_type fixctxs fixccls in
  let rec_sign =
    List.fold_left2 (fun env' id t ->
      let sort = Retyping.get_type_of env !evdref t in
      let fixprot =
	try mkApp (Lazy.force Subtac_utils.fix_proto, [|sort; t|])
	with e -> t
      in
	(id,None,fixprot) :: env')
      [] fixnames fixtypes
  in
  let env_rec = push_named_context rec_sign env in

  (* Get interpretation metadatas *)
  let impls = Constrintern.compute_full_internalization_env env Constrintern.Recursive [] fixnames fixtypes fiximps in
  let notations = List.flatten ntnl in

  (* Interp bodies with rollback because temp use of notations/implicit *)
  let fixdefs =
    States.with_state_protection (fun () ->
      List.iter (Metasyntax.set_notation_for_interpretation impls) notations;
      list_map3 (interp_fix_body evdref env_rec impls) fixctxs fixl fixccls)
      () in

  (* Instantiate evars and check all are resolved *)
  let evd,_ = Evarconv.consider_remaining_unif_problems env_rec !evdref in
  let evd = Typeclasses.resolve_typeclasses
    ~onlyargs:true ~split:true ~fail:false env_rec evd
  in
  let evd = Evarutil.nf_evar_defs evd in
  let fixdefs = List.map (nf_evar evd) fixdefs in
  let fixtypes = List.map (nf_evar evd) fixtypes in
  let rec_sign = nf_named_context_evar evd rec_sign in

  let recdefs = List.length rec_sign in
  List.iter (check_evars env_rec Evd.empty evd) fixdefs;
  List.iter (check_evars env Evd.empty evd) fixtypes;
  Command.check_mutuality env kind (List.combine fixnames fixdefs);

  (* Russell-specific code *)

  (* Get the interesting evars, those that were not instanciated *)
  let isevars = Evd.undefined_evars evd in
  let evm =  isevars in
  (* Solve remaining evars *)
  let rec collect_evars id def typ imps =
      (* Generalize by the recursive prototypes  *)
    let def =
      Termops.it_mkNamedLambda_or_LetIn def rec_sign
    and typ =
      Termops.it_mkNamedProd_or_LetIn typ rec_sign
    in
    let evm' = Subtac_utils.evars_of_term evm Evd.empty def in
    let evm' = Subtac_utils.evars_of_term evm evm' typ in
    let evars, _, def, typ = Eterm.eterm_obligations env id isevars evm' recdefs def typ in
      (id, def, typ, imps, evars)
  in
  let defs = list_map4 collect_evars fixnames fixdefs fixtypes fiximps in
    (match fixkind with
      | IsFixpoint wfl ->
	  let possible_indexes =
	    list_map3 compute_possible_guardness_evidences wfl fixctxs fixtypes in
	  let fixdecls = Array.of_list (List.map (fun x -> Name x) fixnames),
	    Array.of_list fixtypes,
	    Array.of_list (List.map (subst_vars (List.rev fixnames)) fixdefs)
	  in
	  let indexes = Pretyping.search_guard dummy_loc (Global.env ()) possible_indexes fixdecls in
	    list_iter_i (fun i _ -> Inductive.check_fix env ((indexes,i),fixdecls)) l
      | IsCoFixpoint -> ());
    Subtac_obligations.add_mutual_definitions defs notations fixkind

let out_n = function
    Some n -> n
  | None -> raise Not_found

let build_recursive l b =
  let g = List.map (fun ((_,wf,_,_,_),_) -> wf) l in
    match g, l with
	[(n, CWfRec r)], [(((_,id),_,bl,typ,def),ntn)] ->
	  ignore(build_wellfounded (id, n, bl, typ, def) r
		    (match n with Some n -> mkIdentC (snd n) | None ->
		      errorlabstrm "Subtac_command.build_recursive"
			(str "Recursive argument required for well-founded fixpoints"))
		    ntn false)

      | [(n, CMeasureRec (m, r))], [(((_,id),_,bl,typ,def),ntn)] ->
	  ignore(build_wellfounded (id, n, bl, typ, def) (Option.default (CRef lt_ref) r)
		    m ntn false)

      | _, _ when List.for_all (fun (n, ro) -> ro = CStructRec) g ->
	  let fixl = List.map (fun (((_,id),_,bl,typ,def),ntn) ->
	    ({Command.fix_name = id; Command.fix_binders = bl; Command.fix_body = def; Command.fix_type = typ},ntn)) l
	  in interp_recursive (IsFixpoint g) fixl b
      | _, _ ->
	  errorlabstrm "Subtac_command.build_recursive"
	    (str "Well-founded fixpoints not allowed in mutually recursive blocks")

let build_corecursive l b =
  let fixl = List.map (fun (((_,id),bl,typ,def),ntn) ->
    ({Command.fix_name = id; Command.fix_binders = bl; Command.fix_body = def; Command.fix_type = typ},ntn))
    l in
  interp_recursive IsCoFixpoint fixl b
