open Evd
open Libnames
open Coqlib
open Term
open Names
open Util

(****************************************************************************)
(* Library linking *)

let contrib_name = "subtac"

let subtac_dir = [contrib_name]
let fix_sub_module = "FixSub"
let utils_module = "Utils"
let fixsub_module = subtac_dir @ [fix_sub_module]
let utils_module = subtac_dir @ [utils_module]
let init_constant dir s = gen_constant contrib_name dir s
let init_reference dir s = gen_reference contrib_name dir s

let fixsub = lazy (init_constant fixsub_module "Fix_sub")
let ex_pi1 = lazy (init_constant utils_module "ex_pi1")
let ex_pi2 = lazy (init_constant utils_module "ex_pi2")

let make_ref l s = lazy (init_reference l s)
let well_founded_ref = make_ref ["Init";"Wf"] "Well_founded"
let acc_ref = make_ref  ["Init";"Wf"] "Acc"
let acc_inv_ref = make_ref  ["Init";"Wf"] "Acc_inv"
let fix_sub_ref = make_ref ["subtac";"FixSub"] "Fix_sub"
let fix_measure_sub_ref = make_ref ["subtac";"FixSub"] "Fix_measure_sub"
let lt_ref = make_ref ["Init";"Peano"] "lt"
let lt_wf_ref = make_ref ["Wf_nat"] "lt_wf"

let make_ref s = Qualid (dummy_loc, qualid_of_string s)
let sig_ref = make_ref "Init.Specif.sig"
let proj1_sig_ref = make_ref "Init.Specif.proj1_sig"
let proj2_sig_ref = make_ref "Init.Specif.proj2_sig"

let build_sig () = 
  { proj1 = init_constant ["Init"; "Specif"] "proj1_sig";
    proj2 = init_constant ["Init"; "Specif"] "proj2_sig";
    elim = init_constant ["Init"; "Specif"] "sig_rec";
    intro = init_constant ["Init"; "Specif"] "exist";
    typ = init_constant ["Init"; "Specif"] "sig" }

let sig_ = lazy (build_sig ())

let eq_ind = lazy (init_constant ["Init"; "Logic"] "eq")
let eq_rec = lazy (init_constant ["Init"; "Logic"] "eq_rec")
let eq_ind_ref = lazy (init_reference ["Init"; "Logic"] "eq")
let refl_equal_ref = lazy (init_reference ["Init"; "Logic"] "refl_equal")

let eqdep_ind = lazy (init_constant [ "Logic";"Eqdep"] "eq_dep")
let eqdep_rec = lazy (init_constant ["Logic";"Eqdep"] "eq_dep_rec")
let eqdep_ind_ref = lazy (init_reference [ "Logic";"Eqdep"] "eq_dep")
let eqdep_intro_ref = lazy (init_reference [ "Logic";"Eqdep"] "eq_dep_intro")

let jmeq_ind = lazy (init_constant ["Logic";"JMeq"] "JMeq")
let jmeq_rec = lazy (init_constant ["Logic";"JMeq"] "JMeq_rec")
let jmeq_ind_ref = lazy (init_reference ["Logic";"JMeq"] "JMeq")
let jmeq_refl_ref = lazy (init_reference ["Logic";"JMeq"] "JMeq_refl")

let ex_ind = lazy (init_constant ["Init"; "Logic"] "ex")
let ex_intro = lazy (init_reference ["Init"; "Logic"] "ex_intro")

let proj1 = lazy (init_constant ["Init"; "Logic"] "proj1")
let proj2 = lazy (init_constant ["Init"; "Logic"] "proj2")

let boolind = lazy (init_constant ["Init"; "Datatypes"] "bool")
let sumboolind = lazy (init_constant ["Init"; "Specif"] "sumbool")
let natind = lazy (init_constant ["Init"; "Datatypes"] "nat")
let intind = lazy (init_constant ["ZArith"; "binint"] "Z")
let existSind = lazy (init_constant ["Init"; "Specif"] "sigS")
  
let existS = lazy (build_sigma_type ())

let prod = lazy (build_prod ())


(* orders *)
let well_founded = lazy (init_constant ["Init"; "Wf"] "well_founded")
let fix = lazy (init_constant ["Init"; "Wf"] "Fix")
let acc = lazy (init_constant ["Init"; "Wf"] "Acc")
let acc_inv = lazy (init_constant ["Init"; "Wf"] "Acc_inv")

let extconstr = Constrextern.extern_constr true (Global.env ())
let extsort s = Constrextern.extern_constr true (Global.env ()) (mkSort s)

open Pp

let my_print_constr = Termops.print_constr_env
let my_print_constr_expr = Ppconstr.pr_constr_expr
let my_print_rel_context env ctx = Printer.pr_rel_context env ctx
let my_print_context = Termops.print_rel_context
let my_print_named_context = Termops.print_named_context
let my_print_env = Termops.print_env
let my_print_rawconstr = Printer.pr_rawconstr_env
let my_print_evardefs = Evd.pr_evar_defs

let my_print_tycon_type = Evarutil.pr_tycon_type

let debug_level = 2

let debug_on = true

let debug n s = 
  if debug_on then
    if !Options.debug && n >= debug_level then
      msgnl s
    else ()
  else ()

let debug_msg n s = 
  if debug_on then
    if !Options.debug  && n >= debug_level then s
    else mt ()
  else mt ()

let trace s = 
  if debug_on then
    if !Options.debug  && debug_level > 0 then msgnl s
    else ()
  else ()

let wf_relations = Hashtbl.create 10

let std_relations () = 
  let add k v = Hashtbl.add wf_relations k v in
    add (init_constant ["Init"; "Peano"] "lt")
      (lazy (init_constant ["Arith"; "Wf_nat"] "lt_wf"))
      
let std_relations = Lazy.lazy_from_fun std_relations

type binders = Topconstr.local_binder list

let app_opt c e = 
  match c with
      Some constr -> constr e
    | None -> e	

let print_args env args = 
  Array.fold_right (fun a acc -> my_print_constr env a ++ spc () ++ acc) args (str "")

let make_existential loc env isevars c =
  let evar = Evarutil.e_new_evar isevars env ~src:(loc, QuestionMark) c in
  let (key, args) = destEvar evar in
    (try debug 2 (str "Constructed evar " ++ int key ++ str " applied to args: " ++
		  print_args env args) with _ -> ());
    evar

let make_existential_expr loc env c =
  let key = Evarutil.new_untyped_evar () in
  let evar = Topconstr.CEvar (loc, key) in
    debug 2 (str "Constructed evar " ++ int key);
    evar

let string_of_hole_kind = function
  | ImplicitArg _ -> "ImplicitArg"
  | BinderType _ -> "BinderType"
  | QuestionMark -> "QuestionMark"
  | CasesType -> "CasesType"
  | InternalHole -> "InternalHole"
  | TomatchTypeParameter _ -> "TomatchTypeParameter"
      
let non_instanciated_map env evd =
  let evm = evars_of !evd in
    List.fold_left 
      (fun evm (key, evi) -> 
	 let (loc,k) = evar_source key !evd in
	   debug 2 (str "evar " ++ int key ++ str " has kind " ++ 
		      str (string_of_hole_kind k));
	   match k with 
	       QuestionMark -> Evd.add evm key evi
	     | _ ->
	       debug 2 (str " and is an implicit");
	       Pretype_errors.error_unsolvable_implicit loc env evm k)
      Evd.empty (Evarutil.non_instantiated evm)

let global_kind = Decl_kinds.IsDefinition Decl_kinds.Definition
let goal_kind = Decl_kinds.Global, Decl_kinds.DefinitionBody Decl_kinds.Definition

let global_proof_kind = Decl_kinds.IsProof Decl_kinds.Lemma
let goal_proof_kind = Decl_kinds.Global, Decl_kinds.Proof Decl_kinds.Lemma

let global_fix_kind = Decl_kinds.IsDefinition Decl_kinds.Fixpoint
let goal_fix_kind = Decl_kinds.Global, Decl_kinds.DefinitionBody Decl_kinds.Fixpoint

open Tactics
open Tacticals

let id x = x
let filter_map f l = 
  let rec aux acc = function
      hd :: tl -> (match f hd with Some t -> aux (t :: acc) tl
		     | None -> aux acc tl)
    | [] -> List.rev acc
  in aux [] l

let build_dependent_sum l =
  let rec aux names conttac conttype = function
      (n, t) :: ((_ :: _) as tl) ->
	let hyptype = substl names t in
	  trace (spc () ++ str ("treating evar " ^ string_of_id n));
	  (try trace (str " assert: " ++ my_print_constr (Global.env ()) hyptype)
	   with _ -> ());
	let tac = assert_tac true (Name n) hyptype in
	let conttac = 
	  (fun cont -> 
	     conttac
	     (tclTHENS tac
		([intros;
		  (tclTHENSEQ 
		     [constructor_tac (Some 1) 1 
			(Rawterm.ImplicitBindings [mkVar n]);
		      cont]);
		 ])))
	in
	let conttype = 
	  (fun typ -> 
	     let tex = mkLambda (Name n, t, typ) in
	       conttype
		 (mkApp (Lazy.force ex_ind, [| t; tex |])))
	in
	  aux (mkVar n :: names) conttac conttype tl
    | (n, t) :: [] -> 
	(conttac intros, conttype t)
    | [] -> raise (Invalid_argument "build_dependent_sum")
  in aux [] id id (List.rev l)       
	  
open Proof_type
open Tacexpr

let mkProj1 a b c = 
  mkApp (Lazy.force proj1, [| a; b; c |])

let mkProj2 a b c = 
  mkApp (Lazy.force proj2, [| a; b; c |])

let mk_ex_pi1 a b c =
  mkApp (Lazy.force ex_pi1, [| a; b; c |])

let mk_ex_pi2 a b c =
  mkApp (Lazy.force ex_pi2, [| a; b; c |])
    

let mkSubset name typ prop = 
  mkApp ((Lazy.force sig_).typ,
	 [| typ; mkLambda (name, typ, prop) |])

let and_tac l hook =
  let andc = Coqlib.build_coq_and () in      
  let rec aux ((accid, goal, tac, extract) as acc) = function
    | [] -> (* Singleton *) acc
	
    | (id, x, elgoal, eltac) :: tl ->
	let tac' = tclTHEN simplest_split (tclTHENLIST [tac; eltac]) in
	let proj = fun c -> mkProj2 goal elgoal c in
	let extract = List.map (fun (id, x, y, f) -> (id, x, y, (fun c -> f (mkProj1 goal elgoal c)))) extract in
	  aux ((string_of_id id) ^ "_" ^ accid, mkApp (andc, [| goal; elgoal |]), tac', 
	       (id, x, elgoal, proj) :: extract) tl

  in
  let and_proof_id, and_goal, and_tac, and_extract = 
    match l with
      | [] -> raise (Invalid_argument "and_tac: empty list of goals")
      | (hdid, x, hdg, hdt) :: tl -> 
	  aux (string_of_id hdid, hdg, hdt, [hdid, x, hdg, (fun c -> c)]) tl
  in
  let and_proofid = id_of_string (and_proof_id ^ "_and_proof") in
    Command.start_proof and_proofid goal_kind and_goal
      (hook (fun c -> List.map (fun (id, x, t, f) -> (id, x, t, f c)) and_extract));
    trace (str "Started and proof");
    Pfedit.by and_tac;
    trace (str "Applied and tac")
      

let destruct_ex ext ex = 
  let rec aux c acc = 
    match kind_of_term c with
	App (f, args) ->
	  (match kind_of_term f with
	       Ind i when i = Term.destInd (Lazy.force ex_ind) && Array.length args = 2 ->
		 let (dom, rng) = 
		   try (args.(0), args.(1))
		   with _ -> assert(false)
		 in
		 let pi1 = (mk_ex_pi1 dom rng acc) in
		 let rng_body = 
		   match kind_of_term rng with
		       Lambda (_, _, t) -> subst1 pi1 t
		     | t -> rng
		 in
		   pi1 :: aux rng_body (mk_ex_pi2 dom rng acc)
	     | _ -> [acc])
      | _ -> [acc]
  in aux ex ext

open Rawterm

let rec concatMap f l = 
  match l with
      hd :: tl -> f hd @ concatMap f tl      
    | [] -> []
	
let list_mapi f = 
  let rec aux i = function 
      hd :: tl -> f i hd :: aux (succ i) tl 
    | [] -> []
  in aux 0

(*
let make_discr (loc, po, tml, eqns) =
  let mkHole = RHole (dummy_loc, InternalHole) in
  
  let rec vars_of_pat = function
      RPatVar (loc, n) -> (match n with Anonymous -> [] | Name n -> [n])
    | RPatCstr (loc, csrt, pats, _) -> 
	concatMap vars_of_pat pats
  in
  let rec constr_of_pat l = function 
      RPatVar (loc, n) -> 
	(match n with 
	     Anonymous -> 
	       let n = next_name_away_from "x" l in
		 RVar n, (n :: l)
	   | Name n -> RVar n, l)
    | RPatCstr (loc, csrt, pats, _) -> 
	let (args, vars) =
	  List.fold_left
	    (fun (args, vars) x ->
	       let c, vars = constr_of_pat vars x in
		 c :: args, vars)
	    ([], l) pats
	in		 
	  RApp ((RRef (dummy_loc, ConstructRef cstr)), args), vars
  in
  let rec constr_of_pat l = function 
      RPatVar (loc, n) -> 
	(match n with 
	     Anonymous -> 
	       let n = next_name_away_from "x" l in
		 RVar n, (n :: l)
	   | Name n -> RVar n, l)
    | RPatCstr (loc, csrt, pats, _) -> 
	let (args, vars) =
	  List.fold_left
	    (fun (args, vars) x ->
	       let c, vars = constr_of_pat vars x in
		 c :: args, vars)
	    ([], l) pats
	in		 
	  RApp ((RRef (dummy_loc, ConstructRef cstr)), args), vars
  in
  let constrs_of_pats v l =
    List.fold_left 
      (fun (v, acc) x -> 
	 let x', v' = constr_of_pat v x in
	   (l', v' :: acc))
      (v, []) l
  in
  let rec pat_of_pat l = function
      RPatVar (loc, n) -> 
	let n', l = match n with
	    Anonymous -> 
	      let n = next_name_away_from "x" l in
		n, n :: l
	  | Name n -> n, n :: l 
	in
	  RPatVar (loc, Name n'), l
    | RPatCstr (loc, cstr, pats, (loc, alias)) ->
	let args, vars, s = 
	  List.fold_left (fun (args, vars) x -> 
			    let pat', vars = pat_of_pat vars pat in
			      pat' :: args, vars)
	    ([], alias :: l) pats
	in RPatCstr (loc, cstr, args, (loc, alias)), vars
  in
  let pats_of_pats l =
    List.fold_left 
      (fun (v, acc) x -> 
	 let x', v' = pat_of_pat v x in
	   (v', x' :: acc))
      ([], []) l
  in
  let eq_of_pat p used c = 
    let constr, vars' = constr_of_pat used p in
    let eq = RApp (dummy_loc, RRef (dummy_loc, Lazy.force eqind_ref), [mkHole; constr; c]) in
      vars', eq
  in
  let eqs_of_pats ps used cstrs =
    List.fold_left2 
      (fun (vars, eqs) pat c ->
	 let (vars', eq) = eq_of_pat pat c in
	   match eqs with 
	       None -> Some eq 
	     | Some eqs ->
		 Some (RApp (dummy_loc, RRef (dummy_loc, Lazy.force and_ref), [eq, eqs])))
      (used, None) ps cstrs
  in
  let quantify c l =
    List.fold_left
      (fun acc name -> RProd (dummy_loc, name, mkHole, acc))
      c l
  in
  let quantpats = 
    List.fold_left
      (fun (acc, pats) ((loc, idl, cpl, c) as x) ->
	 let vars, cpl = pats_of_pats cpl in
	 let l', constrs = constrs_of_pats vars cpl in	   
	 let discrs = 
	   List.map (fun (_, _, cpl', _) -> 
		       let qvars, eqs = eqs_of_pats cpl' l' constrs in
		       let neg = RApp (dummy_loc, RRef (dummy_loc, Lazy.force not_ref), [out_some eqs]) in
		       let pat_ineq = quantify qvars neg in
			 
		    )
	     pats in
	   
			 


	   
	   

	   (x, pat_ineq))
  in
    List.fold_left 
      (fun acc ((loc, idl, cpl, c0) pat) -> 
    
		
		let c' = 
		  List.fold_left 
		    (fun acc (n, t) ->
		       RLambda (dummy_loc, n, mkHole, acc))
		    c eqs_types
		in (loc, idl, cpl, c'))
      eqns
  i
*)
(* let rewrite_cases_aux (loc, po, tml, eqns) = *)
(*   let tml = list_mapi (fun i (c, (n, opt)) -> c,  *)
(* 		       ((match n with *)
(* 			    Name id -> (match c with *)
(* 					  | RVar (_, id') when id = id' -> *)
(* 					      Name (id_of_string (string_of_id id ^ "'")) *)
(* 					  | _ -> n) *)
(* 			  | Anonymous -> Name (id_of_string ("x" ^ string_of_int i))), *)
(* 			opt)) tml  *)
(*   in *)
(*   let mkHole = RHole (dummy_loc, InternalHole) in *)
(*   (\* let mkeq c n = RApp (dummy_loc, RRef (dummy_loc, (Lazy.force eqind_ref)), *\) *)
(* (\* 		       [mkHole; c; n]) *\) *)
(* (\*   in *\) *)
(*   let mkeq c n = RApp (dummy_loc, RRef (dummy_loc, (Lazy.force eqdep_ind_ref)), *)
(* 		       [mkHole; c; mkHole; n]) *)
(*   in *)
(*   let eqs_types =  *)
(*     List.map *)
(*       (fun (c, (n, _)) -> *)
(* 	 let id = match n with Name id -> id | _ -> assert false in *)
(* 	 let heqid = id_of_string ("Heq" ^ string_of_id id) in *)
(* 	   Name heqid, mkeq c (RVar (dummy_loc, id))) *)
(*       tml *)
(*   in *)
(*   let po =  *)
(*     List.fold_right *)
(*       (fun (n,t) acc -> *)
(* 	 RProd (dummy_loc, Anonymous, t, acc)) *)
(*       eqs_types (match po with  *)
(* 		     Some e -> e *)
(* 		   | None -> mkHole) *)
(*   in *)
(*   let eqns =    *)
(*     List.map (fun (loc, idl, cpl, c) -> *)
(* 		let c' =  *)
(* 		  List.fold_left  *)
(* 		    (fun acc (n, t) -> *)
(* 		       RLambda (dummy_loc, n, mkHole, acc)) *)
(* 		    c eqs_types *)
(* 		in (loc, idl, cpl, c')) *)
(*       eqns *)
(*   in *)
(*   let mk_refl_equal c = RApp (dummy_loc, RRef (dummy_loc, Lazy.force refl_equal_ref), *)
(* 			      [mkHole; c]) *)
(*   in *)
(*   (\*let mk_refl_equal c = RApp (dummy_loc, RRef (dummy_loc, Lazy.force refl_equal_ref), *)
(* 			      [mkHole; c]) *)
(*   in*\) *)
(*   let refls = List.map (fun (c, _) -> mk_refl_equal c) tml in *)
(*   let case = RCases (loc,Some po,tml,eqns) in *)
(*   let app = RApp (dummy_loc, case, refls) in *)
(*     app *)

(* let rec rewrite_cases c =  *)
(*   match c with  *)
(*       RCases _ -> let c' = map_rawconstr rewrite_cases c in *)
(* 	(match c' with  *)
(* 	   | RCases (x, y, z, w) -> rewrite_cases_aux (x,y,z,w) *)
(* 	   | _ -> assert(false)) *)
(*     | _ -> map_rawconstr rewrite_cases c *)
	  
(* let rewrite_cases env c = *)
(*   let c' = rewrite_cases c in *)
(*   let _ = trace (str "Rewrote cases: " ++ spc () ++ my_print_rawconstr env c') in *)
(*     c' *)

let list_mapi f = 
  let rec aux i = function 
      hd :: tl -> f i hd :: aux (succ i) tl 
    | [] -> []
  in aux 0

open Rawterm

let rewrite_cases_aux (loc, po, tml, eqns) =
  let tml' = list_mapi (fun i (c, (n, opt)) -> c, 
		       ((match n with
			    Name id -> (match c with
					  | RVar (_, id') when id = id' ->
					      id, (id_of_string (string_of_id id ^ "Heq_id"))
					  | RVar (_, id') ->
					      id', id
					  | _ -> id_of_string (string_of_id id ^ "Heq_id"), id)
			   | Anonymous -> 
			       let str = "Heq_id" ^ string_of_int i in
				 id_of_string str, id_of_string (str ^ "'")),
			opt)) tml 
  in
  let mkHole = RHole (dummy_loc, InternalHole) in
  let mkCoerceCast c = RCast (dummy_loc, c, CastCoerce, mkHole) in
  let mkeq c n = RApp (dummy_loc, RRef (dummy_loc, (Lazy.force eq_ind_ref)),
		       [mkHole; c; n])
  in
  let eqs_types = 
    List.map
      (fun (c, ((id, id'), _)) ->
	 let heqid = id_of_string ("Heq" ^ string_of_id id) in
	   Name heqid, mkeq (RVar (dummy_loc, id')) c)
      tml'
  in
  let po = 
    List.fold_right
      (fun (n,t) acc ->
	 RProd (dummy_loc, Anonymous, t, acc))
      eqs_types (match po with 
		     Some e -> e
		   | None -> mkHole)
  in
  let eqns =   
    List.map (fun (loc, idl, cpl, c) ->
		let c' = 
		  List.fold_left 
		    (fun acc (n, t) ->
		       RLambda (dummy_loc, n, mkHole, acc))
		    c eqs_types
		in (loc, idl, cpl, c'))
      eqns
  in
  let mk_refl_equal c = RApp (dummy_loc, RRef (dummy_loc, Lazy.force refl_equal_ref),
			      [mkHole; c])
  in
  let refls = List.map (fun (c, ((id, _), _)) -> mk_refl_equal (mkCoerceCast c)) tml' in
  let tml'' = List.map (fun (c, ((id, id'), opt)) -> c, (Name id', opt)) tml' in
  let case = RCases (loc,Some po,tml'',eqns) in
  let app = RApp (dummy_loc, case, refls) in
(*   let letapp = List.fold_left (fun acc (c, ((id, id'), opt)) -> RLetIn (dummy_loc, Name id, c, acc)) *)
(* 		 app tml' *)
(*   in *)
    app

let rec rewrite_cases c = 
  match c with 
      RCases _ -> let c' = map_rawconstr rewrite_cases c in
	(match c' with 
	   | RCases (x, y, z, w) -> rewrite_cases_aux (x,y,z,w)
	   | _ -> assert(false))
    | _ -> map_rawconstr rewrite_cases c
	  
let rewrite_cases env c = c
(*   let c' = rewrite_cases c in *)
(*   let _ = trace (str "Rewrote cases: " ++ spc () ++ my_print_rawconstr env c') in *)
(*     c' *)

let id_of_name = function
    Name n -> n
  | Anonymous -> raise (Invalid_argument "id_of_name")

let definition_message id =
  Options.if_verbose message ((string_of_id id) ^ " is defined")

let recursive_message v =
  match Array.length v with
    | 0 -> error "no recursive definition"
    | 1 -> (Printer.pr_global v.(0) ++ str " is recursively defined")
    | _ -> hov 0 (prvect_with_sep pr_coma Printer.pr_global v ++
		    spc () ++ str "are recursively defined")

(* Solve an obligation using tactics, return the corresponding proof term *)
(*
let solve_by_tac ev t =
  debug 1 (str "Solving goal using tactics: " ++ Evd.pr_evar_info ev);
  let goal = Proof_trees.mk_goal ev.evar_hyps ev.evar_concl None in
  debug 1 (str "Goal created");
  let ts = Tacmach.mk_pftreestate goal in
  debug 1 (str "Got pftreestate");
  let solved_state = Tacmach.solve_pftreestate t ts in
  debug 1 (str "Solved goal");
    let _, l = Tacmach.extract_open_pftreestate solved_state in
      List.iter (fun (_, x) -> debug 1 (str "left hole of type " ++ my_print_constr (Global.env()) x)) l;
    let c = Tacmach.extract_pftreestate solved_state in
    debug 1 (str "Extracted term");
    debug 1 (str "Term constructed in solve by tac: " ++ my_print_constr (Global.env ()) c);
    c
    *)

let solve_by_tac evi t =
  debug 2 (str "Solving goal using tactics: " ++ Evd.pr_evar_info evi);
  let id = id_of_string "H" in
  try 
    Pfedit.start_proof id (Decl_kinds.Local,Decl_kinds.Proof Decl_kinds.Lemma) evi.evar_hyps evi.evar_concl
    (fun _ _ -> ());
    Pfedit.by (tclCOMPLETE t);
    let _,(const,_,_) = Pfedit.cook_proof () in 
      Pfedit.delete_current_proof (); const.Entries.const_entry_body
  with e -> 
    Pfedit.delete_current_proof();
    raise Exit

let rec string_of_list sep f = function
    [] -> ""
  | x :: [] -> f x
  | x :: ((y :: _) as tl) -> f x ^ sep ^ string_of_list sep f tl

let string_of_intset d = 
  string_of_list "," string_of_int (Intset.elements d)

(**********************************************************)
(* Pretty-printing *)
open Printer
open Ppconstr
open Nameops
open Termops
open Evd

let pr_meta_map evd =
  let ml = meta_list evd in
  let pr_name = function
      Name id -> str"[" ++ pr_id id ++ str"]"
    | _ -> mt() in
  let pr_meta_binding = function
    | (mv,Cltyp (na,b)) ->
      	hov 0 
	  (pr_meta mv ++ pr_name na ++ str " : " ++
           print_constr b.rebus ++ fnl ())
    | (mv,Clval(na,b,_)) ->
      	hov 0 
	  (pr_meta mv ++ pr_name na ++ str " := " ++
             print_constr (fst b).rebus ++ fnl ())
  in
  prlist pr_meta_binding ml    

let pr_idl idl = prlist_with_sep pr_spc pr_id idl

let pr_evar_info evi =
  let phyps = 
    (*pr_idl (List.rev (ids_of_named_context (evar_context evi))) *)
    Printer.pr_named_context (Global.env()) (evar_context evi)
  in
  let pty = print_constr evi.evar_concl in
  let pb =
    match evi.evar_body with
      | Evar_empty -> mt ()
      | Evar_defined c -> spc() ++ str"=> "  ++ print_constr c
  in
  hov 2 (str"["  ++ phyps ++ spc () ++ str"|- "  ++ pty ++ pb ++ str"]")

let pr_evar_map sigma =
  h 0 
    (prlist_with_sep pr_fnl
      (fun (ev,evi) ->
        h 0 (str(string_of_existential ev)++str"=="++ pr_evar_info evi))
      (to_list sigma))

let pr_constraints pbs =
  h 0
    (prlist_with_sep pr_fnl (fun (pbty,t1,t2) ->
      print_constr t1 ++ spc() ++
      str (match pbty with
	| Reduction.CONV -> "=="
	| Reduction.CUMUL -> "<=") ++ 
      spc() ++ print_constr t2) pbs)

let pr_evar_defs evd =
  let pp_evm =
    let evars = evars_of evd in
    if evars = empty then mt() else
      str"EVARS:"++brk(0,1)++pr_evar_map evars++fnl() in
  let pp_met =
    if meta_list evd = [] then mt() else
      str"METAS:"++brk(0,1)++pr_meta_map evd in
  v 0 (pp_evm ++ pp_met)
