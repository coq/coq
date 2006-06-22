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

let eqind = lazy (init_constant ["Init"; "Logic"] "eq")
let eqind_ref = lazy (init_reference ["Init"; "Logic"] "eq")
let refl_equal_ref = lazy (init_reference ["Init"; "Logic"] "refl_equal")

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
let my_print_context = Termops.print_rel_context
let my_print_env = Termops.print_env
let my_print_rawconstr = Printer.pr_rawconstr_env
let my_print_evardefs = Evd.pr_evar_defs

let my_print_tycon_type = Evarutil.pr_tycon_type

let debug_level = 2

let debug n s = 
  if !Options.debug && n >= debug_level then
    msgnl s
  else ()

let debug_msg n s = 
  if !Options.debug  && n >= debug_level then s
  else mt ()

let trace s = 
  if !Options.debug  && debug_level > 0 then msgnl s
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

let build_dependent_sum l =
  let rec aux (tac, typ) = function
      (n, t) :: tl ->
	let t' = mkLambda (Name n, t, typ) in
	  trace (spc () ++ str ("treating evar " ^ string_of_id n));
	  (try trace (str " assert: " ++ my_print_constr (Global.env ()) t)	    	     
	   with _ -> ());
	let tac' = 
	  tclTHENS (assert_tac true (Name n) t) 
	    ([intros;
	      (tclTHENSEQ 
		 [constructor_tac (Some 1) 1 
		    (Rawterm.ImplicitBindings [mkVar n]);
		  tac]);
	     ])
	in
	let newt = mkApp (Lazy.force ex_ind, [| t; t'; |]) in
	  aux (tac', newt) tl
    | [] -> tac, typ
  in 
    match l with 
	(_, hd) :: tl -> aux (intros, hd) tl
      | [] -> raise (Invalid_argument "build_dependent_sum")

let id x = x

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
  let mkeq c n = RApp (dummy_loc, RRef (dummy_loc, (Lazy.force eqind_ref)),
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
	  
let rewrite_cases env c =
  let c' = rewrite_cases c in
  let _ = trace (str "Rewrote cases: " ++ spc () ++ my_print_rawconstr env c') in
    c'
