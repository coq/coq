open Evd
open Libnames
open Coqlib
open Term
open Names
open Util

let ($) f x = f x

(****************************************************************************)
(* Library linking *)

let contrib_name = "Program"

let subtac_dir = [contrib_name]
let fix_sub_module = "Wf"
let utils_module = "Utils"
let fixsub_module = subtac_dir @ [fix_sub_module]
let utils_module = subtac_dir @ [utils_module]
let tactics_module = subtac_dir @ ["Tactics"]
let init_constant dir s = gen_constant contrib_name dir s
let init_reference dir s = gen_reference contrib_name dir s

let fixsub = lazy (init_constant fixsub_module "Fix_sub")
let ex_pi1 = lazy (init_constant utils_module "ex_pi1")
let ex_pi2 = lazy (init_constant utils_module "ex_pi2")

let make_ref l s = lazy (init_reference l s)
let well_founded_ref = make_ref ["Init";"Wf"] "Well_founded"
let acc_ref = make_ref  ["Init";"Wf"] "Acc"
let acc_inv_ref = make_ref  ["Init";"Wf"] "Acc_inv"
let fix_sub_ref = make_ref fixsub_module "Fix_sub"
let measure_on_R_ref = make_ref fixsub_module "MR"
let fix_measure_sub_ref = make_ref fixsub_module "Fix_measure_sub"
let refl_ref = make_ref ["Init";"Logic"] "refl_equal"

let make_ref s = Qualid (dummy_loc, qualid_of_string s)
let lt_ref = make_ref "Init.Peano.lt"
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

let fix_proto = lazy (init_constant tactics_module "fix_proto")
let fix_proto_ref () = 
  match Nametab.global (make_ref "Program.Tactics.fix_proto") with
  | ConstRef c -> c
  | _ -> assert false

let eq_ind = lazy (init_constant ["Init"; "Logic"] "eq")
let eq_rec = lazy (init_constant ["Init"; "Logic"] "eq_rec")
let eq_rect = lazy (init_constant ["Init"; "Logic"] "eq_rect")
let eq_refl = lazy (init_constant ["Init"; "Logic"] "refl_equal")
let eq_ind_ref = lazy (init_reference ["Init"; "Logic"] "eq")
let refl_equal_ref = lazy (init_reference ["Init"; "Logic"] "refl_equal")

let not_ref = lazy (init_constant ["Init"; "Logic"] "not")

let and_typ = lazy (Coqlib.build_coq_and ())

let eqdep_ind = lazy (init_constant [ "Logic";"Eqdep"] "eq_dep")
let eqdep_rec = lazy (init_constant ["Logic";"Eqdep"] "eq_dep_rec")
let eqdep_ind_ref = lazy (init_reference [ "Logic";"Eqdep"] "eq_dep")
let eqdep_intro_ref = lazy (init_reference [ "Logic";"Eqdep"] "eq_dep_intro")

let jmeq_ind =
  lazy (check_required_library ["Coq";"Logic";"JMeq"];
	init_constant ["Logic";"JMeq"] "JMeq")
let jmeq_rec =
  lazy (check_required_library ["Coq";"Logic";"JMeq"];
	init_constant ["Logic";"JMeq"] "JMeq_rec")
let jmeq_refl =
  lazy (check_required_library ["Coq";"Logic";"JMeq"];
	init_constant ["Logic";"JMeq"] "JMeq_refl")

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
    if !Flags.debug && n >= debug_level then
      msgnl s
    else ()
  else ()

let debug_msg n s =
  if debug_on then
    if !Flags.debug  && n >= debug_level then s
    else mt ()
  else mt ()

let trace s =
  if debug_on then
    if !Flags.debug  && debug_level > 0 then msgnl s
    else ()
  else ()

let rec pp_list f = function
    [] -> mt()
  | x :: y -> f x ++ spc () ++ pp_list f y

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

let make_existential loc ?(opaque = Define true) env isevars c =
  let evar = Evarutil.e_new_evar isevars env ~src:(loc, QuestionMark opaque) c in
  let (key, args) = destEvar evar in
    (try trace (str "Constructed evar " ++ int key ++ str " applied to args: " ++
		  print_args env args ++ str " for type: "++
		  my_print_constr env c) with _ -> ());
    evar

let make_existential_expr loc env c =
  let key = Evarutil.new_untyped_evar () in
  let evar = Topconstr.CEvar (loc, key, None) in
    debug 2 (str "Constructed evar " ++ int key);
    evar

let string_of_hole_kind = function
  | ImplicitArg _ -> "ImplicitArg"
  | BinderType _ -> "BinderType"
  | QuestionMark _ -> "QuestionMark"
  | CasesType -> "CasesType"
  | InternalHole -> "InternalHole"
  | TomatchTypeParameter _ -> "TomatchTypeParameter"
  | GoalEvar -> "GoalEvar"
  | ImpossibleCase -> "ImpossibleCase"

let evars_of_term evc init c =
  let rec evrec acc c =
    match kind_of_term c with
    | Evar (n, _) when Evd.mem evc n -> Evd.add acc n (Evd.find evc n)
    | Evar (n, _) -> assert(false)
    | _ -> fold_constr evrec acc c
  in
    evrec init c

let non_instanciated_map env evd evm =
  List.fold_left
    (fun evm (key, evi) ->
       let (loc,k) = evar_source key !evd in
	 debug 2 (str "evar " ++ int key ++ str " has kind " ++
		    str (string_of_hole_kind k));
	 match k with
	 | QuestionMark _ -> Evd.add evm key evi
	 | ImplicitArg (_,_,false) -> Evd.add evm key evi
	 | _ ->
	     debug 2 (str " and is an implicit");
	     Pretype_errors.error_unsolvable_implicit loc env evm (Evarutil.nf_evar_info evm evi) k None)
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
	let tac = assert_tac (Name n) hyptype in
	let conttac =
	  (fun cont ->
	     conttac
	     (tclTHENS tac
		([intros;
		  (tclTHENSEQ
		     [constructor_tac false (Some 1) 1
			(Rawterm.ImplicitBindings [inj_open (mkVar n)]);
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

let mk_eq typ x y = mkApp (Lazy.force eq_ind, [| typ; x ; y |])
let mk_eq_refl typ x = mkApp (Lazy.force eq_refl, [| typ; x |])
let mk_JMeq typ x typ' y = mkApp (Lazy.force jmeq_ind, [| typ; x ; typ'; y |])
let mk_JMeq_refl typ x = mkApp (Lazy.force jmeq_refl, [| typ; x |])

let unsafe_fold_right f = function
    hd :: tl -> List.fold_right f tl hd
  | [] -> raise (Invalid_argument "unsafe_fold_right")

let mk_conj l =
  let conj_typ = Lazy.force and_typ in
    unsafe_fold_right
      (fun c conj ->
	 mkApp (conj_typ, [| c ; conj |]))
      l

let mk_not c =
  let notc = Lazy.force not_ref in
    mkApp (notc, [| c |])

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

let id_of_name = function
    Name n -> n
  | Anonymous -> raise (Invalid_argument "id_of_name")

let definition_message id =
  Nameops.pr_id id ++ str " is defined"

let recursive_message v =
  match Array.length v with
    | 0 -> error "no recursive definition"
    | 1 -> (Printer.pr_constant (Global.env ()) v.(0) ++ str " is recursively defined")
    | _ -> hov 0 (prvect_with_sep pr_coma (Printer.pr_constant (Global.env ())) v ++
		    spc () ++ str "are recursively defined")

let print_message m =
  Flags.if_verbose ppnl m

(* Solve an obligation using tactics, return the corresponding proof term *)
let solve_by_tac evi t =
  let id = id_of_string "H" in
  try
    Pfedit.start_proof id goal_kind evi.evar_hyps evi.evar_concl
    (fun _ _ -> ());
    Pfedit.by (tclCOMPLETE t);
    let _,(const,_,_,_) = Pfedit.cook_proof ignore in
      Pfedit.delete_current_proof (); 
      Inductiveops.control_only_guard (Global.env ())
	const.Entries.const_entry_body;
      const.Entries.const_entry_body
  with e ->
    Pfedit.delete_current_proof();
    raise e

(* let apply_tac t goal = t goal *)

(* let solve_by_tac evi t = *)
(*   let ev = 1 in *)
(*   let evm = Evd.add Evd.empty ev evi in *)
(*   let goal = {it = evi; sigma = evm } in *)
(*   let (res, valid) = apply_tac t goal in *)
(*     if res.it = [] then *)
(*       let prooftree = valid [] in *)
(*       let proofterm, obls = Refiner.extract_open_proof res.sigma prooftree in *)
(* 	if obls = [] then proofterm *)
(* 	else raise Exit *)
(*     else raise Exit *)

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

let pr_evar_defs sigma =
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
    let evars =  evd in
    if evars = empty then mt() else
      str"EVARS:"++brk(0,1)++pr_evar_defs evars++fnl() in
  let pp_met =
    if meta_list evd = [] then mt() else
      str"METAS:"++brk(0,1)++pr_meta_map evd in
  v 0 (pp_evm ++ pp_met)

let contrib_tactics_path =
  make_dirpath (List.map id_of_string ["Tactics";contrib_name;"Coq"])
let tactics_tac s =
  lazy(make_kn (MPfile contrib_tactics_path) (make_dirpath []) (mk_label s))

let tactics_call tac args =
  TacArg(TacCall(dummy_loc, ArgArg(dummy_loc, Lazy.force (tactics_tac tac)),args))
