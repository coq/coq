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

let make_ref s =  Qualid (dummy_loc, (qualid_of_string s))
let well_founded_ref = make_ref "Init.Wf.Well_founded"
let acc_ref = make_ref "Init.Wf.Acc"
let acc_inv_ref = make_ref "Init.Wf.Acc_inv"
let fix_sub_ref = make_ref "Coq.subtac.FixSub.Fix_sub"
let lt_wf_ref = make_ref "Coq.Wf_nat.lt_wf"
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
  
let existS = lazy (build_sigma_set ())

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
let my_print_context = Termops.print_rel_context
let my_print_env = Termops.print_env
let my_print_rawconstr = Printer.pr_rawconstr_env
let my_print_evardefs = Evd.pr_evar_defs

let my_print_tycon_type = Evarutil.pr_tycon_type


let debug n s = 
  if !Options.debug then
    msgnl s
  else ()

let debug_msg n s = 
  if !Options.debug then s
  else mt ()

let trace s = 
  if !Options.debug then msgnl s
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
    debug 2 (str "Constructed evar " ++ int key ++ str " applied to args: " ++
	     print_args env args);
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

let global_fix_kind = Decl_kinds.IsDefinition Decl_kinds.Fixpoint
let goal_fix_kind = Decl_kinds.Global, Decl_kinds.DefinitionBody Decl_kinds.Fixpoint

open Tactics
open Tacticals

let build_dependent_sum l =
  let rec aux (acc, tac, typ) = function
      (n, t) :: tl ->
	let t' = mkLambda (Name n, t, typ) in
	  trace (str ("treating " ^ string_of_id n) ++
		 str "assert: " ++ my_print_constr (Global.env ()) t);
	let tac' = 
	  tclTHEN (assert_tac true (Name n) t) 
	    (tclTHENLIST
	       [intros;
		(tclTHENSEQ 
		   [tclTRY (constructor_tac (Some 1) 1 
		       (Rawterm.ImplicitBindings [mkVar n]));
		    tac]);
	       ])
	in
	  aux (mkApp (Lazy.force ex_ind, [| t; t'; |]), tac', t') tl
    | [] -> acc, tac, typ
  in 
    match l with 
	(_, hd) :: tl -> aux (hd, intros, hd) tl
      | [] -> raise (Invalid_argument "build_dependent_sum")

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
      | (hdid, x, hdg, hdt) :: tl -> aux (string_of_id hdid, hdg, hdt, [hdid, x, hdg, (fun c -> c)]) tl
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
		   (mk_ex_pi1 dom rng acc) :: aux rng (mk_ex_pi2 dom rng acc)
	     | _ -> [acc])
      | _ -> [acc]
  in aux ex ext


