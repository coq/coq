open Names
open Pp

(* arnaud: trucs factices *)
module Pfedit =
  struct
    let delete_current_proof _ = Util.anomaly "Indfun_common.delete_current_proof: fantome"
    let get_pftreestate _ = Util.anomaly "Indufun_common.get_pftreestate: fantome"
    let current_proof_statement _ = Util.anomaly "Indufun_common.current_proof_statement: fantome"
  end
module Refiner =
  struct
    let extract_open_pftreestate _ = Util.anomaly "Indfun_common.extract_open_pftreestate: fantome"
    let evc_of_pftreestate _ = Util.anomaly "Indfun_common.evc_of_pftreestate: fantome"
    let proof_of_pftreestate _ = Util.anomaly "Indfun_common.proof_of_pftreestate: fantome" 
  end

(* arnaud:/trucs factices *)

open Libnames

let mk_prefix pre id = id_of_string (pre^(string_of_id id))
let mk_rel_id = mk_prefix "R_"
let mk_correct_id id = Nameops.add_suffix (mk_rel_id id) "_correct"
let mk_complete_id id = Nameops.add_suffix (mk_rel_id id) "_complete"
let mk_equation_id id = Nameops.add_suffix id "_equation"

let msgnl m =
  ()

let invalid_argument s = raise (Invalid_argument s)


let fresh_id avoid s = Termops.next_global_ident_away true (id_of_string s) avoid

let fresh_name avoid s = Name (fresh_id avoid s)

let get_name avoid ?(default="H") = function
  | Anonymous -> fresh_name avoid default
  | Name n -> Name n

let array_get_start a =
  try 
    Array.init
      (Array.length a - 1)
      (fun i -> a.(i))
  with Invalid_argument "index out of bounds" -> 
    invalid_argument "array_get_start"
      
let id_of_name = function
    Name id -> id
  | _ -> raise Not_found

let locate  ref =
    let (loc,qid) = qualid_of_reference ref in
    Nametab.locate qid

let locate_ind ref =
  match locate ref with
    | IndRef x -> x
    | _ -> raise Not_found

let locate_constant ref =
  match locate ref with
    | ConstRef x -> x
    | _ -> raise Not_found


let locate_with_msg msg f x =
  try
    f x
  with
    | Not_found -> raise (Util.UserError("", msg))
    | e -> raise e


let filter_map filter f =
  let rec it = function
    | [] -> []
    | e::l ->
	if filter e
	then
	  (f e) :: it l
	else it l
  in
  it


let chop_rlambda_n  =
  let rec chop_lambda_n acc n rt =
      if n == 0
      then List.rev acc,rt
      else
	match rt with
	  | Rawterm.RLambda(_,name,t,b) -> chop_lambda_n ((name,t,false)::acc) (n-1) b
	  | Rawterm.RLetIn(_,name,v,b) -> chop_lambda_n ((name,v,true)::acc) (n-1) b
	  | _ -> 
	      raise (Util.UserError("chop_rlambda_n",
				    str "chop_rlambda_n: Not enough Lambdas"))
  in
  chop_lambda_n []

let chop_rprod_n  =
  let rec chop_prod_n acc n rt =
      if n == 0
      then List.rev acc,rt
      else
	match rt with
	  | Rawterm.RProd(_,name,t,b) -> chop_prod_n ((name,t)::acc) (n-1) b
	  | _ -> raise (Util.UserError("chop_rprod_n",str "chop_rprod_n: Not enough products"))
  in
  chop_prod_n []



let list_union_eq eq_fun l1 l2 =
  let rec urec = function
    | [] -> l2
    | a::l -> if List.exists (eq_fun a) l2 then urec l else a::urec l
  in
  urec l1

let list_add_set_eq eq_fun x l =
  if List.exists (eq_fun x) l then l else x::l

  


let const_of_id id =
  let _,princ_ref = 
    qualid_of_reference (Libnames.Ident (Util.dummy_loc,id))
  in
  try Nametab.locate_constant princ_ref
  with Not_found -> Util.error ("cannot find "^ string_of_id id)

let def_of_const t =
   match (Term.kind_of_term t) with
    Term.Const sp -> 
      (try (match (Global.lookup_constant sp) with
             {Declarations.const_body=Some c} -> Declarations.force c
	     |_ -> assert false)
       with _ -> assert false)
    |_ -> assert false

let coq_constant s =
  Coqlib.gen_constant_in_modules "RecursiveDefinition" 
    (Coqlib.init_modules @ Coqlib.arith_modules) s;;

let constant sl s =
  constr_of_global
    (Nametab.locate (make_qualid(Names.make_dirpath 
			   (List.map id_of_string (List.rev sl)))
	       (id_of_string s)));;

let find_reference sl s =
    (Nametab.locate (make_qualid(Names.make_dirpath 
			   (List.map id_of_string (List.rev sl)))
	       (id_of_string s)));;

let eq = lazy(coq_constant "eq")
let refl_equal = lazy(coq_constant "refl_equal")

(*****************************************************************)
(* Copy of the standart save mechanism but without the much too  *)
(* slow reduction function                                       *) 
(*****************************************************************)
open Declarations
open Entries
open Decl_kinds
open Declare
let definition_message id =
  Flags.if_verbose message ((string_of_id id) ^ " is defined")


let save with_clean id const (locality,kind) hook =
  let {const_entry_body = pft;
       const_entry_type = tpo;
       const_entry_opaque = opacity } = const in
  let l,r = match locality with
    | Local when Lib.sections_are_opened () ->
        let k = logical_kind_of_goal_kind kind in
	let c = SectionLocalDef (pft, tpo, opacity) in
	let _ = declare_variable id (Lib.cwd(), c, k) in
	(Local, VarRef id)
    | Local ->
        let k = logical_kind_of_goal_kind kind in
        let kn = declare_constant id (DefinitionEntry const, k) in
	(Global, ConstRef kn)
    | Global ->
        let k = logical_kind_of_goal_kind kind in
        let kn = declare_constant id (DefinitionEntry const, k) in
	(Global, ConstRef kn) in
  if with_clean then  Pfedit.delete_current_proof ();
  hook l r;
  definition_message id




let extract_pftreestate pts =
  let pfterm,subgoals = Refiner.extract_open_pftreestate pts in
  let tpfsigma = Refiner.evc_of_pftreestate pts in 
  let exl = Evarutil.non_instantiated tpfsigma  in
  if subgoals <> [] or exl <> [] then
    Util.errorlabstrm "extract_proof"
      (if subgoals <> [] then
        str "Attempt to save an incomplete proof"
      else
        str "Attempt to save a proof with existential variables still non-instantiated");
  let env = Global.env_of_context (Refiner.proof_of_pftreestate pts).(*arnaud:Proof_type*)Tacticals.goal.Evd.evar_hyps in
  env,tpfsigma,pfterm


let nf_betaiotazeta =
  let clos_norm_flags flgs env sigma t =
    Closure.norm_val (Closure.create_clos_infos flgs env) (Closure.inject (Reductionops.nf_evar sigma t)) in
  clos_norm_flags Closure.betaiotazeta  

let nf_betaiota =
  let clos_norm_flags flgs env sigma t =
    Closure.norm_val (Closure.create_clos_infos flgs env) (Closure.inject (Reductionops.nf_evar sigma t)) in
  clos_norm_flags Closure.betaiota  

let cook_proof do_reduce =
  let pfs = Pfedit.get_pftreestate () 
(*   and ident = Pfedit.get_current_proof_name ()  *)
  and (ident,strength,concl,hook) = Pfedit.current_proof_statement ()  in
  let env,sigma,pfterm = extract_pftreestate pfs in
  let pfterm = 
    if do_reduce
    then nf_betaiota env sigma pfterm
    else pfterm
  in
  (ident,
   ({ const_entry_body = pfterm;
      const_entry_type = Some concl;
      const_entry_opaque = false;
      const_entry_boxed = false},
    strength, hook))


let new_save_named opacity =
  let id,(const,persistence,hook) = cook_proof true  in
  let const = { const with const_entry_opaque = opacity } in
  save true id const persistence hook

let get_proof_clean do_reduce = 
  let result = cook_proof do_reduce in 
  Pfedit.delete_current_proof ();
  result

let with_full_print f a = 
  let old_implicit_args = Impargs.is_implicit_args ()
  and old_strict_implicit_args =  Impargs.is_strict_implicit_args ()
  and old_contextual_implicit_args = Impargs.is_contextual_implicit_args () in
  let old_rawprint = !Flags.raw_print in 
  Flags.raw_print := true;
  Impargs.make_implicit_args false;
  Impargs.make_strict_implicit_args false;
  Impargs.make_contextual_implicit_args false;
  try 
    let res = f a in 
    Impargs.make_implicit_args old_implicit_args;
    Impargs.make_strict_implicit_args old_strict_implicit_args;
    Impargs.make_contextual_implicit_args old_contextual_implicit_args;
    Flags.raw_print := old_rawprint;
    res
  with  
    | e -> 
	Impargs.make_implicit_args old_implicit_args;
	Impargs.make_strict_implicit_args old_strict_implicit_args;
	Impargs.make_contextual_implicit_args old_contextual_implicit_args;
	Flags.raw_print := old_rawprint;
	raise e






(**********************)

type function_info = 
    { 
      function_constant : constant;
      graph_ind : inductive;
      equation_lemma : constant option;
      correctness_lemma : constant option;
      completeness_lemma : constant option; 
      rect_lemma : constant option;
      rec_lemma : constant option;
      prop_lemma : constant option;
      is_general : bool; (* Has this function been defined using general recursive definition *)
    }
      

(* type function_db  = function_info list *)

(* let function_table = ref ([] : function_db) *)


let from_function = ref Cmap.empty
let from_graph = ref Indmap.empty
(*
let rec do_cache_info finfo = function 
  | [] -> raise Not_found 
  | (finfo'::finfos as l) -> 
      if finfo' == finfo then l 
      else if finfo'.function_constant = finfo.function_constant 
      then finfo::finfos
      else
	let res = do_cache_info finfo finfos in 
	if res == finfos then l else  finfo'::l
  

let cache_Function (_,(finfos)) = 
  let new_tbl = 
    try do_cache_info finfos !function_table
    with Not_found -> finfos::!function_table
  in  
  if new_tbl != !function_table 
  then function_table := new_tbl
*)

let cache_Function (_,finfos) = 
  from_function := Cmap.add finfos.function_constant finfos !from_function;
  from_graph := Indmap.add finfos.graph_ind finfos !from_graph


let load_Function _  = cache_Function
let open_Function _ = cache_Function
let subst_Function (_,subst,finfos) = 
  let do_subst_con c = fst (Mod_subst.subst_con subst c)
  and do_subst_ind (kn,i) = (Mod_subst.subst_kn subst kn,i)
  in
  let function_constant' = do_subst_con finfos.function_constant in 
  let graph_ind' = do_subst_ind finfos.graph_ind in 
  let equation_lemma' = Option.smartmap do_subst_con finfos.equation_lemma in 
  let correctness_lemma' = Option.smartmap do_subst_con finfos.correctness_lemma in 
  let completeness_lemma' = Option.smartmap do_subst_con finfos.completeness_lemma in 
  let rect_lemma' = Option.smartmap do_subst_con finfos.rect_lemma in
  let rec_lemma' = Option.smartmap do_subst_con finfos.rec_lemma in 
  let prop_lemma' =  Option.smartmap do_subst_con finfos.prop_lemma in 
  if function_constant' == finfos.function_constant && 
    graph_ind' == finfos.graph_ind && 
    equation_lemma' == finfos.equation_lemma &&
    correctness_lemma' == finfos.correctness_lemma && 
    completeness_lemma' == finfos.completeness_lemma && 
    rect_lemma' == finfos.rect_lemma && 
    rec_lemma' == finfos.rec_lemma && 
    prop_lemma' == finfos.prop_lemma 
  then finfos 
  else
    { function_constant = function_constant';
      graph_ind = graph_ind';
      equation_lemma = equation_lemma' ;
      correctness_lemma = correctness_lemma' ;
      completeness_lemma = completeness_lemma' ;
      rect_lemma = rect_lemma' ;
      rec_lemma = rec_lemma';
      prop_lemma = prop_lemma';
      is_general = finfos.is_general
    }

let classify_Function (_,infos) = Libobject.Substitute infos

let export_Function infos = Some infos


let discharge_Function (_,finfos) = 
  let function_constant' = Lib.discharge_con finfos.function_constant
  and graph_ind' = Lib.discharge_inductive finfos.graph_ind 
  and equation_lemma' = Option.smartmap Lib.discharge_con finfos.equation_lemma 
  and correctness_lemma' = Option.smartmap Lib.discharge_con finfos.correctness_lemma 
  and completeness_lemma' = Option.smartmap Lib.discharge_con finfos.completeness_lemma 
  and rect_lemma' = Option.smartmap Lib.discharge_con finfos.rect_lemma 
  and rec_lemma' = Option.smartmap Lib.discharge_con finfos.rec_lemma
  and prop_lemma' = Option.smartmap Lib.discharge_con finfos.prop_lemma
  in
  if function_constant' == finfos.function_constant && 
    graph_ind' == finfos.graph_ind && 
    equation_lemma' == finfos.equation_lemma &&
    correctness_lemma' == finfos.correctness_lemma && 
    completeness_lemma' == finfos.completeness_lemma && 
    rect_lemma' == finfos.rect_lemma && 
    rec_lemma' == finfos.rec_lemma && 
    prop_lemma' == finfos.prop_lemma 
  then Some finfos 
  else
    Some { function_constant = function_constant' ;
	   graph_ind = graph_ind' ;
	   equation_lemma = equation_lemma' ;
	   correctness_lemma = correctness_lemma' ;
	   completeness_lemma = completeness_lemma';
	   rect_lemma = rect_lemma';
	   rec_lemma = rec_lemma';
	   prop_lemma = prop_lemma' ;
	   is_general = finfos.is_general
	 }    

open Term
let pr_info f_info = 
  str "function_constant := " ++ Printer.pr_lconstr (mkConst f_info.function_constant)++ fnl () ++
    str "function_constant_type := " ++ 
    (try Printer.pr_lconstr (Global.type_of_global (ConstRef f_info.function_constant)) with _ -> mt ()) ++ fnl () ++
    str "equation_lemma := " ++ (Option.fold_right (fun v acc -> Printer.pr_lconstr (mkConst v)) f_info.equation_lemma (mt ()) ) ++ fnl () ++
    str "completeness_lemma :=" ++ (Option.fold_right (fun v acc -> Printer.pr_lconstr (mkConst v)) f_info.completeness_lemma (mt ()) ) ++ fnl () ++
    str "correctness_lemma := " ++ (Option.fold_right (fun v acc -> Printer.pr_lconstr (mkConst v)) f_info.correctness_lemma (mt ()) ) ++ fnl () ++
    str "rect_lemma := " ++ (Option.fold_right (fun v acc -> Printer.pr_lconstr (mkConst v)) f_info.rect_lemma (mt ()) ) ++ fnl () ++
    str "rec_lemma := " ++ (Option.fold_right (fun v acc -> Printer.pr_lconstr (mkConst v)) f_info.rec_lemma (mt ()) ) ++ fnl () ++
    str "prop_lemma := " ++ (Option.fold_right (fun v acc -> Printer.pr_lconstr (mkConst v)) f_info.prop_lemma (mt ()) ) ++ fnl () ++
    str "graph_ind := " ++ Printer.pr_lconstr (mkInd f_info.graph_ind) ++ fnl () 

let pr_table tb = 
  let l = Cmap.fold (fun k v acc -> v::acc) tb [] in 
  Util.prlist_with_sep fnl pr_info l

let in_Function,out_Function = 
  Libobject.declare_object
    {(Libobject.default_object "FUNCTIONS_DB") with 
       Libobject.cache_function = cache_Function;
       Libobject.load_function  = load_Function;
       Libobject.classify_function  = classify_Function;
       Libobject.subst_function = subst_Function;
       Libobject.export_function = export_Function;
       Libobject.discharge_function = discharge_Function
(*        Libobject.open_function = open_Function; *)
    }



(* Synchronisation with reset *)
let freeze () = 
  !from_function,!from_graph
let unfreeze (functions,graphs) = 
(*   Pp.msgnl (str "unfreezing function_table : " ++ pr_table l); *)
  from_function := functions;
  from_graph := graphs

let init () = 
(*   Pp.msgnl (str "reseting function_table");  *)
  from_function := Cmap.empty;
  from_graph := Indmap.empty

let _ = 
  Summary.declare_summary "functions_db_sum"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_module = false; 
      Summary.survive_section = false }

let find_or_none id = 
  try Some 
    (match Nametab.locate (make_short_qualid id) with ConstRef c -> c | _ -> Util.anomaly "Not a constant" 
    ) 
  with Not_found -> None



let find_Function_infos f = 
  Cmap.find f !from_function


let find_Function_of_graph ind = 
  Indmap.find ind !from_graph
  
let update_Function finfo = 
(*   Pp.msgnl (pr_info finfo); *)
  Lib.add_anonymous_leaf (in_Function finfo)
      
  
let add_Function is_general f = 
  let f_id = id_of_label (con_label f) in 
  let equation_lemma = find_or_none (mk_equation_id f_id)
  and correctness_lemma = find_or_none (mk_correct_id f_id) 
  and completeness_lemma = find_or_none (mk_complete_id f_id) 
  and rect_lemma = find_or_none (Nameops.add_suffix f_id "_rect")
  and rec_lemma = find_or_none (Nameops.add_suffix f_id "_rec")
  and prop_lemma = find_or_none (Nameops.add_suffix f_id "_ind")
  and graph_ind = 
    match Nametab.locate (make_short_qualid (mk_rel_id f_id)) 
    with | IndRef ind -> ind | _ -> Util.anomaly "Not an inductive"
  in
  let finfos = 
    { function_constant = f;
      equation_lemma = equation_lemma;
      completeness_lemma = completeness_lemma;
      correctness_lemma = correctness_lemma;
      rect_lemma = rect_lemma;
      rec_lemma = rec_lemma;
      prop_lemma = prop_lemma;
      graph_ind = graph_ind;
      is_general = is_general
      
    }
  in
  update_Function finfos

let pr_table () = pr_table !from_function
(*********************************)
(* Debuging *)
let function_debug = ref false 
open Goptions

let function_debug_sig =
  {
    optsync = false;
    optname = "Function debug";
    optkey =  PrimaryTable("Function_debug");
    optread = (fun () -> !function_debug);
    optwrite = (fun b -> function_debug := b)
  }

let _ = declare_bool_option function_debug_sig


let do_observe () = 
  !function_debug = true
      
      
    
exception Building_graph of exn 
exception Defining_principle of exn
