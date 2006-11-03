open Printf
open Pp
open Subtac_utils

open Term
open Names
open Libnames
open Summary
open Libobject
open Entries
open Decl_kinds
open Util
open Evd

type obligation =
    { obl_name : identifier;
      obl_type : types;
      obl_body : constr option;
      obl_deps : Intset.t;
    }

type obligations = (obligation array * int)

type program_info = {
  prg_name: identifier;
  prg_body: constr;
  prg_type: types;
  prg_obligations: obligations;
}

let evar_of_obligation o = { evar_hyps = Environ.empty_named_context_val ; 
			     evar_concl = o.obl_type ; 
			     evar_body = Evar_empty ;
			     evar_extra = None }

module ProgMap = Map.Make(struct type t = identifier let compare = compare end)

let map_replace k v m = ProgMap.add k v (ProgMap.remove k m)

let map_cardinal m = 
  let i = ref 0 in 
    ProgMap.iter (fun _ _ -> incr i) m;
    !i

exception Found of program_info

let map_first m = 
  try
    ProgMap.iter (fun _ v -> raise (Found v)) m;
    assert(false)
  with Found x -> x
    
let from_prg : program_info ProgMap.t ref = ref ProgMap.empty

let _ = 
  Summary.declare_summary "program-tcc-table"
    { Summary.freeze_function = (fun () -> !from_prg);
      Summary.unfreeze_function =
        (fun v -> from_prg := v);
      Summary.init_function =
        (fun () -> from_prg := ProgMap.empty);
      Summary.survive_module = false;
      Summary.survive_section = false }

let declare_definition prg = 
(*  let obls_constrs = 
    Array.fold_right (fun x acc -> (out_some x.obl_evar.evar_body) :: acc) (fst prg.prg_obligations) []
  in*)
  let ce = 
    { const_entry_body = prg.prg_body;
      const_entry_type = Some prg.prg_type;
      const_entry_opaque = false;
      const_entry_boxed = false} 
  in
  let _constant = Declare.declare_constant 
    prg.prg_name (DefinitionEntry ce,IsDefinition Definition)
  in
    Subtac_utils.definition_message prg.prg_name
    
open Evd

let terms_of_evar ev = 
  match ev.evar_body with
      Evar_defined b ->
	let nc = Environ.named_context_of_val ev.evar_hyps in
	let body = Termops.it_mkNamedLambda_or_LetIn b nc in
	let typ = Termops.it_mkNamedProd_or_LetIn ev.evar_concl nc in
	  body, typ
    | _ -> assert(false)
	  
let declare_obligation obl body =
  let ce = 
    { const_entry_body = body;
      const_entry_type = Some obl.obl_type;
      const_entry_opaque = true;
      const_entry_boxed = false} 
  in
  let constant = Declare.declare_constant obl.obl_name (DefinitionEntry ce,IsProof Property)
  in
    Subtac_utils.definition_message obl.obl_name;
    { obl with obl_body = Some (mkConst constant) }
      
let try_tactics obls = 
  Array.map
    (fun obl ->
       match obl.obl_body with
	   None ->
	     (try
		let ev = evar_of_obligation obl in
		let c = Subtac_utils.solve_by_tac ev Auto.default_full_auto in	       
		  declare_obligation obl c		  
	      with _ -> obl)
	 | _ -> obl)
    obls
        
let add_entry n b t obls =
  Options.if_verbose pp (str (string_of_id n) ++ str " has type-checked");
  let init_obls e = 
    Array.map
      (fun (n, t, d) ->
         { obl_name = n ; obl_body = None; obl_type = t; obl_deps = d })
      e
  in
    if Array.length obls = 0 then (
      Options.if_verbose ppnl (str ".");
    declare_definition { prg_name = n ; prg_body = b ; prg_type = t ; prg_obligations = ([||], 0) } )
    else (
      let len = Array.length obls in
      let _ = Options.if_verbose ppnl (str ", generating " ++ int len ++ str " obligation(s)") in
      let obls = init_obls obls in
      let rem = Array.fold_left (fun acc obl -> if obl.obl_body = None then succ acc else acc) 0 obls in
      let prg = { prg_name = n ; prg_body = b ; prg_type = t ; prg_obligations = (obls, rem) } in
	if rem < len then 
	  Options.if_verbose ppnl (int rem ++ str " obligation(s) remaining.");
	if rem = 0 then 
	  declare_definition prg
	else
	  from_prg := ProgMap.add n prg !from_prg)
	    
let error s = Util.error s

let get_prog name =
  let prg_infos = !from_prg in
    match name with
	Some n -> ProgMap.find n prg_infos
      | None -> 
	  (let n = map_cardinal prg_infos in
	     match n with 
		 0 -> error "No obligations remaining"
	       | 1 -> map_first prg_infos
	       | _ -> error "More than one program with unsolved obligations")

let update_obls prg obls rem = 
  let prg' = { prg with prg_obligations = (obls, rem) } in
    if rem > 1 then (
      debug 2 (int rem ++ str " obligations remaining");
      from_prg := map_replace prg.prg_name prg' !from_prg)
    else (
      declare_definition prg';
      from_prg := ProgMap.remove prg.prg_name !from_prg
    )		 
	    
let is_defined obls x = obls.(x).obl_body <> None

let deps_remaining obls x = 
  let deps = obls.(x).obl_deps in
    Intset.fold
      (fun x acc -> 
	 if is_defined obls x then acc
	 else x :: acc)
      deps []

let subst_deps obls obl =
  let t' = 
    Intset.fold
      (fun x acc ->
	 let xobl = obls.(x) in
	 let oblb = out_some xobl.obl_body in
	   Term.subst1 oblb (Term.subst_var xobl.obl_name acc))
      obl.obl_deps obl.obl_type
  in { obl with obl_type = t' }

let subtac_obligation (user_num, name) =
  let num = pred user_num in
  let prg = get_prog name in
  let obls, rem = prg.prg_obligations in
    if num < Array.length obls then
      let obl = obls.(num) in
	match obl.obl_body with
	    None -> 
	      (match deps_remaining obls num with
		  [] ->
		    let obl = subst_deps obls obl in
		    Command.start_proof obl.obl_name Subtac_utils.goal_proof_kind obl.obl_type
		      (fun strength gr -> 
			 debug 2 (str "Proof of obligation " ++ int user_num ++ str " finished");		   
			 let obl = { obl with obl_body = Some (Libnames.constr_of_global gr) } in
			 let obls = Array.copy obls in
			 let _ = obls.(num) <- obl in
			   update_obls prg obls (pred rem));
		    trace (str "Started obligation " ++ int user_num ++ str "  proof")
     		 | l -> msgnl (str "Obligation " ++ int user_num ++ str " depends on obligation(s) "
		     ++ str (string_of_list ", " (fun x -> string_of_int (succ x)) l)))
	  | Some r -> error "Obligation already solved"
    else error (sprintf "Unknown obligation number %i" (succ num))
      
      
let obligations_of_evars evars =
  let arr = 
    Array.of_list
      (List.map
	 (fun (n, t) ->
	    { obl_name = n;
	      obl_type = t;
	      obl_body = None;
	      obl_deps = Intset.empty;
	    }) evars)
  in arr, Array.length arr

let solve_obligations n tac = 
  let prg = get_prog n in
  let obls, rem = prg.prg_obligations in
  let rem = ref rem in
  let obls' = 
    Array.map (fun x -> 
		 match x.obl_body with 
		     Some _ -> x
		   | None -> 
		       try
			 let t = Subtac_utils.solve_by_tac (evar_of_obligation x) tac in
			   decr rem;
			   { x with obl_body = Some t }
		       with _ -> x)
      obls
  in
    update_obls prg obls' !rem

open Pp
let show_obligations n =
  let prg = get_prog n in
  let obls, rem = prg.prg_obligations in
    msgnl (int rem ++ str " obligation(s) remaining: ");
    Array.iteri (fun i x -> 
		   match x.obl_body with 
		       None -> msgnl (int (succ i) ++ str " : " ++ spc () ++ 
					my_print_constr (Global.env ()) x.obl_type)
		    | Some _ -> ())
      obls
			
