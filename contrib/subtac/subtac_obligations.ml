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

type obligation =
    { obl_name : identifier;
      obl_type  : types;
      obl_body : constr option;
    }

type obligations = (obligation array * int)

type program_info = {
  prg_name: identifier;
  prg_body: constr list -> constr;
  prg_type: types;
  prg_obligations: obligations;
}

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
  let obls_constrs = 
    Array.fold_right (fun x acc -> (out_some x.obl_body) :: acc) (fst prg.prg_obligations) []
  in
  let ce = 
    { const_entry_body = prg.prg_body obls_constrs;
      const_entry_type = Some prg.prg_type;
      const_entry_opaque = false;
      const_entry_boxed = false} 
  in
  let _constant = Declare.declare_constant 
    prg.prg_name (DefinitionEntry ce,IsDefinition Definition)
  in
    Subtac_utils.definition_message prg.prg_name
    
open Evd

let add_entry n b t obls =
  Options.if_verbose pp (str (string_of_id n) ++ str " has type-checked");
  let try_tactics e = 
    List.fold_left 
      (fun acc (n, t) ->
	 let ev = { evar_concl = t ; evar_body = Evar_empty ; 
		    evar_hyps = Environ.empty_named_context_val ; evar_extra = None } 
	 in 
	 let cstr = 
	   try
	     let c = Subtac_utils.solve_by_tac ev Auto.default_full_auto in	       
	       Some c
	   with _ -> None
	 in { obl_name = n ; obl_type = t; obl_body = cstr } :: acc)
      [] e
  in
    match obls with
	[] -> Options.if_verbose ppnl (str ".");
	  declare_definition { prg_name = n ; prg_body = b ; prg_type = t ; prg_obligations = ([||], 0) }
      | l -> 
	  let len = List.length l in
	  let _ = Options.if_verbose ppnl (str ", generating " ++ int len ++ str " obligation(s)") in
	  let obls = try_tactics l in
	  let rem = List.fold_left (fun acc obl -> if obl.obl_body = None then succ acc else acc) 0 obls in
	  let prg = { prg_name = n ; prg_body = b ; prg_type = t ; prg_obligations = (Array.of_list obls, rem) } in
	    if rem < len then 
	      Options.if_verbose ppnl (int rem ++ str " obligation(s) remaining.");
	    if rem = 0 then 
	      declare_definition prg
	    else
	      from_prg := ProgMap.add n prg !from_prg
		
(*		
let (theory_to_obj, obj_to_theory) = 
  let cache_th (name,th) = add_entry name th
  and export_th x = Some x in
  declare_object
    {(default_object "program-tcc") with
      open_function = (fun i o -> if i=1 then cache_th o);
      cache_function = cache_th;
      subst_function = (fun _ -> assert(false));
      classify_function = (fun (_,x) -> Dispose);
      export_function = export_th }
*)

let error s = Util.error s

let subtac_obligation (user_num, name) =
  let num = pred user_num in
  let prg_infos = !from_prg in
  let prg = 
    match name with
	Some n -> ProgMap.find n prg_infos
      | None -> 
	  (let n = map_cardinal prg_infos in
	     match n with 
		 0 -> error "No obligations remaining"
	       | 1 -> map_first prg_infos
	       | _ -> error "More than one program with unsolved obligations")
  in
  let obls, rem = prg.prg_obligations in
    if num < Array.length obls then
      let obl = obls.(num) in
	match obl.obl_body with
	    None -> 
	      Command.start_proof obl.obl_name Subtac_utils.goal_proof_kind obl.obl_type
		(fun strength gr -> 
		   debug 2 (str "Proof of obligation " ++ int user_num ++ str " finished");		   
		   let obl = { obl with obl_body = Some (Libnames.constr_of_global gr) } in
		   let obls = Array.copy obls in
		   let _ = obls.(num) <- obl in
		   let prg' = { prg with prg_obligations = (obls, pred rem) } in
		     if rem > 1 then (
		       debug 2 (int rem ++ str " obligations remaining");
		       from_prg := map_replace prg.prg_name prg' !from_prg)
		     else (
		       declare_definition prg';
		       from_prg := ProgMap.remove prg.prg_name !from_prg
		     ));
	      trace (str "Started obligation " ++ int user_num ++ str "  proof")
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
	    }) evars)
  in arr, Array.length arr
