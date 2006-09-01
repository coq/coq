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


type obligation =
    { obl_name : identifier;
      obl_type  : types;
      obl_body : global_reference option;
    }

type obligations = (obligation array * int)

type program_info = {
  prg_name: identifier;
  prg_body: constr;
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
  let x = ref None in 
    try
      ProgMap.iter (fun _ v -> raise (Found v)) m;
      assert(false)
    with Found x -> x
      
let map_single m = 
  if map_cardinal m = 1 then map_first m
  else raise (Invalid_argument "map_single") 
    
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
    
let add_entry _ e =
  from_prg := ProgMap.add e.prg_name e !from_prg
    
(* let subst_th (_,subst,th) =  *)
(*   let c' = subst_mps subst th.ring_carrier in                    *)
(*   let eq' = subst_mps subst th.ring_req in *)
(*   let thm1' = subst_mps subst th.ring_lemma1 in *)
(*   let thm2' = subst_mps subst th.ring_lemma2 in *)
(*   let tac'= subst_tactic subst th.ring_cst_tac in *)
(*   if c' == th.ring_carrier && *)
(*      eq' == th.ring_req && *)
(*      thm1' == th.ring_lemma1 && *)
(*      thm2' == th.ring_lemma2 && *)
(*      tac' == th.ring_cst_tac then th *)
(*   else *)
(*     { ring_carrier = c'; *)
(*       ring_req = eq'; *)
(*       ring_cst_tac = tac'; *)
(*       ring_lemma1 = thm1'; *)
(*       ring_lemma2 = thm2' } *)


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

let declare_definition prg = 
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

let error s = Util.error s


let subtac_obligation (num, name) =
  let num = pred num in
  let prg_infos = !from_prg in
  let prg = 
    match name with
	Some n -> ProgMap.find n prg_infos
      | None -> 
	  (try map_single prg_infos 
	   with _ -> error "More than one program with unsolved obligations")
  in
  let obls, rem = prg.prg_obligations in
    if num < Array.length obls then
      let obl = obls.(num) in
	match obl.obl_body with
	    None -> 
	      Command.start_proof obl.obl_name Subtac_utils.goal_proof_kind obl.obl_type
		(fun strength gr -> 
		   debug 2 (str "Proof of obligation " ++ int num ++ str " finished");
		   let rem = snd prg.prg_obligations in
		     if rem > 0 then (
		       let obl = { obl with obl_body = Some gr } in
		       let obls = Array.copy obls in
			 obls.(num) <- obl;
			 from_prg := map_replace prg.prg_name { prg with prg_obligations = (obls, rem) } !from_prg)
		     else (
		       declare_definition prg;
		       from_prg := ProgMap.remove prg.prg_name !from_prg
		     ));
		trace (str "Started obligation " ++ int num ++ str "  proof")
	  | Some r -> error "Obligation already solved"
    else error (sprintf "Unknown obligation number %i" (succ num))
      
