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

type obligation_info = (Names.identifier * Term.types * Intset.t) array

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
  prg_type: constr;
  prg_obligations: obligations;
  prg_deps : (identifier * int) list;
}

let assumption_message id =
  Options.if_verbose message ((string_of_id id) ^ " is assumed")

let default_tactic : Proof_type.tactic ref = ref Refiner.tclIDTAC

let set_default_tactic t = default_tactic := t

let evar_of_obligation o = { evar_hyps = Environ.empty_named_context_val ; 
			     evar_concl = o.obl_type ; 
			     evar_body = Evar_empty ;
			     evar_extra = None }

let subst_deps obls deps t =
  Intset.fold
    (fun x acc ->
       let xobl = obls.(x) in
	 debug 3 (str "Trying to get body of obligation " ++ int x);
       let oblb = 
	 try out_some xobl.obl_body
	 with _ ->
	   debug 3 (str "Couldn't get body of obligation " ++ int x);
	   assert(false)
       in
	 Term.subst1 oblb (Term.subst_var xobl.obl_name acc))
    deps t

let subst_deps_obl obls obl =
  let t' = subst_deps obls obl.obl_deps obl.obl_type in
    { obl with obl_type = t' }

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

open Evd

let terms_of_evar ev = 
  match ev.evar_body with
      Evar_defined b ->
	let nc = Environ.named_context_of_val ev.evar_hyps in
	let body = Termops.it_mkNamedLambda_or_LetIn b nc in
	let typ = Termops.it_mkNamedProd_or_LetIn ev.evar_concl nc in
	  body, typ
    | _ -> assert(false)
	  
let rec intset_to = function
    -1 -> Intset.empty
  | n -> Intset.add n (intset_to (pred n))
  
let subst_body prg = 
  let obls, _ = prg.prg_obligations in
    subst_deps obls (intset_to (pred (Array.length obls))) prg.prg_body

let declare_definition prg =
  let ce = 
    { const_entry_body = subst_body prg;
      const_entry_type = Some prg.prg_type;
      const_entry_opaque = false;
      const_entry_boxed = false} 
  in
  let _constant = Declare.declare_constant 
    prg.prg_name (DefinitionEntry ce,IsDefinition Definition)
  in
    Subtac_utils.definition_message prg.prg_name

open Pp
open Ppconstr

let declare_mutual_definition l =
  let len = List.length l in
  let l, nvlist = List.split l in
  let namerec = Array.of_list (List.map (fun x -> x.prg_name) l) in
  let arrec = 
    Array.of_list (List.map (fun x -> snd (decompose_prod_n len x.prg_type)) l)
  in
  let recvec = 
    Array.of_list 
      (List.map (fun x -> 
		   let subs = (subst_body x) in
		     snd (decompose_lam_n len subs)) l)
  in
  let nvrec = Array.of_list nvlist in
  let recdecls = (Array.map (fun id -> Name id) namerec, arrec, recvec) in
  let rec declare i fi =
    (try trace (str "Declaring: " ++ pr_id fi ++ spc () ++
		  my_print_constr (Global.env()) (recvec.(i)));
     with _ -> ());
    let ce = 
      { const_entry_body = mkFix ((nvrec,i),recdecls); 
        const_entry_type = Some arrec.(i);
        const_entry_opaque = false;
        const_entry_boxed = true} in
    let kn = Declare.declare_constant fi (DefinitionEntry ce,IsDefinition Fixpoint)
    in
      ConstRef kn
  in
  let lrefrec = Array.mapi declare namerec in
    Options.if_verbose ppnl (recursive_message lrefrec)
         
let declare_obligation obl body =
  let ce = 
    { const_entry_body = body;
      const_entry_type = Some obl.obl_type;
      const_entry_opaque = false;
      const_entry_boxed = false} 
  in
  let constant = Declare.declare_constant obl.obl_name 
    (DefinitionEntry ce,IsProof Property)
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
        
let red = Reductionops.nf_betaiota

let init_prog_info n b t deps obls =
  let obls' = 
    Array.mapi
      (fun i (n, t, d) ->
	 debug 2 (str "Adding obligation " ++ int i ++ str " with deps : " ++ str (string_of_intset d));
         { obl_name = n ; obl_body = None; 
	   obl_type = red t; 
	   obl_deps = d })
      obls
  in
    { prg_name = n ; prg_body = b; prg_type = red t; prg_obligations = (obls', Array.length obls');
      prg_deps = deps }
    
let pperror cmd = Util.errorlabstrm "Subtac" cmd
let error s = pperror (str s)

let get_prog name =
  let prg_infos = !from_prg in
    match name with
	Some n -> 
	  (try ProgMap.find n prg_infos
	   with Not_found -> error ("No obligations for program " ^ string_of_id n))
      | None -> 
	  (let n = map_cardinal prg_infos in
	     match n with 
		 0 -> error "No obligations remaining"
	       | 1 -> map_first prg_infos
	       | _ -> error "More than one program with unsolved obligations")

let obligations_solved prg = (snd prg.prg_obligations) = 0

let update_obls prg obls rem = 
  let prg' = { prg with prg_obligations = (obls, rem) } in
    from_prg := map_replace prg.prg_name prg' !from_prg;
    if rem > 0 then (
      Options.if_verbose msgnl (int rem ++ str " obligation(s) remaining");
    )
    else (
      debug 2 (str "No more obligations remaining");
      match prg'.prg_deps with
	  [] ->
	    declare_definition prg';
	    from_prg := ProgMap.remove prg.prg_name !from_prg
	| l ->
	    let progs = List.map (fun (x,y) -> ProgMap.find x !from_prg, y) prg'.prg_deps in
	      if List.for_all (fun x -> obligations_solved (fst x)) progs then 
		declare_mutual_definition progs)

let add_definition n b t obls =
  Options.if_verbose pp (str (string_of_id n) ++ str " has type-checked");
  let prg = init_prog_info n b t [] obls in
  let obls,_ = prg.prg_obligations in
  if Array.length obls = 0 then (
    Options.if_verbose ppnl (str ".");
    declare_definition prg)
  else (
    let len = Array.length obls in
    let _ = Options.if_verbose ppnl (str ", generating " ++ int len ++ str " obligation(s)") in
      from_prg := ProgMap.add n prg !from_prg)
	
let add_mutual_definitions l =
  let deps = List.map (fun (n, nclen, b, t, obls) -> n, nclen) l in
  let upd = List.fold_left
      (fun acc (n, nclen, b, t, obls) ->
	 let prg = init_prog_info n b t deps obls in
	   ProgMap.add n prg acc)
      !from_prg l
  in
    from_prg := upd;
    let prg = (ProgMap.find (fst (List.hd deps)) !from_prg) in
    let o, r = prg.prg_obligations in
      update_obls prg o r
	    
let is_defined obls x = obls.(x).obl_body <> None

let deps_remaining obls deps = 
    Intset.fold
      (fun x acc -> 
	 if is_defined obls x then acc
	 else x :: acc)
      deps []

let subtac_obligation (user_num, name, typ) =
  let num = pred user_num in
  let prg = get_prog name in
  let obls, rem = prg.prg_obligations in
    if num < Array.length obls then
      let obl = obls.(num) in
	match obl.obl_body with
	    None -> 
	      (match deps_remaining obls obl.obl_deps with
		  [] ->
		    let obl = subst_deps_obl obls obl in
		    Command.start_proof obl.obl_name Subtac_utils.goal_proof_kind obl.obl_type
		      (fun strength gr -> 
			 debug 2 (str "Proof of obligation " ++ int user_num ++ str " finished");		   
			 let obl = { obl with obl_body = Some (Libnames.constr_of_global gr) } in
			 let obls = Array.copy obls in
			 let _ = obls.(num) <- obl in
			   update_obls prg obls (pred rem));
		      Pfedit.by !default_tactic;
		      trace (str "Started obligation " ++ int user_num ++ str "  proof")
     		 | l -> pperror (str "Obligation " ++ int user_num ++ str " depends on obligation(s) "
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
  let obls' = Array.copy obls in
  let _ = 
    Array.iteri (fun i x -> 
		 match x.obl_body with 
		     Some _ -> ()
		   | None -> 
		       (try
			  if deps_remaining obls' x.obl_deps = [] then
			    let t = Subtac_utils.solve_by_tac (evar_of_obligation x) tac in
			      decr rem;
			      obls'.(i) <- { x with obl_body = Some t }
			  else ()
			with UserError (s, cmds) ->
			  debug 1 cmds
			  | _ -> ()))
      obls'
  in
    update_obls prg obls' !rem

let admit_obligations n =
  let prg = get_prog n in
  let obls, rem = prg.prg_obligations in
  let obls' = 
    Array.mapi (fun i x -> 
		 match x.obl_body with 
		     None -> 
			 let kn = Declare.declare_constant x.obl_name (ParameterEntry x.obl_type, IsAssumption Conjectural) in
			   assumption_message x.obl_name;
			   { x with obl_body = Some (mkConst kn) }
		   | Some _ -> x)
      obls
  in
    update_obls prg obls' 0


open Pp
let show_obligations n =
  let prg = get_prog n in
  let n = prg.prg_name in
  let obls, rem = prg.prg_obligations in
    msgnl (int rem ++ str " obligation(s) remaining: ");
    Array.iteri (fun i x -> 
		   match x.obl_body with 
		       None -> msgnl (str "Obligation" ++ spc() ++ int (succ i) ++ spc () ++ str "of" ++ spc() ++ str (string_of_id n) ++ str ":" ++ spc () ++ 
					my_print_constr (Global.env ()) x.obl_type ++ str "." ++ fnl ())
		    | Some _ -> ())
      obls
			
