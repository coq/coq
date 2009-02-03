(* -*- compile-command: "make -C ../.. bin/coqtop.byte" -*- *)
open Printf
open Pp
open Subtac_utils
open Command
open Environ

open Term
open Names
open Libnames
open Summary
open Libobject
open Entries
open Decl_kinds
open Util
open Evd
open Declare
open Proof_type

type definition_hook = global_reference -> unit

let ppwarn cmd = Pp.warn (str"Program:" ++ cmd)
let pperror cmd = Util.errorlabstrm "Program" cmd
let error s = pperror (str s)

exception NoObligations of identifier option

let explain_no_obligations = function
    Some ident -> str "No obligations for program " ++ str (string_of_id ident)
  | None -> str "No obligations remaining"

type obligation_info = (Names.identifier * Term.types * loc * obligation_definition_status * Intset.t
			 * Tacexpr.raw_tactic_expr option) array
  
type obligation =
    { obl_name : identifier;
      obl_type : types;
      obl_location : loc;
      obl_body : constr option;
      obl_status : obligation_definition_status;
      obl_deps : Intset.t;
      obl_tac : Tacexpr.raw_tactic_expr option;
    }

type obligations = (obligation array * int)

type notations = (string * Topconstr.constr_expr * Topconstr.scope_name option) list

type program_info = {
  prg_name: identifier;
  prg_body: constr;
  prg_type: constr;
  prg_obligations: obligations;
  prg_deps : identifier list;
  prg_fixkind : Command.fixpoint_kind option ;
  prg_implicits : (Topconstr.explicitation * (bool * bool)) list;
  prg_notations : notations ;
  prg_kind : definition_kind;
  prg_hook : definition_hook;
}

let assumption_message id =
  Flags.if_verbose message ((string_of_id id) ^ " is assumed")

let default_tactic : Proof_type.tactic ref = ref Refiner.tclIDTAC
let default_tactic_expr : Tacexpr.glob_tactic_expr ref = ref (Tacexpr.TacId [])

let set_default_tactic t = default_tactic_expr := t; default_tactic := Tacinterp.eval_tactic t

(* true = All transparent, false = Opaque if possible *)
let proofs_transparency = ref true

let set_proofs_transparency = (:=) proofs_transparency
let get_proofs_transparency () = !proofs_transparency

open Goptions

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "transparency of Program obligations";
      optkey   = (SecondaryTable ("Transparent","Obligations"));
      optread  = get_proofs_transparency;
      optwrite = set_proofs_transparency; } 

let evar_of_obligation o = make_evar (Global.named_context_val ()) o.obl_type

let get_obligation_body expand obl =
  let c = Option.get obl.obl_body in
    if expand && obl.obl_status = Expand then 
      match kind_of_term c with
      | Const c -> constant_value (Global.env ()) c
      | _ -> c
    else c

let subst_deps expand obls deps t =
  let subst =
    Intset.fold
      (fun x acc ->
	let xobl = obls.(x) in
	let oblb = 
	  try get_obligation_body expand xobl
	  with _ -> assert(false)
	in (xobl.obl_name, oblb) :: acc)
      deps []
  in(*  Termops.it_mkNamedProd_or_LetIn t subst *)
    Term.replace_vars subst t
    
let subst_deps_obl obls obl =
  let t' = subst_deps false obls obl.obl_deps obl.obl_type in
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

let freeze () = !from_prg, !default_tactic_expr
let unfreeze (v, t) = from_prg := v; set_default_tactic t
let init () =
  from_prg := ProgMap.empty; set_default_tactic (Subtac_utils.tactics_call "obligation_tactic" [])

(** Beware: if this code is dynamically loaded via dynlink after the start
    of Coq, then this [init] function will not be run by [Lib.init ()].
    Luckily, here we can launch [init] at load-time. *)

let _ = init ()

let _ = 
  Summary.declare_summary "program-tcc-table"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_module = false;
      Summary.survive_section = false }

let progmap_union = ProgMap.fold ProgMap.add

let cache (_, (infos, tac)) =
  from_prg := infos;
  set_default_tactic tac

let (input,output) = 
  declare_object
    { (default_object "Program state") with
      cache_function = cache;
      load_function = (fun _ -> cache);
      open_function = (fun _ -> cache);
      classify_function = (fun _ -> Dispose);
      export_function = (fun x -> Some x) }
    
open Evd
	  
let rec intset_to = function
    -1 -> Intset.empty
  | n -> Intset.add n (intset_to (pred n))
  
let subst_body expand prg = 
  let obls, _ = prg.prg_obligations in
  let ints = intset_to (pred (Array.length obls)) in
    subst_deps expand obls ints prg.prg_body,
  subst_deps expand obls ints (Termops.refresh_universes prg.prg_type)
    
let declare_definition prg =
  let body, typ = subst_body false prg in
    (try trace (str "Declaring: " ++ Ppconstr.pr_id prg.prg_name ++ spc () ++
		  my_print_constr (Global.env()) body ++ str " : " ++ 
		  my_print_constr (Global.env()) prg.prg_type);
     with _ -> ());
  let (local, boxed, kind) = prg.prg_kind in
  let ce = 
    { const_entry_body = body;
      const_entry_type = Some typ;
      const_entry_opaque = false;
      const_entry_boxed = boxed} 
  in
    (Command.get_declare_definition_hook ()) ce;
    match local with
    | Local when Lib.sections_are_opened () ->
        let c =
          SectionLocalDef(ce.const_entry_body,ce.const_entry_type,false) in
        let _ = declare_variable prg.prg_name (Lib.cwd(),c,IsDefinition kind) in
          print_message (Subtac_utils.definition_message prg.prg_name);
          if Pfedit.refining () then 
            Flags.if_verbose msg_warning 
	      (str"Local definition " ++ Nameops.pr_id prg.prg_name ++ 
		  str" is not visible from current goals");
          VarRef prg.prg_name
    | (Global|Local) ->
	let c =
	  Declare.declare_constant 
	    prg.prg_name (DefinitionEntry ce,IsDefinition (pi3 prg.prg_kind))
	in
	let gr = ConstRef c in
	  if Impargs.is_implicit_args () || prg.prg_implicits <> [] then
	    Impargs.declare_manual_implicits false gr prg.prg_implicits;
	  print_message (Subtac_utils.definition_message prg.prg_name);
	  prg.prg_hook gr;
	  gr

open Pp
open Ppconstr

let rec lam_index n t acc =
  match kind_of_term t with
    | Lambda (na, _, b) ->
	if na = Name n then acc
	else lam_index n b (succ acc)
    | _ -> raise Not_found
	
let compute_possible_guardness_evidences (n,_) fixbody fixtype =
  match n with 
  | Some (loc, n) -> [lam_index n fixbody 0]
  | None -> 
      (* If recursive argument was not given by user, we try all args.
	 An earlier approach was to look only for inductive arguments,
	 but doing it properly involves delta-reduction, and it finally 
         doesn't seem to worth the effort (except for huge mutual 
	 fixpoints ?) *)
      let m = Term.nb_prod fixtype in
      let ctx = fst (decompose_prod_n_assum m fixtype) in
	list_map_i (fun i _ -> i) 0 ctx

let reduce_fix =
  Reductionops.clos_norm_flags Closure.betaiotazeta (Global.env ()) Evd.empty

let declare_mutual_definition l =
  let len = List.length l in
  let fixdefs, fixtypes, fiximps = 
    list_split3
      (List.map (fun x -> 
	let subs, typ = (subst_body false x) in
	  (strip_lam_n len subs), snd (decompose_prod_n len typ), x.prg_implicits) l)
  in
(*   let fixdefs = List.map reduce_fix fixdefs in *)
  let fixkind = Option.get (List.hd l).prg_fixkind in
  let arrrec, recvec = Array.of_list fixtypes, Array.of_list fixdefs in
  let fixdecls = (Array.of_list (List.map (fun x -> Name x.prg_name) l), arrrec, recvec) in
  let boxed = true (* TODO *) in
  let fixnames = (List.hd l).prg_deps in
  let kind = if fixkind <> IsCoFixpoint then Fixpoint else CoFixpoint in
  let indexes, fixdecls =
    match fixkind with
      | IsFixpoint wfl ->
	  let possible_indexes =
	    list_map3 compute_possible_guardness_evidences wfl fixdefs fixtypes in
	  let indexes = Pretyping.search_guard dummy_loc (Global.env ()) possible_indexes fixdecls in
	    Some indexes, list_map_i (fun i _ -> mkFix ((indexes,i),fixdecls)) 0 l
      | IsCoFixpoint ->
	  None, list_map_i (fun i _ -> mkCoFix (i,fixdecls)) 0 l
  in      
  (* Declare the recursive definitions *)
  let kns = list_map4 (declare_fix boxed kind) fixnames fixdecls fixtypes fiximps in
    (* Declare notations *)
    List.iter (Command.declare_interning_data ([],[])) (List.hd l).prg_notations;
    Flags.if_verbose ppnl (Command.recursive_message kind indexes fixnames);
    (match List.hd kns with ConstRef kn -> kn | _ -> assert false)
      
let declare_obligation obl body =
  match obl.obl_status with
  | Expand -> { obl with obl_body = Some body }
  | Define opaque ->
      let ce = 
	{ const_entry_body = body;
	  const_entry_type = Some obl.obl_type;
	  const_entry_opaque = 
	    (if get_proofs_transparency () then false 
	      else opaque) ;
	  const_entry_boxed = false} 
      in
      let constant = Declare.declare_constant obl.obl_name 
	(DefinitionEntry ce,IsProof Property)
      in
	print_message (Subtac_utils.definition_message obl.obl_name);
	{ obl with obl_body = Some (mkConst constant) }
	  
let red = Reductionops.nf_betaiota

let init_prog_info n b t deps fixkind notations obls impls kind hook =
  let obls' = 
    Array.mapi
      (fun i (n, t, l, o, d, tac) ->
	 debug 2 (str "Adding obligation " ++ int i ++ str " with deps : " ++ str (string_of_intset d));
         { obl_name = n ; obl_body = None; 
	   obl_location = l; obl_type = red t; obl_status = o;
	   obl_deps = d; obl_tac = tac })
      obls
  in
    { prg_name = n ; prg_body = b; prg_type = red t; prg_obligations = (obls', Array.length obls');
      prg_deps = deps; prg_fixkind = fixkind ; prg_notations = notations ;
      prg_implicits = impls; prg_kind = kind; prg_hook = hook; }
    
let get_prog name =
  let prg_infos = !from_prg in
    match name with
	Some n -> 
	  (try ProgMap.find n prg_infos
	   with Not_found -> raise (NoObligations (Some n)))
      | None -> 
	  (let n = map_cardinal prg_infos in
	     match n with 
		 0 -> raise (NoObligations None)
	       | 1 -> map_first prg_infos
	       | _ -> error "More than one program with unsolved obligations")

let get_prog_err n = 
  try get_prog n with NoObligations id -> pperror (explain_no_obligations id)

let obligations_solved prg = (snd prg.prg_obligations) = 0

let update_state s = 
(*   msgnl (str "Updating obligations info"); *)
  Lib.add_anonymous_leaf (input s)

type progress = 
    | Remain of int 
    | Dependent
    | Defined of global_reference
	  
let obligations_message rem =
  if rem > 0 then
    if rem = 1 then
      Flags.if_verbose msgnl (int rem ++ str " obligation remaining")
    else
      Flags.if_verbose msgnl (int rem ++ str " obligations remaining")
  else
    Flags.if_verbose msgnl (str "No more obligations remaining")

let update_obls prg obls rem = 
  let prg' = { prg with prg_obligations = (obls, rem) } in
    from_prg := map_replace prg.prg_name prg' !from_prg;
    obligations_message rem;
    let res = 
      if rem > 0 then Remain rem
      else (
	match prg'.prg_deps with
	    [] ->
	      let kn = declare_definition prg' in
		from_prg := ProgMap.remove prg.prg_name !from_prg;
		Defined kn
	  | l ->
	      let progs = List.map (fun x -> ProgMap.find x !from_prg) prg'.prg_deps in
		if List.for_all (fun x -> obligations_solved x) progs then 
		  (let kn = declare_mutual_definition progs in
		     from_prg := List.fold_left
		       (fun acc x -> 
			 ProgMap.remove x.prg_name acc) !from_prg progs;
		    Defined (ConstRef kn))
		else Dependent);
    in
      update_state (!from_prg, !default_tactic_expr);
      res
	    
let is_defined obls x = obls.(x).obl_body <> None

let deps_remaining obls deps = 
  Intset.fold
    (fun x acc -> 
      if is_defined obls x then acc
      else x :: acc)
    deps []

let has_dependencies obls n =
  let res = ref false in
    Array.iteri
      (fun i obl -> 
	if i <> n && Intset.mem n obl.obl_deps then
	  res := true)
      obls;
    !res
      
let kind_of_opacity o =
  match o with
  | Define false | Expand -> Subtac_utils.goal_kind
  | _ -> Subtac_utils.goal_proof_kind

let not_transp_msg = 
  str "Obligation should be transparent but was declared opaque." ++ spc () ++
    str"Use 'Defined' instead."

let warn_not_transp () = ppwarn not_transp_msg
let error_not_transp () = pperror not_transp_msg

let rec solve_obligation prg num =
  let user_num = succ num in
  let obls, rem = prg.prg_obligations in
  let obl = obls.(num) in
    if obl.obl_body <> None then
      pperror (str "Obligation" ++ spc () ++ int user_num ++ str "already" ++ spc() ++ str "solved.")    
    else
      match deps_remaining obls obl.obl_deps with
      | [] ->
	  let obl = subst_deps_obl obls obl in
	    Command.start_proof obl.obl_name (kind_of_opacity obl.obl_status) obl.obl_type
	      (fun strength gr -> 
		let cst = match gr with ConstRef cst -> cst | _ -> assert false in
		let obl = 
		  let transparent = evaluable_constant cst (Global.env ()) in
		  let body =
		    match obl.obl_status with
		    | Expand ->
			if not transparent then error_not_transp ()
			else constant_value (Global.env ()) cst
		    | Define opaque ->
			if not opaque && not transparent then error_not_transp ()
			else Libnames.constr_of_global gr
		  in { obl with obl_body = Some body }
		in
		let obls = Array.copy obls in
		let _ = obls.(num) <- obl in
		  match update_obls prg obls (pred rem) with
		  | Remain n when n > 0 ->
		      if has_dependencies obls num then
			ignore(auto_solve_obligations (Some prg.prg_name) None)
		  | _ -> ());
	    trace (str "Started obligation " ++ int user_num ++ str "  proof: " ++
		      Subtac_utils.my_print_constr (Global.env ()) obl.obl_type);
	    Pfedit.by !default_tactic;
	    Flags.if_verbose (fun () -> msg (Printer.pr_open_subgoals ())) ()
      | l -> pperror (str "Obligation " ++ int user_num ++ str " depends on obligation(s) "
		       ++ str (string_of_list ", " (fun x -> string_of_int (succ x)) l))
	  
and subtac_obligation (user_num, name, typ) =
  let num = pred user_num in
  let prg = get_prog_err name in
  let obls, rem = prg.prg_obligations in
    if num < Array.length obls then
      let obl = obls.(num) in
	match obl.obl_body with
	    None -> solve_obligation prg num
	  | Some r -> error "Obligation already solved"
    else error (sprintf "Unknown obligation number %i" (succ num))
      
   
and solve_obligation_by_tac prg obls i tac =
  let obl = obls.(i) in
  match obl.obl_body with 
      Some _ -> false
    | None -> 
	(try
	    if deps_remaining obls obl.obl_deps = [] then
	     let obl = subst_deps_obl obls obl in
	     let tac = 
	       match tac with
	       | Some t -> t
	       | None -> 
		   match obl.obl_tac with
		   | Some t -> Tacinterp.interp t
		   | None -> !default_tactic
	     in
	     let t = Subtac_utils.solve_by_tac (evar_of_obligation obl) tac in
	       obls.(i) <- declare_obligation obl t;
	       true
	    else false
	  with
	    | Stdpp.Exc_located(_, Proof_type.LtacLocated (_, Refiner.FailError (_, s)))
	    | Stdpp.Exc_located(_, Refiner.FailError (_, s))
	    | Refiner.FailError (_, s) ->
		user_err_loc (obl.obl_location, "solve_obligation", s)
	    | e -> false)

and solve_prg_obligations prg tac = 
  let obls, rem = prg.prg_obligations in
  let rem = ref rem in
  let obls' = Array.copy obls in
  let _ = 
    Array.iteri (fun i x -> 
		   if solve_obligation_by_tac prg obls' i tac then
		     decr rem)
      obls'
  in
    update_obls prg obls' !rem

and solve_obligations n tac = 
  let prg = get_prog_err n in
    solve_prg_obligations prg tac

and solve_all_obligations tac = 
  ProgMap.iter (fun k v -> ignore(solve_prg_obligations v tac)) !from_prg
      
and try_solve_obligation n prg tac = 
  let prg = get_prog prg in 
  let obls, rem = prg.prg_obligations in
  let obls' = Array.copy obls in
    if solve_obligation_by_tac prg obls' n tac then
      ignore(update_obls prg obls' (pred rem));

and try_solve_obligations n tac = 
  try ignore (solve_obligations n tac) with NoObligations _ -> ()

and auto_solve_obligations n tac : progress =
  Flags.if_verbose msgnl (str "Solving obligations automatically...");
  try solve_prg_obligations (get_prog_err n) tac with NoObligations _ -> Dependent
      
open Pp
let show_obligations ?(msg=true) n =
  let prg = get_prog_err n in
  let n = prg.prg_name in
  let obls, rem = prg.prg_obligations in
  let showed = ref 5 in
    if msg then msgnl (int rem ++ str " obligation(s) remaining: ");
    Array.iteri (fun i x -> 
		   match x.obl_body with 
		   | None -> 
		       if !showed > 0 then (
			 decr showed;
			 msgnl (str "Obligation" ++ spc() ++ int (succ i) ++ spc () ++
				   str "of" ++ spc() ++ str (string_of_id n) ++ str ":" ++ spc () ++ 
				   hov 1 (my_print_constr (Global.env ()) x.obl_type ++ str "." ++ fnl ())))
		   | Some _ -> ())
      obls
      
let show_term n =
  let prg = get_prog_err n in
  let n = prg.prg_name in
    msgnl (str (string_of_id n) ++ spc () ++ str":" ++ spc () ++
	      my_print_constr (Global.env ()) prg.prg_type ++ spc () ++ str ":=" ++ fnl ()
	    ++ my_print_constr (Global.env ()) prg.prg_body)

let add_definition n b t ?(implicits=[]) ?(kind=Global,false,Definition) ?tactic ?(hook=fun x -> ()) obls =
  Flags.if_verbose pp (str (string_of_id n) ++ str " has type-checked");
  let prg = init_prog_info n b t [] None [] obls implicits kind hook in
  let obls,_ = prg.prg_obligations in
  if Array.length obls = 0 then (
    Flags.if_verbose ppnl (str ".");    
    let cst = declare_definition prg in 
      from_prg := ProgMap.remove prg.prg_name !from_prg;
      Defined cst)
  else (
    let len = Array.length obls in
    let _ = Flags.if_verbose ppnl (str ", generating " ++ int len ++ str " obligation(s)") in
      from_prg := ProgMap.add n prg !from_prg; 
      let res = auto_solve_obligations (Some n) tactic in
	match res with
	| Remain rem -> Flags.if_verbose (fun () -> show_obligations ~msg:false (Some n)) (); res
	| _ -> res)
	
let add_mutual_definitions l ?tactic ?(kind=Global,false,Definition) notations fixkind =
  let deps = List.map (fun (n, b, t, imps, obls) -> n) l in
  let upd = List.fold_left
      (fun acc (n, b, t, imps, obls) ->
	let prg = init_prog_info n b t deps (Some fixkind) notations obls imps kind (fun x -> ()) in
	  ProgMap.add n prg acc)
      !from_prg l
  in
    from_prg := upd;
    let _defined = 
      List.fold_left (fun finished x -> 
	if finished then finished 
	else
	  let res = auto_solve_obligations (Some x) tactic in
	    match res with
	    | Defined _ -> (* If one definition is turned into a constant, the whole block is defined. *) true
	    | _ -> false) 
	false deps
    in ()
	
let admit_obligations n =
  let prg = get_prog_err n in
  let obls, rem = prg.prg_obligations in
    Array.iteri (fun i x -> 
		 match x.obl_body with 
		     None -> 
                       let x = subst_deps_obl obls x in
		       let kn = Declare.declare_constant x.obl_name (ParameterEntry (x.obl_type,false), IsAssumption Conjectural) in
			 assumption_message x.obl_name;
			 obls.(i) <- { x with obl_body = Some (mkConst kn) }
		   | Some _ -> ())
      obls;
    ignore(update_obls prg obls 0)

exception Found of int

let array_find f arr = 
  try Array.iteri (fun i x -> if f x then raise (Found i)) arr;
    raise Not_found
  with Found i -> i

let next_obligation n =
  let prg = get_prog_err n in
  let obls, rem = prg.prg_obligations in
  let i = 
    try array_find (fun x ->  x.obl_body = None && deps_remaining obls x.obl_deps = []) obls
    with Not_found -> anomaly "Could not find a solvable obligation."
  in solve_obligation prg i
      			
let default_tactic () = !default_tactic
