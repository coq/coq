(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Pp_control
open Pp
open Util
open System
open Names
open Term
open Himsg
open Reduction

open Putil
open Ptype
open Past
open Penv
open Putil

let extraction env c =
  let ren = initial_renaming env in
  let sign = Pcicenv.now_sign_of ren env in
  let fsign = Mach.fsign_of_sign (Evd.mt_evd()) sign in
  match Mach.infexecute (Evd.mt_evd()) (sign,fsign) c with
    | (_,Inf j) -> j._VAL
    | (_,Logic) -> failwith "Prog_extract.pp: should be informative"

(* les tableaux jouent un role particulier, puisqu'ils seront extraits
 * vers des tableaux ML *)

let sp_access = coq_constant ["correctness"; "Arrays"] "access"
let access = ConstRef sp_access

let has_array = ref false

let pp_conversions () =
  [< 'sTR"\
let rec int_of_pos = function
    XH -> 1
  | XI p -> 2 * (int_of_pos p) + 1
  | XO p -> 2 * (int_of_pos p)
;;

let int_of_z = function
    ZERO -> 0
  | POS p -> int_of_pos p
  | NEG p -> -(int_of_pos p)
;;
" >] (* '"' *)

(* collect all section-path in a CIC constant *)

let spset_of_cci env c =
  let spl = Fw_env.collect (extraction env c) in
  let sps = List.fold_left (fun e x -> SpSet.add x e) SpSet.empty spl in
  has_array := !has_array or (SpSet.mem sp_access sps);
  SpSet.remove sp_access sps


(* collect all Coq constants and all pgms appearing in a given program *)

let add_id env ((sp,ids) as s) id =
  if is_local env id then
    s
  else if is_global id then
    (sp,IdSet.add id ids)
  else
    try (SpSet.add (Nametab.sp_of_id FW id) sp,ids) with Not_found -> s

let collect env =
  let rec collect_desc env s = function
    | Var x -> add_id env s x
    | Acc x -> add_id env s x
    | Aff (x,e1) -> add_id env (collect_rec env s e1) x
    | TabAcc (_,x,e1) ->
	has_array := true;
	add_id env (collect_rec env s e1) x
    | TabAff (_,x,e1,e2) ->
	has_array := true;
	add_id env (collect_rec env (collect_rec env s e1) e2) x
    | Seq bl ->
	List.fold_left (fun s st -> match st with
			    Statement p -> collect_rec env s p
			  | _ -> s) s bl
    | If (e1,e2,e3) ->
    	collect_rec env (collect_rec env (collect_rec env s e1) e2) e3
    | While (b,_,_,bl) ->
	let s = List.fold_left (fun s st -> match st with
				    Statement p -> collect_rec env s p
				  | _ -> s) s bl in
	  collect_rec env s b
    | Lam (bl,e) ->
	collect_rec (traverse_binders env bl) s e
    | App (e1,l) ->
	let s = List.fold_left (fun s a -> match a with
				    Term t -> collect_rec env s t
				  | Type _ | Refarg _ -> s) s l in
	  collect_rec env s e1
    | SApp (_,l) ->
	List.fold_left (fun s a -> collect_rec env s a) s l
    | LetRef (x,e1,e2) ->
	let (_,v),_,_,_ = e1.info.kappa in
	  collect_rec (add (x,Ref v) env) (collect_rec env s e1) e2
    | LetIn (x,e1,e2) ->
	let (_,v),_,_,_ = e1.info.kappa in
	  collect_rec (add (x,v) env) (collect_rec env s e1) e2
    | LetRec (f,bl,_,_,e) ->
	let env' = traverse_binders env bl in
	let env'' = add (f,make_arrow bl e.info.kappa) env' in
	  collect_rec env'' s e
    | Debug (_,e1) -> collect_rec env s e1
    | PPoint (_,d) -> collect_desc env s d
    | Expression c ->
	let (sp,ids) = s in
	let sp' = spset_of_cci env c in
	SpSet.fold 
	  (fun s (es,ei) ->
	     let id = basename s in
	     if is_global id then (*SpSet.add s*)es,IdSet.add id ei
	     else SpSet.add s es,ei)
	  sp' (sp,ids)

  and collect_rec env s p = collect_desc env s p.desc

  in
  collect_rec env (SpSet.empty,IdSet.empty)


(* On a besoin de faire du renommage, tout comme pour l'extraction des
 * termes Coq. En ce qui concerne les globaux, on utilise la table de
 * Fwtoml. Pour les objects locaux, on introduit la structure de
 * renommage rename_struct
 *)

module Ocaml_ren = Ocaml.OCaml_renaming

let rename_global id =
  let id' = Ocaml_ren.rename_global_term !Fwtoml.globals (Name id) in
  Fwtoml.add_global_renaming (id,id');
  id'

type rename_struct = { rn_map : identifier IdMap.t;
		       rn_avoid : identifier list }

let rn_empty = { rn_map = IdMap.empty; rn_avoid = [] }

let rename_local rn id =
  let id' = Ocaml_ren.rename_term (!Fwtoml.globals@rn.rn_avoid) (Name id) in
  { rn_map = IdMap.add id id' rn.rn_map; rn_avoid = id' :: rn.rn_avoid },
  id'

let get_local_name rn id = IdMap.find id rn.rn_map

let get_name env rn id =
  if is_local env id then
    get_local_name rn id
  else
    Fwtoml.get_global_name id

let rec rename_binders rn = function
  | [] -> rn
  | (id,_) :: bl -> let rn',_ = rename_local rn id in rename_binders rn' bl

(* on a bespoin d'un pretty-printer de constr particulier, qui reconnaisse
 * les acces a des references et dans des tableaux, et qui de plus n'imprime
 * pas de GENTERM lorsque des identificateurs ne sont pas visibles.
 * Il est simplifie dans la mesure ou l'on a ici que des constantes et
 * des applications.
 *)

let putpar par s =
  if par then [< 'sTR"("; s; 'sTR")" >] else s

let is_ref env id =
  try
    (match type_in_env env id with Ref _ -> true | _ -> false)
  with
    Not_found -> false

let rec pp_constr env rn = function
  | VAR id ->
      if is_ref env id then 
	[< 'sTR"!"; pID (get_name env rn id) >] 
      else
	pID (get_name env rn id)
  | DOPN((Const _|MutInd _|MutConstruct _) as oper, _) ->
      pID (Fwtoml.name_of_oper oper)
  | DOPN(AppL,v) ->
      if Array.length v = 0 then
	  [< >]
      else begin
	match v.(0) with
	    DOPN(Const sp,_) when sp = sp_access ->
	      [< pp_constr env rn v.(3); 
		 'sTR".(int_of_z "; pp_constr env rn v.(4); 'sTR")" >]
	  | _ ->
	      hOV 2 (putpar true (prvect_with_sep (fun () -> [< 'sPC >])
				    (pp_constr env rn) v))
      end
  | DOP2(Cast,c,_) -> pp_constr env rn c
  | _ -> failwith "Prog_extract.pp_constr: unexpected constr"


(* pretty-print of imperative programs *)

let collect_lambda = 
  let rec collect acc p = match p.desc with
    | Lam(bl,t) -> collect (bl@acc) t
    | x         -> acc,p
  in 
  collect []

let pr_binding rn = 
  prlist_with_sep (fun () -> [< >])
    (function 
       | (id,(Untyped | BindType _)) -> 
	   [< 'sTR" "; pID (get_local_name rn id) >]
       | (id,BindSet) -> [< >])

let pp_prog id =
  let rec pp_d env rn par = function
    | Var x -> pID (get_name env rn x)
    | Acc x -> [< 'sTR"!"; pID (get_name env rn x) >]
    | Aff (x,e1) -> [< pID (get_name env rn x); 
		       'sTR" := "; hOV 0 (pp env rn false e1) >]
    | TabAcc (_,x,e1) ->
	[< pID (get_name env rn x); 
	   'sTR".(int_of_z "; hOV 0 (pp env rn true e1); 'sTR")" >]
    | TabAff (_,x,e1,e2) ->
	[< pID (get_name env rn x);
	   'sTR".(int_of_z "; hOV 0 (pp env rn true e1); 'sTR")";
	   'sTR" <-"; 'sPC; hOV 2 (pp env rn false e2) >]
    | Seq bl ->
	[< 'sTR"begin"; 'fNL;
	   'sTR"  "; hOV 0 [< pp_block env rn bl; >]; 'fNL;
	   'sTR"end" >]
    | If (e1,e2,e3) ->
	putpar par [< 'sTR"if "; (pp env rn false e1);
		      'sTR" then"; 'fNL;
		      'sTR"  "; hOV 0 (pp env rn false e2); 'fNL;
		      'sTR"else"; 'fNL;
		      'sTR"  "; hOV 0 (pp env rn false e3) >]
	(* optimisations : then begin .... end else begin ... end *)
    | While (b,inv,_,bl) ->
	[< 'sTR"while "; (pp env rn false b); 'sTR" do"; 'fNL;		    
	   'sTR"  ";
	   hOV 0 [< (match inv with
			 None -> [< >] 
		       | Some c -> [< 'sTR"(* invariant: "; pTERM c.a_value ; 
				      'sTR" *)"; 'fNL >]);
		    pp_block env rn bl; >]; 'fNL;
	   'sTR"done"; >]
    | Lam (bl,e) ->
	let env' = traverse_binders env bl in
	let rn' = rename_binders rn bl in
	  putpar par 
	    (hOV 2 [< 'sTR"fun"; pr_binding rn' bl; 'sTR" ->";
		      'sPC; pp env' rn' false e >])
    | SApp ((Var id)::_,  [e1; e2])
	when id = connective_and or id = connective_or ->
	  let conn = if id = connective_and then "&" else "or" in
	  putpar par 
	    (hOV 0 [< pp env rn true e1; 'sPC; 'sTR conn; 'sPC;
		      pp env rn true e2 >])
    | SApp ((Var id)::_, [e]) when id = connective_not ->
	putpar par 
	  (hOV 0 [< 'sTR"not"; 'sPC; pp env rn true e >])
    | SApp _ ->
	invalid_arg "Prog_extract.pp_prog (SApp)"
    | App(e1,[]) ->
	hOV 0 (pp env rn false e1)
    | App (e1,l) ->
	putpar true
	  (hOV 2 [< pp env rn true e1;
		    prlist (function 
				Term p -> [< 'sPC; pp env rn true p >]
			      | Refarg x -> [< 'sPC; pID (get_name env rn x) >]
			      | Type _ -> [< >]) 
		      l >])
    | LetRef (x,e1,e2) ->
	let (_,v),_,_,_ = e1.info.kappa in
	let env' = add (x,Ref v) env in
	let rn',x' = rename_local rn x in
	putpar par 
	  (hOV 0 [< 'sTR"let "; pID x'; 'sTR" = ref "; pp env rn false e1;
		    'sTR" in"; 'fNL; pp env' rn' false e2 >])
    | LetIn (x,e1,e2) ->
	let (_,v),_,_,_ = e1.info.kappa in
	let env' = add (x,v) env in
	let rn',x' = rename_local rn x in
	putpar par 
	  (hOV 0 [< 'sTR"let "; pID x'; 'sTR" = "; pp env rn false e1;
		    'sTR" in"; 'fNL; pp env' rn' false e2 >])
    | LetRec (f,bl,_,_,e) ->
	let env' = traverse_binders env bl in
	let rn' = rename_binders rn bl in
	let env'' = add (f,make_arrow bl e.info.kappa) env' in
	let rn'',f' = rename_local rn' f in
	putpar par 
	  (hOV 0 [< 'sTR"let rec "; pID f'; pr_binding rn' bl; 'sTR" ="; 'fNL;
		    'sTR"  "; hOV 0 [< pp env'' rn'' false e >]; 'fNL;
		    'sTR"in "; pID f' >])
    | Debug (_,e1) -> pp env rn par e1
    | PPoint (_,d) -> pp_d env rn par d
    | Expression c -> 
	pp_constr env rn (extraction env c)

  and pp_block env rn bl =
    let bl =
      map_succeed (function Statement p -> p | _ -> failwith "caught") bl
    in
      prlist_with_sep (fun () -> [< 'sTR";"; 'fNL >])
      	(fun p -> hOV 0 (pp env rn false p)) bl

  and pp env rn par p = 
    [< pp_d env rn par p.desc >]

  and pp_mut v c = match v with
    | Ref _ ->
	[< 'sTR"ref "; pp_constr empty rn_empty (extraction empty c) >]
    | Array (n,_) ->
	[< 'sTR"Array.create "; 'cUT;
	   putpar true 
	     [< 'sTR"int_of_z ";
		pp_constr empty rn_empty (extraction empty n) >];
	   'sTR" "; pp_constr empty rn_empty (extraction empty c) >]
    | _ -> invalid_arg "pp_mut"
  in
  let v = lookup_global id in
  let id' = rename_global id in
    if is_mutable v then
      try
	let c = find_init id in
	hOV 0 [< 'sTR"let "; pID id'; 'sTR" = "; pp_mut v c >]
      with Not_found -> 
	errorlabstrm "Prog_extract.pp_prog"
	  [< 'sTR"The variable "; pID id;
	     'sTR" must be initialized first !" >]
    else
      match find_pgm id with
	| None -> 
	    errorlabstrm "Prog_extract.pp_prog"
	      [< 'sTR"The program "; pID id;
		 'sTR" must be realized first !" >]
      	| Some p ->
	    let bl,p = collect_lambda p in
	    let rn = rename_binders rn_empty bl in
	    let env = traverse_binders empty bl in
	    hOV 0  [< 'sTR"let "; pID id'; pr_binding rn bl; 'sTR" ="; 'fNL; 
		      'sTR"  "; hOV 2 (pp env rn false p) >]

(* extraction des programmes impératifs/fonctionnels vers ocaml *)

(* Il faut parfois importer des modules non ouverts, sinon
 * Ocaml.OCaml_pp_file.pp echoue en disant "machin is not a defined
 * informative object". Cela dit, ce n'est pas tres satisfaisant, vu que
 * la constante existe quand meme: il vaudrait mieux contourner l'echec
 * de ml_import.fwsp_of_id
 *)

let import sp = match repr_path sp with
  | [m],_,_ ->
      begin
	try Library.import_export_module m true
        with _ -> ()
      end
  | _ -> ()

let pp_ocaml file prm =
  has_array := false;
  (* on separe objects Coq et programmes *)
  let cic,pgms =
    List.fold_left
      (fun (sp,ids) id ->
	 if is_global id then (sp,IdSet.add id ids) else (IdSet.add id sp,ids))
      (IdSet.empty,IdSet.empty) prm.needed
  in
  (* on met les programmes dans l'ordre et pour chacun on recherche les
   * objects Coq necessaires, que l'on rajoute a l'ensemble cic *)
  let cic,_,pgms =
    let o_pgms = fold_all (fun (id,_) l -> id::l) empty [] in
    List.fold_left
      (fun (cic,pgms,pl) id -> 
	 if IdSet.mem id pgms then
	   let spl,pgms' =
	     try
	       (match find_pgm id with
		  | Some p -> collect empty p
		  | None ->
		      (try 
			 let c = find_init id in
			 spset_of_cci empty c,IdSet.empty
		       with Not_found -> 
			 SpSet.empty,IdSet.empty))
	     with Not_found -> SpSet.empty,IdSet.empty
	   in
	   let cic' = 
	     SpSet.fold 
	       (fun sp cic -> import sp; IdSet.add (basename sp) cic)
	       spl cic
	   in
	   (cic',IdSet.union pgms pgms',id::pl)
	 else
	   (cic,pgms,pl)) 
      (cic,pgms,[]) o_pgms
  in
  let cic = IdSet.elements cic in
  (* on pretty-print *)
  let prm' = { needed = cic; expand = prm.expand; 
	       expansion = prm.expansion; exact = prm.exact } 
  in
  let strm = [< Ocaml.OCaml_pp_file.pp_recursive prm';
		'fNL; 'fNL;
		if !has_array then pp_conversions() else [< >];
		prlist (fun p -> [< pp_prog p; 'fNL; 'sTR";;"; 'fNL; 'fNL >])
		  pgms
	     >]
  in
  (* puis on ecrit dans le fichier *)
  let chan = open_trapping_failure open_out file ".ml" in
  let ft = with_output_to chan in
  begin
    try  pP_with ft strm ; pp_flush_with ft ()
    with e -> pp_flush_with ft () ; close_out chan; raise e
  end;
  close_out chan
    

(* Initializations of mutable objects *)

let initialize id com =
  let loc = Ast.loc com in
  let c = constr_of_com (Evd.mt_evd()) (initial_sign()) com in
  let ty = type_of (Evd.mt_evd()) (initial_sign()) c in
  try
    let v = lookup_global id in
    let ety = match v with 
      | Ref (TypePure c) -> c | Array (_,TypePure c) -> c
      | _ -> raise Not_found 
    in
    if conv (Evd.mt_evd()) ty ety then
      initialize id c
    else
      errorlabstrm "Prog_extract.initialize"
	[< 'sTR"Not the expected type for the mutable "; pID id >]
  with Not_found -> 
    errorlabstrm "Prog_extract.initialize"
      [< pr_id id; 'sTR" is not a mutable" >]

(* grammaire *)

open Vernacinterp

let _ = vinterp_add "IMPERATIVEEXTRACTION"
	  (function 
	     | VARG_STRING file :: rem ->
		 let prm = parse_param rem in (fun () -> pp_ocaml file prm)
	     | _ -> assert false)
	  
let _ = vinterp_add "INITIALIZE"
	  (function 
	     | [VARG_IDENTIFIER id ; VARG_COMMAND com] ->
		 (fun () -> initialize id com)
	     | _ -> assert false)
