(**
   - Get types of existentials ;
   - Flatten dependency tree (prefix order) ;
   - Replace existentials by De Bruijn indices in term, applied to the right arguments ;
   - Apply term prefixed by quantification on "existentials".
*)

open Term
open Names
open Evd
open List
open Pp
open Util

let reverse_array arr = 
  Array.of_list (List.rev (Array.to_list arr))
    
let trace s = 
  if !Options.debug then (msgnl s; msgerr s)
  else ()

(** Utilities to find indices in lists *)
let list_index x l =
  let rec aux i = function
      k :: tl -> if k = x then i else aux (succ i) tl
    | [] -> raise Not_found
  in aux 0 l

let list_assoc_index x l =
  let rec aux i = function
      (k, _, v) :: tl -> if k = x then i else aux (succ i) tl
    | [] -> raise Not_found
  in aux 0 l

(** Substitute evar references in t using De Bruijn indices, 
  where n binders were passed through. *)
let subst_evars evs n t = 
  let evar_info id = 
    let rec aux i = function
	(k, h, v) :: tl -> 
	  if k = id then (i, h, v) else aux (succ i) tl
      | [] -> raise Not_found
    in 
    let (idx, hyps, v) = aux 0 evs in
      n + idx + 1, hyps
  in
  let rec substrec depth c = match kind_of_term c with
    | Evar (k, args) ->
	(let index, hyps = 
	   try evar_info k
	   with Not_found -> 
	     anomaly ("eterm: existential variable " ^ string_of_int k ^ " not found")
	 in
	 (try trace (str "Evar " ++ int k ++ str " found, applied to " ++ int (Array.length args) ++ str "arguments," ++
		       int (List.length hyps) ++ str " hypotheses"); 	      with _ -> () );
	 let ex = mkRel (index + depth) in
	   (* Evar arguments are created in inverse order, 
	      and we must not apply to defined ones (i.e. LetIn's)
	   *)
	 let args =
	   let rec aux hyps args acc =
	     match hyps, args with
		 ((_, None, _) :: tlh), (c :: tla) -> 
		   aux tlh tla ((map_constr_with_binders succ substrec depth c) :: acc)
	       | ((_, Some _, _) :: tlh), (_ :: tla) ->
		   aux tlh tla acc
	       | [], [] -> acc
	       | _, _ -> acc (* failwith "subst_evars: invalid argument" *)
	   in aux hyps (Array.to_list args) [] 
	 in
	   mkApp (ex, Array.of_list args))
    | _ -> map_constr_with_binders succ substrec depth c
  in 
    substrec 0 t

let subst_evar_constr evs n t = 
  let evar_info id = 
    let rec aux i = function
	(k, n, h, v) :: tl -> 
	  if k = id then (n, h, v) else aux (succ i) tl
      | [] -> raise Not_found
    in 
    let (c, hyps, v) = aux 0 evs in
      c, hyps
  in
  let rec substrec depth c = match kind_of_term c with
    | Evar (k, args) ->
	(let ex, hyps = 
	   try evar_info k
	   with Not_found -> 
	     anomaly ("eterm: existential variable " ^ string_of_int k ^ " not found")
	 in
	   (try trace (str "Evar " ++ int k ++ str " found, applied to " ++ int (Array.length args) ++ str "arguments," ++
		       int (List.length hyps) ++ str " hypotheses"); 	      with _ -> () );
	   (* Evar arguments are created in inverse order, 
	      and we must not apply to defined ones (i.e. LetIn's)
	   *)
	 let args =
	   let rec aux hyps args acc =
	     match hyps, args with
		 ((_, None, _) :: tlh), (c :: tla) -> 
		   aux tlh tla ((map_constr_with_binders succ substrec depth c) :: acc)
	       | ((_, Some _, _) :: tlh), (_ :: tla) ->
		   aux tlh tla acc
	       | [], [] -> acc
	       | _, _ -> acc (*failwith "subst_evars: invalid argument"*)
	   in aux hyps (Array.to_list args) [] 
	 in
	   mkApp (ex, Array.of_list args))
    | _ -> map_constr_with_binders succ substrec depth c
  in 
    substrec 0 t

      
(** Substitute variable references in t using De Bruijn indices, 
  where n binders were passed through. *)
let subst_vars acc n t = 
  let var_index id = 
    let idx = list_index id acc in
      idx + 1
  in
  let rec substrec depth c = match kind_of_term c with
    | Var v -> (try mkRel (depth + (var_index v)) with Not_found -> c)
    | _ -> map_constr_with_binders succ substrec depth c
  in 
    substrec 0 t

(** Rewrite type of an evar ([ H1 : t1, ... Hn : tn |- concl ])
  to a product : forall H1 : t1, ..., forall Hn : tn, concl.
  Changes evars and hypothesis references to De Bruijn indices.
*)
let etype_of_evar evs ev hyps =
  let rec aux acc n = function
      (id, copt, t) :: tl ->
	let t' = subst_evars evs n t in
	let t'' = subst_vars acc 0 t' in
	let copt' = option_map (subst_evars evs n) copt in
	let copt' = option_map (subst_vars acc 0) copt' in
 	  mkNamedProd_or_LetIn (id, copt', t'') (aux (id :: acc) (succ n) tl)
    | [] ->
	let t' = subst_evars evs n ev.evar_concl in
	  subst_vars acc 0 t'	
  in aux [] 0 (rev hyps)


open Tacticals
    
let eterm_term evm t tycon = 
  (* 'Serialize' the evars, we assume that the types of the existentials
     refer to previous existentials in the list only *)
  let evl = to_list evm in
    trace (str "Eterm, transformed to list");
  let evts = 
    (* Remove existential variables in types and build the corresponding products *)
    fold_right 
      (fun (id, ev) l ->
	 trace (str "Eterm: " ++ str "treating evar: " ++ int id);
	 let hyps = Environ.named_context_of_val ev.evar_hyps in
	 let evtyp = etype_of_evar l ev hyps in
	   trace (str "Evar's type is: " ++ Termops.print_constr_env (Global.env ()) evtyp);
	 let y' = (id, hyps, evtyp) in
	   y' :: l) 
      evl []
  in 
  let t' = (* Substitute evar refs in the term by De Bruijn indices *)
    subst_evars evts 0 t 
  in
  let evar_names = 
    let i = ref 0 in
      List.map (fun (id, _, c) -> incr i; (id_of_string ("evar_" ^ string_of_int !i)), c) evts
  in
  let evar_bl =
    List.map (fun (id, c) -> Name id, None, c) evar_names
  in
  let anon_evar_bl = List.map (fun (_, x, y) -> (Anonymous, x, y)) evar_bl in
    (* Generalize over the existential variables *)
  let t'' = Termops.it_mkLambda_or_LetIn t' evar_bl 
  and tycon = option_map 
    (fun typ -> Termops.it_mkProd_wo_LetIn typ anon_evar_bl) tycon
  in
    (try 
       trace (str "Term given to eterm" ++ spc () ++
		Termops.print_constr_env (Global.env ()) t);
       trace (str "Term constructed in eterm" ++ spc () ++
		Termops.print_constr_env (Global.env ()) t'');
       ignore(option_map 
		(fun typ ->
		   trace (str "Type :" ++ spc () ++
			    Termops.print_constr_env (Global.env ()) typ))
		tycon);
     with _ -> ());
    t'', tycon, evar_names

let rec take n l = 
  if n = 0 then [] else List.hd l :: take (pred n) (List.tl l)    

let trunc_named_context n ctx = 
  let len = List.length ctx in
    take (len - n) ctx
  
let eterm_obligations name nclen evm t tycon = 
  (* 'Serialize' the evars, we assume that the types of the existentials
     refer to previous existentials in the list only *)
  let evl = to_list evm in
  trace (str "Eterm, transformed to list");
  let evts = 
    (* Remove existential variables in types and build the corresponding products *)
    fold_right 
      (fun (id, ev) l ->
	 trace (str "Eterm: " ++ str "treating evar: " ++ int id);
	 let hyps = Environ.named_context_of_val ev.evar_hyps in
	 let hyps = trunc_named_context nclen hyps in
	   trace (str "Named context is: " ++ Printer.pr_named_context (Global.env ()) hyps);
	 let evtyp = etype_of_evar l ev hyps in
	   trace (str "Evar's type is: " ++ Termops.print_constr_env (Global.env ()) evtyp);
	 let y' = (id, hyps, evtyp) in
	   y' :: l) 
      evl []
  in 
  let evar_names = 
    let i = ref 0 in
      List.map (fun (id, h, c) -> incr i; 
		  (id, id_of_string (string_of_id name ^ "_obligation_" ^ string_of_int !i), h, c)) evts
  in
  let t' = (* Substitute evar refs in the term by De Bruijn indices *)
    subst_evar_constr (List.map (fun (id, n, h, c) -> id, mkVar n, h, c) evar_names) 0 t 
  in
  let _, evars =
    fold_right
      (fun (_, n, h, c) (acc, l) ->
	 let evt = Termops.it_mkProd_wo_LetIn c acc in
	   ((Name n, None, c) :: acc, (n, evt) :: l))
      evar_names ([], [])
  in
    (try 
       trace (str "Term given to eterm" ++ spc () ++
		Termops.print_constr_env (Global.env ()) t);
       trace (str "Term constructed in eterm" ++ spc () ++
		Termops.print_constr_env (Global.env ()) t');
       ignore(iter
		(fun (n, typ) ->
		   trace (str "Evar :" ++ spc () ++ str (string_of_id n) ++
			    Termops.print_constr_env (Global.env ()) typ))
		evars);
     with _ -> ());
    let subst_closure l = 
      let l' = List.map2 (fun (id, _, h, c) cst -> (id, cst, h, c)) evar_names l in
      let _, l'' = 
	List.fold_right 
	  (fun (id, cst, h, c) (acc, res) ->
	     let cst' = applist (cst, List.rev acc) in
	       (cst' :: acc, (id, cst', h, c) :: res))
	  l' ([], [])
      in
      let t' = subst_evar_constr l'' 0 t in
	trace (str "Term constructed in eterm" ++ spc () ++
		 Termops.print_constr_env (Global.env ()) t');
	t'
    in
      subst_closure, evars

let mkMetas n = 
  let rec aux i acc = 
    if i > 0 then aux (pred i) (Evarutil.mk_new_meta () :: acc)
    else acc
  in aux n []

let eterm evm t (tycon : types option) = 
  let t, tycon, evs = eterm_term evm t tycon in
    match tycon with
	Some typ -> Tactics.apply_term (mkCast (t, DEFAULTcast, typ)) []
      | None -> Tactics.apply_term t (mkMetas (List.length evs))
     
open Tacmach

let etermtac (evm, t) = eterm evm t None
