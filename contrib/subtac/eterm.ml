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
open Subtac_utils

(* arnaud: trucs factices *)
type tactic = Tacticals.tactic
(* arnaud:/trucs factices *)

let trace s = 
  if !Flags.debug then (msgnl s; msgerr s)
  else ()

let succfix (depth, fixrels) = 
  (succ depth, List.map succ fixrels)

(** Substitute evar references in t using De Bruijn indices, 
  where n binders were passed through. *)
let subst_evar_constr evs n t = 
  let seen = ref Intset.empty in
  let transparent = ref Idset.empty in
  let evar_info id = List.assoc id evs in
  let rec substrec (depth, fixrels) c = match kind_of_term c with
    | Evar (k, args) ->
	let (id, idstr), hyps, chop, _, _ = 
	  try evar_info k
	  with Not_found -> 
	    anomaly ("eterm: existential variable " ^ string_of_int k ^ " not found")
	in
        seen := Intset.add id !seen;
	  (* Evar arguments are created in inverse order, 
	     and we must not apply to defined ones (i.e. LetIn's)
	  *)
	let args = 
	  let n = match chop with None -> 0 | Some c -> c in 
	  let (l, r) = list_chop n (List.rev (Array.to_list args)) in
	    List.rev r
	in
	let args =
	  let rec aux hyps args acc =
	     match hyps, args with
		 ((_, None, _) :: tlh), (c :: tla) -> 
		   aux tlh tla ((map_constr_with_binders succfix substrec (depth, fixrels) c) :: acc)
	       | ((_, Some _, _) :: tlh), (_ :: tla) ->
		   aux tlh tla acc
	       | [], [] -> acc
	       | _, _ -> acc (*failwith "subst_evars: invalid argument"*)
	  in aux hyps args [] 
	in
  	  (try trace (str "Evar " ++ int k ++ str " found, applied to " ++ int (List.length args) ++ str "arguments," ++
			int (List.length hyps) ++ str " hypotheses" ++ spc () ++
			pp_list (fun x -> my_print_constr (Global.env ()) x) args);
 	   with _ -> ());
	  if List.exists (fun x -> match kind_of_term x with Rel n -> List.mem n fixrels | _ -> false) args then
	    transparent := Idset.add idstr !transparent;
	  mkApp (mkVar idstr, Array.of_list args)
    | Fix _ ->
	map_constr_with_binders succfix substrec (depth, 1 :: fixrels) c
    | _ -> map_constr_with_binders succfix substrec (depth, fixrels) c
  in 
  let t' = substrec (0, []) t in
    t', !seen, !transparent

      
(** Substitute variable references in t using De Bruijn indices, 
  where n binders were passed through. *)
let subst_vars acc n t = 
  let var_index id = Util.list_index id acc in
  let rec substrec depth c = match kind_of_term c with
    | Var v -> (try mkRel (depth + (var_index v)) with Not_found -> c)
    | _ -> map_constr_with_binders succ substrec depth c
  in 
    substrec 0 t

(** Rewrite type of an evar ([ H1 : t1, ... Hn : tn |- concl ])
    to a product : forall H1 : t1, ..., forall Hn : tn, concl.
    Changes evars and hypothesis references to variable references.
    A little optimization: don't include unnecessary let-ins and their dependencies.
*) 
let etype_of_evar evs hyps concl =
  let rec aux acc n = function
      (id, copt, t) :: tl ->
	let t', s, trans = subst_evar_constr evs n t in
	let t'' = subst_vars acc 0 t' in
	let rest, s', trans' = aux (id :: acc) (succ n) tl in
	let s' = Intset.union s s' in
	let trans' = Idset.union trans trans' in
	  (match copt with
	      Some c -> 
		if noccurn 1 rest then lift (-1) rest, s', trans'
		else
		  let c', s'', trans'' = subst_evar_constr evs n c in
		  let c' = subst_vars acc 0 c' in
		    mkNamedProd_or_LetIn (id, Some c', t'') rest, 
		Intset.union s'' s', 
		Idset.union trans'' trans'
	    | None -> 
		mkNamedProd_or_LetIn (id, None, t'') rest, s', trans')
    | [] ->
	let t', s, trans = subst_evar_constr evs n concl in
	  subst_vars acc 0 t', s, trans
  in aux [] 0 (rev hyps)


open Tacticals
    
let trunc_named_context n ctx = 
  let len = List.length ctx in
    list_firstn (len - n) ctx
  
let rec chop_product n t = 
  if n = 0 then Some t
  else 
    match kind_of_term t with
      | Prod (_, _, b) ->  if noccurn 1 b then chop_product (pred n) (Termops.pop b) else None
      | _ -> None

let eterm_obligations env name isevars evm fs t tycon = 
  (* 'Serialize' the evars, we assume that the types of the existentials
     refer to previous existentials in the list only *)
  trace (str " In eterm: isevars: " ++ my_print_evardefs isevars);
  trace (str "Term given to eterm" ++ spc () ++
	    Termops.print_constr_env (Global.env ()) t);
  let nc = Environ.named_context env in
  let nc_len = Sign.named_context_length nc in
  let evl = List.rev (to_list evm) in
  let evn = 
    let i = ref (-1) in
      List.rev_map (fun (id, ev) -> incr i; 
		      (id, (!i, id_of_string
			      (string_of_id name ^ "_obligation_" ^ string_of_int (succ !i))),
		       ev)) evl
  in
  let evts = 
    (* Remove existential variables in types and build the corresponding products *)
    fold_right 
      (fun (id, (n, nstr), ev) l ->
	 let hyps = Environ.named_context_of_val ev.evar_hyps in
	 let hyps = trunc_named_context nc_len hyps in
	 let evtyp, deps, transp = etype_of_evar l hyps ev.evar_concl in
	 let evtyp, hyps, chop = 
	   match chop_product fs evtyp with
	       Some t -> 
		 (try
		    trace (str "Choped a product: " ++ spc () ++
			     Termops.print_constr_env (Global.env ()) evtyp ++ str " to " ++ spc () ++
			     Termops.print_constr_env (Global.env ()) t);
		  with _ -> ());
		 t, trunc_named_context fs hyps, fs
	     | None -> evtyp, hyps, 0
	 in
	 let loc, k = evar_source id isevars in
	 let opacity = match k with QuestionMark o -> o | _ -> true in
	 let opaque = if not opacity || chop <> fs then None else Some chop in
	 let y' = (id, ((n, nstr), hyps, opaque, evtyp, deps)) in
	   y' :: l) 
      evn []
  in 
  let t', _, transparent = (* Substitute evar refs in the term by variables *)
    subst_evar_constr evts 0 t 
  in
  let evars = 
    List.map (fun (_, ((_, name), _, opaque, typ, deps)) -> name, typ, not (opaque = None) && not (Idset.mem name transparent), deps) evts
  in
    (try
       trace (str "Term constructed in eterm" ++ spc () ++
		Termops.print_constr_env (Global.env ()) t');
       ignore(iter
		(fun (name, typ, _, deps) ->
		   trace (str "Evar :" ++ spc () ++ str (string_of_id name) ++
			    Termops.print_constr_env (Global.env ()) typ))
		evars);
     with _ -> ());
    Array.of_list (List.rev evars), t'

let mkMetas n = list_tabulate (fun _ -> Evarutil.mk_new_meta ()) n

(* let eterm evm t (tycon : types option) =  *)
(*   let t, tycon, evs = eterm_term evm t tycon in *)
(*     match tycon with *)
(* 	Some typ -> Tactics.apply_term (mkCast (t, DEFAULTcast, typ)) [] *)
(*       | None -> Tactics.apply_term t (mkMetas (List.length evs)) *)
     
(* open Tacmach *)

let etermtac ot (*(evm, t)*) = assert(false) (*eterm evm t None *)
