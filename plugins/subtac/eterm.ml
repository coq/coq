(**
   - Get types of existentials ;
   - Flatten dependency tree (prefix order) ;
   - Replace existentials by De Bruijn indices in term, applied to the right arguments ;
   - Apply term prefixed by quantification on "existentials".
*)

open Term
open Sign
open Names
open Evd
open List
open Pp
open Util
open Subtac_utils
open Proof_type

let trace s =
  if !Flags.debug then (msgnl s; msgerr s)
  else ()

let succfix (depth, fixrels) =
  (succ depth, List.map succ fixrels)

type oblinfo =
  { ev_name: int * identifier;
    ev_hyps: named_context;
    ev_status: obligation_definition_status;
    ev_chop: int option;
    ev_src: hole_kind located;
    ev_typ: types;
    ev_tac: tactic option;
    ev_deps: Intset.t }

(* spiwack: Store field for internalizing ev_tac in evar_infos' evar_extra. *)
open Store.Field
let evar_tactic = Store.field ()

(** Substitute evar references in t using De Bruijn indices,
  where n binders were passed through. *)

let subst_evar_constr evs n idf t = 
  let seen = ref Intset.empty in
  let transparent = ref Idset.empty in
  let evar_info id = List.assoc id evs in
  let rec substrec (depth, fixrels) c = match kind_of_term c with
    | Evar (k, args) ->
	let { ev_name = (id, idstr) ;
	      ev_hyps = hyps ; ev_chop = chop } =
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
		   aux tlh tla ((substrec (depth, fixrels) c) :: acc)
	       | ((_, Some _, _) :: tlh), (_ :: tla) ->
		   aux tlh tla acc
	       | [], [] -> acc
	       | _, _ -> acc (*failwith "subst_evars: invalid argument"*)
	  in aux hyps args []
	in
	  if List.exists (fun x -> match kind_of_term x with Rel n -> List.mem n fixrels | _ -> false) args then
	    transparent := Idset.add idstr !transparent;
	  mkApp (idf idstr, Array.of_list args)
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
*)
let etype_of_evar evs hyps concl =
  let rec aux acc n = function
      (id, copt, t) :: tl ->
	let t', s, trans = subst_evar_constr evs n mkVar t in
	let t'' = subst_vars acc 0 t' in
	let rest, s', trans' = aux (id :: acc) (succ n) tl in
	let s' = Intset.union s s' in
	let trans' = Idset.union trans trans' in
	  (match copt with
	      Some c -> 
		let c', s'', trans'' = subst_evar_constr evs n mkVar c in
		let c' = subst_vars acc 0 c' in
		  mkNamedProd_or_LetIn (id, Some c', t'') rest,
		Intset.union s'' s',
		Idset.union trans'' trans'
	    | None ->
		mkNamedProd_or_LetIn (id, None, t'') rest, s', trans')
    | [] ->
	let t', s, trans = subst_evar_constr evs n mkVar concl in
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

let evar_dependencies evm ev =
  let one_step deps =
    Intset.fold (fun ev s ->
      let evi = Evd.find evm ev in
	Intset.union (Evarutil.evars_of_evar_info evi) s)
      deps deps
  in
  let rec aux deps =
    let deps' = one_step deps in
      if Intset.equal deps deps' then deps
      else aux deps'
  in aux (Intset.singleton ev)
      
let move_after (id, ev, deps as obl) l = 
  let rec aux restdeps = function
    | (id', _, _) as obl' :: tl -> 
	let restdeps' = Intset.remove id' restdeps in
	  if Intset.is_empty restdeps' then
	    obl' :: obl :: tl
	  else obl' :: aux restdeps' tl
    | [] -> [obl]
  in aux (Intset.remove id deps) l
    
let sort_dependencies evl =
  let rec aux l found list =
    match l with
    | (id, ev, deps) as obl :: tl ->
	let found' = Intset.union found (Intset.singleton id) in
	  if Intset.subset deps found' then
	    aux tl found' (obl :: list)
	  else aux (move_after obl tl) found list
    | [] -> List.rev list
  in aux evl Intset.empty []

let map_evar_body f = function
  | Evar_empty -> Evar_empty
  | Evar_defined c -> Evar_defined (f c)

open Environ
      
let map_evar_info f evi =
  { evi with evar_hyps = val_of_named_context (map_named_context f (named_context_of_val evi.evar_hyps));
    evar_concl = f evi.evar_concl;
    evar_body = map_evar_body f evi.evar_body }
    
let eterm_obligations env name isevars evm fs ?status t ty = 
  (* 'Serialize' the evars *)
  let nc = Environ.named_context env in
  let nc_len = Sign.named_context_length nc in
  let evl = List.rev (to_list evm) in
  let evl = List.map (fun (id, ev) -> (id, ev, evar_dependencies evm id)) evl in
  let sevl = sort_dependencies evl in
  let evl = List.map (fun (id, ev, _) -> id, ev) sevl in
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
	 let hyps = Evd.evar_filtered_context ev in
	 let hyps = trunc_named_context nc_len hyps in
	 let evtyp, deps, transp = etype_of_evar l hyps ev.evar_concl in
	 let evtyp, hyps, chop =
	   match chop_product fs evtyp with
	   | Some t -> t, trunc_named_context fs hyps, fs
	   | None -> evtyp, hyps, 0
	 in
	 let loc, k = evar_source id isevars in
	 let status = match k with QuestionMark o -> Some o | _ -> status in
	 let status, chop = match status with
	   | Some (Define true as stat) ->
	       if chop <> fs then Define false, None
	       else stat, Some chop
	   | Some s -> s, None
	   | None -> Define true, None
	 in
	 let tac = match evar_tactic.get ev.evar_extra with
	   | Some t ->
	       if Dyn.tag t = "tactic" then
		 Some (Tacinterp.interp 
			  (Tacinterp.globTacticIn (Tacinterp.tactic_out t)))
	       else None
	   | None -> None
	 in
	 let info = { ev_name = (n, nstr);
		      ev_hyps = hyps; ev_status = status; ev_chop = chop;
		      ev_src = loc, k; ev_typ = evtyp ; ev_deps = deps; ev_tac = tac }
	 in (id, info) :: l)
      evn []
  in
  let t', _, transparent = (* Substitute evar refs in the term by variables *)
    subst_evar_constr evts 0 mkVar t 
  in
  let ty, _, _ = subst_evar_constr evts 0 mkVar ty in
  let evars = 
    List.map (fun (ev, info) ->
      let { ev_name = (_, name); ev_status = status;
	    ev_src = src; ev_typ = typ; ev_deps = deps; ev_tac = tac } = info
      in
      let status = match status with
	| Define true when Idset.mem name transparent -> Define false
	| _ -> status
      in name, typ, src, status, deps, tac) evts
  in
  let evnames = List.map (fun (ev, info) -> ev, snd info.ev_name) evts in
  let evmap f c = pi1 (subst_evar_constr evts 0 f c) in
    Array.of_list (List.rev evars), (evnames, evmap), t', ty

let mkMetas n = list_tabulate (fun _ -> Evarutil.mk_new_meta ()) n
