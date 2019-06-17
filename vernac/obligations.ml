(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Printf
open Decl_kinds

(**
   - Get types of existentials ;
   - Flatten dependency tree (prefix order) ;
   - Replace existentials by de Bruijn indices in term, applied to the right arguments ;
   - Apply term prefixed by quantification on "existentials".
*)

open Term
open Constr
open Vars
open Names
open Evd
open Pp
open CErrors
open Util

module NamedDecl = Context.Named.Declaration

open DeclareObl

let succfix (depth, fixrels) =
  (succ depth, List.map succ fixrels)

let check_evars env evm =
  Evar.Map.iter
    (fun key evi ->
       if Evd.is_obligation_evar evm key then ()
       else
         let (loc,k) = evar_source key evm in
         Pretype_errors.error_unsolvable_implicit ?loc env evm key None)
  (Evd.undefined_map evm)

type oblinfo =
  { ev_name: int * Id.t;
    ev_hyps: EConstr.named_context;
    ev_status: bool * Evar_kinds.obligation_definition_status;
    ev_chop: int option;
    ev_src: Evar_kinds.t Loc.located;
    ev_typ: types;
    ev_tac: unit Proofview.tactic option;
    ev_deps: Int.Set.t }

(** Substitute evar references in t using de Bruijn indices,
  where n binders were passed through. *)

let subst_evar_constr evm evs n idf t =
  let seen = ref Int.Set.empty in
  let transparent = ref Id.Set.empty in
  let evar_info id = List.assoc_f Evar.equal id evs in
  let rec substrec (depth, fixrels) c = match EConstr.kind evm c with
    | Evar (k, args) ->
	let { ev_name = (id, idstr) ;
	      ev_hyps = hyps ; ev_chop = chop } =
	  try evar_info k
	  with Not_found ->
	    anomaly ~label:"eterm" (Pp.str "existential variable " ++ int (Evar.repr k) ++ str " not found.")
	in
        seen := Int.Set.add id !seen;
	  (* Evar arguments are created in inverse order,
	     and we must not apply to defined ones (i.e. LetIn's)
	  *)
	let args =
	  let n = match chop with None -> 0 | Some c -> c in
	  let (l, r) = List.chop n (List.rev (Array.to_list args)) in
	    List.rev r
	in
	let args =
	  let rec aux hyps args acc =
             let open Context.Named.Declaration in
	     match hyps, args with
		 (LocalAssum _ :: tlh), (c :: tla) ->
		   aux tlh tla ((substrec (depth, fixrels) c) :: acc)
	       | (LocalDef _ :: tlh), (_ :: tla) ->
		   aux tlh tla acc
	       | [], [] -> acc
	       | _, _ -> acc (*failwith "subst_evars: invalid argument"*)
	  in aux hyps args []
	in
	  if List.exists
            (fun x -> match EConstr.kind evm x with
            | Rel n -> Int.List.mem n fixrels
            | _ -> false) args
          then
	    transparent := Id.Set.add idstr !transparent;
          EConstr.mkApp (idf idstr, Array.of_list args)
    | Fix _ ->
        EConstr.map_with_binders evm succfix substrec (depth, 1 :: fixrels) c
    | _ -> EConstr.map_with_binders evm succfix substrec (depth, fixrels) c
  in
  let t' = substrec (0, []) t in
    EConstr.to_constr evm t', !seen, !transparent


(** Substitute variable references in t using de Bruijn indices,
  where n binders were passed through. *)
let subst_vars acc n t =
  let var_index id = Util.List.index Id.equal id acc in
  let rec substrec depth c = match Constr.kind c with
    | Var v -> (try mkRel (depth + (var_index v)) with Not_found -> c)
    | _ -> Constr.map_with_binders succ substrec depth c
  in
    substrec 0 t

(** Rewrite type of an evar ([ H1 : t1, ... Hn : tn |- concl ])
    to a product : forall H1 : t1, ..., forall Hn : tn, concl.
    Changes evars and hypothesis references to variable references.
*)
let etype_of_evar evm evs hyps concl =
  let open Context.Named.Declaration in
  let rec aux acc n = function
      decl :: tl ->
        let t', s, trans = subst_evar_constr evm evs n EConstr.mkVar (NamedDecl.get_type decl) in
	let t'' = subst_vars acc 0 t' in
	let rest, s', trans' = aux (NamedDecl.get_id decl :: acc) (succ n) tl in
	let s' = Int.Set.union s s' in
	let trans' = Id.Set.union trans trans' in
	  (match decl with
            | LocalDef (id,c,_) ->
                let c', s'', trans'' = subst_evar_constr evm evs n EConstr.mkVar c in
		let c' = subst_vars acc 0 c' in
                  mkNamedProd_or_LetIn (LocalDef (id, c', t'')) rest,
		Int.Set.union s'' s',
		Id.Set.union trans'' trans'
            | LocalAssum (id,_) ->
                mkNamedProd_or_LetIn (LocalAssum (id, t'')) rest, s', trans')
    | [] ->
        let t', s, trans = subst_evar_constr evm evs n EConstr.mkVar concl in
	  subst_vars acc 0 t', s, trans
  in aux [] 0 (List.rev hyps)

let trunc_named_context n ctx =
  let len = List.length ctx in
    List.firstn (len - n) ctx

let rec chop_product n t =
  let pop t = Vars.lift (-1) t in
  if Int.equal n 0 then Some t
  else
    match Constr.kind t with
      | Prod (_, _, b) ->  if noccurn 1 b then chop_product (pred n) (pop b) else None
      | _ -> None

let evar_dependencies evm oev =
  let one_step deps =
    Evar.Set.fold (fun ev s ->
      let evi = Evd.find evm ev in
      let deps' = evars_of_filtered_evar_info evm evi in
      if Evar.Set.mem oev deps' then
        invalid_arg ("Ill-formed evar map: cycle detected for evar " ^ Pp.string_of_ppcmds @@ Evar.print oev)
      else Evar.Set.union deps' s)
      deps deps
  in
  let rec aux deps =
    let deps' = one_step deps in
      if Evar.Set.equal deps deps' then deps
      else aux deps'
  in aux (Evar.Set.singleton oev)

let move_after (id, ev, deps as obl) l =
  let rec aux restdeps = function
    | (id', _, _) as obl' :: tl ->
	let restdeps' = Evar.Set.remove id' restdeps in
	  if Evar.Set.is_empty restdeps' then
	    obl' :: obl :: tl
	  else obl' :: aux restdeps' tl
    | [] -> [obl]
  in aux (Evar.Set.remove id deps) l

let sort_dependencies evl =
  let rec aux l found list =
    match l with
    | (id, ev, deps) as obl :: tl ->
	let found' = Evar.Set.union found (Evar.Set.singleton id) in
	  if Evar.Set.subset deps found' then
	    aux tl found' (obl :: list)
	  else aux (move_after obl tl) found list
    | [] -> List.rev list
  in aux evl Evar.Set.empty []

open Environ

let eterm_obligations env name evm fs ?status t ty =
  (* 'Serialize' the evars *)
  let nc = Environ.named_context env in
  let nc_len = Context.Named.length nc in
  let evm = Evarutil.nf_evar_map_undefined evm in
  let evl = Evarutil.non_instantiated evm in
  let evl = Evar.Map.bindings evl in
  let evl = List.map (fun (id, ev) -> (id, ev, evar_dependencies evm id)) evl in
  let sevl = sort_dependencies evl in
  let evl = List.map (fun (id, ev, _) -> id, ev) sevl in
  let evn =
    let i = ref (-1) in
      List.rev_map (fun (id, ev) -> incr i;
		      (id, (!i, Id.of_string
			      (Id.to_string name ^ "_obligation_" ^ string_of_int (succ !i))),
		       ev)) evl
  in
  let evts =
    (* Remove existential variables in types and build the corresponding products *)
    List.fold_right
      (fun (id, (n, nstr), ev) l ->
	 let hyps = Evd.evar_filtered_context ev in
         let hyps = trunc_named_context nc_len hyps in
         let evtyp, deps, transp = etype_of_evar evm l hyps ev.evar_concl in
	 let evtyp, hyps, chop =
	   match chop_product fs evtyp with
	   | Some t -> t, trunc_named_context fs hyps, fs
	   | None -> evtyp, hyps, 0
	 in
	 let loc, k = evar_source id evm in
	 let status = match k with
           | Evar_kinds.QuestionMark { Evar_kinds.qm_obligation=o } -> o
           | _ -> match status with
                 | Some o -> o
                 | None -> Evar_kinds.Define (not (Program.get_proofs_transparency ()))
         in
         let force_status, status, chop = match status with
	   | Evar_kinds.Define true as stat ->
	      if not (Int.equal chop fs) then true, Evar_kinds.Define false, None
	      else false, stat, Some chop
	   | s -> false, s, None
	 in
	 let info = { ev_name = (n, nstr);
		      ev_hyps = hyps; ev_status = force_status, status; ev_chop = chop;
		      ev_src = loc, k; ev_typ = evtyp ; ev_deps = deps; ev_tac = None }
	 in (id, info) :: l)
      evn []
  in
  let t', _, transparent = (* Substitute evar refs in the term by variables *)
    subst_evar_constr evm evts 0 EConstr.mkVar t
  in
  let ty, _, _ = subst_evar_constr evm evts 0 EConstr.mkVar ty in
  let evars = 
    List.map (fun (ev, info) ->
      let { ev_name = (_, name); ev_status = force_status, status;
	    ev_src = src; ev_typ = typ; ev_deps = deps; ev_tac = tac } = info
      in
      let force_status, status = match status with
	| Evar_kinds.Define true when Id.Set.mem name transparent ->
	  true, Evar_kinds.Define false
	| _ -> force_status, status
      in name, typ, src, (force_status, status), deps, tac) evts
  in
  let evnames = List.map (fun (ev, info) -> ev, snd info.ev_name) evts in
  let evmap f c = pi1 (subst_evar_constr evm evts 0 f c) in
    Array.of_list (List.rev evars), (evnames, evmap), t', ty

let pperror cmd = CErrors.user_err ~hdr:"Program" cmd
let error s = pperror (str s)

let reduce c =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  EConstr.Unsafe.to_constr (Reductionops.clos_norm_flags CClosure.betaiota env sigma (EConstr.of_constr c))

exception NoObligations of Id.t option

let explain_no_obligations = function
    Some ident -> str "No obligations for program " ++ Id.print ident
  | None -> str "No obligations remaining"

type obligation_info =
    (Names.Id.t * types * Evar_kinds.t Loc.located *
       (bool * Evar_kinds.obligation_definition_status)
       * Int.Set.t * unit Proofview.tactic option) array

let assumption_message = Declare.assumption_message

let default_tactic = ref (Proofview.tclUNIT ())

let evar_of_obligation o = make_evar (Global.named_context_val ()) (EConstr.of_constr o.obl_type)

let subst_deps expand obls deps t =
  let osubst = obl_substitution expand obls deps in
    (Vars.replace_vars (List.map (fun (n, (_, b)) -> n, b) osubst) t)

let subst_deps_obl obls obl =
  let t' = subst_deps true obls obl.obl_deps obl.obl_type in
    { obl with obl_type = t' }

open Evd

let unfold_entry cst = Hints.HintsUnfoldEntry [EvalConstRef cst]

let add_hint local prg cst =
  Hints.add_hints ~local [Id.to_string prg.prg_name] (unfold_entry cst)

let init_prog_info ?(opaque = false) ?hook sign n udecl b t ctx deps fixkind
                   notations obls impls ~scope ~poly ~kind reduce =
  let obls', b =
    match b with
    | None ->
	assert(Int.equal (Array.length obls) 0);
	let n = Nameops.add_suffix n "_obligation" in
	  [| { obl_name = n; obl_body = None;
	       obl_location = Loc.tag Evar_kinds.InternalHole; obl_type = t;
	       obl_status = false, Evar_kinds.Expand; obl_deps = Int.Set.empty;
	       obl_tac = None } |],
	mkVar n
    | Some b ->
	Array.mapi
	  (fun i (n, t, l, o, d, tac) ->
            { obl_name = n ; obl_body = None;
	      obl_location = l; obl_type = t; obl_status = o;
	      obl_deps = d; obl_tac = tac })
	  obls, b
  in
  let ctx = UState.make_flexible_nonalgebraic ctx in
    { prg_name = n
    ; prg_body = b
    ; prg_type = reduce t
    ; prg_ctx = ctx
    ; prg_univdecl = udecl
    ; prg_obligations = (obls', Array.length obls')
    ; prg_deps = deps
    ; prg_fixkind = fixkind
    ; prg_notations = notations
    ; prg_implicits = impls
    ; prg_poly = poly
    ; prg_scope = scope
    ; prg_kind = kind
    ; prg_reduce = reduce
    ; prg_hook = hook
    ; prg_opaque = opaque
    ; prg_sign = sign }

let map_cardinal m =
  let i = ref 0 in
  ProgMap.iter (fun _ v ->
      if snd (CEphemeron.get v).prg_obligations > 0 then incr i) m;
  !i

exception Found of program_info CEphemeron.key

let map_first m =
  try
    ProgMap.iter (fun _ v ->
		  if snd (CEphemeron.get v).prg_obligations > 0 then
		    raise (Found v)) m;
    assert(false)
  with Found x -> x

let get_prog name =
  let prg_infos = get_prg_info_map () in
    match name with
	Some n ->
          (try CEphemeron.get (ProgMap.find n prg_infos)
	   with Not_found -> raise (NoObligations (Some n)))
      | None ->
	  (let n = map_cardinal prg_infos in
	     match n with
		 0 -> raise (NoObligations None)
               | 1 -> CEphemeron.get (map_first prg_infos)
	       | _ ->
                let progs = Id.Set.elements (ProgMap.domain prg_infos) in
                let prog = List.hd progs in
                let progs = prlist_with_sep pr_comma Id.print progs in
                user_err
                  (str "More than one program with unsolved obligations: " ++ progs
                  ++ str "; use the \"of\" clause to specify, as in \"Obligation 1 of " ++ Id.print prog ++ str "\""))

let get_any_prog () =
  let prg_infos = get_prg_info_map () in
  let n = map_cardinal prg_infos in
  if n > 0 then CEphemeron.get (map_first prg_infos)
  else raise (NoObligations None)

let get_prog_err n =
  try get_prog n with NoObligations id -> pperror (explain_no_obligations id)

let get_any_prog_err () =
  try get_any_prog () with NoObligations id -> pperror (explain_no_obligations id)

let all_programs () =
  ProgMap.fold (fun k p l -> p :: l) (get_prg_info_map ()) []

let is_defined obls x = not (Option.is_empty obls.(x).obl_body)

let deps_remaining obls deps =
  Int.Set.fold
    (fun x acc ->
      if is_defined obls x then acc
      else x :: acc)
    deps []


let goal_kind = DeclareDef.(Global Declare.ImportNeedQualified, DefinitionBody Definition)
let goal_proof_kind = DeclareDef.(Global Declare.ImportNeedQualified, Proof Lemma)

let kind_of_obligation o =
  match o with
  | Evar_kinds.Define false
  | Evar_kinds.Expand -> goal_kind
  | _ -> goal_proof_kind

let rec string_of_list sep f = function
    [] -> ""
  | x :: [] -> f x
  | x :: ((y :: _) as tl) -> f x ^ sep ^ string_of_list sep f tl

(* Solve an obligation using tactics, return the corresponding proof term *)
let warn_solve_errored = CWarnings.create ~name:"solve_obligation_error" ~category:"tactics" (fun err ->
    Pp.seq [str "Solve Obligations tactic returned error: "; err; fnl ();
            str "This will become an error in the future"])

let solve_by_tac ?loc name evi t poly ctx =
  (* spiwack: the status is dropped. *)
  try
    let (entry,_,ctx') =
      Pfedit.build_constant_by_tactic
        ~name ~poly ctx evi.evar_hyps evi.evar_concl t in
    let env = Global.env () in
    let (body, eff) = Future.force entry.Proof_global.proof_entry_body in
    let body = Safe_typing.inline_private_constants env (body, eff.Evd.seff_private) in
    let ctx' = Evd.merge_context_set ~sideff:true Evd.univ_rigid (Evd.from_ctx ctx') (snd body) in
    Inductiveops.control_only_guard env ctx' (EConstr.of_constr (fst body));
    Some (fst body, entry.Proof_global.proof_entry_type, Evd.evar_universe_context ctx')
  with
  | Refiner.FailError (_, s) as exn ->
    let _ = CErrors.push exn in
    user_err ?loc ~hdr:"solve_obligation" (Lazy.force s)
  (* If the proof is open we absorb the error and leave the obligation open *)
  | Proof.OpenProof _ ->
    None
  | e when CErrors.noncritical e ->
    let err = CErrors.print e in
    warn_solve_errored ?loc err;
    None

let obligation_hook prg obl num auto { DeclareDef.Hook.S.uctx = ctx'; dref; _ } =
  let obls, rem = prg.prg_obligations in
  let cst = match dref with GlobRef.ConstRef cst -> cst | _ -> assert false in
  let transparent = evaluable_constant cst (Global.env ()) in
  let () = match obl.obl_status with
      (true, Evar_kinds.Expand)
    | (true, Evar_kinds.Define true) ->
       if not transparent then err_not_transp ()
    | _ -> ()
  in
  let inst, ctx' =
    if not prg.prg_poly (* Not polymorphic *) then
      (* The universe context was declared globally, we continue
         from the new global environment. *)
      let ctx = UState.make (Global.universes ()) in
      let ctx' = UState.merge_subst ctx (UState.subst ctx') in
      Univ.Instance.empty, ctx'
    else
      (* We get the right order somehow, but surely it could be enforced in a clearer way. *)
      let uctx = UState.context ctx' in
      Univ.UContext.instance uctx, ctx'
  in
  let obl = { obl with obl_body = Some (DefinedObl (cst, inst)) } in
  let () = if transparent then add_hint true prg cst in
  let obls = Array.copy obls in
  let () = obls.(num) <- obl in
  let prg = { prg with prg_ctx = ctx' } in
  let () =
    try ignore (update_obls prg obls (pred rem))
    with e when CErrors.noncritical e ->
      let e = CErrors.push e in
      pperror (CErrors.iprint (ExplainErr.process_vernac_interp_error e))
  in
  if pred rem > 0 then begin
    let deps = dependencies obls num in
    if not (Int.Set.is_empty deps) then
      ignore (auto (Some prg.prg_name) deps None)
  end

let rec solve_obligation prg num tac =
  let user_num = succ num in
  let obls, rem = prg.prg_obligations in
  let obl = obls.(num) in
  let remaining = deps_remaining obls obl.obl_deps in
  let () =
    if not (Option.is_empty obl.obl_body) then
      pperror (str "Obligation" ++ spc () ++ int user_num ++ str "already" ++ spc() ++ str "solved.");
    if not (List.is_empty remaining) then
      pperror (str "Obligation " ++ int user_num ++ str " depends on obligation(s) "
        ++ str (string_of_list ", " (fun x -> string_of_int (succ x)) remaining));
  in
  let obl = subst_deps_obl obls obl in
  let scope, kind = kind_of_obligation (snd obl.obl_status) in
  let evd = Evd.from_ctx prg.prg_ctx in
  let evd = Evd.update_sigma_env evd (Global.env ()) in
  let auto n oblset tac = auto_solve_obligations n ~oblset tac in
  let proof_ending = Lemmas.Proof_ending.End_obligation (DeclareObl.{name = prg.prg_name; num; auto}) in
  let hook = DeclareDef.Hook.make (obligation_hook prg obl num auto) in
  let info = Lemmas.Info.make ~hook ~proof_ending ~scope ~kind () in
  let poly = prg.prg_poly in
  let lemma = Lemmas.start_lemma ~sign:prg.prg_sign ~name:obl.obl_name ~poly ~info evd (EConstr.of_constr obl.obl_type) in
  let lemma = fst @@ Lemmas.by !default_tactic lemma in
  let lemma = Option.cata (fun tac -> Lemmas.set_endline_tactic tac lemma) lemma tac in
  lemma

and obligation (user_num, name, typ) tac =
  let num = pred user_num in
  let prg = get_prog_err name in
  let obls, rem = prg.prg_obligations in
    if num >= 0 && num < Array.length obls then
      let obl = obls.(num) in
	match obl.obl_body with
          | None -> solve_obligation prg num tac
	  | Some r -> error "Obligation already solved"
    else error (sprintf "Unknown obligation number %i" (succ num))


and solve_obligation_by_tac prg obls i tac =
  let obl = obls.(i) in
    match obl.obl_body with
    | Some _ -> None
    | None ->
      if List.is_empty (deps_remaining obls obl.obl_deps) then
        let obl = subst_deps_obl obls obl in
        let tac =
          match tac with
          | Some t -> t
          | None ->
            match obl.obl_tac with
            | Some t -> t
            | None -> !default_tactic
        in
        let evd = Evd.from_ctx prg.prg_ctx in
        let evd = Evd.update_sigma_env evd (Global.env ()) in
        match solve_by_tac ?loc:(fst obl.obl_location) obl.obl_name (evar_of_obligation obl) tac
                prg.prg_poly (Evd.evar_universe_context evd) with
        | None -> None
        | Some (t, ty, ctx) ->
          let uctx = UState.univ_entry ~poly:prg.prg_poly ctx in
          let prg = {prg with prg_ctx = ctx} in
          let def, obl' = declare_obligation prg obl t ty uctx in
          obls.(i) <- obl';
          if def && not prg.prg_poly then (
            (* Declare the term constraints with the first obligation only *)
            let evd = Evd.from_env (Global.env ()) in
            let evd = Evd.merge_universe_subst evd (Evd.universe_subst (Evd.from_ctx ctx)) in
            let ctx' = Evd.evar_universe_context evd in
            Some {prg with prg_ctx = ctx'})
          else Some prg
      else None

and solve_prg_obligations prg ?oblset tac =
  let obls, rem = prg.prg_obligations in
  let rem = ref rem in
  let obls' = Array.copy obls in
  let set = ref Int.Set.empty in
  let p = match oblset with
    | None -> (fun _ -> true)
    | Some s -> set := s;
      (fun i -> Int.Set.mem i !set)
  in
  let prgref = ref prg in
  let () =
    Array.iteri (fun i x ->
      if p i then
        match solve_obligation_by_tac !prgref obls' i tac with
	| None -> ()
 	| Some prg' ->
	   prgref := prg';
	   let deps = dependencies obls i in
 	   (set := Int.Set.union !set deps;
 	    decr rem))
      obls'
  in
    update_obls !prgref obls' !rem

and solve_obligations n tac =
  let prg = get_prog_err n in
    solve_prg_obligations prg tac

and solve_all_obligations tac =
  ProgMap.iter (fun k v -> ignore(solve_prg_obligations (CEphemeron.get v) tac)) (get_prg_info_map ())

and try_solve_obligation n prg tac =
  let prg = get_prog prg in
  let obls, rem = prg.prg_obligations in
  let obls' = Array.copy obls in
    match solve_obligation_by_tac prg obls' n tac with
    | Some prg' -> ignore(update_obls prg' obls' (pred rem))
    | None -> ()

and try_solve_obligations n tac =
  try ignore (solve_obligations n tac) with NoObligations _ -> ()

and auto_solve_obligations n ?oblset tac : progress =
  Flags.if_verbose Feedback.msg_info (str "Solving obligations automatically...");
  try solve_prg_obligations (get_prog_err n) ?oblset tac with NoObligations _ -> Dependent

open Pp
let show_obligations_of_prg ?(msg=true) prg =
  let n = prg.prg_name in
  let obls, rem = prg.prg_obligations in
  let showed = ref 5 in
    if msg then Feedback.msg_info (int rem ++ str " obligation(s) remaining: ");
    Array.iteri (fun i x ->
		   match x.obl_body with
		   | None ->
		       if !showed > 0 then (
		         decr showed;
			 let x = subst_deps_obl obls x in
                         let env = Global.env () in
                         let sigma = Evd.from_env env in
			 Feedback.msg_info (str "Obligation" ++ spc() ++ int (succ i) ++ spc () ++
				   str "of" ++ spc() ++ Id.print n ++ str ":" ++ spc () ++
                                   hov 1 (Printer.pr_constr_env env sigma x.obl_type ++
					    str "." ++ fnl ())))
		   | Some _ -> ())
      obls

let show_obligations ?(msg=true) n =
  let progs = match n with
    | None -> all_programs ()
    | Some n ->
        try [ProgMap.find n (get_prg_info_map ())]
	with Not_found -> raise (NoObligations (Some n))
  in List.iter (fun x -> show_obligations_of_prg ~msg (CEphemeron.get x)) progs

let show_term n =
  let prg = get_prog_err n in
  let n = prg.prg_name in
  let env = Global.env () in
  let sigma = Evd.from_env env in
    (Id.print n ++ spc () ++ str":" ++ spc () ++
             Printer.pr_constr_env env sigma prg.prg_type ++ spc () ++ str ":=" ++ fnl ()
            ++ Printer.pr_constr_env env sigma prg.prg_body)

let add_definition ~name ?term t ctx ?(univdecl=UState.default_univ_decl)
                   ?(implicits=[]) ~poly ?(scope=DeclareDef.Global Declare.ImportDefaultBehavior) ?(kind=Definition) ?tactic
    ?(reduce=reduce) ?hook ?(opaque = false) obls =
  let sign = Lemmas.initialize_named_context_for_proof () in
  let info = Id.print name ++ str " has type-checked" in
  let prg = init_prog_info sign ~opaque name univdecl term t ctx [] None [] obls implicits ~poly ~scope ~kind reduce ?hook in
  let obls,_ = prg.prg_obligations in
  if Int.equal (Array.length obls) 0 then (
    Flags.if_verbose Feedback.msg_info (info ++ str ".");
    let cst = DeclareObl.declare_definition prg in
    Defined cst)
  else (
    let len = Array.length obls in
    let () = Flags.if_verbose Feedback.msg_info (info ++ str ", generating " ++ int len ++ str (String.plural len " obligation")) in
      progmap_add name (CEphemeron.create prg);
      let res = auto_solve_obligations (Some name) tactic in
	match res with
        | Remain rem -> Flags.if_verbose (fun () -> show_obligations ~msg:false (Some name)) (); res
	| _ -> res)

let add_mutual_definitions l ctx ?(univdecl=UState.default_univ_decl) ?tactic
                           ~poly ?(scope=DeclareDef.Global Declare.ImportDefaultBehavior) ?(kind=Definition) ?(reduce=reduce)
    ?hook ?(opaque = false) notations fixkind =
  let sign = Lemmas.initialize_named_context_for_proof () in
  let deps = List.map (fun (n, b, t, imps, obls) -> n) l in
    List.iter
    (fun  (n, b, t, imps, obls) ->
     let prg = init_prog_info sign ~opaque n univdecl (Some b) t ctx deps (Some fixkind)
       notations obls imps ~poly ~scope ~kind reduce ?hook
     in progmap_add n (CEphemeron.create prg)) l;
    let _defined =
      List.fold_left (fun finished x ->
	if finished then finished
	else
	  let res = auto_solve_obligations (Some x) tactic in
	    match res with
            | Defined _ ->
                (* If one definition is turned into a constant,
		   the whole block is defined. *) true
	    | _ -> false)
	false deps
    in ()

let admit_prog prg =
  let obls, rem = prg.prg_obligations in
  let obls = Array.copy obls in
    Array.iteri
      (fun i x ->
        match x.obl_body with
        | None ->
            let x = subst_deps_obl obls x in
            let ctx = UState.univ_entry ~poly:false prg.prg_ctx in
            let kn = Declare.declare_constant x.obl_name ~local:Declare.ImportNeedQualified
              (Declare.ParameterEntry (None,(x.obl_type,ctx),None), IsAssumption Conjectural)
            in
              assumption_message x.obl_name;
              obls.(i) <- { x with obl_body = Some (DefinedObl (kn, Univ.Instance.empty)) }
        | Some _ -> ())
      obls;
    ignore(update_obls prg obls 0)

let rec admit_all_obligations () =
  let prg = try Some (get_any_prog ()) with NoObligations _ -> None in
  match prg with
  | None -> ()
  | Some prg ->
    admit_prog prg;
    admit_all_obligations ()

let admit_obligations n =
  match n with
  | None -> admit_all_obligations ()
  | Some _ ->
    let prg = get_prog_err n in
    admit_prog prg

let next_obligation n tac =
  let prg = match n with
  | None -> get_any_prog_err ()
  | Some _ -> get_prog_err n
  in
  let obls, rem = prg.prg_obligations in
  let is_open _ x = Option.is_empty x.obl_body && List.is_empty (deps_remaining obls x.obl_deps) in
  let i = match Array.findi is_open obls with
  | Some i -> i
  | None -> anomaly (Pp.str "Could not find a solvable obligation.")
  in
  solve_obligation prg i tac

let check_program_libraries () =
  Coqlib.check_required_library Coqlib.datatypes_module_name;
  Coqlib.check_required_library ["Coq";"Init";"Specif"];
  Coqlib.check_required_library ["Coq";"Program";"Tactics"]
