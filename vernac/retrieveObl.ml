(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(**
   - Get types of existentials ;
   - Flatten dependency tree (prefix order) ;
   - Replace existentials by de Bruijn indices in term, applied to the right arguments ;
   - Apply term prefixed by quantification on "existentials".
*)

let check_evars env evm =
  Evar.Map.iter
    (fun key evi ->
      if Evd.is_obligation_evar evm key then ()
      else
        let loc, k = Evd.evar_source evi in
        Pretype_errors.error_unsolvable_implicit ?loc env evm key None)
    (Evd.undefined_map evm)

type obligation_info =
  ( Names.Id.t
  * Constr.types
  * Evar_kinds.t Loc.located
  * (bool * Evar_kinds.obligation_definition_status)
  * Int.Set.t
  * unit Proofview.tactic option )
  array

type oblinfo =
  { ev_name : int * Id.t
  ; ev_hyps : EConstr.named_context
  ; ev_status : bool * Evar_kinds.obligation_definition_status
  ; ev_chop : int option
  ; ev_src : Evar_kinds.t Loc.located
  ; ev_typ : Constr.types
  ; ev_tac : unit Proofview.tactic option
  ; ev_deps : Int.Set.t }

(** Substitute evar references in t using de Bruijn indices,
  where n binders were passed through. *)

let succfix (depth, fixrels) = (succ depth, List.map succ fixrels)

let subst_evar_constr evm evs n idf t =
  let seen = ref Int.Set.empty in
  let transparent = ref Id.Set.empty in
  let evar_info id = CList.assoc_f Evar.equal id evs in
  let rec substrec (depth, fixrels) c =
    match EConstr.kind evm c with
    | Constr.Evar (k, args) ->
      let {ev_name = id, idstr; ev_hyps = hyps; ev_chop = chop} =
        try evar_info k
        with Not_found ->
          CErrors.anomaly ~label:"eterm"
            Pp.(
              str "existential variable "
              ++ int (Evar.repr k)
              ++ str " not found.")
      in
      seen := Int.Set.add id !seen;
      (* Evar arguments are created in inverse order,
         and we must not apply to defined ones (i.e. LetIn's)
      *)
      let args =
        let args = Evd.expand_existential evm (k, args) in
        let n = match chop with None -> 0 | Some c -> c in
        let l, r = CList.chop n (List.rev args) in
        List.rev r
      in
      let args =
        let rec aux hyps args acc =
          let open Context.Named.Declaration in
          match (hyps, args) with
          | LocalAssum _ :: tlh, c :: tla ->
            aux tlh tla (substrec (depth, fixrels) c :: acc)
          | LocalDef _ :: tlh, _ :: tla -> aux tlh tla acc
          | [], [] -> acc
          | _, _ -> acc
          (*failwith "subst_evars: invalid argument"*)
        in
        aux hyps args []
      in
      if
        List.exists
          (fun x ->
            match EConstr.kind evm x with
            | Constr.Rel n -> Int.List.mem n fixrels
            | _ -> false)
          args
      then transparent := Id.Set.add idstr !transparent;
      EConstr.mkApp (idf idstr, Array.of_list args)
    | Constr.Fix _ ->
      EConstr.map_with_binders evm succfix substrec (depth, 1 :: fixrels) c
    | _ -> EConstr.map_with_binders evm succfix substrec (depth, fixrels) c
  in
  let t' = substrec (0, []) t in
  (EConstr.to_constr evm t', !seen, !transparent)

(** Substitute variable references in t using de Bruijn indices,
  where n binders were passed through. *)
let subst_vars acc n t =
  let var_index id = Util.List.index Id.equal id acc in
  let rec substrec depth c =
    match Constr.kind c with
    | Constr.Var v -> (
      try Constr.mkRel (depth + var_index v) with Not_found -> c )
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
    | decl :: tl -> (
      let t', s, trans =
        subst_evar_constr evm evs n EConstr.mkVar
          (Context.Named.Declaration.get_type decl)
      in
      let t'' = subst_vars acc 0 t' in
      let rest, s', trans' =
        aux (Context.Named.Declaration.get_id decl :: acc) (succ n) tl
      in
      let s' = Int.Set.union s s' in
      let trans' = Id.Set.union trans trans' in
      match decl with
      | LocalDef (id, c, _) ->
        let c', s'', trans'' = subst_evar_constr evm evs n EConstr.mkVar c in
        let c' = subst_vars acc 0 c' in
        ( Term.mkNamedProd_or_LetIn (LocalDef (EConstr.Unsafe.to_binder_annot id, c', t'')) rest
        , Int.Set.union s'' s'
        , Id.Set.union trans'' trans' )
      | LocalAssum (id, _) ->
        (Term.mkNamedProd_or_LetIn (LocalAssum (EConstr.Unsafe.to_binder_annot id, t'')) rest, s', trans') )
    | [] ->
      let t', s, trans = subst_evar_constr evm evs n EConstr.mkVar concl in
      (subst_vars acc 0 t', s, trans)
  in
  aux [] 0 (List.rev hyps)

let trunc_named_context n ctx =
  let len = List.length ctx in
  CList.firstn (len - n) ctx

let rec chop_product n t =
  let pop t = Vars.lift (-1) t in
  if Int.equal n 0 then Some t
  else
    match Constr.kind t with
    | Constr.Prod (_, _, b) ->
      if Vars.noccurn 1 b then chop_product (pred n) (pop b) else None
    | _ -> None

let evar_dependencies evm oev =
  let one_step deps =
    Evar.Set.fold
      (fun ev s ->
        let evi = Evd.find_undefined evm ev in
        let deps' = Evd.evars_of_filtered_evar_info evm evi in
        if Evar.Set.mem oev deps' then
          invalid_arg
            ( "Ill-formed evar map: cycle detected for evar "
            ^ Pp.string_of_ppcmds @@ Evar.print oev )
        else Evar.Set.union deps' s)
      deps deps
  in
  let rec aux deps =
    let deps' = one_step deps in
    if Evar.Set.equal deps deps' then deps else aux deps'
  in
  aux (Evar.Set.singleton oev)

let move_after ((id, ev, deps) as obl) l =
  let rec aux restdeps = function
    | ((id', _, _) as obl') :: tl ->
      let restdeps' = Evar.Set.remove id' restdeps in
      if Evar.Set.is_empty restdeps' then obl' :: obl :: tl
      else obl' :: aux restdeps' tl
    | [] -> [obl]
  in
  aux (Evar.Set.remove id deps) l

let sort_dependencies evl =
  let rec aux l found list =
    match l with
    | ((id, ev, deps) as obl) :: tl ->
      let found' = Evar.Set.union found (Evar.Set.singleton id) in
      if Evar.Set.subset deps found' then aux tl found' (obl :: list)
      else aux (move_after obl tl) found list
    | [] -> List.rev list
  in
  aux evl Evar.Set.empty []

type obligation_name_lifter =
  (Names.Id.t -> EConstr.t) -> EConstr.t -> Constr.t

let retrieve_obligations env name evm fs ?deps ?status t ty =
  (* 'Serialize' the evars *)
  let nc = Environ.named_context env in
  let nc_len = Context.Named.length nc in
  let evm = Evarutil.nf_evar_map_undefined evm in
  let evl = Evd.undefined_map evm in
  let evl = match deps with
  | None -> evl
  | Some deps -> Evar.Map.filter (fun ev _ -> Evar.Set.mem ev deps) evl
  in
  let evl = Evar.Map.bindings evl in
  let evl = List.map (fun (id, ev) -> (id, ev, evar_dependencies evm id)) evl in
  let sevl = sort_dependencies evl in
  let evl = List.map (fun (id, ev, _) -> (id, ev)) sevl in
  let evn =
    let i = ref (-1) in
    List.rev_map
      (fun (id, ev) ->
        incr i;
        ( id
        , ( !i
          , Id.of_string
              (Id.to_string name ^ "_obligation_" ^ string_of_int (succ !i)) )
        , ev ))
      evl
  in
  let evts =
    (* Remove existential variables in types and build the corresponding products *)
    List.fold_right
      (fun (id, (n, nstr), ev) evs ->
        let hyps = Evd.evar_filtered_context ev in
        let hyps = trunc_named_context nc_len hyps in
        let evtyp, deps, transp = etype_of_evar evm evs hyps (Evd.evar_concl ev) in
        let evtyp, hyps, chop =
          match chop_product fs evtyp with
          | Some t -> (t, trunc_named_context fs hyps, fs)
          | None -> (evtyp, hyps, 0)
        in
        let loc, k = Evd.evar_source (Evd.find_undefined evm id) in
        let status =
          match k with
          | Evar_kinds.QuestionMark {Evar_kinds.qm_obligation = o} -> o
          | _ -> (
            match status with
            | Some o -> o
            | None ->
              Evar_kinds.Define (not (Program.get_proofs_transparency ())) )
        in
        let force_status, status, chop =
          match status with
          | Evar_kinds.Define true as stat ->
            if not (Int.equal chop fs) then (true, Evar_kinds.Define false, None)
            else (false, stat, Some chop)
          | s -> (false, s, None)
        in
        let info =
          { ev_name = (n, nstr)
          ; ev_hyps = hyps
          ; ev_status = (force_status, status)
          ; ev_chop = chop
          ; ev_src = (loc, k)
          ; ev_typ = evtyp
          ; ev_deps = deps
          ; ev_tac = None }
        in
        (id, info) :: evs)
      evn []
  in
  let t', _, transparent =
    (* Substitute evar refs in the term by variables *)
    subst_evar_constr evm evts 0 EConstr.mkVar t
  in
  let ty, _, _ = subst_evar_constr evm evts 0 EConstr.mkVar ty in
  let evars =
    List.map
      (fun (ev, info) ->
        let { ev_name = _, name
            ; ev_status = force_status, status
            ; ev_src = src
            ; ev_typ = typ
            ; ev_deps = deps
            ; ev_tac = tac } =
          info
        in
        let force_status, status =
          match status with
          | Evar_kinds.Define true when Id.Set.mem name transparent ->
            (true, Evar_kinds.Define false)
          | _ -> (force_status, status)
        in
        (name, typ, src, (force_status, status), deps, tac))
      evts
  in
  let evnames = List.map (fun (ev, info) -> (ev, snd info.ev_name)) evts in
  let evmap f c = Util.pi1 (subst_evar_constr evm evts 0 f c) in
  (Array.of_list (List.rev evars), (evnames, evmap), t', ty)
