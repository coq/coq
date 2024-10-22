(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Glob_term
open CErrors
open Util
open Names

(*
   Some basic functions to rebuild glob_constr
   In each of them the location is Loc.ghost
*)
let mkGRef ref = DAst.make @@ GRef (ref, None)
let mkGVar id = DAst.make @@ GVar id
let mkGApp (rt, rtl) = DAst.make @@ GApp (rt, rtl)
let mkGLambda (n, t, b) = DAst.make @@ GLambda (n, None, Explicit, t, b)
let mkGProd (n, t, b) = DAst.make @@ GProd (n, None, Explicit, t, b)
let mkGLetIn (n, b, t, c) = DAst.make @@ GLetIn (n, None, b, t, c)
let mkGCases (rto, l, brl) = DAst.make @@ GCases (RegularStyle, rto, l, brl)

let mkGHole () =
  DAst.make
  @@ GHole (GBinderType Anonymous)

(*
  Some basic functions to decompose glob_constrs
  These are analogous to the ones constrs
*)
let glob_decompose_app =
  let rec decompose_rapp acc rt =
    (*     msgnl (str "glob_decompose_app on : "++ Printer.pr_glob_constr rt); *)
    match DAst.get rt with
    | GApp (rt, rtl) ->
      decompose_rapp (List.fold_left (fun y x -> x :: y) acc rtl) rt
    | _ -> (rt, List.rev acc)
  in
  decompose_rapp []

(* [glob_make_eq t1 t2] build the glob_constr corresponding to [t2 = t1] *)
let glob_make_eq ?(typ = mkGHole ()) t1 t2 =
  mkGApp (mkGRef (Rocqlib.lib_ref "core.eq.type"), [typ; t2; t1])

(* [glob_make_neq t1 t2] build the glob_constr corresponding to [t1 <> t2] *)
let glob_make_neq t1 t2 =
  mkGApp (mkGRef (Rocqlib.lib_ref "core.not.type"), [glob_make_eq t1 t2])

let remove_name_from_mapping mapping na =
  match na with Anonymous -> mapping | Name id -> Id.Map.remove id mapping

let change_vars =
  let rec change_vars mapping rt =
    DAst.map_with_loc
      (fun ?loc -> function GRef _ as x -> x
        | GVar id ->
          let new_id = try Id.Map.find id mapping with Not_found -> id in
          GVar new_id | GEvar _ as x -> x | GPatVar _ as x -> x
        | GApp (rt', rtl) ->
          GApp (change_vars mapping rt', List.map (change_vars mapping) rtl)
        | GProj (f, rtl, rt) ->
          GProj (f, List.map (change_vars mapping) rtl, change_vars mapping rt)
        | GLambda (name, r, k, t, b) ->
          GLambda
            ( name
            , r, k
            , change_vars mapping t
            , change_vars (remove_name_from_mapping mapping name) b )
        | GProd (name, r, k, t, b) ->
          GProd
            ( name
            , r, k
            , change_vars mapping t
            , change_vars (remove_name_from_mapping mapping name) b )
        | GLetIn (name, r, def, typ, b) ->
          GLetIn
            ( name
            , r
            , change_vars mapping def
            , Option.map (change_vars mapping) typ
            , change_vars (remove_name_from_mapping mapping name) b )
        | GLetTuple (nal, (na, rto), b, e) ->
          let new_mapping =
            List.fold_left remove_name_from_mapping mapping nal
          in
          GLetTuple
            ( nal
            , (na, Option.map (change_vars mapping) rto)
            , change_vars mapping b
            , change_vars new_mapping e )
        | GCases (sty, infos, el, brl) ->
          GCases
            ( sty
            , infos
            , List.map (fun (e, x) -> (change_vars mapping e, x)) el
            , List.map (change_vars_br mapping) brl )
        | GIf (b, (na, e_option), lhs, rhs) ->
          GIf
            ( change_vars mapping b
            , (na, Option.map (change_vars mapping) e_option)
            , change_vars mapping lhs
            , change_vars mapping rhs )
        | GRec _ -> user_err ?loc Pp.(str "Local (co)fixes are not supported")
        | GFloat _ as x -> x
        | GCast (b, k, c) ->
          GCast (change_vars mapping b, k, change_vars mapping c)
        | GArray (u, t, def, ty) ->
          GArray
            ( u
            , Array.map (change_vars mapping) t
            , change_vars mapping def
            , change_vars mapping ty )
        | GSort _ | GHole _ | GGenarg _ | GInt _ | GString _ as x -> x)
      rt
  and change_vars_br mapping ({CAst.loc; v = idl, patl, res} as br) =
    let new_mapping = List.fold_right Id.Map.remove idl mapping in
    if Id.Map.is_empty new_mapping then br
    else CAst.make ?loc (idl, patl, change_vars new_mapping res)
  in
  change_vars

let rec alpha_pat excluded pat =
  let loc = pat.CAst.loc in
  match DAst.get pat with
  | PatVar Anonymous ->
    let new_id = Indfun_common.fresh_id excluded "_x" in
    (DAst.make ?loc @@ PatVar (Name new_id), new_id :: excluded, Id.Map.empty)
  | PatVar (Name id) ->
    if Id.List.mem id excluded then
      let new_id = Namegen.next_ident_away id (Id.Set.of_list excluded) in
      ( DAst.make ?loc @@ PatVar (Name new_id)
      , new_id :: excluded
      , Id.Map.add id new_id Id.Map.empty )
    else (pat, excluded, Id.Map.empty)
  | PatCstr (constr, patl, na) ->
    let new_na, new_excluded, map =
      match na with
      | Name id when Id.List.mem id excluded ->
        let new_id = Namegen.next_ident_away id (Id.Set.of_list excluded) in
        (Name new_id, new_id :: excluded, Id.Map.add id new_id Id.Map.empty)
      | _ -> (na, excluded, Id.Map.empty)
    in
    let new_patl, new_excluded, new_map =
      List.fold_left
        (fun (patl, excluded, map) pat ->
          let new_pat, new_excluded, new_map = alpha_pat excluded pat in
          (new_pat :: patl, new_excluded, Id.Map.fold Id.Map.add new_map map))
        ([], new_excluded, map) patl
    in
    ( DAst.make ?loc @@ PatCstr (constr, List.rev new_patl, new_na)
    , new_excluded
    , new_map )

let alpha_patl excluded patl =
  let patl, new_excluded, map =
    List.fold_left
      (fun (patl, excluded, map) pat ->
        let new_pat, new_excluded, new_map = alpha_pat excluded pat in
        (new_pat :: patl, new_excluded, Id.Map.fold Id.Map.add new_map map))
      ([], excluded, Id.Map.empty)
      patl
  in
  (List.rev patl, new_excluded, map)

let raw_get_pattern_id pat acc =
  let rec get_pattern_id pat =
    match DAst.get pat with
    | PatVar Anonymous -> assert false
    | PatVar (Name id) -> [id]
    | PatCstr (constr, patternl, _) ->
      List.fold_right
        (fun pat idl ->
          let idl' = get_pattern_id pat in
          idl' @ idl)
        patternl []
  in
  get_pattern_id pat @ acc

let get_pattern_id pat = raw_get_pattern_id pat []

let rec alpha_rt excluded rt =
  let loc = rt.CAst.loc in
  let new_rt =
    DAst.make ?loc
    @@
    match DAst.get rt with
    | (GRef _ | GVar _ | GEvar _ | GPatVar _) as rt -> rt
    | GLambda (Anonymous, r, k, t, b) ->
      let new_id =
        Namegen.next_ident_away (Id.of_string "_x") (Id.Set.of_list excluded)
      in
      let new_excluded = new_id :: excluded in
      let new_t = alpha_rt new_excluded t in
      let new_b = alpha_rt new_excluded b in
      GLambda (Name new_id, r, k, new_t, new_b)
    | GProd (Anonymous, r, k, t, b) ->
      let new_t = alpha_rt excluded t in
      let new_b = alpha_rt excluded b in
      GProd (Anonymous, r, k, new_t, new_b)
    | GLetIn (Anonymous, r, b, t, c) ->
      let new_b = alpha_rt excluded b in
      let new_t = Option.map (alpha_rt excluded) t in
      let new_c = alpha_rt excluded c in
      GLetIn (Anonymous, r, new_b, new_t, new_c)
    | GLambda (Name id, r, k, t, b) ->
      let new_id = Namegen.next_ident_away id (Id.Set.of_list excluded) in
      let t, b =
        if Id.equal new_id id then (t, b)
        else
          let replace = change_vars (Id.Map.add id new_id Id.Map.empty) in
          (t, replace b)
      in
      let new_excluded = new_id :: excluded in
      let new_t = alpha_rt new_excluded t in
      let new_b = alpha_rt new_excluded b in
      GLambda (Name new_id, r, k, new_t, new_b)
    | GProd (Name id, r, k, t, b) ->
      let new_id = Namegen.next_ident_away id (Id.Set.of_list excluded) in
      let new_excluded = new_id :: excluded in
      let t, b =
        if Id.equal new_id id then (t, b)
        else
          let replace = change_vars (Id.Map.add id new_id Id.Map.empty) in
          (t, replace b)
      in
      let new_t = alpha_rt new_excluded t in
      let new_b = alpha_rt new_excluded b in
      GProd (Name new_id, r, k, new_t, new_b)
    | GLetIn (Name id, r, b, t, c) ->
      let new_id = Namegen.next_ident_away id (Id.Set.of_list excluded) in
      let c =
        if Id.equal new_id id then c
        else change_vars (Id.Map.add id new_id Id.Map.empty) c
      in
      let new_excluded = new_id :: excluded in
      let new_b = alpha_rt new_excluded b in
      let new_t = Option.map (alpha_rt new_excluded) t in
      let new_c = alpha_rt new_excluded c in
      GLetIn (Name new_id, r, new_b, new_t, new_c)
    | GLetTuple (nal, (na, rto), t, b) ->
      let rev_new_nal, new_excluded, mapping =
        List.fold_left
          (fun (nal, excluded, mapping) na ->
            match na with
            | Anonymous -> (na :: nal, excluded, mapping)
            | Name id ->
              let new_id =
                Namegen.next_ident_away id (Id.Set.of_list excluded)
              in
              if Id.equal new_id id then (na :: nal, id :: excluded, mapping)
              else
                ( Name new_id :: nal
                , id :: excluded
                , Id.Map.add id new_id mapping ))
          ([], excluded, Id.Map.empty)
          nal
      in
      let new_nal = List.rev rev_new_nal in
      let new_rto, new_t, new_b =
        if Id.Map.is_empty mapping then (rto, t, b)
        else
          let replace = change_vars mapping in
          (Option.map replace rto, t, replace b)
      in
      let new_t = alpha_rt new_excluded new_t in
      let new_b = alpha_rt new_excluded new_b in
      let new_rto = Option.map (alpha_rt new_excluded) new_rto in
      GLetTuple (new_nal, (na, new_rto), new_t, new_b)
    | GCases (sty, infos, el, brl) ->
      let new_el =
        List.map (function rt, i -> (alpha_rt excluded rt, i)) el
      in
      GCases (sty, infos, new_el, List.map (alpha_br excluded) brl)
    | GIf (b, (na, e_o), lhs, rhs) ->
      GIf
        ( alpha_rt excluded b
        , (na, Option.map (alpha_rt excluded) e_o)
        , alpha_rt excluded lhs
        , alpha_rt excluded rhs )
    | GRec _ -> user_err Pp.(str "Not handled GRec")
    | (GSort _ | GInt _ | GFloat _ | GString _ | GHole _ | GGenarg _) as rt -> rt
    | GCast (b, k, c) ->
      GCast (alpha_rt excluded b, k, alpha_rt excluded c)
    | GApp (f, args) ->
      GApp (alpha_rt excluded f, List.map (alpha_rt excluded) args)
    | GProj (f, args, c) ->
      GProj (f, List.map (alpha_rt excluded) args, alpha_rt excluded c)
    | GArray (u, t, def, ty) ->
      GArray
        ( u
        , Array.map (alpha_rt excluded) t
        , alpha_rt excluded def
        , alpha_rt excluded ty )
  in
  new_rt

and alpha_br excluded {CAst.loc; v = ids, patl, res} =
  let new_patl, new_excluded, mapping = alpha_patl excluded patl in
  let new_ids = List.fold_right raw_get_pattern_id new_patl [] in
  let new_excluded = new_ids @ excluded in
  let renamed_res = change_vars mapping res in
  let new_res = alpha_rt new_excluded renamed_res in
  CAst.make ?loc (new_ids, new_patl, new_res)

(*
   [is_free_in id rt] checks if [id] is a free variable in [rt]
*)
let is_free_in id =
  let rec is_free_in x =
    DAst.with_loc_val
      (fun ?loc -> function GRef _ -> false | GVar id' -> Id.compare id' id == 0
        | GEvar _ -> false | GPatVar _ -> false
        | GApp (rt, rtl) | GProj (_, rtl, rt) -> List.exists is_free_in (rt :: rtl)
        | GLambda (n, _, _, t, b) | GProd (n, _, _, t, b) ->
          let check_in_b =
            match n with Name id' -> not (Id.equal id' id) | _ -> true
          in
          is_free_in t || (check_in_b && is_free_in b)
        | GLetIn (n, _, b, t, c) ->
          let check_in_c =
            match n with Name id' -> not (Id.equal id' id) | _ -> true
          in
          is_free_in b
          || Option.cata is_free_in true t
          || (check_in_c && is_free_in c)
        | GCases (_, _, el, brl) ->
          List.exists (fun (e, _) -> is_free_in e) el
          || List.exists is_free_in_br brl
        | GLetTuple (nal, _, b, t) ->
          let check_in_nal =
            not
              (List.exists
                 (function Name id' -> Id.equal id' id | _ -> false)
                 nal)
          in
          is_free_in t || (check_in_nal && is_free_in b)
        | GIf (cond, _, br1, br2) ->
          is_free_in cond || is_free_in br1 || is_free_in br2
        | GRec _ -> user_err Pp.(str "Not handled GRec") | GSort _ -> false
        | GHole _ -> false
        | GGenarg _ -> false (* XXX isn't this incorrect? *)
        | GCast (b, _, t) ->
          is_free_in b || is_free_in t
        | GInt _ | GFloat _ | GString _ -> false
        | GArray (_u, t, def, ty) ->
          Array.exists is_free_in t || is_free_in def || is_free_in ty)
      x
  and is_free_in_br {CAst.v = ids, _, rt} =
    (not (Id.List.mem id ids)) && is_free_in rt
  in
  is_free_in

let rec pattern_to_term pt =
  DAst.with_val
    (function
      | PatVar Anonymous -> assert false
      | PatVar (Name id) -> mkGVar id
      | PatCstr (constr, patternl, _) ->
        let cst_narg =
          Inductiveops.constructor_nallargs (Global.env ()) constr
        in
        let implicit_args =
          Array.to_list
            (Array.init (cst_narg - List.length patternl) (fun _ -> mkGHole ()))
        in
        let patl_as_term = List.map pattern_to_term patternl in
        mkGApp
          (mkGRef (GlobRef.ConstructRef constr), implicit_args @ patl_as_term))
    pt

let replace_var_by_term x_id term =
  let rec replace_var_by_pattern x =
    DAst.map
      (function
        | GVar id when Id.compare id x_id == 0 -> DAst.get term
        | (GRef _ | GVar _ | GEvar _ | GPatVar _) as rt -> rt
        | GApp (rt', rtl) ->
          GApp (replace_var_by_pattern rt', List.map replace_var_by_pattern rtl)
        | GProj (f, rtl, rt) ->
          GProj (f, List.map replace_var_by_pattern rtl, replace_var_by_pattern rt)
        | GLambda (Name id, _, _, _, _) as rt when Id.compare id x_id == 0 -> rt
        | GLambda (name, r, k, t, b) ->
          GLambda (name, r, k, replace_var_by_pattern t, replace_var_by_pattern b)
        | GProd (Name id, _, _, _, _) as rt when Id.compare id x_id == 0 -> rt
        | GProd (name, r, k, t, b) ->
          GProd (name, r, k, replace_var_by_pattern t, replace_var_by_pattern b)
        | GLetIn (Name id, _, _, _, _) as rt when Id.compare id x_id == 0 -> rt
        | GLetIn (name, r, def, typ, b) ->
          GLetIn
            ( name
            , r
            , replace_var_by_pattern def
            , Option.map replace_var_by_pattern typ
            , replace_var_by_pattern b )
        | GLetTuple (nal, _, _, _) as rt
          when List.exists
                 (function Name id -> Id.equal id x_id | _ -> false)
                 nal ->
          rt
        | GLetTuple (nal, (na, rto), def, b) ->
          GLetTuple
            ( nal
            , (na, Option.map replace_var_by_pattern rto)
            , replace_var_by_pattern def
            , replace_var_by_pattern b )
        | GCases (sty, infos, el, brl) ->
          GCases
            ( sty
            , infos
            , List.map (fun (e, x) -> (replace_var_by_pattern e, x)) el
            , List.map replace_var_by_pattern_br brl )
        | GIf (b, (na, e_option), lhs, rhs) ->
          GIf
            ( replace_var_by_pattern b
            , (na, Option.map replace_var_by_pattern e_option)
            , replace_var_by_pattern lhs
            , replace_var_by_pattern rhs )
        | GRec _ -> CErrors.user_err (Pp.str "Not handled GRec")
        | (GSort _ | GHole _ | GGenarg _) as rt -> rt (* is this correct for GGenarg? *)
        | GInt _ as rt -> rt
        | GFloat _ as rt -> rt
        | GString _ as rt -> rt
        | GArray (u, t, def, ty) ->
          GArray
            ( u
            , Array.map replace_var_by_pattern t
            , replace_var_by_pattern def
            , replace_var_by_pattern ty )
        | GCast (b, k, c) ->
          GCast (replace_var_by_pattern b, k, replace_var_by_pattern c))
      x
  and replace_var_by_pattern_br ({CAst.loc; v = idl, patl, res} as br) =
    if List.exists (fun id -> Id.compare id x_id == 0) idl then br
    else CAst.make ?loc (idl, patl, replace_var_by_pattern res)
  in
  replace_var_by_pattern

(* checking unifiability of patterns *)
exception NotUnifiable

let rec are_unifiable_aux env = function
  | [] -> ()
  | (l, r) :: eqs -> (
    match (DAst.get l, DAst.get r) with
    | PatVar _, _ | _, PatVar _ -> are_unifiable_aux env eqs
    | PatCstr (constructor1, cpl1, _), PatCstr (constructor2, cpl2, _) ->
      if not (Environ.QConstruct.equal env constructor2 constructor1) then
        raise NotUnifiable
      else
        let eqs' =
          try List.combine cpl1 cpl2 @ eqs
          with Invalid_argument _ -> anomaly (Pp.str "are_unifiable_aux.")
        in
        are_unifiable_aux env eqs' )

let are_unifiable env pat1 pat2 =
  try
    are_unifiable_aux env [(pat1, pat2)];
    true
  with NotUnifiable -> false

let rec eq_cases_pattern_aux env = function
  | [] -> ()
  | (l, r) :: eqs -> (
    match (DAst.get l, DAst.get r) with
    | PatVar _, PatVar _ -> eq_cases_pattern_aux env eqs
    | PatCstr (constructor1, cpl1, _), PatCstr (constructor2, cpl2, _) ->
      if not (Environ.QConstruct.equal env constructor2 constructor1) then
        raise NotUnifiable
      else
        let eqs' =
          try List.combine cpl1 cpl2 @ eqs
          with Invalid_argument _ -> anomaly (Pp.str "eq_cases_pattern_aux.")
        in
        eq_cases_pattern_aux env eqs'
    | _ -> raise NotUnifiable )

let eq_cases_pattern env pat1 pat2 =
  try
    eq_cases_pattern_aux env [(pat1, pat2)];
    true
  with NotUnifiable -> false

let ids_of_pat =
  let rec ids_of_pat ids =
    DAst.with_val (function
      | PatVar Anonymous -> ids
      | PatVar (Name id) -> Id.Set.add id ids
      | PatCstr (_, patl, _) -> List.fold_left ids_of_pat ids patl)
  in
  ids_of_pat Id.Set.empty

let expand_as =
  let rec add_as map rt =
    match DAst.get rt with
    | PatVar _ -> map
    | PatCstr (_, patl, Name id) ->
      Id.Map.add id (pattern_to_term rt) (List.fold_left add_as map patl)
    | PatCstr (_, patl, _) -> List.fold_left add_as map patl
  in
  let rec expand_as map =
    DAst.map (function
      | (GRef _ | GEvar _ | GPatVar _ | GSort _ | GHole _ | GGenarg _ | GInt _
         | GFloat _ | GString _ ) as rt -> rt
      | GVar id as rt -> (
        try DAst.get (Id.Map.find id map) with Not_found -> rt )
      | GApp (f, args) -> GApp (expand_as map f, List.map (expand_as map) args)
      | GProj (f, args, c) -> GProj (f, List.map (expand_as map) args, expand_as map c)
      | GLambda (na, r, k, t, b) ->
        GLambda (na, r, k, expand_as map t, expand_as map b)
      | GProd (na, r, k, t, b) -> GProd (na, r, k, expand_as map t, expand_as map b)
      | GLetIn (na, r, v, typ, b) ->
        GLetIn
          (na, r, expand_as map v, Option.map (expand_as map) typ, expand_as map b)
      | GLetTuple (nal, (na, po), v, b) ->
        GLetTuple
          ( nal
          , (na, Option.map (expand_as map) po)
          , expand_as map v
          , expand_as map b )
      | GIf (e, (na, po), br1, br2) ->
        GIf
          ( expand_as map e
          , (na, Option.map (expand_as map) po)
          , expand_as map br1
          , expand_as map br2 )
      | GRec _ -> user_err Pp.(str "Not handled GRec")
      | GCast (b, k, c) ->
        GCast (expand_as map b, k, expand_as map c)
      | GCases (sty, po, el, brl) ->
        GCases
          ( sty
          , Option.map (expand_as map) po
          , List.map (fun (rt, t) -> (expand_as map rt, t)) el
          , List.map (expand_as_br map) brl )
      | GArray (u, t, def, ty) ->
        GArray
          (u, Array.map (expand_as map) t, expand_as map def, expand_as map ty))
  and expand_as_br map {CAst.loc; v = idl, cpl, rt} =
    CAst.make ?loc (idl, cpl, expand_as (List.fold_left add_as map cpl) rt)
  in
  expand_as Id.Map.empty

(* [resolve_and_replace_implicits] solves implicits of its argument and replaces them by their solution *)

let resolve_and_replace_implicits exptyp env sigma rt =
  let open Evd in
  let open Evar_kinds in
  (* we first (pseudo) understand [rt] and get back the computed evar_map *)
  (* FIXME : JF (30/03/2017) I'm not completely sure to have split understand as needed.
     If someone knows how to prevent solved existantial removal in  understand, please do not hesitate to change the computation of [ctx] here *)
  let implicit_holes = ref [] in
  let binder_holes = ref [] in
  let ctx =
    let open Pretyping in
    let open Evarutil in
    (* Intercept the pretyper for holes and record the generated evar *)
    let register_evar kind loc evk = match kind with
    | GImplicitArg (grk, pk, bk) -> implicit_holes := ((loc, grk, pk, bk), evk) :: !implicit_holes
    | GBinderType na -> binder_holes := ((loc, na), evk) :: !binder_holes
    | _ -> ()
    in
    let pretype_hole self kind ?loc ~flags tycon env sigma =
      let sigma, j = default_pretyper.pretype_hole self kind ?loc ~flags tycon env sigma in
      (* The value is guaranteed to be an undefined evar at this point *)
      let evk, _ = EConstr.destEvar sigma j.uj_val in
      let () = register_evar kind loc evk  in
      sigma, j
    in
    let pretype_type self c ?loc ~flags valcon env sigma =
      let sigma, j = default_pretyper.pretype_type self c ?loc ~flags valcon env sigma in
      let () = match DAst.get c, EConstr.kind sigma j.utj_val with
      | GHole (kind), Evar (evk, _) -> register_evar kind c.CAst.loc evk
      | _ -> ()
      in
      sigma, j
    in
    let flags = Pretyping.all_and_fail_flags in
    let pretype_flags = {
      program_mode = false;
      use_coercions = true;
      poly = false;
      resolve_tc = true;
      undeclared_evars_patvars = false;
      patvars_abstract = false;
      unconstrained_sorts = false;
    } in
    let vars = Evarutil.VarSet.variables (Global.env ()) in
    let hypnaming = RenameExistingBut vars in
    let genv = GlobEnv.make ~hypnaming env sigma Glob_ops.empty_lvar in
    let pretyper = { default_pretyper with pretype_hole; pretype_type } in
    let sigma', _ = eval_pretyper pretyper ~flags:pretype_flags (Some exptyp) genv sigma rt in
    solve_remaining_evars flags env ~initial:sigma sigma'
  in
  let ctx = Evd.minimize_universes ctx in
  let f c =
    EConstr.of_constr
      (Evarutil.nf_evars_universes ctx (EConstr.Unsafe.to_constr c))
  in
  let expand_hole evopt default = match evopt with
  | None -> default
  | Some evk ->
    (* we found the evar corresponding to this hole *)
    let EvarInfo evi = Evd.find ctx evk in
    match Evd.evar_body evi with
    | Evar_defined c ->
      (* we just have to lift the solution in glob_term *)
      Detyping.detype Detyping.Now env ctx (f c)
    | Evar_empty ->
      (* the hole was not solved : we do nothing *)
      default
  in
  (* then we map [rt] to replace the implicit holes by their values *)
  let rec change rt =
    match DAst.get rt with
    | GHole (GImplicitArg (grk, pk, bk)) ->
      let eq (loc1, gr1, p1, b1) (loc2, gr2, p2, b2) =
        Environ.QGlobRef.equal env gr1 gr2 && p1 = p2 && b1 == (b2 : bool) && loc1 = (loc2 : Loc.t option)
      in
      let evopt = List.assoc_f_opt eq (rt.CAst.loc, grk, pk, bk) !implicit_holes in
      expand_hole evopt rt
    | GHole (GBinderType na) ->
      let eq (loc1, na1) (loc2, na2) = Name.equal na1 na2 && loc1 = (loc2 : Loc.t option) in
      let evopt = List.assoc_f_opt eq (rt.CAst.loc, na) !binder_holes in
      expand_hole evopt rt
    | _ -> Glob_ops.map_glob_constr change rt
  in
  change rt
