(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open CErrors
open Names
open Libnames
open Libobject
open Nametab
open Tac2expr
open Tac2intern
open Vernacexpr

type tacdef = {
  tacdef_local : bool;
  tacdef_expr : glb_tacexpr;
  tacdef_type : type_scheme;
}

let perform_tacdef visibility ((sp, kn), def) =
  let () = if not def.tacdef_local then Tac2env.push_ltac visibility sp kn in
  Tac2env.define_global kn (def.tacdef_expr, def.tacdef_type)

let load_tacdef i obj = perform_tacdef (Until i) obj
let open_tacdef i obj = perform_tacdef (Exactly i) obj

let cache_tacdef ((sp, kn), def) =
  let () = Tac2env.push_ltac (Until 1) sp kn in
  Tac2env.define_global kn (def.tacdef_expr, def.tacdef_type)

let subst_tacdef (subst, def) =
  let expr' = subst_expr subst def.tacdef_expr in
  let type' = subst_type_scheme subst def.tacdef_type in
  if expr' == def.tacdef_expr && type' == def.tacdef_type then def
  else { def with tacdef_expr = expr'; tacdef_type = type' }

let classify_tacdef o = Substitute o

let inTacDef : tacdef -> obj =
  declare_object {(default_object "TAC2-DEFINITION") with
     cache_function  = cache_tacdef;
     load_function   = load_tacdef;
     open_function   = open_tacdef;
     subst_function = subst_tacdef;
     classify_function = classify_tacdef}

type typdef = {
  typdef_local : bool;
  typdef_expr : glb_quant_typedef;
}

let change_kn_label kn id =
  let (mp, dp, _) = KerName.repr kn in
  KerName.make mp dp (Label.of_id id)

let change_sp_label sp id =
  let (dp, _) = Libnames.repr_path sp in
  Libnames.make_path dp id

let push_typedef visibility sp kn (_, def) = match def with
| GTydDef _ ->
  Tac2env.push_type visibility sp kn
| GTydAlg cstrs ->
  (** Register constructors *)
  let iter (c, _) =
    let spc = change_sp_label sp c in
    let knc = change_kn_label kn c in
    Tac2env.push_ltac visibility spc knc
  in
  Tac2env.push_type visibility sp kn;
  List.iter iter cstrs
| GTydRec _ ->
  assert false (** FIXME *)

let next i =
  let ans = !i in
  let () = incr i in
  ans

let dummy_var i = Id.of_string (Printf.sprintf "_%i" i)

let define_typedef kn (params, def as qdef) = match def with
| GTydDef _ ->
  Tac2env.define_type kn qdef
| GTydAlg cstrs ->
  (** Define constructors *)
  let constant = ref 0 in
  let nonconstant = ref 0 in
  let iter (c, args) =
    let knc = change_kn_label kn c in
    let tag = if List.is_empty args then next constant else next nonconstant in
    let ids = List.mapi (fun i _ -> dummy_var i) args in
    let c = GTacCst (kn, tag, List.map (fun id -> GTacVar id) ids) in
    let c =
      if List.is_empty args then c
      else GTacFun (List.map (fun id -> Name id) ids, c)
    in
    let fold arg tpe = GTypArrow (arg, tpe) in
    let cT = GTypRef (kn, List.init params (fun i -> GTypVar i)) in
    let cT = List.fold_right fold args cT in
    let data = {
      Tac2env.cdata_type = kn;
      cdata_args = params, args;
      cdata_indx = tag;
    } in
    Tac2env.define_constructor knc data;
    Tac2env.define_global knc (c, (params, cT))
  in
  Tac2env.define_type kn qdef;
  List.iter iter cstrs
| GTydRec _ ->
  assert false (** FIXME *)

let perform_typdef vs ((sp, kn), def) =
  let () = if not def.typdef_local then push_typedef vs sp kn def.typdef_expr in
  define_typedef kn def.typdef_expr

let load_typdef i obj = perform_typdef (Until i) obj
let open_typdef i obj = perform_typdef (Exactly i) obj

let cache_typdef ((sp, kn), def) =
  let () = push_typedef (Until 1) sp kn def.typdef_expr in
  define_typedef kn def.typdef_expr

let subst_typdef (subst, def) =
  let expr' = subst_quant_typedef subst def.typdef_expr in
  if expr' == def.typdef_expr then def else { def with typdef_expr = expr' }

let classify_typdef o = Substitute o

let inTypDef : typdef -> obj =
  declare_object {(default_object "TAC2-TYPE-DEFINITION") with
     cache_function  = cache_typdef;
     load_function   = load_typdef;
     open_function   = open_typdef;
     subst_function = subst_typdef;
     classify_function = classify_typdef}

let register_ltac ?(local = false) isrec tactics =
  if isrec then
    let map (na, e) = (na, None, e) in
    let bindings = List.map map tactics in
    let map ((loc, na), e) = match na with
    | Anonymous -> None
    | Name id ->
      let qid = Libnames.qualid_of_ident id in
      let e = CTacLet (Loc.ghost, true, bindings, CTacRef (loc, qid)) in
      let (e, t) = intern e in
      let e = match e with
      | GTacLet (true, _, e) -> assert false
      | _ -> assert false
      in
      Some (e, t)
    in
    let tactics = List.map map tactics in
    assert false (** FIXME *)
  else
    let map ((loc, na), e) =
      let (e, t) = intern e in
      let () =
        if not (is_value e) then
          user_err ~loc (str "Tactic definition must be a syntactical value")
      in
      let id = match na with
      | Anonymous ->
        user_err ~loc (str "Tactic definition must have a name")
      | Name id -> id
      in
      let kn = Lib.make_kn id in
      let exists =
        try let _ = Tac2env.interp_global kn in true with Not_found -> false
      in
      let () =
        if exists then
          user_err ~loc (str "Tactic " ++ Nameops.pr_id id ++ str " already exists")
      in
      (id, e, t)
    in
    let defs = List.map map tactics in
    let iter (id, e, t) =
      let def = {
        tacdef_local = local;
        tacdef_expr = e;
        tacdef_type = t;
      } in
      ignore (Lib.add_leaf id (inTacDef def))
    in
    List.iter iter defs

let register_type ?(local = false) isrec types =
  let same_name ((_, id1), _) ((_, id2), _) = Id.equal id1 id2 in
  let () = match List.duplicates same_name types with
  | [] -> ()
  | ((loc, id), _) :: _ ->
    user_err ~loc (str "Multiple definition of the type name " ++ Id.print id)
  in
  let check ((loc, id), (params, def)) =
    let same_name (_, id1) (_, id2) = Id.equal id1 id2 in
    let () = match List.duplicates same_name params with
    | [] -> ()
    | (loc, id) :: _ ->
      user_err ~loc (str "The type parameter " ++ Id.print id ++
        str " occurs several times")
    in
    match def with
    | CTydDef _ ->
      if isrec then
        user_err ~loc (str "The type abbreviation " ++ Id.print id ++
          str " cannot be recursive")
    | CTydAlg _ -> () (** FIXME *)
    | CTydRec _ -> assert false (** FIXME *)
  in
  let () = List.iter check types in
  let self =
    if isrec then
      let fold accu ((_, id), (params, _)) =
        Id.Map.add id (Lib.make_kn id, List.length params) accu
      in
      List.fold_left fold Id.Map.empty types
    else Id.Map.empty
  in
  let map ((_, id), def) =
    let typdef = {
      typdef_local = local;
      typdef_expr = intern_typedef self def;
    } in
    (id, typdef)
  in
  let types = List.map map types in
  let iter (id, def) = ignore (Lib.add_leaf id (inTypDef def)) in
  List.iter iter types

let register_primitive ?(local = false) (loc, id) t ml =
  let t = intern_open_type t in
  let rec count_arrow = function
  | GTypArrow (_, t) -> 1 + count_arrow t
  | _ -> 0
  in
  let arrows = count_arrow (snd t) in
  let () = if Int.equal arrows 0 then
    user_err ~loc (str "External tactic must have at least one argument") in
  let () =
    try let _ = Tac2env.interp_primitive ml in () with Not_found ->
      user_err ~loc (str "Unregistered primitive " ++
        quote (str ml.mltac_plugin) ++ spc () ++ quote (str ml.mltac_tactic))
  in
  let init i = Id.of_string (Printf.sprintf "x%i" i) in
  let names = List.init arrows init in
  let bnd = List.map (fun id -> Name id) names in
  let arg = List.map (fun id -> GTacVar id) names in
  let e = GTacFun (bnd, GTacPrm (ml, arg)) in
  let def = {
    tacdef_local = local;
    tacdef_expr = e;
    tacdef_type = t;
  } in
  ignore (Lib.add_leaf id (inTacDef def))

let register_struct ?local str = match str with
| StrVal (isrec, e) -> register_ltac ?local isrec e
| StrTyp (isrec, t) -> register_type ?local isrec t
| StrPrm (id, t, ml) -> register_primitive ?local id t ml

(** Printing *)

let print_ltac ref =
  let (loc, qid) = qualid_of_reference ref in
  let kn =
    try Tac2env.locate_ltac qid
    with Not_found -> user_err ~loc (str "Unknown tactic " ++ pr_qualid qid)
  in
  let (_, (_, t)) = Tac2env.interp_global kn in
  Feedback.msg_notice (pr_qualid qid ++ spc () ++ str ":" ++ spc () ++ pr_glbtype t)

(** Calling tactics *)

let solve default tac =
  let status = Proof_global.with_current_proof begin fun etac p ->
    let with_end_tac = if default then Some etac else None in
    let (p, status) = Pfedit.solve SelectAll None tac ?with_end_tac p in
    (* in case a strict subtree was completed,
       go back to the top of the prooftree *)
    let p = Proof.maximal_unfocus Vernacentries.command_focus p in
    p, status
  end in
  if not status then Feedback.feedback Feedback.AddedAxiom

let call ~default e =
  let loc = loc_of_tacexpr e in
  let (e, (_, t)) = intern e in
  let () = check_unit ~loc t in
  let tac = Tac2interp.interp Id.Map.empty e in
  solve default (Proofview.tclIGNORE tac)

(** Primitive algebraic types than can't be defined Coq-side *)

let register_prim_alg name params def =
  let id = Id.of_string name in
  let def = List.map (fun (cstr, tpe) -> (Id.of_string_soft cstr, tpe)) def in
  let def = (params, GTydAlg def) in
  let def = { typdef_local = false; typdef_expr = def } in
  ignore (Lib.add_leaf id (inTypDef def))

let coq_prefix = DirPath.make (List.map Id.of_string ["Ltac2"; "ltac2"; "Coq"])
let coq_def n = KerName.make2 (MPfile coq_prefix) (Label.make n)

let t_list = coq_def "list"

let _ = Mltop.declare_cache_obj begin fun () ->
  register_prim_alg "unit" 0 ["()", []];
  register_prim_alg "list" 1 [
    ("[]", []);
    ("::", [GTypVar 0; GTypRef (t_list, [GTypVar 0])]);
  ];
end "ltac2_plugin"
