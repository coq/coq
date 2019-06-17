(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open CAst
open CErrors
open Names
open Libnames
open Libobject
open Nametab
open Tac2expr
open Tac2print
open Tac2intern

(** Grammar entries *)

module Pltac =
struct
let tac2expr = Pcoq.Entry.create "tactic:tac2expr"

let q_ident = Pcoq.Entry.create "tactic:q_ident"
let q_bindings = Pcoq.Entry.create "tactic:q_bindings"
let q_with_bindings = Pcoq.Entry.create "tactic:q_with_bindings"
let q_intropattern = Pcoq.Entry.create "tactic:q_intropattern"
let q_intropatterns = Pcoq.Entry.create "tactic:q_intropatterns"
let q_destruction_arg = Pcoq.Entry.create "tactic:q_destruction_arg"
let q_induction_clause = Pcoq.Entry.create "tactic:q_induction_clause"
let q_conversion = Pcoq.Entry.create "tactic:q_conversion"
let q_rewriting = Pcoq.Entry.create "tactic:q_rewriting"
let q_clause = Pcoq.Entry.create "tactic:q_clause"
let q_dispatch = Pcoq.Entry.create "tactic:q_dispatch"
let q_occurrences = Pcoq.Entry.create "tactic:q_occurrences"
let q_reference = Pcoq.Entry.create "tactic:q_reference"
let q_strategy_flag = Pcoq.Entry.create "tactic:q_strategy_flag"
let q_constr_matching = Pcoq.Entry.create "tactic:q_constr_matching"
let q_goal_matching = Pcoq.Entry.create "tactic:q_goal_matching"
let q_hintdb = Pcoq.Entry.create "tactic:q_hintdb"
let q_move_location = Pcoq.Entry.create "tactic:q_move_location"
let q_pose = Pcoq.Entry.create "tactic:q_pose"
let q_assert = Pcoq.Entry.create "tactic:q_assert"
end

(** Tactic definition *)

type tacdef = {
  tacdef_local : bool;
  tacdef_mutable : bool;
  tacdef_expr : glb_tacexpr;
  tacdef_type : type_scheme;
}

let perform_tacdef visibility ((sp, kn), def) =
  let () = if not def.tacdef_local then Tac2env.push_ltac visibility sp (TacConstant kn) in
  let data = {
    Tac2env.gdata_expr = def.tacdef_expr;
    gdata_type = def.tacdef_type;
    gdata_mutable = def.tacdef_mutable;
  } in
  Tac2env.define_global kn data

let load_tacdef i obj = perform_tacdef (Until i) obj
let open_tacdef i obj = perform_tacdef (Exactly i) obj

let cache_tacdef ((sp, kn), def) =
  let () = Tac2env.push_ltac (Until 1) sp (TacConstant kn) in
  let data = {
    Tac2env.gdata_expr = def.tacdef_expr;
    gdata_type = def.tacdef_type;
    gdata_mutable = def.tacdef_mutable;
  } in
  Tac2env.define_global kn data

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

(** Type definition *)

type typdef = {
  typdef_local : bool;
  typdef_expr : glb_quant_typedef;
}

let change_kn_label kn id =
  let mp = KerName.modpath kn in
  KerName.make mp (Label.of_id id)

let change_sp_label sp id =
  let (dp, _) = Libnames.repr_path sp in
  Libnames.make_path dp id

let push_typedef visibility sp kn (_, def) = match def with
| GTydDef _ ->
  Tac2env.push_type visibility sp kn
| GTydAlg { galg_constructors = cstrs } ->
  (* Register constructors *)
  let iter (c, _) =
    let spc = change_sp_label sp c in
    let knc = change_kn_label kn c in
    Tac2env.push_constructor visibility spc knc
  in
  Tac2env.push_type visibility sp kn;
  List.iter iter cstrs
| GTydRec fields ->
  (* Register fields *)
  let iter (c, _, _) =
    let spc = change_sp_label sp c in
    let knc = change_kn_label kn c in
    Tac2env.push_projection visibility spc knc
  in
  Tac2env.push_type visibility sp kn;
  List.iter iter fields
| GTydOpn ->
  Tac2env.push_type visibility sp kn

let next i =
  let ans = !i in
  let () = incr i in
  ans

let define_typedef kn (params, def as qdef) = match def with
| GTydDef _ ->
  Tac2env.define_type kn qdef
| GTydAlg { galg_constructors = cstrs } ->
  (* Define constructors *)
  let constant = ref 0 in
  let nonconstant = ref 0 in
  let iter (c, args) =
    let knc = change_kn_label kn c in
    let tag = if List.is_empty args then next constant else next nonconstant in
    let data = {
      Tac2env.cdata_prms = params;
      cdata_type = kn;
      cdata_args = args;
      cdata_indx = Some tag;
    } in
    Tac2env.define_constructor knc data
  in
  Tac2env.define_type kn qdef;
  List.iter iter cstrs
| GTydRec fs ->
  (* Define projections *)
  let iter i (id, mut, t) =
    let knp = change_kn_label kn id in
    let proj = {
      Tac2env.pdata_prms = params;
      pdata_type = kn;
      pdata_ptyp = t;
      pdata_mutb = mut;
      pdata_indx = i;
    } in
    Tac2env.define_projection knp proj
  in
  Tac2env.define_type kn qdef;
  List.iteri iter fs
| GTydOpn ->
  Tac2env.define_type kn qdef

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

(** Type extension *)

type extension_data = {
  edata_name : Id.t;
  edata_args : int glb_typexpr list;
}

type typext = {
  typext_local : bool;
  typext_prms : int;
  typext_type : type_constant;
  typext_expr : extension_data list;
}

let push_typext vis sp kn def =
  let iter data =
    let spc = change_sp_label sp data.edata_name in
    let knc = change_kn_label kn data.edata_name in
    Tac2env.push_constructor vis spc knc
  in
  List.iter iter def.typext_expr

let define_typext kn def =
  let iter data =
    let knc = change_kn_label kn data.edata_name in
    let cdata = {
      Tac2env.cdata_prms = def.typext_prms;
      cdata_type = def.typext_type;
      cdata_args = data.edata_args;
      cdata_indx = None;
    } in
    Tac2env.define_constructor knc cdata
  in
  List.iter iter def.typext_expr

let cache_typext ((sp, kn), def) =
  let () = define_typext kn def in
  push_typext (Until 1) sp kn def

let perform_typext vs ((sp, kn), def) =
  let () = if not def.typext_local then push_typext vs sp kn def in
  define_typext kn def

let load_typext i obj = perform_typext (Until i) obj
let open_typext i obj = perform_typext (Exactly i) obj

let subst_typext (subst, e) =
  let open Mod_subst in
  let subst_data data =
    let edata_args = List.Smart.map (fun e -> subst_type subst e) data.edata_args in
    if edata_args == data.edata_args then data
    else { data with edata_args }
  in
  let typext_type = subst_kn subst e.typext_type in
  let typext_expr = List.Smart.map subst_data e.typext_expr in
  if typext_type == e.typext_type && typext_expr == e.typext_expr then
    e
  else
    { e with typext_type; typext_expr }

let classify_typext o = Substitute o

let inTypExt : typext -> obj =
  declare_object {(default_object "TAC2-TYPE-EXTENSION") with
     cache_function  = cache_typext;
     load_function   = load_typext;
     open_function   = open_typext;
     subst_function = subst_typext;
     classify_function = classify_typext}

(** Toplevel entries *)

let fresh_var avoid x =
  let bad id =
    Id.Set.mem id avoid ||
    (try ignore (Tac2env.locate_ltac (qualid_of_ident id)); true with Not_found -> false)
  in
  Namegen.next_ident_away_from (Id.of_string x) bad

let extract_pattern_type ({loc;v=p} as pat) = match p with
| CPatCnv (pat, ty) -> pat, Some ty
| CPatVar _ | CPatRef _ -> pat, None

(** Mangle recursive tactics *)
let inline_rec_tactic tactics =
  let avoid = List.fold_left (fun accu ({v=id}, _) -> Id.Set.add id accu) Id.Set.empty tactics in
  let map (id, e) = match e.v with
  | CTacFun (pat, _) -> (id, List.map extract_pattern_type pat, e)
  | _ ->
    user_err ?loc:id.loc (str "Recursive tactic definitions must be functions")
  in
  let tactics = List.map map tactics in
  let map (id, pat, e) =
    let fold_var (avoid, ans) (pat, _) =
      let id = fresh_var avoid "x" in
      let loc = pat.loc in
      (Id.Set.add id avoid, CAst.make ?loc id :: ans)
    in
    (* Fresh variables to abstract over the function patterns *)
    let _, vars = List.fold_left fold_var (avoid, []) pat in
    let map_body ({loc;v=id}, _, e) = CAst.(make ?loc @@ CPatVar (Name id)), e in
    let bnd = List.map map_body tactics in
    let pat_of_id {loc;v=id} = CAst.make ?loc @@ CPatVar (Name id) in
    let var_of_id {loc;v=id} =
      let qid = qualid_of_ident ?loc id in
      CAst.make ?loc @@ CTacRef (RelId qid)
    in
    let loc0 = e.loc in
    let vpat = List.map pat_of_id vars in
    let varg = List.map var_of_id vars in
    let e = CAst.make ?loc:loc0 @@ CTacLet (true, bnd, CAst.make ?loc:loc0 @@ CTacApp (var_of_id id, varg)) in
    (id, CAst.make ?loc:loc0 @@ CTacFun (vpat, e))
  in
  List.map map tactics

let check_lowercase {loc;v=id} =
  if Tac2env.is_constructor (Libnames.qualid_of_ident id) then
    user_err ?loc (str "The identifier " ++ Id.print id ++ str " must be lowercase")

let register_ltac ?(local = false) ?(mut = false) isrec tactics =
  let map ({loc;v=na}, e) =
    let id = match na with
    | Anonymous ->
      user_err ?loc (str "Tactic definition must have a name")
    | Name id -> id
    in
    let () = check_lowercase CAst.(make ?loc id) in
    (CAst.(make ?loc id), e)
  in
  let tactics = List.map map tactics in
  let tactics =
    if isrec then inline_rec_tactic tactics else tactics
  in
  let map ({loc;v=id}, e) =
    let (e, t) = intern ~strict:true e in
    let () =
      if not (is_value e) then
        user_err ?loc (str "Tactic definition must be a syntactical value")
    in
    let kn = Lib.make_kn id in
    let exists =
      try let _ = Tac2env.interp_global kn in true with Not_found -> false
    in
    let () =
      if exists then
        user_err ?loc (str "Tactic " ++ Names.Id.print id ++ str " already exists")
    in
    (id, e, t)
  in
  let defs = List.map map tactics in
  let iter (id, e, t) =
    let def = {
      tacdef_local = local;
      tacdef_mutable = mut;
      tacdef_expr = e;
      tacdef_type = t;
    } in
    ignore (Lib.add_leaf id (inTacDef def))
  in
  List.iter iter defs

let qualid_to_ident qid =
  if qualid_is_ident qid then CAst.make ?loc:qid.CAst.loc @@ qualid_basename qid
  else user_err ?loc:qid.CAst.loc (str "Identifier expected")

let register_typedef ?(local = false) isrec types =
  let same_name ({v=id1}, _) ({v=id2}, _) = Id.equal id1 id2 in
  let () = match List.duplicates same_name types with
  | [] -> ()
  | ({loc;v=id}, _) :: _ ->
    user_err ?loc (str "Multiple definition of the type name " ++ Id.print id)
  in
  let check ({loc;v=id}, (params, def)) =
    let same_name {v=id1} {v=id2} = Id.equal id1 id2 in
    let () = match List.duplicates same_name params with
    | [] -> ()
    | {loc;v=id} :: _ ->
      user_err ?loc (str "The type parameter " ++ Id.print id ++
        str " occurs several times")
    in
    match def with
    | CTydDef _ ->
      if isrec then
        user_err ?loc (str "The type abbreviation " ++ Id.print id ++
          str " cannot be recursive")
    | CTydAlg cs ->
      let same_name (id1, _) (id2, _) = Id.equal id1 id2 in
      let () = match List.duplicates same_name cs with
      | [] -> ()
      | (id, _) :: _ ->
        user_err (str "Multiple definitions of the constructor " ++ Id.print id)
      in
      ()
    | CTydRec ps ->
      let same_name (id1, _, _) (id2, _, _) = Id.equal id1 id2 in
      let () = match List.duplicates same_name ps with
      | [] -> ()
      | (id, _, _) :: _ ->
        user_err (str "Multiple definitions of the projection " ++ Id.print id)
      in
      ()
    | CTydOpn ->
      if isrec then
        user_err ?loc (str "The open type declaration " ++ Id.print id ++
          str " cannot be recursive")
  in
  let () = List.iter check types in
  let self =
    if isrec then
      let fold accu ({v=id}, (params, _)) =
        Id.Map.add id (Lib.make_kn id, List.length params) accu
      in
      List.fold_left fold Id.Map.empty types
    else Id.Map.empty
  in
  let map ({v=id}, def) =
    let typdef = {
      typdef_local = local;
      typdef_expr = intern_typedef self def;
    } in
    (id, typdef)
  in
  let types = List.map map types in
  let iter (id, def) = ignore (Lib.add_leaf id (inTypDef def)) in
  List.iter iter types

let register_primitive ?(local = false) {loc;v=id} t ml =
  let t = intern_open_type t in
  let rec count_arrow = function
  | GTypArrow (_, t) -> 1 + count_arrow t
  | _ -> 0
  in
  let arrows = count_arrow (snd t) in
  let () = if Int.equal arrows 0 then
    user_err ?loc (str "External tactic must have at least one argument") in
  let () =
    try let _ = Tac2env.interp_primitive ml in () with Not_found ->
      user_err ?loc (str "Unregistered primitive " ++
        quote (str ml.mltac_plugin) ++ spc () ++ quote (str ml.mltac_tactic))
  in
  let init i = Id.of_string (Printf.sprintf "x%i" i) in
  let names = List.init arrows init in
  let bnd = List.map (fun id -> Name id) names in
  let arg = List.map (fun id -> GTacVar id) names in
  let e = GTacFun (bnd, GTacPrm (ml, arg)) in
  let def = {
    tacdef_local = local;
    tacdef_mutable = false;
    tacdef_expr = e;
    tacdef_type = t;
  } in
  ignore (Lib.add_leaf id (inTacDef def))

let register_open ?(local = false) qid (params, def) =
  let kn =
    try Tac2env.locate_type qid
    with Not_found ->
      user_err ?loc:qid.CAst.loc (str "Unbound type " ++ pr_qualid qid)
  in
  let (tparams, t) = Tac2env.interp_type kn in
  let () = match t with
  | GTydOpn -> ()
  | GTydAlg _ | GTydRec _ | GTydDef _ ->
    user_err ?loc:qid.CAst.loc (str "Type " ++ pr_qualid qid ++ str " is not an open type")
  in
  let () =
    if not (Int.equal (List.length params) tparams) then
      Tac2intern.error_nparams_mismatch ?loc:qid.CAst.loc (List.length params) tparams
  in
  match def with
  | CTydOpn -> ()
  | CTydAlg def ->
    let intern_type t =
      let tpe = CTydDef (Some t) in
      let (_, ans) = intern_typedef Id.Map.empty (params, tpe) in
      match ans with
      | GTydDef (Some t) -> t
      | _ -> assert false
    in
    let map (id, tpe) =
      let tpe = List.map intern_type tpe in
      { edata_name = id; edata_args = tpe }
    in
    let def = List.map map def in
    let def = {
      typext_local = local;
      typext_type = kn;
      typext_prms = tparams;
      typext_expr = def;
    } in
    Lib.add_anonymous_leaf (inTypExt def)
  | CTydRec _ | CTydDef _ ->
    user_err ?loc:qid.CAst.loc (str "Extensions only accept inductive constructors")

let register_type ?local isrec types = match types with
| [qid, true, def] ->
  let () = if isrec then user_err ?loc:qid.CAst.loc (str "Extensions cannot be recursive") in
  register_open ?local qid def
| _ ->
  let map (qid, redef, def) =
    let () = if redef then
      user_err ?loc:qid.loc (str "Types can only be extended one by one")
    in
    (qualid_to_ident qid, def)
  in
  let types = List.map map types in
  register_typedef ?local isrec types

(** Parsing *)

type 'a token =
| TacTerm of string
| TacNonTerm of Name.t * 'a

type scope_rule =
| ScopeRule : (raw_tacexpr, _, 'a) Extend.symbol * ('a -> raw_tacexpr) -> scope_rule

type scope_interpretation = sexpr list -> scope_rule

let scope_table : scope_interpretation Id.Map.t ref = ref Id.Map.empty

let register_scope id s =
  scope_table := Id.Map.add id s !scope_table

module ParseToken =
struct

let loc_of_token = function
| SexprStr {loc} -> loc
| SexprInt {loc} -> loc
| SexprRec (loc, _, _) -> Some loc

let parse_scope = function
| SexprRec (_, {loc;v=Some id}, toks) ->
  if Id.Map.mem id !scope_table then
    Id.Map.find id !scope_table toks
  else
    CErrors.user_err ?loc (str "Unknown scope" ++ spc () ++ Names.Id.print id)
| SexprStr {v=str} ->
  let v_unit = CAst.make @@ CTacCst (AbsKn (Tuple 0)) in
  ScopeRule (Extend.Atoken (Tok.PIDENT (Some str)), (fun _ -> v_unit))
| tok ->
  let loc = loc_of_token tok in
  CErrors.user_err ?loc (str "Invalid parsing token")

let parse_token = function
| SexprStr {v=s} -> TacTerm s
| SexprRec (_, {v=na}, [tok]) ->
  let na = match na with None -> Anonymous | Some id -> Name id in
  let scope = parse_scope tok in
  TacNonTerm (na, scope)
| tok ->
  let loc = loc_of_token tok in
  CErrors.user_err ?loc (str "Invalid parsing token")

end

let parse_scope = ParseToken.parse_scope

type synext = {
  synext_tok : sexpr list;
  synext_exp : raw_tacexpr;
  synext_lev : int option;
  synext_loc : bool;
}

type krule =
| KRule :
  (raw_tacexpr, _, 'act, Loc.t -> raw_tacexpr) Extend.rule *
  ((Loc.t -> (Name.t * raw_tacexpr) list -> raw_tacexpr) -> 'act) -> krule

let rec get_rule (tok : scope_rule token list) : krule = match tok with
| [] -> KRule (Extend.Stop, fun k loc -> k loc [])
| TacNonTerm (na, ScopeRule (scope, inj)) :: tok ->
  let KRule (rule, act) = get_rule tok in
  let rule = Extend.Next (rule, scope) in
  let act k e = act (fun loc acc -> k loc ((na, inj e) :: acc)) in
  KRule (rule, act)
| TacTerm t :: tok ->
  let KRule (rule, act) = get_rule tok in
  let rule = Extend.Next (rule, Extend.Atoken (CLexer.terminal t)) in
  let act k _ = act k in
  KRule (rule, act)

let perform_notation syn st =
  let tok = List.rev_map ParseToken.parse_token syn.synext_tok in
  let KRule (rule, act) = get_rule tok in
  let mk loc args =
    let map (na, e) =
      ((CAst.make ?loc:e.loc @@ CPatVar na), e)
    in
    let bnd = List.map map args in
    CAst.make ~loc @@ CTacLet (false, bnd, syn.synext_exp)
  in
  let rule = Extend.Rule (rule, act mk) in
  let lev = match syn.synext_lev with
  | None -> None
  | Some lev -> Some (string_of_int lev)
  in
  let rule = (lev, None, [rule]) in
  ([Pcoq.ExtendRule (Pltac.tac2expr, None, (None, [rule]))], st)

let ltac2_notation =
  Pcoq.create_grammar_command "ltac2-notation" perform_notation

let cache_synext (_, syn) =
  Pcoq.extend_grammar_command ltac2_notation syn

let open_synext i (_, syn) =
  if Int.equal i 1 then Pcoq.extend_grammar_command ltac2_notation syn

let subst_synext (subst, syn) =
  let e = Tac2intern.subst_rawexpr subst syn.synext_exp in
  if e == syn.synext_exp then syn else { syn with synext_exp = e }

let classify_synext o =
  if o.synext_loc then Dispose else Substitute o

let inTac2Notation : synext -> obj =
  declare_object {(default_object "TAC2-NOTATION") with
     cache_function  = cache_synext;
     open_function   = open_synext;
     subst_function = subst_synext;
     classify_function = classify_synext}

type abbreviation = {
  abbr_body : raw_tacexpr;
}

let perform_abbreviation visibility ((sp, kn), abbr) =
  let () = Tac2env.push_ltac visibility sp (TacAlias kn) in
  Tac2env.define_alias kn abbr.abbr_body

let load_abbreviation i obj = perform_abbreviation (Until i) obj
let open_abbreviation i obj = perform_abbreviation (Exactly i) obj

let cache_abbreviation ((sp, kn), abbr) =
  let () = Tac2env.push_ltac (Until 1) sp (TacAlias kn) in
  Tac2env.define_alias kn abbr.abbr_body

let subst_abbreviation (subst, abbr) =
  let body' = subst_rawexpr subst abbr.abbr_body in
  if body' == abbr.abbr_body then abbr
  else { abbr_body = body' }

let classify_abbreviation o = Substitute o

let inTac2Abbreviation : abbreviation -> obj =
  declare_object {(default_object "TAC2-ABBREVIATION") with
     cache_function  = cache_abbreviation;
     load_function   = load_abbreviation;
     open_function   = open_abbreviation;
     subst_function = subst_abbreviation;
     classify_function = classify_abbreviation}

let register_notation ?(local = false) tkn lev body = match tkn, lev with
| [SexprRec (_, {loc;v=Some id}, [])], None ->
  (* Tactic abbreviation *)
  let () = check_lowercase CAst.(make ?loc id) in
  let body = Tac2intern.globalize Id.Set.empty body in
  let abbr = { abbr_body = body } in
  ignore (Lib.add_leaf id (inTac2Abbreviation abbr))
| _ ->
  (* Check that the tokens make sense *)
  let entries = List.map ParseToken.parse_token tkn in
  let fold accu tok = match tok with
  | TacTerm _ -> accu
  | TacNonTerm (Name id, _) -> Id.Set.add id accu
  | TacNonTerm (Anonymous, _) -> accu
  in
  let ids = List.fold_left fold Id.Set.empty entries in
  (* Globalize so that names are absolute *)
  let body = Tac2intern.globalize ids body in
  let lev = match lev with Some _ -> lev | None -> Some 5 in
  let ext = {
    synext_tok = tkn;
    synext_exp = body;
    synext_lev = lev;
    synext_loc = local;
  } in
  Lib.add_anonymous_leaf (inTac2Notation ext)

type redefinition = {
  redef_kn : ltac_constant;
  redef_body : glb_tacexpr;
}

let perform_redefinition (_, redef) =
  let kn = redef.redef_kn in
  let data = Tac2env.interp_global kn in
  let data = { data with Tac2env.gdata_expr = redef.redef_body } in
  Tac2env.define_global kn data

let subst_redefinition (subst, redef) =
  let kn = Mod_subst.subst_kn subst redef.redef_kn in
  let body = Tac2intern.subst_expr subst redef.redef_body in
  if kn == redef.redef_kn && body == redef.redef_body then redef
  else { redef_kn = kn; redef_body = body }

let classify_redefinition o = Substitute o

let inTac2Redefinition : redefinition -> obj =
  declare_object {(default_object "TAC2-REDEFINITION") with
     cache_function  = perform_redefinition;
     open_function   = (fun _ -> perform_redefinition);
     subst_function = subst_redefinition;
     classify_function = classify_redefinition }

let register_redefinition ?(local = false) qid e =
  let kn =
    try Tac2env.locate_ltac qid
    with Not_found -> user_err ?loc:qid.CAst.loc (str "Unknown tactic " ++ pr_qualid qid)
  in
  let kn = match kn with
  | TacConstant kn -> kn
  | TacAlias _ ->
    user_err ?loc:qid.CAst.loc (str "Cannot redefine syntactic abbreviations")
  in
  let data = Tac2env.interp_global kn in
  let () =
    if not (data.Tac2env.gdata_mutable) then
      user_err ?loc:qid.CAst.loc (str "The tactic " ++ pr_qualid qid ++ str " is not declared as mutable")
  in
  let (e, t) = intern ~strict:true e in
  let () =
    if not (is_value e) then
      user_err ?loc:qid.CAst.loc (str "Tactic definition must be a syntactical value")
  in
  let () =
    if not (Tac2intern.check_subtype t data.Tac2env.gdata_type) then
      let name = int_name () in
      user_err ?loc:qid.CAst.loc (str "Type " ++ pr_glbtype name (snd t) ++
        str " is not a subtype of " ++ pr_glbtype name (snd data.Tac2env.gdata_type))
  in
  let def = {
    redef_kn = kn;
    redef_body = e;
  } in
  Lib.add_anonymous_leaf (inTac2Redefinition def)

let perform_eval ~pstate e =
  let env = Global.env () in
  let (e, ty) = Tac2intern.intern ~strict:false e in
  let v = Tac2interp.interp Tac2interp.empty_environment e in
  let selector, proof =
    match pstate with
    | None ->
      let sigma = Evd.from_env env in
      let name, poly = Id.of_string "ltac2", false in
      Goal_select.SelectAll, Proof.start ~name ~poly sigma []
    | Some pstate ->
      Goal_select.get_default_goal_selector (),
      Proof_global.get_proof pstate
  in
  let v = match selector with
  | Goal_select.SelectNth i -> Proofview.tclFOCUS i i v
  | Goal_select.SelectList l -> Proofview.tclFOCUSLIST l v
  | Goal_select.SelectId id -> Proofview.tclFOCUSID id v
  | Goal_select.SelectAll -> v
  | Goal_select.SelectAlreadyFocused -> assert false (* TODO **)
  in
  let (proof, _, ans) = Proof.run_tactic (Global.env ()) v proof in
  let sigma = Proof.in_proof proof (fun sigma -> sigma) in
  let name = int_name () in
  Feedback.msg_notice (str "- : " ++ pr_glbtype name (snd ty)
    ++ spc () ++  str "=" ++ spc () ++
    Tac2print.pr_valexpr env sigma ans (snd ty))

(** Toplevel entries *)

let register_struct ?local str = match str with
| StrVal (mut, isrec, e) -> register_ltac ?local ~mut isrec e
| StrTyp (isrec, t) -> register_type ?local isrec t
| StrPrm (id, t, ml) -> register_primitive ?local id t ml
| StrSyn (tok, lev, e) -> register_notation ?local tok lev e
| StrMut (qid, e) -> register_redefinition ?local qid e

(** Toplevel exception *)

let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "print Ltac2 backtrace";
  Goptions.optkey = ["Ltac2"; "Backtrace"];
  Goptions.optread = (fun () -> !Tac2interp.print_ltac2_backtrace);
  Goptions.optwrite = (fun b -> Tac2interp.print_ltac2_backtrace := b);
}

let backtrace : backtrace Exninfo.t = Exninfo.make ()

let pr_frame = function
| FrAnon e -> str "Call {" ++ pr_glbexpr e ++ str "}"
| FrLtac kn ->
  str "Call " ++ Libnames.pr_qualid (Tac2env.shortest_qualid_of_ltac (TacConstant kn))
| FrPrim ml ->
  str "Prim <" ++ str ml.mltac_plugin ++ str ":" ++ str ml.mltac_tactic ++ str ">"
| FrExtn (tag, arg) ->
  let obj = Tac2env.interp_ml_object tag in
  str "Extn " ++ str (Tac2dyn.Arg.repr tag) ++ str ":" ++ spc () ++
    obj.Tac2env.ml_print (Global.env ()) arg

let () = register_handler begin function
| Tac2interp.LtacError (kn, args) ->
  let t_exn = KerName.make Tac2env.coq_prefix (Label.make "exn") in
  let v = Tac2ffi.of_open (kn, args) in
  let t = GTypRef (Other t_exn, []) in
  let c = Tac2print.pr_valexpr (Global.env ()) Evd.empty v t in
  hov 0 (str "Uncaught Ltac2 exception:" ++ spc () ++ hov 0 c)
| _ -> raise Unhandled
end

let () = ExplainErr.register_additional_error_info begin fun (e, info) ->
  if !Tac2interp.print_ltac2_backtrace then
    let bt = Exninfo.get info backtrace in
    let bt = match bt with
    | Some bt -> bt
    | None -> raise Exit
    in
    let bt =
      str "Backtrace:" ++ fnl () ++ prlist_with_sep fnl pr_frame bt ++ fnl ()
    in
    Some (Loc.tag @@ Some bt)
  else raise Exit
end

(** Printing *)

let print_ltac qid =
  if Tac2env.is_constructor qid then
    let kn =
      try Tac2env.locate_constructor qid
      with Not_found -> user_err ?loc:qid.CAst.loc (str "Unknown constructor " ++ pr_qualid qid)
    in
    let _ = Tac2env.interp_constructor kn in
    Feedback.msg_notice (hov 2 (str "Constructor" ++ spc () ++ str ":" ++ spc () ++ pr_qualid qid))
  else
    let kn =
      try Tac2env.locate_ltac qid
      with Not_found -> user_err ?loc:qid.CAst.loc (str "Unknown tactic " ++ pr_qualid qid)
    in
    match kn with
    | TacConstant kn ->
      let data = Tac2env.interp_global kn in
      let e = data.Tac2env.gdata_expr in
      let (_, t) = data.Tac2env.gdata_type in
      let name = int_name () in
      Feedback.msg_notice (
        hov 0 (
          hov 2 (pr_qualid qid ++ spc () ++ str ":" ++ spc () ++ pr_glbtype name t) ++ fnl () ++
          hov 2 (pr_qualid qid ++ spc () ++ str ":=" ++ spc () ++ pr_glbexpr e)
        )
      )
    | TacAlias kn ->
      Feedback.msg_notice (str "Alias to ...")

(** Calling tactics *)

let solve ~pstate default tac =
  let pstate, status = Proof_global.map_fold_proof_endline begin fun etac p ->
    let with_end_tac = if default then Some etac else None in
    let g = Goal_select.get_default_goal_selector () in
    let (p, status) = Pfedit.solve g None tac ?with_end_tac p in
    (* in case a strict subtree was completed,
       go back to the top of the prooftree *)
    let p = Proof.maximal_unfocus Vernacentries.command_focus p in
    p, status
  end pstate in
  if not status then Feedback.feedback Feedback.AddedAxiom;
  pstate

let call ~pstate ~default e =
  let loc = e.loc in
  let (e, t) = intern ~strict:false e in
  let () = check_unit ?loc t in
  let tac = Tac2interp.interp Tac2interp.empty_environment e in
  solve ~pstate default (Proofview.tclIGNORE tac)

(** Primitive algebraic types than can't be defined Coq-side *)

let register_prim_alg name params def =
  let id = Id.of_string name in
  let def = List.map (fun (cstr, tpe) -> (Id.of_string_soft cstr, tpe)) def in
  let getn (const, nonconst) (c, args) = match args with
  | [] -> (succ const, nonconst)
  | _ :: _ -> (const, succ nonconst)
  in
  let nconst, nnonconst = List.fold_left getn (0, 0) def in
  let alg = {
    galg_constructors = def;
    galg_nconst = nconst;
    galg_nnonconst = nnonconst;
  } in
  let def = (params, GTydAlg alg) in
  let def = { typdef_local = false; typdef_expr = def } in
  ignore (Lib.add_leaf id (inTypDef def))

let coq_def n = KerName.make Tac2env.coq_prefix (Label.make n)

let def_unit = {
  typdef_local = false;
  typdef_expr = 0, GTydDef (Some (GTypRef (Tuple 0, [])));
}

let t_list = coq_def "list"

let (f_register_constr_quotations, register_constr_quotations) = Hook.make ()

let cache_ltac2_init (_, ()) =
  Hook.get f_register_constr_quotations ()

let load_ltac2_init _ (_, ()) =
  Hook.get f_register_constr_quotations ()

let open_ltac2_init _ (_, ()) =
  Goptions.set_string_option_value_gen ["Default"; "Proof"; "Mode"] "Ltac2"

(** Dummy object that register global rules when Require is called *)
let inTac2Init : unit -> obj =
  declare_object {(default_object "TAC2-INIT") with
    cache_function = cache_ltac2_init;
    load_function = load_ltac2_init;
    open_function = open_ltac2_init;
  }

let _ = Mltop.declare_cache_obj begin fun () ->
  ignore (Lib.add_leaf (Id.of_string "unit") (inTypDef def_unit));
  register_prim_alg "list" 1 [
    ("[]", []);
    ("::", [GTypVar 0; GTypRef (Other t_list, [GTypVar 0])]);
  ];
  Lib.add_anonymous_leaf (inTac2Init ());
end "ltac2_plugin"
