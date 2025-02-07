(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
let ltac2_expr = Procq.Entry.make "ltac2_expr"
let tac2expr_in_env = Procq.Entry.make "tac2expr_in_env"

let q_ident = Procq.Entry.make "q_ident"
let q_bindings = Procq.Entry.make "q_bindings"
let q_with_bindings = Procq.Entry.make "q_with_bindings"
let q_intropattern = Procq.Entry.make "q_intropattern"
let q_intropatterns = Procq.Entry.make "q_intropatterns"
let q_destruction_arg = Procq.Entry.make "q_destruction_arg"
let q_induction_clause = Procq.Entry.make "q_induction_clause"
let q_conversion = Procq.Entry.make "q_conversion"
let q_orient = Procq.Entry.make "q_orient"
let q_rewriting = Procq.Entry.make "q_rewriting"
let q_clause = Procq.Entry.make "q_clause"
let q_dispatch = Procq.Entry.make "q_dispatch"
let q_occurrences = Procq.Entry.make "q_occurrences"
let q_reference = Procq.Entry.make "q_reference"
let q_strategy_flag = Procq.Entry.make "q_strategy_flag"
let q_constr_matching = Procq.Entry.make "q_constr_matching"
let q_goal_matching = Procq.Entry.make "q_goal_matching"
let q_hintdb = Procq.Entry.make "q_hintdb"
let q_move_location = Procq.Entry.make "q_move_location"
let q_pose = Procq.Entry.make "q_pose"
let q_assert = Procq.Entry.make "q_assert"
end

let () =
  let entries = [
    Procq.Entry.Any Pltac.ltac2_expr;
  ] in
  Procq.register_grammars_by_name "ltac2" entries

(** Tactic definition *)

type tacdef = {
  tacdef_local : bool;
  tacdef_mutable : bool;
  tacdef_expr : glb_tacexpr;
  tacdef_type : type_scheme;
  tacdef_deprecation : Deprecation.t option;
}

let define_tacdef ((_,kn), def) =
  let data = {
    Tac2env.gdata_expr = def.tacdef_expr;
    gdata_type = def.tacdef_type;
    gdata_mutable = def.tacdef_mutable;
    gdata_deprecation = def.tacdef_deprecation;
  } in
  Tac2env.define_global kn data

let push_tacdef visibility ((sp, kn), def) =
  if not def.tacdef_local then Tac2env.push_ltac visibility sp (TacConstant kn)

let load_tacdef i obj =
  push_tacdef (Until i) obj;
  define_tacdef obj

let open_tacdef i obj = push_tacdef (Exactly i) obj

(* Not sure if it's correct that we don't "open", do Until 1 and
   Exactly 1 have the same effect? *)
let cache_tacdef ((sp, kn), def as obj) =
  (* unconditional unlike push_tacdef *)
  Tac2env.push_ltac (Until 1) sp (TacConstant kn);
  define_tacdef obj

let subst_tacdef (subst, def) =
  let expr' = subst_expr subst def.tacdef_expr in
  let type' = subst_type_scheme subst def.tacdef_type in
  if expr' == def.tacdef_expr && type' == def.tacdef_type then def
  else { def with tacdef_expr = expr'; tacdef_type = type' }

let classify_tacdef o = Substitute

let inTacDef : Id.t -> tacdef -> obj =
  declare_named_object {(default_object "TAC2-DEFINITION") with
     cache_function  = cache_tacdef;
     load_function   = load_tacdef;
     open_function   = simple_open open_tacdef;
     subst_function = subst_tacdef;
     classify_function = classify_tacdef}

(** Type definition *)

type typdef = {
  typdef_local : bool;
  typdef_abstract : bool;
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
  let iter (warn, c, _) =
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
  let iter (warn, c, args) =
    let knc = change_kn_label kn c in
    let tag = if List.is_empty args then next constant else next nonconstant in
    let data = {
      Tac2env.cdata_prms = params;
      cdata_type = kn;
      cdata_args = args;
      cdata_indx = Some tag;
    } in
    Tac2env.define_constructor ?warn knc data
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
  let expr = def.typdef_expr in
  let expr = if def.typdef_abstract then fst expr, GTydDef None else expr in
  let () = if not def.typdef_local then push_typedef vs sp kn expr in
  define_typedef kn expr

let load_typdef i obj = perform_typdef (Until i) obj
let open_typdef i obj = perform_typdef (Exactly i) obj

let cache_typdef ((sp, kn), def) =
  let () = push_typedef (Until 1) sp kn def.typdef_expr in
  define_typedef kn def.typdef_expr

let subst_typdef (subst, def) =
  let expr' = subst_quant_typedef subst def.typdef_expr in
  if expr' == def.typdef_expr then def else { def with typdef_expr = expr' }

let classify_typdef o = Substitute

let inTypDef : Id.t -> typdef -> obj =
  declare_named_object {(default_object "TAC2-TYPE-DEFINITION") with
     cache_function  = cache_typdef;
     load_function   = load_typdef;
     open_function   = simple_open open_typdef;
     subst_function = subst_typdef;
     classify_function = classify_typdef}

(** Type extension *)

type extension_data = {
  edata_warn : UserWarn.t option;
  edata_name : Id.t;
  edata_args : int glb_typexpr list;
}

type typext = {
  typext_local : bool;
  typext_prms : int;
  typext_type : type_constant;
  typext_expr : extension_data list;
}

let push_typext vis prefix def =
  let iter data =
    let spc = Libnames.make_path prefix.obj_dir data.edata_name in
    let knc = KerName.make prefix.obj_mp (Label.of_id data.edata_name) in
    Tac2env.push_constructor vis spc knc
  in
  List.iter iter def.typext_expr

let define_typext mp def =
  let iter data =
    let knc = KerName.make mp (Label.of_id data.edata_name) in
    let cdata = {
      Tac2env.cdata_prms = def.typext_prms;
      cdata_type = def.typext_type;
      cdata_args = data.edata_args;
      cdata_indx = None;
    } in
    Tac2env.define_constructor ?warn:data.edata_warn knc cdata
  in
  List.iter iter def.typext_expr

let cache_typext (prefix, def) =
  let () = define_typext prefix.obj_mp def in
  push_typext (Until 1) prefix def

let perform_typext vs (prefix, def) =
  let () = if not def.typext_local then push_typext vs prefix def in
  define_typext prefix.obj_mp def

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

let classify_typext o = Substitute

let inTypExt : typext -> obj =
  declare_named_object_gen {(default_object "TAC2-TYPE-EXTENSION") with
     cache_function  = cache_typext;
     load_function   = load_typext;
     open_function   = simple_open open_typext;
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
| CPatAtm _ | CPatVar _ | CPatRef _ | CPatOr _ | CPatAs _ | CPatRecord _ -> pat, None

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

let check_value ?loc e =
  if not (is_value e) then
    user_err ?loc
      (str "Tactic definition must be a syntactical value." ++ spc() ++
       str "Consider using a thunk.")

let check_ltac_exists {loc;v=id} =
  let kn = Lib.make_kn id in
  let exists =
    try let _ = Tac2env.interp_global kn in true with Not_found -> false
  in
  if exists then
    user_err ?loc (str "Tactic " ++ Names.Id.print id ++ str " already exists")


let register_ltac ?deprecation ?(local = false) ?(mut = false) isrec tactics =
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
  let map (lid, ({loc=eloc} as e)) =
    let (e, t) = intern ~strict:true [] e in
    let () = check_value ?loc:eloc e in
    let () = check_ltac_exists lid in
    (lid.v, e, t)
  in
  let defs = List.map map tactics in
  let iter (id, e, t) =
    let def = {
      tacdef_local = local;
      tacdef_mutable = mut;
      tacdef_expr = e;
      tacdef_type = t;
      tacdef_deprecation = deprecation;
    } in
    Lib.add_leaf (inTacDef id def)
  in
  List.iter iter defs

let qualid_to_ident qid =
  if qualid_is_ident qid then CAst.make ?loc:qid.CAst.loc @@ qualid_basename qid
  else user_err ?loc:qid.CAst.loc (str "Identifier expected")

let register_typedef ?(local = false) ?(abstract=false) isrec types =
  let same_name ({v=id1}, _) ({v=id2}, _) = Id.equal id1 id2 in
  let () = match List.duplicates same_name types with
  | [] -> ()
  | ({loc;v=id}, _) :: _ ->
    user_err ?loc (str "Multiple definition of the type name " ++ Id.print id)
  in
  let () =
    let check_existing_type ({v=id},_) =
      let (_, kn) = Lib.make_foname id in
      try let _ = Tac2env.interp_type kn in
        user_err (str "Multiple definition of the type name " ++ Id.print id)
      with Not_found -> ()
    in
    List.iter check_existing_type types
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
      let same_name (_, id1, _) (_, id2, _) = Id.equal id1 id2 in
      let () = match List.duplicates same_name cs with
      | [] -> ()
      | (_, id, _) :: _ ->
        user_err (str "Multiple definitions of the constructor " ++ Id.print id)
      in
      let () =
        let check_uppercase_ident (_,id,_) =
          if not (Tac2env.is_constructor_id id)
          then user_err (str "Constructor name should start with an uppercase letter " ++ Id.print id)
        in
        List.iter check_uppercase_ident cs
      in
      let () =
        let check_existing_ctor (_, id, _) =
          let (_, kn) = Lib.make_foname id in
          try let _ = Tac2env.interp_constructor kn in
            user_err (str "Constructor already defined in this module " ++ Id.print id)
          with Not_found -> ()
        in
        List.iter check_existing_ctor cs
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
                       str " cannot be recursive");
      if abstract then
        (* Naive implementation allows to use and match on already
           existing constructors but not declare new ones outside the
           type's origin module. Not sure that's what we want so
           forbid it for now. *)
        user_err ?loc (str "Open types currently do not support #[abstract].")
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
      typdef_abstract = abstract;
      typdef_expr = intern_typedef self def;
    } in
    (id, typdef)
  in
  let types = List.map map types in
  let iter (id, def) = Lib.add_leaf (inTypDef id def) in
  List.iter iter types

let register_primitive ?deprecation ?(local = false) ({loc;v=id} as lid) t ml =
  let () = check_ltac_exists lid in
  let t = intern_open_type t in
  let () =
    try let _ = Tac2env.interp_primitive ml in () with Not_found ->
      user_err ?loc (str "Unregistered primitive " ++
        quote (str ml.mltac_plugin) ++ spc () ++ quote (str ml.mltac_tactic))
  in
  let e = GTacPrm ml in
  let def = {
    tacdef_local = local;
    tacdef_mutable = false;
    tacdef_expr = e;
    tacdef_type = t;
    tacdef_deprecation = deprecation;
  } in
  Lib.add_leaf (inTacDef id def)

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
    let () =
      let same_name (_, id1, _) (_, id2, _) = Id.equal id1 id2 in
      let () = match List.duplicates same_name def with
        | [] -> ()
        | (_, id, _) :: _ ->
          user_err (str "Multiple definitions of the constructor " ++ Id.print id)
      in
      let check_existing_ctor (_, id, _) =
          let (_, kn) = Lib.make_foname id in
          try let _ = Tac2env.interp_constructor kn in
            user_err (str "Constructor already defined in this module " ++ Id.print id)
          with Not_found -> ()
      in
      let () = List.iter check_existing_ctor def in
      ()
    in
    let intern_type t =
      let tpe = CTydDef (Some t) in
      let (_, ans) = intern_typedef Id.Map.empty (params, tpe) in
      match ans with
      | GTydDef (Some t) -> t
      | _ -> assert false
    in
    let map (atts, id, tpe) =
      if not (Tac2env.is_constructor_id id)
      then user_err (str "Constructor name should start with an uppercase letter " ++ Id.print id) ;
      let warn = Attributes.parse Attributes.user_warns atts in
      let tpe = List.map intern_type tpe in
      { edata_warn = warn; edata_name = id; edata_args = tpe }
    in
    let def = List.map map def in
    let def = {
      typext_local = local;
      typext_type = kn;
      typext_prms = tparams;
      typext_expr = def;
    } in
    Lib.add_leaf (inTypExt def)
  | CTydRec _ | CTydDef _ ->
    user_err ?loc:qid.CAst.loc (str "Extensions only accept inductive constructors")

let register_type ?local ?abstract isrec types = match types with
| [qid, true, def] ->
  let () = if isrec then user_err ?loc:qid.CAst.loc (str "Extensions cannot be recursive.") in
  let () = if Option.default false abstract
    then user_err ?loc:qid.loc (str "Extensions cannot be abstract.")
  in
  register_open ?local qid def
| _ ->
  let map (qid, redef, def) =
    let () = if redef then
      user_err ?loc:qid.loc (str "Types can only be extended one by one")
    in
    (qualid_to_ident qid, def)
  in
  let types = List.map map types in
  register_typedef ?local ?abstract isrec types

(** Parsing *)

type 'a token =
| TacTerm of string
| TacNonTerm of Name.t * 'a

type scope_rule =
| ScopeRule : (raw_tacexpr, _, 'a) Procq.Symbol.t * ('a -> raw_tacexpr) -> scope_rule

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
  ScopeRule (Procq.Symbol.token (Tok.PIDENT (Some str)), (fun _ -> v_unit))
| tok ->
  let loc = loc_of_token tok in
  CErrors.user_err ?loc (str "Invalid parsing token")

let parse_token = function
| SexprStr {v=s} -> TacTerm s
| SexprRec (_, na, [tok]) ->
  let na = match na.CAst.v with
  | None -> Anonymous
  | Some id ->
    let () = check_lowercase (CAst.make ?loc:na.CAst.loc id) in
    Name id
  in
  let scope = parse_scope tok in
  TacNonTerm (na, scope)
| tok ->
  let loc = loc_of_token tok in
  CErrors.user_err ?loc (str "Invalid parsing token")

let rec print_scope = function
| SexprStr s -> str s.CAst.v
| SexprInt i -> int i.CAst.v
| SexprRec (_, {v=na}, []) -> Option.cata Id.print (str "_") na
| SexprRec (_, {v=na}, e) ->
  Option.cata Id.print (str "_") na ++ str "(" ++ pr_sequence print_scope e ++ str ")"

let print_token = function
| SexprStr {v=s} -> quote (str s)
| SexprRec (_, {v=na}, [tok]) -> print_scope tok
| _ -> assert false

end

let parse_scope = ParseToken.parse_scope

type synext = {
  synext_kn : KerName.t;
  synext_tok : sexpr list;
  synext_lev : int;
  synext_loc : bool;
  synext_depr : Deprecation.t option;
}

type krule =
| KRule :
  (raw_tacexpr, _, 'act, Loc.t -> raw_tacexpr) Procq.Rule.t *
  ((Loc.t -> (Name.t * raw_tacexpr) list -> raw_tacexpr) -> 'act) -> krule

let rec get_rule (tok : scope_rule token list) : krule = match tok with
| [] -> KRule (Procq.Rule.stop, fun k loc -> k loc [])
| TacNonTerm (na, ScopeRule (scope, inj)) :: tok ->
  let KRule (rule, act) = get_rule tok in
  let rule = Procq.Rule.next rule scope in
  let act k e = act (fun loc acc -> k loc ((na, inj e) :: acc)) in
  KRule (rule, act)
| TacTerm t :: tok ->
  let KRule (rule, act) = get_rule tok in
  let rule = Procq.(Rule.next rule (Symbol.token (Procq.terminal t))) in
  let act k _ = act k in
  KRule (rule, act)

let deprecated_ltac2_notation =
  Deprecation.create_warning
    ~object_name:"Ltac2 notation"
    ~warning_name_if_no_since:"deprecated-ltac2-notation"
    (fun (toks : sexpr list) -> pr_sequence ParseToken.print_token toks)

(* This is a hack to preserve the level 4 entry which is initially empty. The
   grammar engine has the great idea to silently delete empty levels on rule
   removal, so we have to work around this using the Procq API.
   FIXME: we should really keep those levels around instead. *)
let get_reinit = function
| 4 -> Some (Gramlib.Gramext.LeftA, Gramlib.Gramext.After "5")
| _ -> None

let perform_notation syn st =
  let tok = List.rev_map ParseToken.parse_token syn.synext_tok in
  let KRule (rule, act) = get_rule tok in
  let mk loc args =
    let () = match syn.synext_depr with
    | None -> ()
    | Some depr -> deprecated_ltac2_notation ~loc (syn.synext_tok, depr)
    in
    let map (na, e) =
      ((CAst.make ?loc:e.loc na), e)
    in
    let bnd = List.map map args in
    CAst.make ~loc @@ CTacSyn (bnd, syn.synext_kn)
  in
  let rule = Procq.Production.make rule (act mk) in
  let pos = Some (string_of_int syn.synext_lev) in
  let rule = Procq.Reuse (pos, [rule]) in
  match get_reinit syn.synext_lev with
  | None ->
    ([Procq.ExtendRule (Pltac.ltac2_expr, rule)], st)
  | Some reinit ->
    ([Procq.ExtendRuleReinit (Pltac.ltac2_expr, reinit, rule)], st)

let ltac2_notation =
  Procq.create_grammar_command "ltac2-notation" { gext_fun = perform_notation; gext_eq = (==) (* FIXME *) }

let cache_synext syn =
  Procq.extend_grammar_command ltac2_notation syn

let open_synext i syn =
  if Int.equal i 1 then Procq.extend_grammar_command ltac2_notation syn

let subst_synext (subst, syn) =
  let kn = Mod_subst.subst_kn subst syn.synext_kn in
  if kn == syn.synext_kn then syn
  else { syn with synext_kn = kn }

let classify_synext o =
  if o.synext_loc then Dispose else Substitute

let ltac2_notation_cat = Libobject.create_category "ltac2.notations"

let inTac2Notation : synext -> obj =
  declare_object {(default_object "TAC2-NOTATION") with
     object_stage = Summary.Stage.Synterp;
     cache_function  = cache_synext;
     open_function   = simple_open ~cat:ltac2_notation_cat open_synext;
     subst_function = subst_synext;
     classify_function = classify_synext}

let cache_synext_interp (local,kn,tac) =
  Tac2env.define_notation kn tac

let open_synext_interp i o =
  if Int.equal i 1 then cache_synext_interp o

let subst_notation_data subst = function
  | Tac2env.UntypedNota body as n ->
    let body' = Tac2intern.subst_rawexpr subst body in
    if body' == body then n else UntypedNota body'
  | TypedNota { nota_prms=prms; nota_argtys=argtys; nota_ty=ty; nota_body=body } as n ->
    let body' = Tac2intern.subst_expr subst body in
    let argtys' = Id.Map.Smart.map (subst_type subst) argtys in
    let ty' = subst_type subst ty in
    if body' == body && argtys' == argtys && ty' == ty then n
    else TypedNota {nota_body=body'; nota_argtys=argtys'; nota_ty=ty'; nota_prms=prms}

let subst_synext_interp (subst, (local,kn,tac as o)) =
  let tac' = subst_notation_data subst tac in
  let kn' = Mod_subst.subst_kn subst kn in
  if kn' == kn && tac' == tac then o else
  (local, kn', tac')

let classify_synext_interp (local,_,_) =
  if local then Dispose else Substitute

let inTac2NotationInterp : (bool*KerName.t*Tac2env.notation_data) -> obj =
  declare_object {(default_object "TAC2-NOTATION-INTERP") with
     cache_function  = cache_synext_interp;
     open_function   = simple_open ~cat:ltac2_notation_cat open_synext_interp;
     subst_function = subst_synext_interp;
     classify_function = classify_synext_interp}

type abbreviation = {
  abbr_body : raw_tacexpr;
  abbr_depr : Deprecation.t option;
}

let perform_abbreviation visibility ((sp, kn), abbr) =
  let () = Tac2env.push_ltac visibility sp (TacAlias kn) in
  Tac2env.define_alias ?deprecation:abbr.abbr_depr kn abbr.abbr_body

let load_abbreviation i obj = perform_abbreviation (Until i) obj
let open_abbreviation i obj = perform_abbreviation (Exactly i) obj

let cache_abbreviation ((sp, kn), abbr) =
  let () = Tac2env.push_ltac (Until 1) sp (TacAlias kn) in
  Tac2env.define_alias ?deprecation:abbr.abbr_depr kn abbr.abbr_body

let subst_abbreviation (subst, abbr) =
  let body' = subst_rawexpr subst abbr.abbr_body in
  if body' == abbr.abbr_body then abbr
  else { abbr_body = body'; abbr_depr = abbr.abbr_depr }

let classify_abbreviation o = Substitute

let inTac2Abbreviation : Id.t -> abbreviation -> obj =
  declare_named_object {(default_object "TAC2-ABBREVIATION") with
     cache_function  = cache_abbreviation;
     load_function   = load_abbreviation;
     open_function   = simple_open ~cat:ltac2_notation_cat open_abbreviation;
     subst_function = subst_abbreviation;
     classify_function = classify_abbreviation}

let rec string_of_scope = function
| SexprStr s -> Printf.sprintf "str(%s)" s.CAst.v
| SexprInt i -> Printf.sprintf "int(%i)" i.CAst.v
| SexprRec (_, {v=na}, []) -> Option.cata Id.to_string "_" na
| SexprRec (_, {v=na}, e) ->
  Printf.sprintf "%s(%s)" (Option.cata Id.to_string "_" na) (String.concat " " (List.map string_of_scope e))

let string_of_token = function
| SexprStr {v=s} -> Printf.sprintf "str(%s)" s
| SexprRec (_, {v=na}, [tok]) -> string_of_scope tok
| _ -> assert false

let make_fresh_key tokens =
  let prods = String.concat "_" (List.map string_of_token tokens) in
  (* We embed the hash of the kernel name in the label so that the identifier
      should be mostly unique. This ensures that including two modules
      together won't confuse the corresponding labels. *)
  let hash = (ModPath.hash (Lib.current_mp ())) land 0x7FFFFFFF in
  let lbl = Id.of_string_soft (Printf.sprintf "%s_%08X" prods hash) in
  Lib.make_kn lbl

type notation_interpretation_data =
| Abbreviation of Id.t * Deprecation.t option * raw_tacexpr
| Synext of bool * KerName.t * Id.Set.t * raw_tacexpr

let register_notation atts tkn lev body =
  let deprecation, local = Attributes.(parse Notations.(deprecation ++ locality)) atts in
  let local = Option.default false local in
  match tkn, lev with
  | [SexprRec (_, {loc;v=Some id}, [])], None ->
    (* Tactic abbreviation *)
    let () = check_lowercase CAst.(make ?loc id) in
    Abbreviation(id, deprecation, body)
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
    let lev = match lev with
    | Some n ->
      let () =
        if n < 0 || n > 6 then
          user_err (str "Notation levels must range between 0 and 6")
      in
      n
    | None -> 5
    in
    let key = make_fresh_key tkn in
    let ext = {
      synext_kn = key;
      synext_tok = tkn;
      synext_lev = lev;
      synext_loc = local;
      synext_depr = deprecation;
    } in
    Lib.add_leaf (inTac2Notation ext);
    Synext (local,key,ids,body)

let register_notation_interpretation = function
  | Abbreviation (id, deprecation, body) ->
    let body = Tac2intern.globalize Id.Set.empty body in
    let abbr = { abbr_body = body; abbr_depr = deprecation } in
    Lib.add_leaf (inTac2Abbreviation id abbr)
  | Synext (local,kn,ids,body) ->
    let data = intern_notation_data ids body in
    Lib.add_leaf (inTac2NotationInterp (local,kn,data))

type redefinition = {
  redef_kn : ltac_constant;
  redef_body : glb_tacexpr;
  redef_old : Id.t option;
}

let perform_redefinition redef =
  let kn = redef.redef_kn in
  let data = Tac2env.interp_global kn in
  let body = match redef.redef_old with
  | None -> redef.redef_body
  | Some id ->
    (* Rebind the old value with a let-binding *)
    GTacLet (false, [Name id, data.Tac2env.gdata_expr], redef.redef_body)
  in
  let data = { data with Tac2env.gdata_expr = body } in
  Tac2env.define_global kn data

let subst_redefinition (subst, redef) =
  let kn = Mod_subst.subst_kn subst redef.redef_kn in
  let body = Tac2intern.subst_expr subst redef.redef_body in
  if kn == redef.redef_kn && body == redef.redef_body then redef
  else { redef_kn = kn; redef_body = body; redef_old = redef.redef_old }

let classify_redefinition o = Substitute

let inTac2Redefinition : redefinition -> obj =
  declare_object
    {(default_object "TAC2-REDEFINITION") with
     cache_function  = perform_redefinition;
     open_function   = simple_open (fun _ -> perform_redefinition);
     subst_function = subst_redefinition;
     classify_function = classify_redefinition;
    }

let register_redefinition qid old ({loc=eloc} as e) =
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
  let ctx = match old with
  | None -> []
  | Some { CAst.v = id } -> [id, data.Tac2env.gdata_type]
  in
  let (e, t) = intern ~strict:true ctx e in
  let () = check_value ?loc:eloc e in
  let () =
    if not (Tac2intern.check_subtype t data.Tac2env.gdata_type) then
      let name = int_name () in
      user_err ?loc:qid.CAst.loc (str "Type " ++ pr_glbtype name (snd t) ++
        str " is not a subtype of " ++ pr_glbtype name (snd data.Tac2env.gdata_type))
  in
  let old = Option.map (fun { CAst.v = id } -> id) old in
  let def = {
    redef_kn = kn;
    redef_body = e;
    redef_old = old;
  } in
  Lib.add_leaf (inTac2Redefinition def)

let perform_eval ~pstate e =
  let env = Global.env () in
  let (e, ty) = Tac2intern.intern ~strict:false [] e in
  let v = Tac2interp.interp Tac2interp.empty_environment e in
  let proof =
    match pstate with
    | None ->
      let sigma = Evd.from_env env in
      let name, poly = Id.of_string "ltac2", false in
      Proof.start ~name ~poly sigma []
    | Some pstate ->
      Declare.Proof.get pstate
  in
  let (proof, _, ans) = Proof.run_tactic (Global.env ()) v proof in
  let { Proof.sigma } = Proof.data proof in
  let name = int_name () in
  Feedback.msg_notice (str "- : " ++ pr_glbtype name (snd ty)
    ++ spc () ++  str "=" ++ spc () ++
    Tac2print.pr_valexpr env sigma ans (snd ty))

(** Toplevel entries *)

let warn_modtype = CWarnings.create ~name:"ltac2-in-modtype" ~category:CWarnings.CoreCategories.ltac2 ~default:AsError
    Pp.(fun what -> strbrk "Ltac2 " ++ str what ++ strbrk " should not be defined inside module types: functor application to arguments of this module type will be unchecked")


let check_modtype what =
  if Lib.is_modtype ()
  then warn_modtype what

let abstract_att = Attributes.bool_attribute ~name:"abstract"

let register_struct atts str = match str with
| StrVal (mut, isrec, e) ->
  check_modtype "definitions";
  let deprecation, local = Attributes.(parse Notations.(deprecation ++ locality)) atts in
  register_ltac ?deprecation ?local ~mut isrec e
| StrTyp (isrec, t) ->
  check_modtype "types";
  let local, abstract = Attributes.(parse Notations.(locality ++ abstract_att)) atts in
  register_type ?local ?abstract isrec t
| StrPrm (id, t, ml) ->
  check_modtype "externals";
  let deprecation, local = Attributes.(parse Notations.(deprecation ++ locality)) atts in
  register_primitive ?deprecation ?local id t ml
| StrMut (qid, old, e) ->
  let () = Attributes.unsupported_attributes atts in
  register_redefinition qid old e

(** Toplevel exception *)

let pr_frame = function
| FrAnon e -> str "Call {" ++ pr_glbexpr ~avoid:Id.Set.empty e ++ str "}"
| FrLtac kn ->
  str "Call " ++ pr_tacref Id.Set.empty kn
| FrPrim ml ->
  str "Prim <" ++ str ml.mltac_plugin ++ str ":" ++ str ml.mltac_tactic ++ str ">"
| FrExtn (tag, arg) ->
  let obj = Tac2env.interp_ml_object tag in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  str "Extn " ++ str (Tac2dyn.Arg.repr tag) ++ str ":" ++ spc () ++
    obj.Tac2env.ml_print env sigma arg

let () = register_handler begin function
| Tac2interp.LtacError (kn, args) ->
  let t_exn = KerName.make Tac2env.rocq_prefix (Label.make "exn") in
  let v = Tac2ffi.of_open (kn, args) in
  let t = GTypRef (Other t_exn, []) in
  let c = Tac2print.pr_valexpr (Global.env ()) Evd.empty v t in
  Some (hov 0 (str "Uncaught Ltac2 exception:" ++ spc () ++ hov 0 c))
| _ -> None
end

let () = CErrors.register_additional_error_info begin fun info ->
  if !Tac2bt.print_ltac2_backtrace then
    let bt = Exninfo.get info Tac2bt.backtrace in
    match bt with
    | None -> None
    | Some bt ->
      let bt = List.rev bt in
      let bt =
        str "Backtrace:" ++ fnl () ++ prlist_with_sep fnl pr_frame bt ++ fnl ()
      in
      Some bt
  else None
end

(** Printing *)

let print_constant ~print_def qid ?info data =
  let e = data.Tac2env.gdata_expr in
  let (_, t) = data.Tac2env.gdata_type in
  let name = int_name () in
  let def = if print_def then
      fnl () ++ hov 2
        (pr_qualid qid ++ spc () ++ str ":=" ++ spc () ++ pr_glbexpr ~avoid:Id.Set.empty e)
    else mt()
  in
  let info = match info with
    | None -> mt()
    | Some info -> fnl() ++ fnl() ++ hov 2 (str "Compiled as" ++ spc() ++ str info.Tac2env.source)
  in
  hov 0 (
    hov 2 (pr_qualid qid ++ spc () ++ str ":" ++ spc () ++ pr_glbtype name t) ++ def ++ info
  )

let print_type ~print_def qid kn =
  let nparams, data = Tac2env.interp_type kn in
  let name = int_name () in
  let params = List.init nparams (fun i -> GTypVar i) in
  let ty = match params with
    | [] -> pr_qualid qid
    | [t] -> pr_glbtype name t ++ spc() ++ pr_qualid qid
    | _ -> surround (prlist_with_sep pr_comma (pr_glbtype name) params) ++ spc() ++ pr_qualid qid
  in
  let def = if not print_def || (match data with GTydDef None -> true | _ -> false)
    then mt()
    else spc() ++ str ":= " ++ match data with
      | GTydDef None -> assert false
      | GTydDef (Some t) -> pr_glbtype name t
      | GTydAlg { galg_constructors = [] } -> str "[ ]"
      | GTydAlg { galg_constructors = ctors } ->
        let pr_ctor (_, id, argtys) =
          (* XXX print warning atrtribute? *)
          hov 0
            (Id.print id ++ if CList.is_empty argtys then mt()
             else spc() ++surround (prlist_with_sep pr_comma (pr_glbtype name) argtys))
        in
        hv 0 (str "[ " ++ prlist_with_sep (fun () -> spc() ++ str "| ") pr_ctor ctors ++ str " ]")
      | GTydRec fields ->
        let pr_field (id, ismut, t) =
          hov 0 ((if ismut then str "mutable " else mt()) ++ Id.print id
                 ++ spc() ++ str ": " ++ pr_glbtype name t) ++ str ";"
        in
        hv 2 (str "{ " ++ prlist_with_sep spc pr_field fields ++ str " }")
      | GTydOpn ->
        let ctors = KNmap.bindings (Tac2env.find_all_constructors_in_type kn) in
        if CList.is_empty ctors then str "[ .. ]"
        else
          let pr_ctor (ckn, cdata) =
            let argtys = cdata.Tac2env.cdata_args in
            hov 0
              (Tac2print.pr_constructor ckn ++ if CList.is_empty argtys then mt()
               else spc() ++surround (prlist_with_sep pr_comma (pr_glbtype name) argtys))
          in
          hov 0 (str "[ .." ++ spc() ++ str "| "
                 ++ prlist_with_sep (fun () -> spc() ++ str "| ") pr_ctor ctors
                   ++ str " ]")
  in
  hov 2 (ty ++ def)

let print_tacref ~print_def qid = function
  | TacConstant kn ->
    let data = Tac2env.interp_global kn in
    let info = Option.map fst (Tac2env.get_compiled_global kn) in
    print_constant ~print_def qid data ?info
  | TacAlias kn ->
    let { Tac2env.alias_body = body } = Tac2env.interp_alias kn in
    str "Notation" ++ spc() ++ pr_qualid qid ++ str " :=" ++ spc()
    ++ Tac2print.pr_rawexpr_gen E5 ~avoid:Id.Set.empty body

let print_constructor qid kn =
  let cdata = Tac2env.interp_constructor kn in
  let name = int_name () in
  let ty = GTypRef (Other cdata.cdata_type, List.init cdata.cdata_prms (fun i -> GTypVar i)) in
  let ty = List.fold_right (fun arg ty -> GTypArrow (arg,ty)) cdata.cdata_args ty in
  pr_qualid qid ++ spc() ++ str ": " ++ Tac2print.pr_glbtype name ty

let locatable_ltac2 = "Ltac2"

type ltac2_object =
  | Type of type_constant
  | Constructor of ltac_constructor
  | TacRef of tacref

let locate_object qid =
  try Type (Tac2env.locate_type qid)
  with Not_found ->
  try Constructor (Tac2env.locate_constructor qid)
  with Not_found ->
  TacRef (Tac2env.locate_ltac qid)

let locate_all_object qid =
  let open Tac2env in
  (List.map (fun x -> Type x) (locate_extended_all_type qid))
  @ (List.map (fun x -> Constructor x) (locate_extended_all_constructor qid))
  @ (List.map (fun x -> TacRef x) (locate_extended_all_ltac qid))

let shortest_qualid_of_object = function
  | Type kn -> Tac2env.shortest_qualid_of_type kn
  | Constructor kn -> Tac2env.shortest_qualid_of_constructor kn
  | TacRef kn -> Tac2env.shortest_qualid_of_ltac Id.Set.empty kn

let path_of_object = function
  | Type kn -> Tac2env.path_of_type kn
  | Constructor kn -> Tac2env.path_of_constructor kn
  | TacRef kn -> Tac2env.path_of_ltac kn

let print_object ~print_def qid = function
  | Type kn -> str "Ltac2 Type" ++ spc() ++ print_type ~print_def qid kn
  | Constructor kn -> str "Ltac2 constructor" ++ spc() ++ print_constructor qid kn
  | TacRef kn -> str "Ltac2 " ++ print_tacref ~print_def qid kn

let () =
  let open Prettyp in
  let locate qid = try Some (qid, locate_object qid) with Not_found -> None in
  let locate_all qid = List.map (fun x -> qid, x) (locate_all_object qid) in
  let shortest_qualid (_,kn) = shortest_qualid_of_object kn in
  let name (_,kn) =
    let hdr = match kn with
      | Type _ -> str "Ltac2 Type"
      | TacRef (TacConstant _) -> str "Ltac2"
      | TacRef (TacAlias _) -> str "Ltac2 Notation"
      | Constructor _ -> str "Ltac2 Constructor"
    in
    hdr ++ spc () ++ pr_path (path_of_object kn)
  in
  let print (qid,kn) = print_object ~print_def:true qid kn in
  let about (qid,kn) = print_object ~print_def:false qid kn in
  register_locatable locatable_ltac2 {
    locate;
    locate_all;
    shortest_qualid;
    name;
    print;
    about;
  }

let print_located_tactic qid =
  Feedback.msg_notice (Prettyp.print_located_other (Global.env ()) locatable_ltac2 qid)

let print_ltac2 qid =
  if Tac2env.is_constructor qid then
    let kn =
      try Tac2env.locate_constructor qid
      with Not_found -> user_err ?loc:qid.CAst.loc (str "Unknown constructor " ++ pr_qualid qid)
    in
    Feedback.msg_notice (print_constructor qid kn)
  else
    let kn =
      try Tac2env.locate_ltac qid
      with Not_found -> user_err ?loc:qid.CAst.loc (str "Unknown tactic " ++ pr_qualid qid)
    in
    Feedback.msg_notice (print_tacref ~print_def:true qid kn)

let print_ltac2_type qid =
  match Tac2env.locate_type qid with
  | exception Not_found -> user_err ?loc:qid.CAst.loc (str "Unknown Ltac2 type " ++ pr_qualid qid)
  | kn ->
    Feedback.msg_notice (print_type ~print_def:true qid kn)

let print_signatures () =
  let entries = KNmap.bindings (Tac2env.globals ()) in
  let sort (kn1, _) (kn2, _) = KerName.compare kn1 kn2 in
  let entries = List.sort sort entries in
  let map (kn, entry) =
    let qid =
      try Some (Tac2env.shortest_qualid_of_ltac Id.Set.empty (TacConstant kn))
      with Not_found -> None
    in
    match qid with
    | None -> None
    | Some qid -> Some (qid, entry)
  in
  let entries = List.map_filter map entries in
  let pr_entry (qid, data) =
    hov 2 (print_constant ~print_def:false qid data)
  in
  Feedback.msg_notice (prlist_with_sep fnl pr_entry entries)

let typecheck_expr e =
  let e, (_,t) = Tac2intern.intern ~strict:false [] e in
  let name = int_name() in
  let pp =
    pr_glbexpr_gen E5 ~avoid:Id.Set.empty e ++ spc() ++
    str ":" ++ spc() ++ pr_glbtype name t
  in
  Feedback.msg_notice pp

let globalize_expr e =
  let avoid = Id.Set.empty in
  let e = Tac2intern.debug_globalize_allow_ext avoid e in
  Feedback.msg_notice (Tac2print.pr_rawexpr_gen E5 ~avoid e)

(** Calling tactics *)

let ltac2_interp e =
  let loc = e.loc in
  let (e, t) = intern ~strict:false [] e in
  let () = check_unit ?loc t in
  let tac = Tac2interp.interp Tac2interp.empty_environment e in
  Proofview.tclIGNORE tac

let ComTactic.Interpreter ltac2_interp = ComTactic.register_tactic_interpreter "rocq-runtime.plugins.ltac2" ltac2_interp

let call ~pstate g ~with_end_tac tac =
  let g = Option.default (Goal_select.get_default_goal_selector()) g in
  ComTactic.solve ~pstate ~with_end_tac g ~info:None (ltac2_interp tac)

let call_par ~pstate ~with_end_tac tac =
  ComTactic.solve_parallel ~pstate ~info:None (ltac2_interp tac) ~abstract:false ~with_end_tac

(** Primitive algebraic types than can't be defined Rocq-side *)

let register_prim_alg name params def =
  let id = Id.of_string name in
  let def = List.map (fun (cstr, tpe) -> (None, Id.of_string_soft cstr, tpe)) def in
  let getn (const, nonconst) (_, c, args) = match args with
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
  let def = { typdef_local = false; typdef_abstract = false; typdef_expr = def } in
  Lib.add_leaf (inTypDef id def)

let rocq_def n = KerName.make Tac2env.rocq_prefix (Label.make n)

let def_unit = {
  typdef_local = false;
  typdef_abstract = false;
  typdef_expr = 0, GTydDef (Some (GTypRef (Tuple 0, [])));
}

let t_list = rocq_def "list"

let () = Mltop.declare_cache_obj begin fun () ->
  let unit = Id.of_string "unit" in
  Lib.add_leaf (inTypDef unit def_unit);
  register_prim_alg "list" 1 [
    ("[]", []);
    ("::", [GTypVar 0; GTypRef (Other t_list, [GTypVar 0])]);
  ];
end "rocq-runtime.plugins.ltac2"
