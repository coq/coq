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
open Locus
open Tac2env
open Tac2print
open Tac2expr
open Tac2typing_env

(** Hardwired types and constants *)

let rocq_type n = KerName.make Tac2env.rocq_prefix (Label.make n)

let t_int = rocq_type "int"
let t_string = rocq_type "string"
let t_constr = rocq_type "constr"
let t_preterm = rocq_type "preterm"
let t_pattern = rocq_type "pattern"
let t_bool = rocq_type "bool"

let ltac2_env : Tac2typing_env.t Genintern.Store.field =
  Genintern.Store.field "ltac2_env"

let drop_ltac2_env store =
  Genintern.Store.remove store ltac2_env

let error_nargs_mismatch ?loc kn nargs nfound =
  let cstr = Tac2env.shortest_qualid_of_constructor kn in
  user_err ?loc (str "Constructor " ++ pr_qualid cstr ++ str " expects " ++
    int nargs ++ str " arguments, but is applied to " ++ int nfound ++
    str " arguments")

let error_nparams_mismatch ?loc nargs nfound =
  user_err ?loc (str "Type expects " ++ int nargs ++
    str " arguments, but is applied to " ++ int nfound ++
    str " arguments")

let rec intern_type env ({loc;v=t} : raw_typexpr) : TVar.t glb_typexpr = match t with
| CTypVar (Name id) -> GTypVar (get_alias (CAst.make ?loc id) env)
| CTypVar Anonymous -> GTypVar (fresh_id env)
| CTypRef (rel, args) ->
  let (kn, nparams) = match rel with
  | RelId qid ->
    begin match (if qualid_is_ident qid then find_rec_var (qualid_basename qid) env else None) with
    | Some (kn, n) ->
      (Other kn, n)
    | None ->
      let kn =
        try Tac2env.locate_type qid
        with Not_found ->
          user_err ?loc (str "Unbound type constructor " ++ pr_qualid qid)
      in
      let (nparams, _) = Tac2env.interp_type kn in
      (Other kn, nparams)
    end
  | AbsKn (Other kn) ->
    let (nparams, _) = Tac2env.interp_type kn in
    (Other kn, nparams)
  | AbsKn (Tuple n) ->
    (Tuple n, n)
  in
  let nargs = List.length args in
  let () =
    if not (Int.equal nparams nargs) then
      let qid = match rel with
      | RelId lid -> lid
      | AbsKn (Other kn) -> shortest_qualid_of_type ?loc kn
      | AbsKn (Tuple _) -> assert false
      in
      user_err ?loc (strbrk "The type constructor " ++ pr_qualid qid ++
        strbrk " expects " ++ int nparams ++ strbrk " argument(s), but is here \
        applied to " ++ int nargs ++ strbrk "argument(s)")
  in
  GTypRef (kn, List.map (fun t -> intern_type env t) args)
| CTypArrow (t1, t2) -> GTypArrow (intern_type env t1, intern_type env t2)

let fresh_type_scheme env (t : type_scheme) : TVar.t glb_typexpr =
  let (n, t) = t in
  let subst = Array.init n (fun _ -> fresh_id env) in
  let substf i = GTypVar subst.(i) in
  subst_type substf t

let fresh_mix_type_scheme env (t : mix_type_scheme) : TVar.t glb_typexpr =
  let (n, t) = t in
  let subst = Array.init n (fun _ -> fresh_id env) in
  let substf = function
  | LVar i -> GTypVar subst.(i)
  | GVar n -> GTypVar n
  in
  subst_type substf t

(** Term typing *)

let is_pure_constructor kn =
  match snd (Tac2env.interp_type kn) with
  | GTydAlg _ | GTydOpn -> true
  | GTydRec fields ->
    let is_pure (_, mut, _) = not mut in
    List.for_all is_pure fields
  | GTydDef _ -> assert false (** Type definitions have no constructors *)

let is_pure_field kn i =
  match snd (Tac2env.interp_type kn) with
  | GTydRec fields ->
    let is_pure (_, mut, _) = not mut in
    is_pure (List.nth fields i)
  | GTydAlg _ | GTydOpn | GTydDef _ -> assert false

let rec is_value = function
| GTacAtm (AtmInt _) | GTacVar _ | GTacPrm _ -> true
| GTacFun (bnd,_) -> assert (not (CList.is_empty bnd)); true
| GTacAtm (AtmStr _) | GTacApp _ -> false
| GTacRef kn -> not (Tac2env.interp_global kn).gdata_mutable
| GTacCst (Tuple _, _, el) -> List.for_all is_value el
| GTacCst (_, _, []) -> true
| GTacOpn (_, el) -> List.for_all is_value el
| GTacCst (Other kn, _, el) -> is_pure_constructor kn && List.for_all is_value el
| GTacLet (_, bnd, e) ->
  (* in the recursive case the bnd are guaranteed to be values but it doesn't hurt to check *)
  is_value e && List.for_all (fun (_, e) -> is_value e) bnd
| GTacPrj (kn,e,i) -> is_pure_field kn i && is_value e
| GTacCse _ | GTacSet _ | GTacExt _
| GTacWth _ | GTacFullMatch _ -> false

let is_rec_rhs = function
| GTacFun _ -> true
| GTacAtm _ | GTacVar _ | GTacRef _ | GTacApp _ | GTacLet _ | GTacPrj _
| GTacSet _ | GTacExt _ | GTacPrm _ | GTacCst _
| GTacCse _ | GTacOpn _ | GTacWth _ | GTacFullMatch _-> false

let warn_not_unit =
  CWarnings.create ~name:"not-unit" ~category:CWarnings.CoreCategories.ltac2
    (fun (env, t) ->
      strbrk "This expression should have type unit but has type " ++
      pr_glbtype env t ++ str ".")

let check_elt_unit loc env t =
  let maybe_unit = match kind env t with
  | GTypVar _ -> true
  | GTypArrow _ -> false
  | GTypRef (Tuple 0, []) -> true
  | GTypRef _ -> false
  in
  if not maybe_unit then warn_not_unit ?loc (env, t)

let is_empty_type env t = match kind env t with
  | GTypVar _ | GTypArrow _ | GTypRef (Tuple _, _) -> false
  | GTypRef (Other kn, _) ->
  let def = Tac2env.interp_type kn in
  match def with
  | _, GTydAlg { galg_constructors = [] } -> true
  | _ -> false

let check_elt_empty loc env t = match kind env t with
| GTypVar _ ->
  user_err ?loc (str "Cannot infer an empty type for this expression")
| GTypArrow _ | GTypRef (Tuple _, _) ->
  user_err ?loc (str "Type" ++ spc () ++ pr_glbtype env t ++ spc () ++ str "is not an empty type")
| GTypRef (Other kn, _) ->
  let def = Tac2env.interp_type kn in
  match def with
  | _, GTydAlg { galg_constructors = [] } -> kn
  | _ ->
    user_err ?loc (str "Type" ++ spc () ++ pr_glbtype env t ++ spc () ++ str "is not an empty type")

let check_unit ?loc t =
  let env = empty_env () in
  (* Should not matter, t should be closed. *)
  let t = fresh_type_scheme env t in
  let maybe_unit = match kind env t with
  | GTypVar _ -> true
  | GTypArrow _ -> false
  | GTypRef (Tuple 0, []) -> true
  | GTypRef _ -> false
  in
  if not maybe_unit then warn_not_unit ?loc (env, t)

let get_constructor env var = match var with
| RelId qid ->
  let c = try Some (Tac2env.locate_constructor qid) with Not_found -> None in
  begin match c with
  | Some knc ->
    Tac2env.constructor_user_warn knc ;
    Other knc
  | None ->
    CErrors.user_err ?loc:qid.CAst.loc (str "Unbound constructor " ++ pr_qualid qid)
  end
| AbsKn knc -> knc

let get_projection var = match var with
| RelId qid ->
  let kn = try Tac2env.locate_projection qid with Not_found ->
    user_err ?loc:qid.CAst.loc (pr_qualid qid ++ str " is not a projection")
  in
  Tac2env.interp_projection kn
| AbsKn kn ->
  Tac2env.interp_projection kn

let intern_atm env = function
| AtmInt n -> (GTacAtm (AtmInt n), GTypRef (Other t_int, []))
| AtmStr s -> (GTacAtm (AtmStr s), GTypRef (Other t_string, []))

(** Internalization *)

(** Used to generate a fresh tactic variable for pattern-expansion *)
let fresh_var avoid =
  let bad id =
    Id.Set.mem id avoid ||
    (try ignore (locate_ltac (qualid_of_ident id)); true with Not_found -> false)
  in
  Namegen.next_ident_away_from (Id.of_string "p") bad

let add_name accu = function
| Name id -> Id.Set.add id accu
| Anonymous -> accu

let loc_of_relid = function
| RelId {loc} -> loc
| AbsKn _ -> None

let is_unit_pattern = function
| CPatRef (AbsKn (Tuple 0), []) -> true
| _ -> false

let extract_pattern_type ({loc;v=p} as pat) = match p with
| CPatCnv (pat, ty) -> pat, Some ty
| CPatAtm _ | CPatVar _ | CPatRef _ | CPatOr _ | CPatAs _ | CPatRecord _ ->
  if is_unit_pattern p then
    (* Special handling of () patterns *)
    let t_unit = CAst.make ?loc @@ CTypRef (AbsKn (Tuple 0), []) in
    pat, Some t_unit
  else pat, None

(** Expand pattern: [p => t] becomes [x => match x with p => t end] *)
let expand_pattern avoid bnd =
  let fold (avoid, bnd) (pat, t) =
    let na, expand = match pat.v with
    | CPatVar na ->
      (* Don't expand variable patterns *)
      na, None
    | _ ->
      if is_unit_pattern pat.v then
        Anonymous, None
      else
        let id = fresh_var avoid in
        let qid = RelId (qualid_of_ident ?loc:pat.loc id) in
        Name id, Some qid
    in
    let avoid = ids_of_pattern avoid pat in
    let avoid = add_name avoid na in
    (avoid, (na, pat, expand) :: bnd)
  in
  let (_, bnd) = List.fold_left fold (avoid, []) bnd in
  let fold e (na, pat, expand) = match expand with
  | None -> e
  | Some qid ->
    let loc = loc_of_relid qid in
    CAst.make ?loc @@ CTacCse (CAst.make ?loc @@ CTacRef qid, [pat, e])
  in
  let expand e = List.fold_left fold e bnd in
  let nas = List.rev_map (fun (na, _, _) -> na) bnd in
  (nas, expand)

let is_alias env qid = match get_variable env qid with
| ArgArg (TacAlias _) -> true
| ArgVar _ | (ArgArg (TacConstant _)) -> false

let is_user_name qid = match qid with
| AbsKn _ -> false
| RelId _ -> true

let deprecated_ltac2_alias =
  Deprecation.create_warning
    ~object_name:"Ltac2 alias"
    ~warning_name_if_no_since:"deprecated-ltac2-alias"
    (fun kn -> pr_qualid (Tac2env.shortest_qualid_of_ltac Id.Set.empty (TacAlias kn)))

let deprecated_ltac2_def =
  Deprecation.create_warning
    ~object_name:"Ltac2 definition"
    ~warning_name_if_no_since:"deprecated-ltac2-definition"
    (fun kn -> pr_qualid (Tac2env.shortest_qualid_of_ltac Id.Set.empty (TacConstant kn)))

let check_deprecated_ltac2 ?loc qid def =
  if is_user_name qid then match def with
  | TacAlias kn ->
    begin match (Tac2env.interp_alias kn).alias_depr with
    | None -> ()
    | Some depr -> deprecated_ltac2_alias ?loc (kn, depr)
    end
  | TacConstant kn ->
    begin match (Tac2env.interp_global kn).gdata_deprecation with
    | None -> ()
    | Some depr -> deprecated_ltac2_def ?loc (kn, depr)
    end

type ('a,'b) field =
  | PresentField of 'a
  | MissingField of 'b

let intern_record env loc fs =
  let map (proj, e) =
    let loc = match proj with
    | RelId {CAst.loc} -> loc
    | AbsKn _ -> None
    in
    let proj = get_projection proj in
    (loc, proj, e)
  in
  let fs = List.map map fs in
  let kn = match fs with
  | [] -> user_err ?loc (str "Cannot infer the corresponding record type")
  | (_, proj, _) :: _ -> proj.pdata_type
  in
  let params, typdef = match Tac2env.interp_type kn with
  | n, GTydRec def -> n, def
  | _ -> assert false
  in
  let subst = Array.init params (fun _ -> fresh_id env) in
  (* Set the answer [args] imperatively *)
  let args = Array.make (List.length typdef) None in
  let iter (loc, pinfo, e) =
    if KerName.equal kn pinfo.pdata_type then
      let index = pinfo.pdata_indx in
      match args.(index) with
      | None ->
        let exp = subst_type (fun i -> GTypVar subst.(i)) pinfo.pdata_ptyp in
        args.(index) <- Some (e, exp)
      | Some _ ->
        let (name, _, _) = List.nth typdef pinfo.pdata_indx in
        user_err ?loc (str "Field " ++ Id.print name ++ str " is defined \
          several times")
    else
      user_err ?loc (str "Field " ++ (*KerName.print knp ++*) str " does not \
        pertain to record definition " ++ pr_typref pinfo.pdata_type)
  in
  let () = List.iter iter fs in
  let args = Array.mapi (fun i arg -> match arg with
      | None ->
        let field, _, typ = List.nth typdef i in
        let typ' = subst_type (fun i -> GTypVar subst.(i)) typ in
        MissingField (i, field, typ, typ')
      | Some arg -> PresentField arg)
      args
  in
  let tparam = List.init params (fun i -> GTypVar subst.(i)) in
  kn, tparam, args

let ctor_data_for_patterns kn data = {
  ctyp = Some data.cdata_type;
  cnargs = List.length data.cdata_args;
  cindx = match data.cdata_indx with None -> Open kn | Some i -> Closed i;
}

let ctor_data_of_tuple n = {
  ctyp = None;
  cnargs = n;
  cindx = Closed 0;
}

type wip_pat_r =
  | PatVar of Name.t
  | PatAtm of atom
  | PatRef of ctor_data_for_patterns * wip_pat list
  | PatOr of wip_pat list
  | PatAs of wip_pat * lident
and wip_pat = wip_pat_r CAst.t

let catchall = CAst.make (PatVar Anonymous)

let pat_or ?loc = function
  | [] -> assert false
  | [x] -> x
  | pats -> CAst.make ?loc (PatOr pats)

let rec intern_pat_rec env cpat t =
  let loc = cpat.loc in
  match cpat.v with
  | CPatVar x -> begin match x with
      | Anonymous -> Id.Map.empty, CAst.make ?loc (PatVar x)
      | Name id ->
        let patvars = Id.Map.singleton id (loc,t) in
        patvars, CAst.make ?loc (PatVar x)
    end
  | CPatAtm atm ->
    let _, t' = intern_atm env atm in
    let () = unify ?loc env t t' in
    Id.Map.empty, CAst.make ?loc (PatAtm atm)
  | CPatAs (p, x) ->
    let patvars, p = intern_pat_rec env p t in
    let patvars = Id.Map.update x.v (function
        | Some _ ->
          CErrors.user_err ?loc
            Pp.(str "Variable " ++ Id.print x.v ++
                str " is bound several times in this matching.")
        | None -> Some (x.loc,t))
        patvars
    in
    patvars, CAst.make ?loc (PatAs (p, x))
  | CPatRef (ctor,args) ->
    let ctor = get_constructor env ctor in
    let ctor, argts =
      let nargs = List.length args in
      match ctor with
      | Tuple n ->
        assert (Int.equal nargs n);
        let ts = List.init n (fun _ -> GTypVar (fresh_id env)) in
        let () = unify ?loc env t (GTypRef (ctor, ts)) in
        ctor_data_of_tuple n, ts
      | Other kn ->
        let data = interp_constructor kn in
        let nexpectargs = List.length data.cdata_args in
        if not (Int.equal nargs nexpectargs) then error_nargs_mismatch ?loc kn nexpectargs nargs;
        let subst = Array.init data.cdata_prms (fun _ -> fresh_id env) in
        let substf i = GTypVar subst.(i) in
        let types = List.map (fun t -> subst_type substf t) data.cdata_args in
        let targs = List.init data.cdata_prms substf in
        let ans = GTypRef (Other data.cdata_type, targs) in
        let () = unify ?loc env t ans in
        ctor_data_for_patterns kn data, types
    in
    let patvars, args = CList.fold_left2_map (fun patvars arg argt ->
        let argvars, arg = intern_pat_rec env arg argt in
        let patvars = Id.Map.union (fun id _ (loc,_) ->
            CErrors.user_err ?loc
              Pp.(str "Variable " ++ Id.print id ++
                  str " is bound several times in this matching."))
            patvars argvars
        in
        patvars, arg)
        Id.Map.empty
        args
        argts
    in
    patvars, CAst.make ?loc (PatRef (ctor,args))
  | CPatRecord pats ->
    let kn, tparam, args = intern_record env loc pats in
    let () = unify ?loc env t (GTypRef (Other kn, tparam)) in
    let args = Array.to_list args in
    let patvars, args = CList.fold_left_map (fun patvars -> function
        | MissingField _ -> patvars, catchall
        | PresentField (arg, argty) ->
          let (argvars,arg) = intern_pat_rec env arg argty in
          let patvars = Id.Map.union (fun id _ (loc,_) ->
              CErrors.user_err ?loc
                Pp.(str "Variable " ++ Id.print id ++
                    str " is bound several times in this matching."))
              patvars argvars
          in
          patvars, arg)
        Id.Map.empty
        args
    in
    let ctor = { ctyp = Some kn; cnargs = List.length args; cindx = Closed 0 } in
    patvars, CAst.make ?loc (PatRef (ctor, args))
  | CPatCnv (pat,typ) ->
    let typ = intern_type env typ in
    let () = unify ?loc env t typ in
    intern_pat_rec env pat typ
  | CPatOr [] -> assert false
  | CPatOr (first::rest) ->
    let patvars, first = intern_pat_rec env first t in
    let rest = List.map (fun pat ->
        let patvars', pat = intern_pat_rec env pat t in
        if not (Id.Map.equal (fun (_,t) (loc,t') ->
            unify ?loc env t t';
            true)
            patvars patvars')
        (* TODO say what variables are differently bound *)
        then CErrors.user_err ?loc Pp.(str "These patterns do not bind the same variables.");
        pat)
        rest
    in
    patvars, CAst.make ?loc (PatOr (first::rest))


let intern_pat env cpat t =
  let patvars, pat = intern_pat_rec env cpat t in
  Id.Map.map (fun (_,v) -> monomorphic v) patvars, pat

let rec glb_of_wip_pat_r = function
  | PatVar x -> GPatVar x
  | PatAtm atm -> GPatAtm atm
  | PatRef (ctor,pats) -> GPatRef (ctor, List.map glb_of_wip_pat pats)
  | PatOr pats -> GPatOr (List.map glb_of_wip_pat pats)
  | PatAs (p,x) -> GPatAs (glb_of_wip_pat p, x.v)
and glb_of_wip_pat pat = glb_of_wip_pat_r pat.CAst.v

(** Pattern analysis for non-exhaustiveness and (TODO) useless patterns based on
    "Warnings for pattern matching", Luc Maranget, Journal of Functional Programming, 17(3), 2007 *)
let default_matrix =
  let rec default_row = function
    | [] -> assert false
    | {v=PatRef _ | PatAtm _} :: _ -> []
    | {v=PatVar _} :: rest -> [rest]
    | {v=PatOr pats} :: rest -> List.map_append default_row (List.map (fun x -> x::rest) pats)
    | {v=PatAs (p,_)} :: rest -> default_row (p::rest)
  in
  List.map_append default_row

type generalized_ctor =
  | AtomCtor of atom
  | OtherCtor of ctor_data_for_patterns

let rec root_ctors = function
  | {v=PatVar _} -> []
  | {v=PatRef (ctor,_)} -> [OtherCtor ctor]
  | {v=PatAtm a} -> [AtomCtor a]
  | {v=PatOr pats} -> List.map_append root_ctors pats
  | {v=PatAs (p,_)} -> root_ctors p

(* XXX maybe should be ctor_data_for_patterns list or_tuple ??? *)
type missing_ctors =
  | Unknown
  | Extension of { example : atom option }
  | Known of ctor_data_for_patterns list

type maybe_missing_ctors =
  | Missing of missing_ctors
  | NoMissing of ctor_data_for_patterns list

let make_ctor ctyp tdata is_const n =
  let cnargs = if is_const then 0 else
      let rec find n = function
        | [] -> assert false
        | (_, _, []) :: rem ->
          find n rem
        | (_, _, argtys) :: rem ->
          if Int.equal n 0 then List.length argtys
          else find (pred n) rem
      in
      find n tdata.galg_constructors
  in
  {
    ctyp;
    cindx = Closed n;
    cnargs;
  }

let make_int_example ints =
  let rec aux i = if Int.Set.mem i ints then aux (i+1) else i
  in aux 0

let make_string_example strings =
  let rec aux s = if String.Set.mem s strings then aux (s^"*") else s
  in aux ""

let make_atom_example = function
  | AtomCtor (AtmInt i) :: rest ->
    let ints = List.fold_left (fun ints c -> match c with
        | AtomCtor (AtmInt i) -> Int.Set.add i ints
        | _ -> assert false)
        (Int.Set.singleton i)
        rest
    in
    AtmInt (make_int_example ints)
  | AtomCtor (AtmStr s) :: rest ->
    let strings = List.fold_left (fun strings c -> match c with
        | AtomCtor (AtmStr s) -> String.Set.add s strings
        | _ -> assert false)
        (String.Set.singleton s)
        rest
    in
    AtmStr (make_string_example strings)
  | OtherCtor _ :: _ | [] -> assert false

(* We assume all the constructors in the list are from the same type t *)
let missing_ctors_from env t = function
  | [] -> (* patterns are all wildcards *)
    (* TODO handle match on deep empty eg (empty,empty) *)
    if is_empty_type env t then NoMissing []
    else Missing Unknown
  | AtomCtor _ :: _ as l -> Missing (Extension {example=Some (make_atom_example l)})
  | OtherCtor {ctyp=None; cnargs} :: _ ->
    (* tuple has 1 constructor *) NoMissing [ctor_data_of_tuple cnargs]
  | OtherCtor {cindx=Open _} :: _ -> Missing (Extension {example=None})
  | OtherCtor ({ctyp=Some ctyp} as data) :: _ as ctors ->
    let _, tdata = interp_type ctyp in
    match tdata with
    | GTydOpn | GTydDef _ -> assert false
    | GTydRec _ -> NoMissing [data]
    | GTydAlg tdata ->
      let const = Array.make tdata.galg_nconst false in
      let nonconst = Array.make tdata.galg_nnonconst false in
      let () = List.iter (function
          | OtherCtor {cindx=Closed i; cnargs} ->
            let which = if Int.equal 0 cnargs then const else nonconst in
            which.(i) <- true
          | AtomCtor _ | OtherCtor {cindx=Open _} -> assert false)
          ctors
      in
      let fold is_const i (missing, present) ispresent =
        let ctor = (make_ctor data.ctyp tdata is_const i) in
        if ispresent then missing, ctor :: present
        else ctor :: missing, present
      in
      let acc = CArray.fold_left_i (fold false) ([],[]) nonconst in
      let missing, present = CArray.fold_left_i (fold true) acc const in
      if List.is_empty missing then NoMissing present
      else Missing (Known missing)

let specialized_types env ts ctor = match ts with
  | [] -> assert false
  | t :: rest ->
    let argts = match ctor with
      | AtomCtor _ -> []
      | OtherCtor {ctyp=None; cnargs=n} ->
        let argts = List.init n (fun _ -> GTypVar (fresh_id env)) in
        let () = unify env t (GTypRef (Tuple n, argts)) in
        argts
      | OtherCtor {cindx=Open kn} ->
        let data = interp_constructor kn in
        let subst = Array.init data.cdata_prms (fun _ -> fresh_id env) in
        let substf i = GTypVar subst.(i) in
        let types = List.map (fun t -> subst_type substf t) data.cdata_args in
        let targs = List.init data.cdata_prms substf in
        let ans = GTypRef (Other data.cdata_type, targs) in
        let () = unify env t ans in
        types
      | OtherCtor {ctyp=Some ctyp; cnargs; cindx=Closed i} ->
        let ntargs, tdata = interp_type ctyp in
        match tdata with
        | GTydOpn | GTydDef _ -> assert false
        | GTydRec tdata ->
          let subst = Array.init ntargs (fun _ -> fresh_id env) in
          let substf i = GTypVar subst.(i) in
          let types = List.map (fun (_,_,t) -> subst_type substf t) tdata in
          let targs = List.init ntargs substf in
          let ans = GTypRef (Other ctyp, targs) in
          let () = unify env t ans in
          types
        | GTydAlg tdata ->
          let ctors = List.filter (fun (_, _,argts) ->
              if cnargs = 0
              then List.is_empty argts
              else not (List.is_empty argts))
              tdata.galg_constructors
          in
          let _, _, argts = List.nth ctors i in
          let subst = Array.init ntargs (fun _ -> fresh_id env) in
          let substf i = GTypVar subst.(i) in
          let types = List.map (fun t -> subst_type substf t) argts in
          let targs = List.init ntargs substf in
          let ans = GTypRef (Other ctyp, targs) in
          let () = unify env t ans in
          types
    in
    List.append argts rest

let specialized_multi_matrix (patsP, patsQ, patsR) ctor =
  let same_atom atm atm' = match atm, atm' with
    | AtmInt i, AtmInt j -> Int.equal i j
    | AtmStr i, AtmStr j -> String.equal i j
    | AtmInt _, AtmStr _ | AtmStr _, AtmInt _ -> assert false (* by typing *)
  in
  let same_ctor_indx i j = match i, j with
    | Closed i, Closed j -> Int.equal i j
    | Open kn, Open kn' -> KerName.equal kn kn'
    | Closed _, Open _ | Open _, Closed _ -> false
  in
  let same_ctor ctor ctor' = match ctor, ctor' with
    | AtomCtor atm, AtomCtor atm' -> same_atom atm atm'
    | OtherCtor ctor, OtherCtor ctor' ->
      Int.equal ctor.cnargs ctor'.cnargs
      && same_ctor_indx ctor.cindx ctor'.cindx
    | AtomCtor _, OtherCtor _ | OtherCtor _, AtomCtor _ -> assert false (* by typing *)
  in
  let rec special_row rowP rowQ rowR = match rowP with
    | [] -> assert false
    | {v=PatRef (ctor',args)} :: rest ->
      if same_ctor ctor (OtherCtor ctor') then [List.append args rest, rowQ, rowR]
      else []
    | {v=PatAtm atm} :: rest ->
      if same_ctor ctor (AtomCtor atm) then [rest, rowQ, rowR]
      else []
    | {v=PatVar _} :: rest -> begin match ctor with
        | OtherCtor ctor -> [List.append (List.make ctor.cnargs catchall) rest, rowQ, rowR]
        | AtomCtor _ -> [rest, rowQ, rowR]
      end
    | {v=PatOr pats} :: rest ->
      List.map_append (fun x -> special_row (x::rest) rowQ rowR) pats
    | {v=PatAs (p,_)} :: rest -> special_row (p::rest) rowQ rowR
  in
  let res = List.flatten (List.map3 special_row patsP patsQ patsR) in
  List.split3 res

let specialized_matrix pats ctor =
  (* because the dummy lists are [unit list] we are guaranteed that
     they don't get mixed with [pats], they just get some elements
     dropped or copied *)
  let dummy = List.make (List.length pats) () in
  let pats, _, _ = specialized_multi_matrix (pats, dummy, dummy) ctor in
  pats

let rec lift_interned_pat pat = CAst.map lift_interned_pat_r pat
and lift_interned_pat_r = let open PartialPat in function
    | PatVar x -> Var x
    | PatAtm a -> Atom a
    | PatRef (ctor, pats) -> Ref (ctor, List.map lift_interned_pat pats)
    | PatOr pats -> Or (List.map lift_interned_pat pats)
    | PatAs (p,x) -> As (lift_interned_pat p, x.v)
(*
[ (*row,col*)
  [(0,0); (0,1)];
  [(1,0); (1,1)];
]
*)
(* invariant: ts is n types, pats is a matrix with n columns ([nth pats i] is row i) *)
let rec missing_matches env ts pats n =
  match n with
  | 0 -> begin match pats with [] -> Some [] | _::_ -> None end
  | _ ->
    let root_ctors = List.map_append root_ctors (List.map List.hd pats) in
    match missing_ctors_from env (List.hd ts) root_ctors with
    | NoMissing ctors -> specialized_missing_matches env ts pats n ctors
    | Missing missing_ctors ->
      match missing_matches env (List.tl ts) (default_matrix pats) (n-1) with
      | None -> None
      | Some missing -> match missing_ctors with
        | Unknown -> Some (lift_interned_pat catchall :: missing)
        | Extension {example} -> Some (CAst.make (PartialPat.Extension {example}) :: missing)
        | Known missing_ctors ->
          let misspats = List.map (fun ctor ->
              CAst.make (PatRef (ctor, List.make ctor.cnargs catchall)))
              missing_ctors
          in
          Some (lift_interned_pat (pat_or misspats) :: missing)

and specialized_missing_matches env ts pats n = function
  | [] -> None
  | ctor :: rest ->
    match missing_matches env
            (specialized_types env ts (OtherCtor ctor))
            (specialized_matrix pats (OtherCtor ctor))
            (ctor.cnargs + n - 1)
    with
    | None -> specialized_missing_matches env ts pats n rest
    | Some missing ->
      let args, missing = List.chop ctor.cnargs missing in
      (* TODO continue recursing for more exhaustive output? *)
      Some (CAst.make (PartialPat.Ref (ctor, args)) :: missing)

let check_no_missing_pattern env t pats =
  match missing_matches env [t] (List.map (fun x -> [x]) pats) 1 with
  | None -> ()
  | Some missing ->
    let missing = match missing with [x] -> x | _ -> assert false in
    CErrors.user_err Pp.(
        str "Non exhaustive match. Values in this pattern are not matched:" ++ fnl() ++
        pr_partial_pat missing)

type utility =
  | Useless
  | PartiallyUseless of Loc.t option list

let combine_utilities us =
  let fold (all_useless, useless_locs) = function
    | _, None -> (false, useless_locs)
    | loc, Some Useless -> (all_useless, [loc]::useless_locs)
    | _, Some (PartiallyUseless locs) -> (false, locs::useless_locs)
  in
  let all_useless, useless_locs = List.fold_left fold (true,[]) us in
  if List.is_empty useless_locs then None
  else if all_useless then Some Useless
  else Some (PartiallyUseless (List.flatten (List.rev useless_locs)))

let rec simple_utility env ts pats q =
  match q with
  | [] -> begin match pats with [] -> true | _::_ -> false end
  | pat :: q -> match pat.CAst.v with
    | PatAs (p, _) -> simple_utility env ts pats (p :: q)
    | PatRef (ctor, args) ->
      let ctor = OtherCtor ctor in
      simple_utility env (specialized_types env ts ctor)
        (specialized_matrix pats ctor)
        (args @ q)
    | PatAtm atm ->
      let ctor = AtomCtor atm in
      simple_utility env (specialized_types env ts ctor)
        (specialized_matrix pats ctor)
        q
    | PatOr ps -> List.exists (fun p -> simple_utility env ts pats (p :: q)) ps
    | PatVar _ ->
      let root_ctors = List.map_append root_ctors (List.map List.hd pats) in
      match missing_ctors_from env (List.hd ts) root_ctors with
      | NoMissing ctors ->
        List.exists (fun ctor ->
            let gctor = OtherCtor ctor in
            simple_utility env (specialized_types env ts gctor)
              (specialized_matrix pats gctor)
              (List.make ctor.cnargs catchall @ q))
          ctors
      | Missing _ -> simple_utility env (List.tl ts) (default_matrix pats) q

(* each component of a tuple has as many cols as the corresponding component of the other tuples
   each component of [prefix] has as many rows as the other components of [prefix]
*)
let rec utility env ((tP, tQ, tR) as t) ((preP, preQ, preR) as prefix) (p, q, r) =
  match p with
  | p1 :: p -> begin match p1.CAst.v with
      | PatAs (p1, _) -> utility env t prefix (p1 :: p, q, r)
      | PatRef (ctor, pats) ->
        let ctor = OtherCtor ctor in
        let t = specialized_types env tP ctor, tQ, tR in
        let prefix = specialized_multi_matrix prefix ctor in
        utility env t prefix (pats @ p, q, r)
      | PatAtm atm ->
        let ctor = AtomCtor atm in
        let t = specialized_types env tP ctor, tQ, tR in
        let prefix = specialized_multi_matrix prefix ctor in
        utility env t prefix (p, q, r)
      | PatVar _ ->
        let t = (List.tl tP, List.hd tP :: tQ, tR) in
        let prefix =
          (List.map List.tl preP,
           List.map2 (fun preP preQ -> List.hd preP :: preQ) preP preQ,
           preR)
        in
        utility env t prefix (p, p1 :: q, r)
      | PatOr _ ->
        let t = (List.tl tP, tQ, List.hd tP :: tR) in
        let prefix =
          (List.map List.tl preP,
           preQ,
           List.map2 (fun preP preR -> List.hd preP :: preR) preP preR)
        in
        utility env t prefix (p, q, p1 :: r)
    end
  | [] -> match r with
    | [] -> if simple_utility env tQ preQ q then None else Some Useless
    | _ :: _ ->
      let utilities = List.map_i (fun j rj ->
          let t = ([List.nth tR j], (List.filteri (fun j' _ -> not (Int.equal j j')) tR) @ tQ, []) in
          let r_no_j = List.filteri (fun j' _ -> not (Int.equal j j')) r in
          let preRj = List.map (fun x -> [List.nth x j]) preR in
          let preR_no_j = List.map (fun x -> List.filteri (fun j' _ -> not (Int.equal j j')) x) preR in
          let r_no_j_plus_q = r_no_j @ q in
          let pats = match rj.v with
            | PatOr pats -> pats
            | _ -> assert false
          in
          let fold ((preP, preQ, preR) as prefix) pat =
            let u = utility env t prefix ([pat], r_no_j_plus_q, []) in
            (* [[] :: preR] because the order doesn't matter, they're all empty *)
            let prefix = (preP @ [[pat]], preQ @ [r_no_j_plus_q], [] :: preR) in
            prefix, (pat.loc, u)
          in
          let prefix = (preRj, List.map2 (@) preR_no_j preQ, List.make (List.length preRj) []) in
          let _, us = List.fold_left_map fold prefix pats in
          rj.loc, combine_utilities us)
          0 r
      in
      combine_utilities utilities

let warn_redundant_pattern =
  CWarnings.create ~name:"redundant-pattern" ~category:CWarnings.CoreCategories.ltac2
    (fun partial -> str ("This " ^ (if partial then "pattern" else "clause") ^ " is redundant."))

let check_redundant_clauses env t pats =
  let fold (prefix, dummies) pat =
    let () = match utility env ([t],[],[]) (prefix,dummies,dummies) ([pat],[],[]) with
      | None -> ()
      | Some Useless -> warn_redundant_pattern ?loc:pat.loc false
      | Some (PartiallyUseless locs) -> List.iter (fun loc -> warn_redundant_pattern ?loc true) locs
    in
    prefix @ [[pat]], [] :: dummies
  in
  let _, _ = List.fold_left fold ([],[]) pats in
  ()

(** Pattern view *)

type glb_patexpr =
| GEPatVar of Name.t
| GEPatRef of ctor_data_for_patterns * glb_patexpr list

exception HardCase

let rec to_patexpr env {loc;v=pat} = match pat with
| PatVar na -> GEPatVar na
| PatRef (ctor, pl) ->
  GEPatRef (ctor, List.map (fun p -> to_patexpr env p) pl)
| PatAtm _ | PatOr _ | PatAs _ ->
  raise HardCase

type pattern_kind =
| PKind_empty
| PKind_variant of type_constant or_tuple
| PKind_open
| PKind_any

let get_pattern_kind env pl = match pl with
| [] -> PKind_empty
| p :: pl ->
  let rec get_kind ((p:wip_pat), _) pl = match to_patexpr env p with
  | GEPatVar _ ->
    begin match pl with
    | [] -> PKind_any
    | p :: pl -> get_kind p pl
    end
  | GEPatRef ({ctyp=Some ctyp} as kn, pl) -> begin match kn.cindx with
      | Open kn -> PKind_open
      | Closed _ -> PKind_variant (Other ctyp)
    end
    (* let data = Tac2env.interp_constructor kn in *)
    (* if Option.is_empty data.cdata_indx then PKind_open data.cdata_type *)
    (* else PKind_variant (Other data.cdata_type) *)
  | GEPatRef ({ctyp=None; cnargs=k}, tp) -> PKind_variant (Tuple k)
  in
  get_kind p pl

(** For now, patterns recognized by the pattern-matching compiling are limited
    to depth-one where leaves are either variables or catch-all *)
let to_simple_case env ?loc (e,t) pl =
  let todo () = raise HardCase in
  match get_pattern_kind env pl with
  | PKind_any ->
    let (pat, b) = List.hd pl in
    let na = match to_patexpr env pat with
    | GEPatVar na -> na
    | _ -> assert false
    in
    GTacLet (false, [na, e], b)
  | PKind_empty ->
    let kn = check_elt_empty loc env t in
    GTacCse (e, Other kn, [||], [||])
  | PKind_variant kn ->
    let (nconst, nnonconst, arities) = match kn with
    | Tuple 0 -> 1, 0, [0]
    | Tuple n -> 0, 1, [n]
    | Other kn ->
      let (_, def) = Tac2env.interp_type kn in
      let galg = match def with
        | GTydAlg c -> c
        | GTydRec _ -> raise HardCase
        | _ -> assert false
      in
      let arities = List.map (fun (_, _, args) -> List.length args) galg.galg_constructors in
      galg.galg_nconst, galg.galg_nnonconst, arities
    in
    let const = Array.make nconst None in
    let nonconst = Array.make nnonconst None in
    let rec intern_branch = function
    | [] -> ()
    | (pat, br) :: rem ->
      let () = match pat.v with
      | PatAtm _ | PatOr _ | PatAs _ ->
        raise HardCase
      | PatVar (Name _) -> todo ()
      | PatVar Anonymous ->
        (* Fill all remaining branches *)
        let fill (ncst, narg) arity =
          if Int.equal arity 0 then
            let () =
              if Option.is_empty const.(ncst) then const.(ncst) <- Some br
            in
            (succ ncst, narg)
          else
            let () =
              if Option.is_empty nonconst.(narg) then
                let ids = Array.make arity Anonymous in
                nonconst.(narg) <- Some (ids, br)
            in
            (ncst, succ narg)
        in
        let _, _ = List.fold_left fill (0, 0) arities in
        ()
      | PatRef (ctor, args) ->
        let index = match ctor.cindx with
        | Closed i -> i
        | Open _ -> assert false (* Open in PKind_variant is forbidden by typing *)
        in
        let get_id pat = match pat.v with
        | PatVar na -> na
        | _ -> todo ()
        in
        let ids = List.map get_id args in
        let () =
          if List.is_empty args then
            if Option.is_empty const.(index) then const.(index) <- Some br
            else ()
          else
            let ids = Array.of_list ids in
            if Option.is_empty nonconst.(index) then nonconst.(index) <- Some (ids, br)
            else ()
        in
        ()
      in
      intern_branch rem
    in
    let () = intern_branch pl in
    let map n is_const = function
    | None -> assert false (* exhaustivity check *)
    | Some x -> x
    in
    let const = Array.mapi (fun i o -> map i true o) const in
    let nonconst = Array.mapi (fun i o -> map i false o) nonconst in
    GTacCse (e, kn, const, nonconst)
  | PKind_open ->
    let rec intern_branch map = function
    | [] ->
      user_err ?loc (str "Missing default case")
    | (pat, br) :: rem ->
      match to_patexpr env pat with
      | GEPatVar na ->
        let def = (na, br) in
        (map, def)
      | GEPatRef (knc, args) ->
        let get = function
        | GEPatVar na -> na
        | GEPatRef _ -> todo ()
        in
        let knc = match knc.cindx with
        | Open knc -> knc
        | Closed _ -> assert false (* Closed / Tuple in PKind_open is forbidden by typing *)
        in
        let ids = List.map get args in
        let map =
          if KNmap.mem knc map then
            map
          else
            KNmap.add knc (Anonymous, Array.of_list ids, br) map
        in
        intern_branch map rem
    in
    let (map, def) = intern_branch KNmap.empty pl in
    GTacWth { opn_match = e; opn_branch = map; opn_default = def }

let check ?loc env tycon (e,t as et) =
  match tycon with
  | None -> et
  | Some tycon ->
    let () = unify ?loc env t tycon in
    e,tycon

let tycon_fun_body ?loc env tycon dom =
  match kind env tycon with
  | GTypVar _ ->
    let codom = GTypVar (fresh_id env) in
    let () = unify ?loc env (GTypArrow (dom,codom)) tycon in
    codom
  | GTypArrow (dom',codom) ->
    let () = unify ?loc env (GTypArrow (dom,codom)) tycon in
    codom
  | GTypRef _ ->
    CErrors.user_err ?loc
      Pp.(str "This expression should not be a function, the expected type is" ++ spc() ++
          pr_glbtype env tycon ++ str ".")

let tycon_app ?loc env ~ft t =
  match kind env t with
  | GTypVar _ ->
    let dom = GTypVar (fresh_id env) in
    let codom = GTypVar (fresh_id env) in
    let () = unify ?loc env (GTypArrow (dom,codom)) t in
    dom, codom
  | GTypArrow (dom,codom) -> dom, codom
  | GTypRef _ ->
    let is_fun = match kind env ft with
      | GTypArrow _ -> true
      | _ -> false
    in
    if is_fun then
      CErrors.user_err ?loc
        Pp.(str "This function has type" ++ spc() ++ pr_glbtype env ft ++
            spc() ++ str "and is applied to too many arguments.")
    else
      CErrors.user_err ?loc
        Pp.(str "This expression has type" ++ spc() ++ pr_glbtype env ft ++ str"." ++
            spc() ++ str "It is not a function and cannot be applied.")

let warn_useless_record_with = CWarnings.create ~name:"ltac2-useless-record-with" ~default:AsError
    ~category:CWarnings.CoreCategories.ltac2
    Pp.(fun () ->
        str "All the fields are explicitly listed in this record:" ++
        spc() ++ str "the 'with' clause is useless.")

let expand_notation ?loc el kn =
  match Tac2env.interp_notation kn with
  | UntypedNota body ->
    let el = List.map (fun (pat, e) -> CAst.map (fun na -> CPatVar na) pat, e) el in
    let v = if CList.is_empty el then body else CAst.make ?loc @@ CTacLet(false, el, body) in
    v
  | TypedNota {nota_prms=prms; nota_argtys=argtys; nota_ty=ty; nota_body=body} ->
    let argtys, el = List.fold_left_map (fun argtys (na,arg) ->
        let argty, argtys = match na.CAst.v with
          | Anonymous -> None, argtys
          | Name id -> Some (Id.Map.get id argtys), Id.Map.remove id argtys
        in
        argtys ,(na, arg, argty))
        argtys
        el
    in
    assert (Id.Map.is_empty argtys);
    CAst.make ?loc @@ CTacGlb (prms, el, body, ty)

let warn_unused_variables = CWarnings.create ~name:"ltac2-unused-variable"
    ~category:CWarnings.CoreCategories.ltac2
    Pp.(fun ids -> str "Unused " ++ str (String.lplural ids "variable") ++ str ":" ++ spc() ++ prlist_with_sep spc Id.print ids ++ str ".")

let check_unused_variables ?loc env bnd =
  let unused, _seen = List.fold_right (fun na (unused,seen) -> match na with
      | Anonymous -> (unused, seen)
      | Name id ->
        (* if [id] occurred in the tail of the list, this occurrence is unused
           (eg in [fun x x => x] the first [x] is unused) *)
        let unused =
          if CString.is_prefix "_" (Id.to_string id)
          || (not (Id.Set.mem id seen) && is_used_var id env)
          then unused
          else id :: unused
        in
        unused, (Id.Set.add id seen))
      bnd
      ([], Id.Set.empty)
  in
  if CList.is_empty unused then ()
  else warn_unused_variables ?loc unused

let rec intern_rec env tycon {loc;v=e} =
  let check et = check ?loc env tycon et in
  match e with
| CTacAtm atm -> check (intern_atm env atm)
| CTacRef qid ->
  begin match get_variable env qid with
  | ArgVar {CAst.v=id} ->
    let sch = find_var id env in
    check (GTacVar id, fresh_mix_type_scheme env sch)
  | ArgArg (TacConstant kn) ->
    let { Tac2env.gdata_type = sch; gdata_deprecation = depr } =
      try Tac2env.interp_global kn
      with Not_found ->
        CErrors.anomaly (str "Missing hardwired primitive " ++ KerName.print kn)
    in
    let () = check_deprecated_ltac2 ?loc qid (TacConstant kn) in
    check (GTacRef kn, fresh_type_scheme env sch)
  | ArgArg (TacAlias kn) ->
    let e =
      try Tac2env.interp_alias kn
      with Not_found ->
        CErrors.anomaly (str "Missing hardwired alias " ++ KerName.print kn)
    in
    let () = check_deprecated_ltac2 ?loc qid (TacAlias kn) in
    intern_rec env tycon e.alias_body
  end
| CTacCst qid ->
  let kn = get_constructor env qid in
  intern_constructor env loc tycon kn []
| CTacFun (bnd, e) ->
  let bnd = List.map extract_pattern_type bnd in
  let map (_, t) = match t with
  | None -> GTypVar (fresh_id env)
  | Some t -> intern_type env t
  in
  let tl = List.map map bnd in
  let (nas, exp) = expand_pattern (bound_vars env) bnd in
  let env, tycon = List.fold_left2 (fun (env,tycon) na t ->
      let tycon = Option.map (fun tycon -> tycon_fun_body ?loc env tycon t) tycon in
      let env = push_name na (monomorphic t) env in
      env, tycon) (env,tycon) nas tl
  in
  let (e, t) = intern_rec env tycon (exp e) in
  let () =
    (* TODO better loc? *)
    check_unused_variables ?loc env nas
  in
  let t = match tycon with
    | None -> List.fold_right (fun t accu -> GTypArrow (t, accu)) tl t
    | Some tycon -> tycon
  in
  (GTacFun (nas, e), t)
| CTacApp ({loc;v=CTacCst qid}, args) ->
  let kn = get_constructor env qid in
  intern_constructor env loc tycon kn args
| CTacApp ({v=CTacRef qid; loc=aloc}, args) when is_alias env qid ->
  let kn = match get_variable env qid with
  | ArgArg (TacAlias kn) -> kn
  | ArgVar _ | (ArgArg (TacConstant _)) -> assert false
  in
  let e = Tac2env.interp_alias kn in
  let () = check_deprecated_ltac2 ?loc:aloc qid (TacAlias kn) in
  let map arg =
    (* Thunk alias arguments *)
    let loc = arg.loc in
    let t_unit = CAst.make ?loc @@ CTypRef (AbsKn (Tuple 0), []) in
    let var = CAst.make ?loc @@ CPatCnv (CAst.make ?loc @@ CPatVar Anonymous, t_unit) in
    CAst.make ?loc @@ CTacFun ([var], arg)
  in
  let args = List.map map args in
  intern_rec env tycon (CAst.make ?loc @@ CTacApp (e.alias_body, args))
| CTacApp (f, args) ->
  let loc = f.loc in
  let (f, ft) = intern_rec env None f in
  let fold t arg =
    let dom, codom = tycon_app ?loc env ~ft t in
    let arg = intern_rec_with_constraint env arg dom in
    (codom, arg)
  in
  let (t, args) = CList.fold_left_map fold ft args in
  check (GTacApp (f, args), t)
| CTacLet (is_rec, el, e) ->
  let map (pat, e) =
    let (pat, ty) = extract_pattern_type pat in
    (pat, ty, e)
  in
  let el = List.map map el in
  let fold accu (pat, _, e) =
    let ids = ids_of_pattern Id.Set.empty pat in
    let common = Id.Set.inter ids accu in
    if Id.Set.is_empty common then Id.Set.union ids accu
    else
      let id = Id.Set.choose common in
      user_err ?loc:pat.loc (str "Variable " ++ Id.print id ++ str " is bound several \
        times in this matching")
  in
  let ids = List.fold_left fold Id.Set.empty el in
  if is_rec then intern_let_rec env loc el tycon e
  else intern_let env loc ids el tycon e
| CTacSyn (el, kn) ->
  let v = expand_notation ?loc el kn in
  intern_rec env tycon v
| CTacCnv (e, tc) ->
  let tc = intern_type env tc in
  let e = intern_rec_with_constraint env e tc in
  check (e, tc)
| CTacSeq (e1, e2) ->
  let loc1 = e1.loc in
  let (e1, t1) = intern_rec env None e1 in
  let (e2, t2) = intern_rec env tycon e2 in
  let () = check_elt_unit loc1 env t1 in
  (GTacLet (false, [Anonymous, e1], e2), t2)
| CTacIft (e, e1, e2) ->
  let e = intern_rec_with_constraint env e (GTypRef (Other t_bool, [])) in
  let (e1, t1) = intern_rec env tycon e1 in
  let t = Option.default t1 tycon in
  let e2 = intern_rec_with_constraint env e2 t in
  (GTacCse (e, Other t_bool, [|e1; e2|], [||]), t)
| CTacCse (e, pl) ->
  let e,brs,rt = intern_case env loc e tycon pl in
  begin try
    let cse = to_simple_case env ?loc e brs in
    cse, rt
  with HardCase ->
    let e, _ = e in
    let brs = List.map (fun (p,br) -> glb_of_wip_pat p, br) brs in
    GTacFullMatch (e,brs), rt
  end
| CTacRec (def, fs) ->
  let kn, tparam, args = intern_record env loc fs in
  let def, args = match def with
    | None ->
      let args = Array.map (function
          | PresentField _ as arg -> arg
          | MissingField (_, field, _, _) -> user_err ?loc (str "Field " ++ Id.print field ++ str " is undefined"))
          args
      in
      None, args
    | Some def ->
      (* To get the best locs on type errors, the order of operations must be
         - unify deftyp expectedtyp
         - intern_rec_with_constraint def
         - intern_rec_with_constraint present fields
      *)
      let deftparam = Array.init (List.length tparam) (fun _ -> GTypVar (fresh_id env)) in
      let used = ref false in
      let args = Array.map (function
          | PresentField _ as arg -> arg
          | MissingField (i, _, ftyp, expectedtyp) ->
            used := true;
            let deftyp = subst_type (fun i -> deftparam.(i)) ftyp in
            (* Can this fail? ie does loc matter? *)
            let () = unify ?loc env deftyp expectedtyp in
            MissingField i)
          args
      in
      let () = if not !used then warn_useless_record_with ?loc (); in
      let def = intern_rec_with_constraint env def (GTypRef (Other kn, Array.to_list deftparam)) in
      let var = match def with
        | GTacVar _ | GTacRef _ -> None
        | _ -> Some (fresh_var (bound_vars env))
      in
      Some (var, def), args
  in
  let args = CArray.map_to_list (function
      | PresentField (arg,argty) -> intern_rec_with_constraint env arg argty
      | MissingField i -> match def with
        | None -> assert false
        | Some (None, def) -> GTacPrj (kn, def, i)
        | Some (Some var, _) -> GTacPrj (kn, GTacVar var, i))
      args
  in
  let e = GTacCst (Other kn, 0, args) in
  let e = match def with
    | None -> e
    | Some (None, _) -> e
    | Some (Some var, def) ->
      GTacLet (false, [Name var, def], e)
  in
  check (e,  GTypRef (Other kn, tparam))
| CTacPrj (e, proj) ->
  let pinfo = get_projection proj in
  let loc = e.loc in
  let (e, t) = intern_rec env None e in
  let subst = Array.init pinfo.pdata_prms (fun _ -> fresh_id env) in
  let params = Array.map_to_list (fun i -> GTypVar i) subst in
  let exp = GTypRef (Other pinfo.pdata_type, params) in
  let () = unify ?loc env t exp in
  let substf i = GTypVar subst.(i) in
  let ret = subst_type substf pinfo.pdata_ptyp in
  check (GTacPrj (pinfo.pdata_type, e, pinfo.pdata_indx), ret)
| CTacSet (e, proj, r) ->
  let pinfo = get_projection proj in
  let () =
    if not pinfo.pdata_mutb then
      let loc = match proj with
      | RelId {CAst.loc} -> loc
      | AbsKn _ -> None
      in
      user_err ?loc (str "Field is not mutable")
  in
  let subst = Array.init pinfo.pdata_prms (fun _ -> fresh_id env) in
  let params = Array.map_to_list (fun i -> GTypVar i) subst in
  let exp = GTypRef (Other pinfo.pdata_type, params) in
  let e = intern_rec_with_constraint env e exp in
  let substf i = GTypVar subst.(i) in
  let ret = subst_type substf pinfo.pdata_ptyp in
  let r = intern_rec_with_constraint env r ret in
  check (GTacSet (pinfo.pdata_type, e, pinfo.pdata_indx, r), GTypRef (Tuple 0, []))
| CTacExt (tag, arg) ->
  let open Genintern in
  let obj = interp_ml_object tag in
  (* External objects do not have access to the named context because this is
     not stable by dynamic semantics. *)
  let genv = Global.env_of_context Environ.empty_named_context_val in
  let ist = empty_glob_sign ~strict:(env_strict env) genv in
  let ist = { ist with extra = Store.set ist.extra ltac2_env env } in
  let arg, tpe = obj.ml_intern ist arg in
  let e = match arg with
  | GlbVal arg -> GTacExt (tag, arg)
  | GlbTacexpr e -> e
  in
  check (e, tpe)
| CTacGlb (prms, args, body, ty) ->
  let tysubst = Array.init prms (fun _ -> fresh_id env) in
  let tysubst i = GTypVar tysubst.(i) in
  let ty = subst_type tysubst ty in
  let ty = match tycon with
    | None -> ty
    | Some tycon ->
      let () = unify ?loc env ty tycon in
      tycon
  in
  let args = List.map (fun (na, arg, ty) ->
      let ty = Option.map (subst_type tysubst) ty in
      let () = match na.CAst.v, ty with
        | Anonymous, None | Name _, Some _ -> ()
        | Anonymous, Some _ | Name _, None -> assert false
      in
      let e, _ = intern_rec env ty arg in
      na.CAst.v, e)
      args
  in
  if CList.is_empty args then body, ty
  else GTacLet (false, args, body), ty

and intern_rec_with_constraint env e exp =
  let (er, t) = intern_rec env (Some exp) e in
  er

and intern_let env loc ids el tycon e =
  let avoid = Id.Set.union ids (bound_vars env) in
  let fold avoid (pat, t, e) =
    let nas, exp = expand_pattern avoid [pat, t] in
    let na = match nas with [x] -> x | _ -> assert false in
    let avoid = List.fold_left add_name avoid nas in
    (avoid, (na, exp, t, e))
  in
  let (_, el) = List.fold_left_map fold avoid el in
  let fold body (na, exp, tc, e) =
    let tc = Option.map (intern_type env) tc in
    let (e, t) = intern_rec env tc e in
    let t = if is_value e then abstract_var env t else monomorphic t in
    (exp body, (na, e, t))
  in
  let (e, elp) = List.fold_left_map fold e el in
  let env = List.fold_left (fun accu (na, _, t) -> push_name na t accu) env elp in
  let (e, t) = intern_rec env tycon e in
  let () = check_unused_variables ?loc env (List.map pi1 elp) in
  let el = List.map (fun (na, e, _) -> na, e) elp in
  (GTacLet (false, el, e), t)

and intern_let_rec env loc el tycon e =
  let map env (pat, t, e) =
    let na = match pat.v with
    | CPatVar na -> na
    | CPatAtm _ | CPatRef _ | CPatCnv _ | CPatOr _ | CPatAs _ | CPatRecord _ ->
      user_err ?loc:pat.loc (str "This kind of pattern is forbidden in let-rec bindings")
    in
    let t = match t with
      | None -> GTypVar (fresh_id env)
      | Some t -> intern_type env t
    in
    let env = push_name na (monomorphic t) env in
    (env, (na, t, e))
  in
  let (env, el) = List.fold_left_map map env el in
  (* Get easily accessible type information about the recursive bindings before they are used.
     Typically "let rec foo (x:int) : bool := ... in ..."
     gets desugared to "let rec foo := fun (x:int) => ... : bool in ..."
     and we want to have "foo : int -> bool" before we see any uses of foo.

     This produces nicer type errors but is otherwise semantically equivalent. *)
  let map (na, t, e) = match e.v with
    | CTacCnv (e',t') ->
      let t' = intern_type env t' in
      let () = unify ?loc:e.loc env t' t in
      na, t', e'
    | CTacFun (bnd,e') ->
      let bnd = List.map extract_pattern_type bnd in
      let map (_, t) = match t with
        | None -> GTypVar (fresh_id env)
        | Some t -> intern_type env t
      in
      let tl = List.map map bnd in
      let nas, exp = expand_pattern (bound_vars env) bnd in
      let t = List.fold_left2 (fun t na tna -> tycon_fun_body ?loc:e.loc env t tna) t nas tl in
      let e', t' = match e'.v with
        | CTacCnv (e',t') ->
          let t' = intern_type env t' in
          let () = unify ?loc:e'.loc env t' t in
          e', t'
        | _ -> e', t
      in
      let t' = List.fold_right (fun tna t' -> GTypArrow (tna, t')) tl t' in
      let pats = List.map (fun na -> CAst.make (CPatVar na)) nas in
      let e' = exp e' in
      (na, t', CAst.make ?loc:e.loc (CTacFun (pats, e')))
    | _ -> (na, t, e)
  in
  let el = List.map map el in
  let map (na, tc, e) =
    let loc_e = e.loc in
    let e = intern_rec_with_constraint env e tc in
    let () =
      if not (is_rec_rhs e) then
        user_err ?loc:loc_e (str "This kind of expression is not allowed as \
          right-hand side of a recursive binding")
    in
    (na, e)
  in
  let el = List.map map el in
  let (e, t) = intern_rec env tycon e in
  let () =
    (* TODO better loc? *)
    check_unused_variables ?loc env (List.map fst el)
  in
  (GTacLet (true, el, e), t)

and intern_constructor env loc tycon kn args = match kn with
| Other kn ->
  let cstr = interp_constructor kn in
  let nargs = List.length cstr.cdata_args in
  if Int.equal nargs (List.length args) then
    let subst = Array.init cstr.cdata_prms (fun _ -> fresh_id env) in
    let substf i = GTypVar subst.(i) in
    let types = List.map (fun t -> subst_type substf t) cstr.cdata_args in
    let targs = List.init cstr.cdata_prms (fun i -> GTypVar subst.(i)) in
    let ans = GTypRef (Other cstr.cdata_type, targs) in
    let ans = match tycon with
      | None -> ans
      | Some tycon ->
        let () = unify ?loc env ans tycon in
        tycon
    in
    let map arg tpe = intern_rec_with_constraint env arg tpe in
    let args = List.map2 map args types in
    match cstr.cdata_indx with
    | Some idx ->
      (GTacCst (Other cstr.cdata_type, idx, args), ans)
    | None ->
      (GTacOpn (kn, args), ans)
  else
    error_nargs_mismatch ?loc kn nargs (List.length args)
| Tuple n ->
  let () = if not (Int.equal n (List.length args)) then begin
      if Int.equal 0 n then
        (* parsing [() bla] produces [CTacApp (Tuple 0, [bla])] but parsing
           [((), ()) bla] produces [CTacApp (CTacApp (Tuple 2, [(); ()]), [bla])]
           so we only need to produce a sensible error for [Tuple 0] *)
        let t = GTypRef (Tuple 0, []) in
        CErrors.user_err ?loc Pp.(
            str "This expression has type" ++ spc () ++ pr_glbtype env t ++
            spc () ++ str "and is not a function")
      else assert false
    end
  in
  let types = List.init n (fun i -> GTypVar (fresh_id env)) in
  let ans = GTypRef (Tuple n, types) in
  let ans = match tycon with
    | None -> ans
    | Some tycon ->
      let () = unify ?loc env ans tycon in
      tycon
  in
  let map arg tpe = intern_rec_with_constraint env arg tpe in
  let args = List.map2 map args types in
  GTacCst (Tuple n, 0, args), ans

and intern_case env loc e tycon pl =
  let e, et = intern_rec env None e in
  let rt = match tycon with
    | Some t -> t
    | None -> GTypVar (fresh_id env)
  in
  let pl = List.map (fun (cpat,cbr) ->
      (* intern_pat: check type of pattern = type of discriminee,
         check or patterns bind same vars to same types,
         return bound vars
         + pattern representation with casts removed and names globalized *)
      let patvars, pat = intern_pat env cpat et in
      let patenv = push_ids patvars env in
      let br = intern_rec_with_constraint patenv cbr rt in
      let () = check_unused_variables ?loc patenv
          (List.map (fun (id,_) -> Name id) (Id.Map.bindings patvars))
      in
      pat, br)
      pl
  in
  let just_patterns = List.map fst pl in
  let () = check_no_missing_pattern env et just_patterns in
  let () = check_redundant_clauses env et just_patterns in
  ((e,et),pl,rt)

type context = (Id.t * type_scheme) list

let intern ~strict ctx e =
  let env = empty_env ~strict () in
  (* XXX not doing check_unused_variables *)
  let fold accu (id, t) = push_name (Name id) (polymorphic t) accu in
  let env = List.fold_left fold env ctx in
  let (e, t) = intern_rec env None e in
  let count = ref 0 in
  let vars = ref TVar.Map.empty in
  let t = normalize env (count, vars) t in
  (e, (!count, t))

let intern_typedef self (ids, t) : glb_quant_typedef =
  let env = set_rec self (empty_env ()) in
  (* Initialize type parameters *)
  let map id = get_alias id env in
  let ids = List.map map ids in
  let count = ref (List.length ids) in
  let vars = ref TVar.Map.empty in
  let iter n id = vars := TVar.Map.add id (GTypVar n) !vars in
  let () = List.iteri iter ids in
  (* Do not accept unbound type variables *)
  let env = reject_unbound_tvar env in
  let intern t =
    let t = intern_type env t in
    normalize env (count, vars) t
  in
  let count = !count in
  match t with
  | CTydDef None -> (count, GTydDef None)
  | CTydDef (Some t) -> (count, GTydDef (Some (intern t)))
  | CTydAlg constrs ->
    let map (atts, c, t) =
      let warn = Attributes.parse Attributes.user_warns atts in
      let t = List.map intern t in
      (warn, c, t)
    in
    let constrs = List.map map constrs in
    let getn (const, nonconst) (_, c, args) = match args with
    | [] -> (succ const, nonconst)
    | _ :: _ -> (const, succ nonconst)
    in
    let nconst, nnonconst = List.fold_left getn (0, 0) constrs in
    let galg = {
      galg_constructors = constrs;
      galg_nconst = nconst;
      galg_nnonconst = nnonconst;
    } in
    (count, GTydAlg galg)
  | CTydRec fields ->
    let map (c, mut, t) = (c, mut, intern t) in
    let fields = List.map map fields in
    (count, GTydRec fields)
  | CTydOpn -> (count, GTydOpn)

let intern_open_type t =
  let env = empty_env () in
  let t = intern_type env t in
  let count = ref 0 in
  let vars = ref TVar.Map.empty in
  let t = normalize env (count, vars) t in
  (!count, t)

(** Subtyping *)

let check_subtype t1 t2 =
  let env = empty_env () in
  let t1 = fresh_type_scheme env t1 in
  (* We build a substitution mimicking rigid variable by using dummy tuples *)
  let rigid i = GTypRef (Tuple (i + 1), []) in
  let (n, t2) = t2 in
  let subst = Array.init n rigid in
  let substf i = subst.(i) in
  let t2 = subst_type substf t2 in
  try unify0 env t1 t2; true with CannotUnify _ -> false

(** Globalization *)

let get_projection0 var = match var with
| RelId qid ->
  let kn = try Tac2env.locate_projection qid with Not_found ->
    user_err ?loc:qid.CAst.loc (pr_qualid qid ++ str " is not a projection")
  in
  kn
| AbsKn kn -> kn

type raw_ext = RawExt : ('a, _) Tac2dyn.Arg.tag * 'a -> raw_ext

let globalize_gen ~tacext ids tac =
  let rec globalize ids ({loc;v=er} as e) = match er with
    | CTacAtm _ -> e
    | CTacRef ref ->
      let mem id = Id.Set.mem id ids in
      begin match get_variable0 mem ref with
      | ArgVar _ -> e
      | ArgArg kn ->
        let () = check_deprecated_ltac2 ?loc ref kn in
        CAst.make ?loc @@ CTacRef (AbsKn kn)
      end
    | CTacCst qid ->
      let knc = get_constructor () qid in
      CAst.make ?loc @@ CTacCst (AbsKn knc)
    | CTacFun (bnd, e) ->
      let fold (pats, accu) pat =
        let accu = ids_of_pattern accu pat in
        let pat = globalize_pattern ids pat in
        (pat :: pats, accu)
      in
      let bnd, ids = List.fold_left fold ([], ids) bnd in
      let bnd = List.rev bnd in
      let e = globalize ids e in
      CAst.make ?loc @@ CTacFun (bnd, e)
    | CTacApp (e, el) ->
      let e = globalize ids e in
      let el = List.map (fun e -> globalize ids e) el in
      CAst.make ?loc @@ CTacApp (e, el)
    | CTacLet (isrec, bnd, e) ->
      let fold accu (pat, _) = ids_of_pattern accu pat in
      let ext = List.fold_left fold Id.Set.empty bnd in
      let eids = Id.Set.union ext ids in
      let e = globalize eids e in
      let map (qid, e) =
        let ids = if isrec then eids else ids in
        let qid = globalize_pattern ids qid in
        (qid, globalize ids e)
      in
      let bnd = List.map map bnd in
      CAst.make ?loc @@ CTacLet (isrec, bnd, e)
    | CTacSyn (el, kn) ->
      let v = expand_notation ?loc el kn in
      globalize ids v
    | CTacCnv (e, t) ->
      let e = globalize ids e in
      CAst.make ?loc @@ CTacCnv (e, t)
    | CTacSeq (e1, e2) ->
      let e1 = globalize ids e1 in
      let e2 = globalize ids e2 in
      CAst.make ?loc @@ CTacSeq (e1, e2)
    | CTacIft (e, e1, e2) ->
      let e = globalize ids e in
      let e1 = globalize ids e1 in
      let e2 = globalize ids e2 in
      CAst.make ?loc @@ CTacIft (e, e1, e2)
    | CTacCse (e, bl) ->
      let e = globalize ids e in
      let bl = List.map (fun b -> globalize_case ids b) bl in
      CAst.make ?loc @@ CTacCse (e, bl)
    | CTacRec (def, r) ->
      let def = Option.map (globalize ids) def in
      let map (p, e) =
        let p = get_projection0 p in
        let e = globalize ids e in
        (AbsKn p, e)
      in
      CAst.make ?loc @@ CTacRec (def, List.map map r)
    | CTacPrj (e, p) ->
      let e = globalize ids e in
      let p = get_projection0 p in
      CAst.make ?loc @@ CTacPrj (e, AbsKn p)
    | CTacSet (e, p, e') ->
      let e = globalize ids e in
      let p = get_projection0 p in
      let e' = globalize ids e' in
      CAst.make ?loc @@ CTacSet (e, AbsKn p, e')
    | CTacExt (tag, arg) -> tacext ?loc (RawExt (tag, arg))
    | CTacGlb (prms, args, body, ty) ->
      let args = List.map (fun (na, arg, ty) -> na, globalize ids arg, ty) args in
      CAst.make ?loc @@ CTacGlb (prms, args, body, ty)

  and globalize_case ids (p, e) =
    (globalize_pattern ids p, globalize ids e)

  and globalize_pattern ids ({loc;v=pr} as p) = match pr with
    | CPatVar _ | CPatAtm _ -> p
    | CPatRef (cst, pl) ->
      let knc = get_constructor () cst in
      let cst = AbsKn knc in
      let pl = List.map (fun p -> globalize_pattern ids p) pl in
      CAst.make ?loc @@ CPatRef (cst, pl)
    | CPatCnv (pat, ty) ->
      let pat = globalize_pattern ids pat in
      CAst.make ?loc @@ CPatCnv (pat, ty)
    | CPatOr pl ->
      let pl = List.map (fun p -> globalize_pattern ids p) pl in
      CAst.make ?loc @@ CPatOr pl
    | CPatAs (p,x) ->
      CAst.make ?loc @@ CPatAs (globalize_pattern ids p, x)
    | CPatRecord pats ->
      let map (p, e) =
        let p = get_projection0 p in
        let e = globalize_pattern ids e in
        (AbsKn p, e)
      in
      CAst.make ?loc @@ CPatRecord (List.map map pats)

  in
  globalize ids tac

let globalize ids tac =
  let tacext ?loc (RawExt (tag,_)) =
    let arg = str (Tac2dyn.Arg.repr tag) in
    CErrors.user_err ?loc (str "Cannot globalize generic arguments of type" ++ spc () ++ arg)
  in
  globalize_gen ~tacext ids tac

let debug_globalize_allow_ext ids tac =
  let tacext ?loc (RawExt (tag,arg)) = CAst.make ?loc @@ CTacExt (tag,arg) in
  globalize_gen ~tacext ids tac

let { Goptions.get = typed_notations } =
  Goptions.declare_bool_option_and_ref
    ~key:["Ltac2";"Typed";"Notations"] ~value:true ()

let intern_notation_data ids body =
  if typed_notations () then
    let env = empty_env ~strict:true () in
    let fold id (env,argtys) =
      let ty = GTypVar (fresh_id env) in
      let env = push_name (Name id) (monomorphic ty) env in
      env, Id.Map.add id ty argtys
    in
    let env, argtys = Id.Set.fold fold ids (env,Id.Map.empty) in
    let body, ty = intern_rec env None body in
    let () = check_unused_variables env
        (List.map (fun (id,_) -> Name id) (Id.Map.bindings argtys))
    in
    let count = ref 0 in
    let vars = ref TVar.Map.empty in
    let argtys = Id.Map.map (fun ty -> normalize env (count, vars) ty) argtys in
    let ty = normalize env (count, vars) ty in
    let prms = !count in
    Tac2env.TypedNota {
      nota_prms = prms;
      nota_argtys = argtys;
      nota_ty = ty;
      nota_body = body;
    }
  else
    let body = globalize ids body in
    Tac2env.UntypedNota body

(** Kernel substitution *)

open Mod_subst

let subst_or_tuple f subst o = match o with
| Tuple _ -> o
| Other v ->
  let v' = f subst v in
  if v' == v then o else Other v'

let rec subst_type subst t = match t with
| GTypVar _ -> t
| GTypArrow (t1, t2) ->
  let t1' = subst_type subst t1 in
  let t2' = subst_type subst t2 in
  if t1' == t1 && t2' == t2 then t
  else GTypArrow (t1', t2')
| GTypRef (kn, tl) ->
  let kn' = subst_or_tuple subst_kn subst kn in
  let tl' = List.Smart.map (fun t -> subst_type subst t) tl in
  if kn' == kn && tl' == tl then t else GTypRef (kn', tl')

let rec subst_glb_pat subst = function
  | (GPatVar _ | GPatAtm _) as pat0 -> pat0
  | GPatRef (ctor,pats) as pat0 ->
    let ctor' =
      let ctyp' = Option.Smart.map (subst_kn subst) ctor.ctyp in
      if ctyp' == ctor.ctyp then ctor
      else {ctor with ctyp = ctyp'}
    in
    let pats' = List.Smart.map (subst_glb_pat subst) pats in
    if ctor' == ctor && pats' == pats then pat0
    else GPatRef (ctor', pats')
  | GPatOr pats as pat0 ->
    let pats' = List.Smart.map (subst_glb_pat subst) pats in
    if pats' == pats then pat0
    else GPatOr pats'
  | GPatAs (p,x) as pat0 ->
    let p' = subst_glb_pat subst p in
    if p' == p then pat0
    else GPatAs (p',x)

let rec subst_expr subst e = match e with
| GTacAtm _ | GTacVar _ | GTacPrm _ -> e
| GTacRef kn -> GTacRef (subst_kn subst kn)
| GTacFun (ids, e) -> GTacFun (ids, subst_expr subst e)
| GTacApp (f, args) ->
  GTacApp (subst_expr subst f, List.map (fun e -> subst_expr subst e) args)
| GTacLet (r, bs, e) ->
  let bs = List.map (fun (na, e) -> (na, subst_expr subst e)) bs in
  GTacLet (r, bs, subst_expr subst e)
| GTacCst (t, n, el) as e0 ->
  let t' = subst_or_tuple subst_kn subst t in
  let el' = List.Smart.map (fun e -> subst_expr subst e) el in
  if t' == t && el' == el then e0 else GTacCst (t', n, el')
| GTacCse (e, ci, cse0, cse1) ->
  let cse0' = Array.map (fun e -> subst_expr subst e) cse0 in
  let cse1' = Array.map (fun (ids, e) -> (ids, subst_expr subst e)) cse1 in
  let ci' = subst_or_tuple subst_kn subst ci in
  GTacCse (subst_expr subst e, ci', cse0', cse1')
| GTacWth { opn_match = e; opn_branch = br; opn_default = (na, def) } as e0 ->
  let e' = subst_expr subst e in
  let def' = subst_expr subst def in
  let fold kn (self, vars, p) accu =
    let kn' = subst_kn subst kn in
    let p' = subst_expr subst p in
    if kn' == kn && p' == p then accu
    else KNmap.add kn' (self, vars, p') (KNmap.remove kn accu)
  in
  let br' = KNmap.fold fold br br in
  if e' == e && br' == br && def' == def then e0
  else GTacWth { opn_match = e'; opn_default = (na, def'); opn_branch = br' }
| GTacFullMatch (e,brs) as e0 ->
  let e' = subst_expr subst e in
  let brs' = List.Smart.map (fun (pat,br as pbr) ->
      let pat' = subst_glb_pat subst pat in
      let br' = subst_expr subst br in
      if pat' == pat && br' == br then pbr
      else (pat',br'))
      brs
  in
  if e' == e && brs' == brs then e0
  else GTacFullMatch (e', brs')
| GTacPrj (kn, e, p) as e0 ->
  let kn' = subst_kn subst kn in
  let e' = subst_expr subst e in
  if kn' == kn && e' == e then e0 else GTacPrj (kn', e', p)
| GTacSet (kn, e, p, r) as e0 ->
  let kn' = subst_kn subst kn in
  let e' = subst_expr subst e in
  let r' = subst_expr subst r in
  if kn' == kn && e' == e && r' == r then e0 else GTacSet (kn', e', p, r')
| GTacExt (tag, arg) ->
  let tpe = interp_ml_object tag in
  let arg' = tpe.ml_subst subst arg in
  if arg' == arg then e else GTacExt (tag, arg')
| GTacOpn (kn, el) as e0 ->
  let kn' = subst_kn subst kn in
  let el' = List.Smart.map (fun e -> subst_expr subst e) el in
  if kn' == kn && el' == el then e0 else GTacOpn (kn', el')

let subst_typedef subst e = match e with
| GTydDef t ->
  let t' = Option.Smart.map (fun t -> subst_type subst t) t in
  if t' == t then e else GTydDef t'
| GTydAlg galg ->
  let map (warn, c, tl as p) =
    let tl' = List.Smart.map (fun t -> subst_type subst t) tl in
    if tl' == tl then p else (warn, c, tl')
  in
  let constrs' = List.Smart.map map galg.galg_constructors in
  if constrs' == galg.galg_constructors then e
  else GTydAlg { galg with galg_constructors = constrs' }
| GTydRec fields ->
  let map (c, mut, t as p) =
    let t' = subst_type subst t in
    if t' == t then p else (c, mut, t')
  in
  let fields' = List.Smart.map map fields in
  if fields' == fields then e else GTydRec fields'
| GTydOpn -> GTydOpn

let subst_quant_typedef subst (prm, def as qdef) =
  let def' = subst_typedef subst def in
  if def' == def then qdef else (prm, def')

let subst_type_scheme subst (prm, t as sch) =
  let t' = subst_type subst t in
  if t' == t then sch else (prm, t')

let subst_or_relid subst ref = match ref with
| RelId _ -> ref
| AbsKn kn ->
  let kn' = subst_or_tuple subst_kn subst kn in
  if kn' == kn then ref else AbsKn kn'

let rec subst_rawtype subst ({loc;v=tr} as t) = match tr with
| CTypVar _ -> t
| CTypArrow (t1, t2) ->
  let t1' = subst_rawtype subst t1 in
  let t2' = subst_rawtype subst t2 in
  if t1' == t1 && t2' == t2 then t else CAst.make ?loc @@ CTypArrow (t1', t2')
| CTypRef (ref, tl) ->
  let ref' = subst_or_relid subst ref in
  let tl' = List.Smart.map (fun t -> subst_rawtype subst t) tl in
  if ref' == ref && tl' == tl then t else CAst.make ?loc @@ CTypRef (ref', tl')

let subst_tacref subst ref = match ref with
| RelId _ -> ref
| AbsKn (TacConstant kn) ->
  let kn' = subst_kn subst kn in
  if kn' == kn then ref else AbsKn (TacConstant kn')
| AbsKn (TacAlias kn) ->
  let kn' = subst_kn subst kn in
  if kn' == kn then ref else AbsKn (TacAlias kn')

let subst_projection subst prj = match prj with
| RelId _ -> prj
| AbsKn kn ->
  let kn' = subst_kn subst kn in
  if kn' == kn then prj else AbsKn kn'

let rec subst_rawpattern subst ({loc;v=pr} as p) = match pr with
| CPatVar _ | CPatAtm _ -> p
| CPatRef (c, pl) ->
  let pl' = List.Smart.map (fun p -> subst_rawpattern subst p) pl in
  let c' = subst_or_relid subst c in
  if pl' == pl && c' == c then p else CAst.make ?loc @@ CPatRef (c', pl')
| CPatCnv (pat, ty) ->
  let pat' = subst_rawpattern subst pat in
  let ty' = subst_rawtype subst ty in
  if pat' == pat && ty' == ty then p else CAst.make ?loc @@ CPatCnv (pat', ty')
| CPatOr pl ->
  let pl' = List.Smart.map (fun p -> subst_rawpattern subst p) pl in
  if pl' == pl then p else CAst.make ?loc @@ CPatOr pl'
| CPatAs (pat,x) ->
  let pat' = subst_rawpattern subst pat in
  if pat' == pat then p else CAst.make ?loc @@ CPatAs (pat', x)
| CPatRecord el ->
  let map (prj, e as p) =
    let prj' = subst_projection subst prj in
    let e' = subst_rawpattern subst e in
    if prj' == prj && e' == e then p else (prj', e')
  in
  let el' = List.Smart.map map el in
  if el' == el then p else CAst.make ?loc @@ CPatRecord el'

(** Used for notations *)
let rec subst_rawexpr subst ({loc;v=tr} as t) = match tr with
| CTacAtm _ -> t
| CTacRef ref ->
  let ref' = subst_tacref subst ref in
  if ref' == ref then t else CAst.make ?loc @@ CTacRef ref'
| CTacCst ref ->
  let ref' = subst_or_relid subst ref in
  if ref' == ref then t else CAst.make ?loc @@ CTacCst ref'
| CTacFun (bnd, e) ->
  let map pat = subst_rawpattern subst pat in
  let bnd' = List.Smart.map map bnd in
  let e' = subst_rawexpr subst e in
  if bnd' == bnd && e' == e then t else CAst.make ?loc @@ CTacFun (bnd', e')
| CTacApp (e, el) ->
  let e' = subst_rawexpr subst e in
  let el' = List.Smart.map (fun e -> subst_rawexpr subst e) el in
  if e' == e && el' == el then t else CAst.make ?loc @@ CTacApp (e', el')
| CTacLet (isrec, bnd, e) ->
  let map (na, e as p) =
    let na' = subst_rawpattern subst na in
    let e' = subst_rawexpr subst e in
    if na' == na && e' == e then p else (na', e')
  in
  let bnd' = List.Smart.map map bnd in
  let e' = subst_rawexpr subst e in
  if bnd' == bnd && e' == e then t else CAst.make ?loc @@ CTacLet (isrec, bnd', e')
| CTacCnv (e, c) ->
  let e' = subst_rawexpr subst e in
  let c' = subst_rawtype subst c in
  if c' == c && e' == e then t else CAst.make ?loc @@ CTacCnv (e', c')
| CTacSeq (e1, e2) ->
  let e1' = subst_rawexpr subst e1 in
  let e2' = subst_rawexpr subst e2 in
  if e1' == e1 && e2' == e2 then t else CAst.make ?loc @@ CTacSeq (e1', e2')
| CTacIft (e, e1, e2) ->
  let e' = subst_rawexpr subst e in
  let e1' = subst_rawexpr subst e1 in
  let e2' = subst_rawexpr subst e2 in
  if e' == e && e1' == e1 && e2' == e2 then t else CAst.make ?loc @@ CTacIft (e', e1', e2')
| CTacCse (e, bl) ->
  let map (p, e as x) =
    let p' = subst_rawpattern subst p in
    let e' = subst_rawexpr subst e in
    if p' == p && e' == e then x else (p', e')
  in
  let e' = subst_rawexpr subst e in
  let bl' = List.Smart.map map bl in
  if e' == e && bl' == bl then t else CAst.make ?loc @@ CTacCse (e', bl')
| CTacRec (def, el) ->
  let def' = Option.Smart.map (subst_rawexpr subst) def in
  let map (prj, e as p) =
    let prj' = subst_projection subst prj in
    let e' = subst_rawexpr subst e in
    if prj' == prj && e' == e then p else (prj', e')
  in
  let el' = List.Smart.map map el in
  if def' == def && el' == el then t else CAst.make ?loc @@ CTacRec (def',el')
| CTacPrj (e, prj) ->
    let prj' = subst_projection subst prj in
    let e' = subst_rawexpr subst e in
    if prj' == prj && e' == e then t else CAst.make ?loc @@ CTacPrj (e', prj')
| CTacSet (e, prj, r) ->
    let prj' = subst_projection subst prj in
    let e' = subst_rawexpr subst e in
    let r' = subst_rawexpr subst r in
    if prj' == prj && e' == e && r' == r then t else CAst.make ?loc @@ CTacSet (e', prj', r')
| CTacGlb (prms, args, body, ty) ->
  let args' = List.Smart.map (fun (na, arg, ty as o) ->
      let arg' = subst_rawexpr subst arg in
      let ty' = Option.Smart.map (subst_type subst) ty in
      if arg' == arg && ty' == ty then o
      else (na, arg', ty'))
      args
  in
  let body' = subst_expr subst body in
  let ty' = subst_type subst ty in
  if args' == args && body' == body && ty' == ty then t
  else CAst.make ?loc @@ CTacGlb (prms, args', body', ty')
| CTacSyn _ | CTacExt _ -> assert false (** Should not be generated by globalization *)

(** Registering *)

let genintern_core ?(check_unused=true) ist locals expected v =
  let open Genintern in
  let env = match Genintern.Store.get ist.extra ltac2_env with
    | None ->
      (* Only happens when Ltac2 is called from a toplevel ltac1 quotation *)
      empty_env ~strict:ist.strict_check ()
    | Some env -> env
  in
  let env = List.fold_left (fun env (na,t) -> push_name na t env) env locals in
  let loc = v.CAst.loc in
  let v, t = intern_rec env expected v in
  let () = if check_unused then check_unused_variables ?loc env (List.map fst locals) in
  env, v, t

let genintern_warn_not_unit ?check_unused ist locals ({CAst.loc} as v) =
  let env, v, t = genintern_core ?check_unused ist locals None v in
  let () = check_elt_unit loc env t in
  v

let genintern ?check_unused ist locals expected v =
  let _, v, _ = genintern_core ?check_unused ist locals (Some expected) v in
  v

let () =
  let open Genintern in
  let intern ist tac =
    let t_preterm = monomorphic (GTypRef (Other t_preterm, [])) in
    let ntn_vars = ist.intern_sign.notation_variable_status in
    let locals =
      Id.Map.fold (fun id _ acc -> (Name id, t_preterm) :: acc) ntn_vars []
    in
    (* don't check unused variables: we may be in the case of
       eg "Notation foo x := (ltac2:(tac) + x)" which shouldn't call x unused *)
    let v = genintern_warn_not_unit ~check_unused:false ist locals tac in
    let ids = Id.Map.domain ntn_vars in
    (ist, (ids, v))
  in
  Genintern.register_intern0 wit_ltac2_constr intern

let () = Gensubst.register_subst0 wit_ltac2_constr (fun s (ids, e) -> ids, subst_expr s e)

let intern_var_quotation_gen ~ispat ist (kind, { CAst.v = id; loc }) =
  let open Genintern in
  let kind = match kind with
    | None -> ConstrVar
    | Some kind -> match Id.to_string kind.CAst.v with
      | "constr" -> ConstrVar
      | "preterm" -> PretermVar
      | "pattern" -> PatternVar
      | _ ->
        CErrors.user_err ?loc:kind.loc
          Pp.(str "Unknown Ltac2 variable quotation kind" ++ spc() ++ Id.print kind.v)
  in
  let typ = match kind with
    | ConstrVar ->
      if ispat
      then CErrors.user_err ?loc Pp.(str "constr quotations not supported in tactic patterns.")
      else t_constr
    | PretermVar ->
      if ispat
      then CErrors.user_err ?loc Pp.(str "preterm quotations not supported in tactic patterns.")
      else t_preterm
    | PatternVar ->
      if not ispat
      then CErrors.user_err ?loc Pp.(str "pattern quotations not supported outside tactic patterns.")
      else t_pattern
  in
  let env = match Genintern.Store.get ist.extra ltac2_env with
    | None ->
      (* Only happens when Ltac2 is called from a constr or ltac1 quotation *)
      empty_env ~strict:ist.strict_check ()
    | Some env -> env
  in
  (* Special handling of notation variables *)
  let () =
    if Id.Map.mem id ist.intern_sign.notation_variable_status then
      (* Always fail for constr, never for preterm *)
      unify ?loc env (GTypRef (Other t_preterm, [])) (GTypRef (Other typ, []))
  in
  let t =
    try find_var id env
    with Not_found ->
      CErrors.user_err ?loc (str "Unbound value " ++ Id.print id)
  in
  let t = fresh_mix_type_scheme env t in
  let () = unify ?loc env t (GTypRef (Other typ, [])) in
  (ist, (kind, id))

let intern_var_quotation = intern_var_quotation_gen ~ispat:false

let () = Genintern.register_intern0 wit_ltac2_var_quotation intern_var_quotation

let intern_var_quotation_pat ?loc ist v =
  intern_var_quotation_gen ~ispat:true ist v

let () = Genintern.register_intern_pat wit_ltac2_var_quotation
    intern_var_quotation_pat

let () = Gensubst.register_subst0 wit_ltac2_var_quotation (fun _ v -> v)
