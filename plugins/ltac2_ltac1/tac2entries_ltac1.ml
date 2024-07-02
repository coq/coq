(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

open Ltac2_plugin

open Tac2expr

let check_lowercase {loc;v=id} =
  if Tac2env.is_constructor (Libnames.qualid_of_ident id) then
    user_err ?loc (str "The identifier " ++ Id.print id ++ str " must be lowercase")

(** Parsing *)

type 'a token =
| TacTerm of string
| TacNonTerm of Name.t * 'a

type 'a token_or_var =
| TokTok of 'a token
| TokVar of Id.t

type scope_rule =
| ScopeRule : (raw_tacexpr, _, 'a) Pcoq.Symbol.t * ('a -> raw_tacexpr) -> scope_rule

type scope_interpretation = sexpr list -> scope_rule

let scope_table : scope_interpretation Id.Map.t ref = ref Id.Map.empty

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
  ScopeRule (Pcoq.Symbol.token (Tok.PIDENT (Some str)), (fun _ -> v_unit))
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

let parse_token_or_var = function
| SexprRec (_, {v=Some na}, []) -> TokVar na
| sexpr -> TokTok (parse_token sexpr)

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

type ('self, 'r) nrule =
| NRule :
  ('self, Gramlib.Grammar.norec, 'act, Loc.t -> 'r) Pcoq.Rule.t *
  ((Loc.t -> (Name.t * raw_tacexpr * Id.t option) list -> 'r) -> 'act) -> ('self, 'r) nrule

let rec get_norec_rule : type self r. scope_rule token_or_var list -> (self, r) nrule = function
| [] -> NRule (Pcoq.Rule.stop, fun k loc -> k loc [])
| TokTok (TacNonTerm (na, ScopeRule (scope, inj))) :: tok ->
  let NRule (rule, act) = get_norec_rule tok in
  let scope = match Pcoq.generalize_symbol scope with
  | None -> user_err Pp.(str "Ltac1 notations cannot mention recursive scopes like \"self\"")
  | Some scope -> scope
  in
  let rule = Pcoq.Rule.next_norec rule scope in
  let act k e = act (fun loc acc -> k loc ((na, inj e, None) :: acc)) in
  NRule (rule, act)
| TokTok (TacTerm t) :: tok ->
  let NRule (rule, act) = get_norec_rule tok in
  let rule = Pcoq.(Rule.next_norec rule (Symbol.token (Pcoq.terminal t))) in
  let act k _ = act k in
  NRule (rule, act)
| TokVar id :: tok ->
  let NRule (rule, act) = get_norec_rule tok in
  let scope = Pcoq.Symbol.nterm Pcoq.Prim.ident in
  let rule = Pcoq.Rule.next_norec rule scope in
  let inj loc = CAst.make ~loc (CTacRef (RelId (qualid_of_ident ~loc id))) in
  let act k e = act (fun loc acc -> k loc ((Name id, inj loc, Some e) :: acc)) in
  NRule (rule, act)

let deprecated_ltac2_notation =
  Deprecation.create_warning
    ~object_name:"Ltac2 in Ltac1 notation"
    ~warning_name_if_no_since:"deprecated-ltac2-in-ltac1-notation"
    (fun (toks : sexpr list) -> pr_sequence ParseToken.print_token toks)

let cache_synext_interp (local,kn,tac) =
  Tac2env.define_notation kn (UntypedNota tac)

let open_synext_interp i o =
  if Int.equal i 1 then cache_synext_interp o

let subst_synext_interp (subst, (local,kn,tac as o)) =
  let tac' = Tac2intern.subst_rawexpr subst tac in
  let kn' = Mod_subst.subst_kn subst kn in
  if kn' == kn && tac' == tac then o else
  (local, kn', tac')

let classify_synext_interp (local,_,_) =
  if local then Dispose else Substitute

let inTac2NotationInterp : (bool*KerName.t*raw_tacexpr) -> obj =
  declare_object {(default_object "TAC2-IN-TAC1-NOTATION-INTERP") with
     cache_function  = cache_synext_interp;
     open_function   = simple_open ~cat:Tac2entries.ltac2_notation_cat open_synext_interp;
     subst_function = subst_synext_interp;
     classify_function = classify_synext_interp}

let rec string_of_scope = function
| SexprStr s -> Printf.sprintf "str(%s)" s.CAst.v
| SexprInt i -> Printf.sprintf "int(%i)" i.CAst.v
| SexprRec (_, {v=na}, []) -> Option.cata Id.to_string "_" na
| SexprRec (_, {v=na}, e) ->
  Printf.sprintf "%s(%s)" (Option.cata Id.to_string "_" na) (String.concat " " (List.map string_of_scope e))

let string_of_token = function
| SexprStr {v=s} -> Printf.sprintf "str(%s)" s
| SexprRec (_, {v=na}, [tok]) -> string_of_scope tok
| SexprRec (_, {v=id}, _) -> Option.cata Id.to_string "_" id
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
| Synext of bool * KerName.t * Id.Set.t * raw_tacexpr

type tac1ext = {
  tac1ext_kn : KerName.t;
  tac1ext_tok : sexpr list;
  tac1ext_lev : int;
  tac1ext_loc : bool;
  tac1ext_depr : Deprecation.t option;
}

let perform_ltac1_notation syn st =
  let tok = List.rev_map ParseToken.parse_token_or_var syn.tac1ext_tok in
  let NRule (rule, act) = get_norec_rule tok in
  let mk loc args =
    let () = match syn.tac1ext_depr with
    | None -> ()
    | Some depr -> deprecated_ltac2_notation ~loc (syn.tac1ext_tok, depr)
    in
    let map (na, e, istac1) =
      ((CAst.make ?loc:e.loc @@ na), e)
    in
    let bnd = List.map map args in
    let map (na, e, tac1) = match tac1 with
    | None -> None
    | Some src ->
      let loc = e.CAst.loc in
      match na with
      | Anonymous -> assert false
      | Name tgt -> Some (loc, src, tgt)
    in
    let ltac1bnd = List.map_filter map args in
    let ast = CAst.make ~loc @@ CTacSyn (bnd, syn.tac1ext_kn) in
    let local = List.map (fun (loc, _, tgt) -> CAst.make ?loc tgt) ltac1bnd in
    let ast = Genarg.in_gen (Genarg.rawwit Tac2env.wit_ltac2in1) (local, ast) in
    let open Ltac_plugin.Tacexpr in
    let ast = TacGeneric (Some "ltac2", ast) in
    if List.is_empty ltac1bnd then
      CAst.make ~loc @@ (TacArg ast)
    else
      (* Ltac1 acrobatics *)
      let fid = Id.of_string "F" in
      let avoid = Id.Set.of_list (List.map (fun (_, src, _) -> src) ltac1bnd) in
      let fid = Namegen.next_ident_away fid avoid in
      let map (loc, src, _) = Reference (Libnames.qualid_of_ident ?loc src) in
      let vars = List.map map ltac1bnd in
      let call = TacCall (CAst.make ~loc @@ (qualid_of_ident ~loc fid, vars)) in
      let call = CAst.make ~loc @@ (TacArg call) in
      CAst.make ~loc @@ (TacLetIn (false, [CAst.make ~loc (Name fid), ast], call))
  in
  let rule = Pcoq.Production.make rule (act mk) in
  let entry, pos =
    let open Ltac_plugin in
    if Int.equal syn.tac1ext_lev 0 then
      Pltac.simple_tactic, None
    else if 1 <= syn.tac1ext_lev && syn.tac1ext_lev <= 5 then
      Pltac.ltac_expr, Some (string_of_int syn.tac1ext_lev)
    else
      user_err Pp.(str ("Invalid Tactic Notation level: "^(string_of_int syn.tac1ext_lev)^"."))
  in
  let rule = Pcoq.Reuse (pos, [rule]) in
  ([Pcoq.ExtendRule (entry, rule)], st)

let ltac2_in_ltac1_notation =
  Pcoq.create_grammar_command "ltac2-in-ltac1-notation"
    { gext_fun = perform_ltac1_notation; gext_eq = (==) (* FIXME *) }

let cache_tac1ext syn =
  Pcoq.extend_grammar_command ltac2_in_ltac1_notation syn

let open_tac1ext i syn =
  if Int.equal i 1 then Pcoq.extend_grammar_command ltac2_in_ltac1_notation syn

let subst_tac1ext (subst, syn) =
  let kn = Mod_subst.subst_kn subst syn.tac1ext_kn in
  if kn == syn.tac1ext_kn then syn else { syn with tac1ext_kn = kn }

let classify_tac1ext o =
  if o.tac1ext_loc then Dispose else Substitute

let inTac1Notation : tac1ext -> obj =
  declare_object {(default_object "TAC2INTAC1-NOTATION") with
     cache_function  = cache_tac1ext;
     object_stage = Summary.Stage.Synterp;
     open_function   = simple_open ~cat:Tac2entries.ltac2_notation_cat open_tac1ext;
     subst_function = subst_tac1ext;
     classify_function = classify_tac1ext}

let register_ltac1_notation atts tkn lev body =
  let deprecation, local = Attributes.(parse Notations.(deprecation ++ locality)) atts in
  let local = Option.default false local in
  match tkn, lev with
  | [SexprRec (_, {loc;v=Some id}, [])], None ->
    (* Tactic abbreviation *)
    user_err (str "Abbreviations are not allowed for Ltac1")
  | _ ->
    (* Check that the tokens make sense *)
    let fold_tok accu tok = match tok with
    | TacTerm _ -> accu
    | TacNonTerm (Name id, _) -> Id.Set.add id accu
    | TacNonTerm (Anonymous, _) -> accu
    in
    let ids =
      let entries = List.map ParseToken.parse_token_or_var tkn in
      let fold accu t = match t with
      | TokTok tok -> fold_tok accu tok
      | TokVar id -> Id.Set.add id accu
      in
      List.fold_left fold Id.Set.empty entries
    in
    let key = make_fresh_key tkn in
    let () =
      let lev = match lev with
      | Some n ->
        n (* FIXME: check that it makes sense *)
      | None -> 5
      in
      let ext = {
        tac1ext_kn = key;
        tac1ext_tok = tkn;
        tac1ext_lev = lev;
        tac1ext_loc = local;
        tac1ext_depr = deprecation;
      } in
      Lib.add_leaf (inTac1Notation ext)
    in
    Synext (local, key, ids, body)

let register_ltac1_notation_interpretation = function
  | Synext (local, kn, ids, body) ->
    let body = Tac2intern.globalize ids body in
    Lib.add_leaf (inTac2NotationInterp (local,kn,body))
