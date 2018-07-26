(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Libobject
open Genarg
open Extend
open Pcoq
open Egramml
open Vernacexpr
open Libnames
open Nameops

type 'a grammar_tactic_prod_item_expr = 'a Pptactic.grammar_tactic_prod_item_expr =
| TacTerm of string
| TacNonTerm of ('a * Names.Id.t option) Loc.located

type raw_argument = string * string option
type argument = Genarg.ArgT.any Extend.user_symbol

(**********************************************************************)
(* Interpret entry names of the form "ne_constr_list" as entry keys   *)

let coincide s pat off =
  let len = String.length pat in
  let break = ref true in
  let i = ref 0 in
  while !break && !i < len do
    let c = Char.code s.[off + !i] in
    let d = Char.code pat.[!i] in
    break := Int.equal c d;
    incr i
  done;
  !break

let atactic n =
  if n = 5 then Aentry Pltac.binder_tactic
  else Aentryl (Pltac.tactic_expr, string_of_int n)

type entry_name = EntryName :
  'a raw_abstract_argument_type * (Tacexpr.raw_tactic_expr, 'a) Extend.symbol -> entry_name

(** Quite ad-hoc *)
let get_tacentry n m =
  let check_lvl n =
    Int.equal m n
    && not (Int.equal m 5) (* Because tactic5 is at binder_tactic *)
    && not (Int.equal m 0) (* Because tactic0 is at simple_tactic *)
  in
  if check_lvl n then EntryName (rawwit Tacarg.wit_tactic, Aself)
  else if check_lvl (n + 1) then EntryName (rawwit Tacarg.wit_tactic, Anext)
  else EntryName (rawwit Tacarg.wit_tactic, atactic n)

let get_separator = function
| None -> user_err Pp.(str "Missing separator.")
| Some sep -> sep

let check_separator ?loc = function
| None -> ()
| Some _ -> user_err ?loc (str "Separator is only for arguments with suffix _list_sep.")

let rec parse_user_entry ?loc s sep =
  let l = String.length s in
  if l > 8 && coincide s "ne_" 0 && coincide s "_list" (l - 5) then
    let entry = parse_user_entry ?loc (String.sub s 3 (l-8)) None in
    check_separator ?loc sep;
    Ulist1 entry
  else if l > 12 && coincide s "ne_" 0 &&
                   coincide s "_list_sep" (l-9) then
    let entry = parse_user_entry ?loc (String.sub s 3 (l-12)) None in
    Ulist1sep (entry, get_separator sep)
  else if l > 5 && coincide s "_list" (l-5) then
    let entry = parse_user_entry ?loc (String.sub s 0 (l-5)) None in
    check_separator ?loc sep;
    Ulist0 entry
  else if l > 9 && coincide s "_list_sep" (l-9) then
    let entry = parse_user_entry ?loc (String.sub s 0 (l-9)) None in
    Ulist0sep (entry, get_separator sep)
  else if l > 4 && coincide s "_opt" (l-4) then
    let entry = parse_user_entry ?loc (String.sub s 0 (l-4)) None in
    check_separator ?loc sep;
    Uopt entry
  else if Int.equal l 7 && coincide s "tactic" 0 && '5' >= s.[6] && s.[6] >= '0' then
    let n = Char.code s.[6] - 48 in
    check_separator ?loc sep;
    Uentryl ("tactic", n)
  else
    let _ = check_separator ?loc sep in
    Uentry s

let interp_entry_name interp symb =
  let rec eval = function
  | Ulist1 e -> Ulist1 (eval e)
  | Ulist1sep (e, sep) -> Ulist1sep (eval e, sep)
  | Ulist0 e -> Ulist0 (eval e)
  | Ulist0sep (e, sep) -> Ulist0sep (eval e, sep)
  | Uopt e -> Uopt (eval e)
  | Uentry s -> Uentry (interp s None)
  | Uentryl (s, n) -> Uentryl (interp s (Some n), n)
  in
  eval symb

(**********************************************************************)
(** Grammar declaration for Tactic Notation (Coq level)               *)

let get_tactic_entry n =
  if Int.equal n 0 then
    Pltac.simple_tactic, None
  else if Int.equal n 5 then
    Pltac.binder_tactic, None
  else if 1<=n && n<5 then
    Pltac.tactic_expr, Some (Extend.Level (string_of_int n))
  else
    user_err Pp.(str ("Invalid Tactic Notation level: "^(string_of_int n)^"."))

(**********************************************************************)
(** State of the grammar extensions                                   *)

type tactic_grammar = {
  tacgram_level : int;
  tacgram_prods : Pptactic.grammar_terminals;
}

(* Declaration of the tactic grammar rule *)

let head_is_ident tg = match tg.tacgram_prods with
| TacTerm _ :: _ -> true
| _ -> false

let rec prod_item_of_symbol lev = function
| Extend.Ulist1 s ->
  let EntryName (Rawwit typ, e) = prod_item_of_symbol lev s in
  EntryName (Rawwit (ListArg typ), Alist1 e)
| Extend.Ulist0 s ->
  let EntryName (Rawwit typ, e) = prod_item_of_symbol lev s in
  EntryName (Rawwit (ListArg typ), Alist0 e)
| Extend.Ulist1sep (s, sep) ->
  let EntryName (Rawwit typ, e) = prod_item_of_symbol lev s in
  EntryName (Rawwit (ListArg typ), Alist1sep (e, Atoken (CLexer.terminal sep)))
| Extend.Ulist0sep (s, sep) ->
  let EntryName (Rawwit typ, e) = prod_item_of_symbol lev s in
  EntryName (Rawwit (ListArg typ), Alist0sep (e, Atoken (CLexer.terminal sep)))
| Extend.Uopt s ->
  let EntryName (Rawwit typ, e) = prod_item_of_symbol lev s in
  EntryName (Rawwit (OptArg typ), Aopt e)
| Extend.Uentry arg ->
  let ArgT.Any tag = arg in
  let wit = ExtraArg tag in
  EntryName (Rawwit wit, Extend.Aentry (genarg_grammar wit))
| Extend.Uentryl (s, n) ->
  let ArgT.Any tag = s in
  assert (coincide (ArgT.repr tag) "tactic" 0);
  get_tacentry n lev

(** Tactic grammar extensions *)

let add_tactic_entry (kn, ml, tg) state =
  let open Tacexpr in
  let entry, pos = get_tactic_entry tg.tacgram_level in
  let mkact loc l =
    let map arg =
      (** HACK to handle especially the tactic(...) entry *)
      let wit = Genarg.rawwit Tacarg.wit_tactic in
      if Genarg.has_type arg wit && not ml then
        Tacexp (Genarg.out_gen wit arg)
      else
        TacGeneric arg
    in
    let l = List.map map l in
    (TacAlias (Loc.tag ~loc (kn,l)):raw_tactic_expr)
  in
  let () =
    if Int.equal tg.tacgram_level 0 && not (head_is_ident tg) then
      user_err Pp.(str "Notation for simple tactic must start with an identifier.")
  in
  let map = function
  | TacTerm s -> GramTerminal s
  | TacNonTerm (loc, (s, ido)) ->
    let EntryName (typ, e) = prod_item_of_symbol tg.tacgram_level s in
    GramNonTerminal (Loc.tag ?loc @@ (Option.map (fun _ -> typ) ido, e))
  in
  let prods = List.map map tg.tacgram_prods in
  let rules = make_rule mkact prods in
  let r = ExtendRule (entry, None, (pos, [(None, None, [rules])])) in
  ([r], state)

let tactic_grammar =
  create_grammar_command "TacticGrammar" add_tactic_entry

let extend_tactic_grammar kn ml ntn = extend_grammar_command tactic_grammar (kn, ml, ntn)

(**********************************************************************)
(* Tactic Notation                                                    *)

let entry_names = ref String.Map.empty

let register_tactic_notation_entry name entry =
  let entry = match entry with
  | ExtraArg arg -> ArgT.Any arg
  | _ -> assert false
  in
  entry_names := String.Map.add name entry !entry_names

let interp_prod_item = function
  | TacTerm s -> TacTerm s
  | TacNonTerm (loc, ((nt, sep), ido)) ->
    let symbol = parse_user_entry ?loc nt sep in
    let interp s = function
    | None ->
      if String.Map.mem s !entry_names then String.Map.find s !entry_names
      else begin match ArgT.name s with
      | None -> user_err Pp.(str ("Unknown entry "^s^"."))
      | Some arg -> arg
      end
    | Some n ->
      (** FIXME: do better someday *)
      assert (String.equal s "tactic");
      begin match Tacarg.wit_tactic with
      | ExtraArg tag -> ArgT.Any tag
      end
    in
    let symbol = interp_entry_name interp symbol in
    TacNonTerm (loc, (symbol, ido))

let make_fresh_key =
  let id = Summary.ref ~name:"TACTIC-NOTATION-COUNTER" 0 in
  fun prods ->
    let cur = incr id; !id in
    let map = function
    | TacTerm s -> s
    | TacNonTerm _ -> "#"
    in
    let prods = String.concat "_" (List.map map prods) in
    (** We embed the hash of the kernel name in the label so that the identifier
        should be mostly unique. This ensures that including two modules
        together won't confuse the corresponding labels. *)
    let hash = (cur lxor (ModPath.hash (Lib.current_mp ()))) land 0x7FFFFFFF in
    let lbl = Id.of_string_soft (Printf.sprintf "%s_%08X" prods hash) in
    Lib.make_kn lbl

type tactic_grammar_obj = {
  tacobj_key : KerName.t;
  tacobj_local : locality_flag;
  tacobj_tacgram : tactic_grammar;
  tacobj_body : Tacenv.alias_tactic;
  tacobj_forml : bool;
}

let pprule pa = {
  Pptactic.pptac_level = pa.tacgram_level;
  pptac_prods = pa.tacgram_prods;
}

let check_key key =
  if Tacenv.check_alias key then
    user_err Pp.(str "Conflicting tactic notations keys. This can happen when including \
    twice the same module.")

let cache_tactic_notation (_, tobj) =
  let key = tobj.tacobj_key in
  let () = check_key key in
  Tacenv.register_alias key tobj.tacobj_body;
  extend_tactic_grammar key tobj.tacobj_forml tobj.tacobj_tacgram;
  Pptactic.declare_notation_tactic_pprule key (pprule tobj.tacobj_tacgram)

let open_tactic_notation i (_, tobj) =
  let key = tobj.tacobj_key in
  if Int.equal i 1 && not tobj.tacobj_local then
    extend_tactic_grammar key tobj.tacobj_forml tobj.tacobj_tacgram

let load_tactic_notation i (_, tobj) =
  let key = tobj.tacobj_key in
  let () = check_key key in
  (** Only add the printing and interpretation rules. *)
  Tacenv.register_alias key tobj.tacobj_body;
  Pptactic.declare_notation_tactic_pprule key (pprule tobj.tacobj_tacgram);
  if Int.equal i 1 && not tobj.tacobj_local then
    extend_tactic_grammar key tobj.tacobj_forml tobj.tacobj_tacgram

let subst_tactic_notation (subst, tobj) =
  let open Tacenv in
  let alias = tobj.tacobj_body in
  { tobj with
    tacobj_key = Mod_subst.subst_kn subst tobj.tacobj_key;
    tacobj_body = { alias with alias_body = Tacsubst.subst_tactic subst alias.alias_body };
  }

let classify_tactic_notation tacobj = Substitute tacobj

let inTacticGrammar : tactic_grammar_obj -> obj =
  declare_object {(default_object "TacticGrammar") with
       open_function = open_tactic_notation;
       load_function = load_tactic_notation;
       cache_function = cache_tactic_notation;
       subst_function = subst_tactic_notation;
       classify_function = classify_tactic_notation}

let cons_production_parameter = function
| TacTerm _ -> None
| TacNonTerm (_, (_, ido)) -> ido

let add_glob_tactic_notation local ~level ?deprecation prods forml ids tac =
  let parule = {
    tacgram_level = level;
    tacgram_prods = prods;
  } in
  let open Tacenv in
  let tacobj = {
    tacobj_key = make_fresh_key prods;
    tacobj_local = local;
    tacobj_tacgram = parule;
    tacobj_body = { alias_args = ids; alias_body = tac; alias_deprecation = deprecation };
    tacobj_forml = forml;
  } in
  Lib.add_anonymous_leaf (inTacticGrammar tacobj)

let add_tactic_notation local n ?deprecation prods e =
  let ids = List.map_filter cons_production_parameter prods in
  let prods = List.map interp_prod_item prods in
  let tac = Tacintern.glob_tactic_env ids (Global.env()) e in
  add_glob_tactic_notation local ~level:n ?deprecation prods false ids tac

(**********************************************************************)
(* ML Tactic entries                                                  *)

exception NonEmptyArgument

(** ML tactic notations whose use can be restricted to an identifier are added
    as true Ltac entries. *)
let extend_atomic_tactic name entries =
  let open Tacexpr in
  let map_prod prods =
    let (hd, rem) = match prods with
    | TacTerm s :: rem -> (s, rem)
    | _ -> assert false (** Not handled by the ML extension syntax *)
    in
    let empty_value = function
    | TacTerm s -> raise NonEmptyArgument
    | TacNonTerm (_, (symb, _)) ->
      let EntryName (typ, e) = prod_item_of_symbol 0 symb in
      let Genarg.Rawwit wit = typ in
      let inj x = TacArg (Loc.tag @@ TacGeneric (Genarg.in_gen typ x)) in
      let default = epsilon_value inj e in
      match default with
      | None -> raise NonEmptyArgument
      | Some def -> Tacintern.intern_tactic_or_tacarg Tacintern.fully_empty_glob_sign def
    in
    try Some (hd, List.map empty_value rem) with NonEmptyArgument -> None
  in
  let entries = List.map map_prod entries in
  let add_atomic i args = match args with
  | None -> ()
  | Some (id, args) ->
    let args = List.map (fun a -> Tacexp a) args in
    let entry = { mltac_name = name; mltac_index = i } in
    let body = TacML (Loc.tag (entry, args)) in
    Tacenv.register_ltac false false (Names.Id.of_string id) body
  in
  List.iteri add_atomic entries

let add_ml_tactic_notation name ~level ?deprecation prods =
  let len = List.length prods in
  let iter i prods =
    let open Tacexpr in
    let get_id = function
    | TacTerm s -> None
    | TacNonTerm (_, (_, ido)) -> ido
    in
    let ids = List.map_filter get_id prods in
    let entry = { mltac_name = name; mltac_index = len - i - 1 } in
    let map id = Reference (Locus.ArgVar (CAst.make id)) in
    let tac = TacML (Loc.tag (entry, List.map map ids)) in
    add_glob_tactic_notation false ~level ?deprecation prods true ids tac
  in
  List.iteri iter (List.rev prods);
  (** We call [extend_atomic_tactic] only for "basic tactics" (the ones at
  tactic_expr level 0) *)
  if Int.equal level 0 then extend_atomic_tactic name prods

(**********************************************************************)
(** Ltac quotations                                                   *)

let ltac_quotations = ref String.Set.empty

let create_ltac_quotation name cast (e, l) =
  let () =
    if String.Set.mem name !ltac_quotations then
      failwith ("Ltac quotation " ^ name ^ " already registered")
  in
  let () = ltac_quotations := String.Set.add name !ltac_quotations in
  let entry = match l with
  | None -> Aentry e
  | Some l -> Aentryl (e, string_of_int l)
  in
(*   let level = Some "1" in *)
  let level = None in
  let assoc = None in
  let rule =
    Next (Next (Next (Next (Next (Stop,
      Atoken (CLexer.terminal name)),
      Atoken (CLexer.terminal ":")),
      Atoken (CLexer.terminal "(")),
      entry),
      Atoken (CLexer.terminal ")"))
  in
  let action _ v _ _ _ loc = cast (Some loc, v) in
  let gram = (level, assoc, [Rule (rule, action)]) in
  Pcoq.grammar_extend Pltac.tactic_arg None (None, [gram])

(** Command *)


type tacdef_kind =
  | NewTac of Id.t
  | UpdateTac of Tacexpr.ltac_constant

let is_defined_tac kn =
  try ignore (Tacenv.interp_ltac kn); true with Not_found -> false

let warn_unusable_identifier =
  CWarnings.create ~name:"unusable-identifier" ~category:"parsing"
      (fun id -> strbrk "The Ltac name" ++ spc () ++ Id.print id ++ spc () ++
        strbrk "may be unusable because of a conflict with a notation.")

let register_ltac local ?deprecation tacl =
  let map tactic_body =
    match tactic_body with
    | Tacexpr.TacticDefinition ({CAst.loc;v=id}, body) ->
        let kn = Lib.make_kn id in
        let id_pp = Id.print id in
        let () = if is_defined_tac kn then
          CErrors.user_err ?loc
            (str "There is already an Ltac named " ++ id_pp ++ str".")
        in
        let is_shadowed =
          try
            match Pcoq.parse_string Pltac.tactic (Id.to_string id) with
            | Tacexpr.TacArg _ -> false
            | _ -> true (* most probably TacAtom, i.e. a primitive tactic ident *)
          with e when CErrors.noncritical e -> true (* prim tactics with args, e.g. "apply" *)
        in
        let () = if is_shadowed then warn_unusable_identifier id in
        NewTac id, body
    | Tacexpr.TacticRedefinition (qid, body) ->
        let kn =
          try Tacenv.locate_tactic qid
          with Not_found ->
            CErrors.user_err ?loc:qid.CAst.loc
                       (str "There is no Ltac named " ++ pr_qualid qid ++ str ".")
        in
        UpdateTac kn, body
  in
  let rfun = List.map map tacl in
  let recvars =
    let fold accu (op, _) = match op with
    | UpdateTac _ -> accu
    | NewTac id -> (Lib.make_path id, Lib.make_kn id) :: accu
    in
    List.fold_left fold [] rfun
  in
  let ist = Tacintern.make_empty_glob_sign () in
  let map (name, body) =
    let body = Flags.with_option Tacintern.strict_check (Tacintern.intern_tactic_or_tacarg ist) body in
    (name, body)
  in
  let defs () =
    (** Register locally the tactic to handle recursivity. This function affects
        the whole environment, so that we transactify it afterwards. *)
    let iter_rec (sp, kn) = Tacenv.push_tactic (Nametab.Until 1) sp kn in
    let () = List.iter iter_rec recvars in
    List.map map rfun
  in
  (* STATE XXX: Review what is going on here. Why does this needs
     protection? Why is not the STM level protection enough? Fishy *)
  let defs = States.with_state_protection defs () in
  let iter (def, tac) = match def with
  | NewTac id ->
    Tacenv.register_ltac false local id tac ?deprecation;
    Flags.if_verbose Feedback.msg_info (Id.print id ++ str " is defined")
  | UpdateTac kn ->
    Tacenv.redefine_ltac local kn tac ?deprecation;
    let name = Tacenv.shortest_qualid_of_tactic kn in
    Flags.if_verbose Feedback.msg_info (Libnames.pr_qualid name ++ str " is redefined")
  in
  List.iter iter defs

(** Queries *)

let print_ltacs () =
  let entries = KNmap.bindings (Tacenv.ltac_entries ()) in
  let sort (kn1, _) (kn2, _) = KerName.compare kn1 kn2 in
  let entries = List.sort sort entries in
  let map (kn, entry) =
    let qid =
      try Some (Tacenv.shortest_qualid_of_tactic kn)
      with Not_found -> None
    in
    match qid with
    | None -> None
    | Some qid -> Some (qid, entry.Tacenv.tac_body)
  in
  let entries = List.map_filter map entries in
  let pr_entry (qid, body) =
    let (l, t) = match body with
    | Tacexpr.TacFun (l, t) -> (l, t)
    | _ -> ([], body)
    in
    let pr_ltac_fun_arg n = spc () ++ Name.print n in
    hov 2 (pr_qualid qid ++ prlist pr_ltac_fun_arg l)
  in
  Feedback.msg_notice (prlist_with_sep fnl pr_entry entries)

let locatable_ltac = "Ltac"

let () =
  let open Prettyp in
  let locate qid = try Some (Tacenv.locate_tactic qid) with Not_found -> None in
  let locate_all = Tacenv.locate_extended_all_tactic in
  let shortest_qualid = Tacenv.shortest_qualid_of_tactic in
  let name kn = str "Ltac" ++ spc () ++ pr_path (Tacenv.path_of_tactic kn) in
  let print kn =
    let qid = qualid_of_path (Tacenv.path_of_tactic kn) in
    Tacintern.print_ltac qid
  in
  let about = name in
  register_locatable locatable_ltac {
    locate;
    locate_all;
    shortest_qualid;
    name;
    print;
    about;
  }

let print_located_tactic qid =
  Feedback.msg_notice (Prettyp.print_located_other locatable_ltac qid)

(** Grammar *)

let () =
  let entries = [
    AnyEntry Pltac.tactic_expr;
    AnyEntry Pltac.binder_tactic;
    AnyEntry Pltac.simple_tactic;
    AnyEntry Pltac.tactic_arg;
  ] in
  register_grammars_by_name "tactic" entries

let get_identifier id =
  (** Workaround for badly-designed generic arguments lacking a closure *)
  Names.Id.of_string_soft ("$" ^ id)


type _ ty_sig =
| TyNil : (Geninterp.interp_sign -> unit Proofview.tactic) ty_sig
| TyIdent : string * 'r ty_sig -> 'r ty_sig
| TyArg :
  ('a, 'b, 'c) Extend.ty_user_symbol * string * 'r ty_sig -> ('c -> 'r) ty_sig
| TyAnonArg :
  ('a, 'b, 'c) Extend.ty_user_symbol * 'r ty_sig -> 'r ty_sig

type ty_ml = TyML : 'r ty_sig * 'r -> ty_ml

let rec untype_user_symbol : type a b c. (a,b,c) ty_user_symbol -> Genarg.ArgT.any user_symbol = fun tu ->
  match tu with
  | TUlist1 l -> Ulist1(untype_user_symbol l)
  | TUlist1sep(l,s) -> Ulist1sep(untype_user_symbol l, s)
  | TUlist0 l -> Ulist0(untype_user_symbol l)
  | TUlist0sep(l,s) -> Ulist0sep(untype_user_symbol l, s)
  | TUopt(o) -> Uopt(untype_user_symbol o)
  | TUentry a -> Uentry (Genarg.ArgT.Any a)
  | TUentryl (a,i) -> Uentryl (Genarg.ArgT.Any a,i)

let rec clause_of_sign : type a. a ty_sig -> Genarg.ArgT.any Extend.user_symbol grammar_tactic_prod_item_expr list =
  fun sign -> match sign with
  | TyNil -> []
  | TyIdent (s, sig') -> TacTerm s :: clause_of_sign sig'
  | TyArg (a, id, sig') ->
    let id = get_identifier id in
    TacNonTerm (None,(untype_user_symbol a,Some id)) :: clause_of_sign sig'
  | TyAnonArg (a, sig') ->
    TacNonTerm (None,(untype_user_symbol a,None)) :: clause_of_sign sig'

let clause_of_ty_ml = function
  | TyML (t,_) -> clause_of_sign t

let rec eval_sign : type a. a ty_sig -> a -> Geninterp.Val.t list -> Geninterp.interp_sign -> unit Proofview.tactic =
  fun sign tac ->
    match sign with
    | TyNil ->
      begin fun vals ist -> match vals with
      | [] -> tac ist
      | _ :: _ -> assert false
      end
    | TyIdent (s, sig') -> eval_sign sig' tac
    | TyArg (a, _, sig') ->
      let f = eval_sign sig' in
      begin fun tac vals ist -> match vals with
      | [] -> assert false
      | v :: vals ->
        let v' = Taccoerce.Value.cast (topwit (Egramml.proj_symbol a)) v in
        f (tac v') vals ist
      end tac
    | TyAnonArg (a, sig') -> eval_sign sig' tac

let eval : ty_ml -> Geninterp.Val.t list -> Geninterp.interp_sign -> unit Proofview.tactic = function
  | TyML (t,tac) -> eval_sign t tac

let is_constr_entry = function
| TUentry a -> Option.has_some @@ genarg_type_eq (ExtraArg a) Stdarg.wit_constr
| _ -> false

let rec only_constr : type a. a ty_sig -> bool = function
| TyNil -> true
| TyIdent(_,_) -> false
| TyArg (u, _, s) -> if is_constr_entry u then only_constr s else false
| TyAnonArg (u, s) -> if is_constr_entry u then only_constr s else false

let rec mk_sign_vars : type a. a ty_sig -> Name.t list = function
| TyNil -> []
| TyIdent (_,s) -> mk_sign_vars s
| TyArg (_, name, s) -> Name (get_identifier name) :: mk_sign_vars s
| TyAnonArg (_, s) -> Anonymous :: mk_sign_vars s

let dummy_id = Id.of_string "_"

let lift_constr_tac_to_ml_tac vars tac =
  let tac _ ist = Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let map = function
    | Anonymous -> None
    | Name id ->
      let c = Id.Map.find id ist.Geninterp.lfun in
      try Some (Taccoerce.Value.of_constr @@ Taccoerce.coerce_to_closed_constr env c)
      with Taccoerce.CannotCoerceTo ty ->
        Taccoerce.error_ltac_variable dummy_id (Some (env,sigma)) c ty
    in
    let args = List.map_filter map vars in
    tac args ist
  end in
  tac

let tactic_extend plugin_name tacname ~level ?deprecation sign =
  let open Tacexpr in
  let ml_tactic_name =
    { mltac_tactic = tacname;
      mltac_plugin = plugin_name }
  in
  match sign with
  | [TyML (TyIdent (name, s),tac) as ml_tac] when only_constr s ->
  (** The extension is only made of a name followed by constr entries: we do not
      add any grammar nor printing rule and add it as a true Ltac definition. *)
    (*
    let patt = make_patt rem in
    let vars = List.map make_var rem in
    let vars = mlexpr_of_list (mlexpr_of_name mlexpr_of_ident) vars in
       *)
    let vars = mk_sign_vars s in
    let ml = { Tacexpr.mltac_name = ml_tactic_name; Tacexpr.mltac_index = 0 } in
    let tac = match s with
    | TyNil -> eval ml_tac
    (** Special handling of tactics without arguments: such tactics do not do
        a Proofview.Goal.nf_enter to compute their arguments. It matters for some
        whole-prof tactics like [shelve_unifiable]. *)
    | _ -> lift_constr_tac_to_ml_tac vars (eval ml_tac)
    in
  (** Arguments are not passed directly to the ML tactic in the TacML node,
      the ML tactic retrieves its arguments in the [ist] environment instead.
      This is the rôle of the [lift_constr_tac_to_ml_tac] function. *)
    let body = Tacexpr.TacFun (vars, Tacexpr.TacML (Loc.tag (ml, [])))in
    let id = Names.Id.of_string name in
    let obj () = Tacenv.register_ltac true false id body ?deprecation in
    let () = Tacenv.register_ml_tactic ml_tactic_name [|tac|] in
    Mltop.declare_cache_obj obj plugin_name
  | _ ->
  let obj () = add_ml_tactic_notation ml_tactic_name ~level ?deprecation (List.map clause_of_ty_ml sign) in
  Tacenv.register_ml_tactic ml_tactic_name @@ Array.of_list (List.map eval sign);
  Mltop.declare_cache_obj obj plugin_name
