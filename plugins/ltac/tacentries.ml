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

let atactic n =
  if n = 5 then Pcoq.Symbol.nterm Pltac.binder_tactic
  else Pcoq.Symbol.nterml Pltac.ltac_expr (string_of_int n)

type entry_name = EntryName :
  'a raw_abstract_argument_type * (Tacexpr.raw_tactic_expr, _, 'a) Pcoq.Symbol.t -> entry_name

(** Quite ad-hoc *)
let get_tacentry n m =
  let check_lvl n =
    Int.equal m n
    && not (Int.equal m 5) (* Because tactic5 is at binder_tactic *)
    && not (Int.equal m 0) (* Because tactic0 is at simple_tactic *)
  in
  if check_lvl n then EntryName (rawwit Tacarg.wit_tactic, Pcoq.Symbol.self)
  else if check_lvl (n + 1) then EntryName (rawwit Tacarg.wit_tactic, Pcoq.Symbol.next)
  else EntryName (rawwit Tacarg.wit_tactic, atactic n)

let get_separator = function
| None -> user_err Pp.(str "Missing separator.")
| Some sep -> sep

let check_separator ?loc = function
| None -> ()
| Some _ -> user_err ?loc (str "Separator is only for arguments with suffix _list_sep.")

let rec parse_user_entry ?loc s sep =
  let open CString in
  let matches pre suf s =
    String.length s > (String.length pre + String.length suf) &&
      is_prefix pre s && is_suffix suf s
  in
  let basename pre suf s =
    let plen = String.length pre in
    String.sub s plen (String.length s - (plen + String.length suf))
  in
  let tactic_len = String.length "tactic" in
  if matches "ne_" "_list" s then
    let entry = parse_user_entry ?loc (basename "ne_" "_list" s) None in
    check_separator ?loc sep;
    Ulist1 entry
  else if matches "ne_" "_list_sep" s then
    let entry = parse_user_entry ?loc (basename "ne_" "_list_sep" s) None in
    Ulist1sep (entry, get_separator sep)
  else if matches "" "_list" s then
    let entry = parse_user_entry ?loc (basename "" "_list" s) None in
    check_separator ?loc sep;
    Ulist0 entry
  else if matches "" "_list_sep" s then
    let entry = parse_user_entry ?loc (basename "" "_list_sep" s) None in
    Ulist0sep (entry, get_separator sep)
  else if matches "" "_opt" s then
    let entry = parse_user_entry ?loc (basename "" "_opt" s) None in
    check_separator ?loc sep;
    Uopt entry
  else if String.length s = tactic_len + 1 && is_prefix "tactic" s
      && '5' >= s.[tactic_len] && s.[tactic_len] >= '0' then
    let n = Char.code s.[tactic_len] - Char.code '0' in
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
    Pltac.ltac_expr, Some (string_of_int n)
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
  EntryName (Rawwit (ListArg typ), Pcoq.Symbol.list1 e)
| Extend.Ulist0 s ->
  let EntryName (Rawwit typ, e) = prod_item_of_symbol lev s in
  EntryName (Rawwit (ListArg typ), Pcoq.Symbol.list0 e)
| Extend.Ulist1sep (s, sep) ->
  let EntryName (Rawwit typ, e) = prod_item_of_symbol lev s in
  EntryName (Rawwit (ListArg typ), Pcoq.Symbol.list1sep e (Pcoq.Symbol.tokens [Pcoq.TPattern (CLexer.terminal sep)]) false)
| Extend.Ulist0sep (s, sep) ->
  let EntryName (Rawwit typ, e) = prod_item_of_symbol lev s in
  EntryName (Rawwit (ListArg typ), Pcoq.Symbol.list0sep e (Pcoq.Symbol.tokens [Pcoq.TPattern (CLexer.terminal sep)]) false)
| Extend.Uopt s ->
  let EntryName (Rawwit typ, e) = prod_item_of_symbol lev s in
  EntryName (Rawwit (OptArg typ), Pcoq.Symbol.opt e)
| Extend.Uentry arg ->
  let ArgT.Any tag = arg in
  let wit = ExtraArg tag in
  EntryName (Rawwit wit, Pcoq.Symbol.nterm (genarg_grammar wit))
| Extend.Uentryl (s, n) ->
  let ArgT.Any tag = s in
  assert (CString.is_suffix "tactic" (ArgT.repr tag));
  get_tacentry n lev

(** Tactic grammar extensions *)

let add_tactic_entry (kn, ml, tg) state =
  let open Tacexpr in
  let entry, pos = get_tactic_entry tg.tacgram_level in
  let mkact loc l =
    let map arg =
      (* HACK to handle especially the tactic(...) entry *)
      let wit = Genarg.rawwit Tacarg.wit_tactic in
      if Genarg.has_type arg wit && not ml then
        Tacexp (Genarg.out_gen wit arg)
      else
        TacGeneric (None, arg)
    in
    let l = List.map map l in
    (CAst.make ~loc (TacAlias (kn,l)):raw_tactic_expr)
  in
  let () =
    if Int.equal tg.tacgram_level 0 && not (head_is_ident tg) then
      user_err Pp.(str "Notation for simple tactic must start with an identifier.")
  in
  let map = function
  | TacTerm s -> GramTerminal s
  | TacNonTerm (loc, (s, ido)) ->
    let EntryName (typ, e) = prod_item_of_symbol tg.tacgram_level s in
    GramNonTerminal (Loc.tag ?loc @@ (typ, e))
  in
  let prods = List.map map tg.tacgram_prods in
  let rules = make_rule mkact prods in
  let r = ExtendRule (entry, Pcoq.Reuse (pos, [rules])) in
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
      | None ->
         if s = "var" then user_err Pp.(str ("var is deprecated, use hyp.")) (* to remove in 8.14 *)
         else user_err Pp.(str ("Unknown entry "^s^"."))
      | Some arg -> arg
      end
    | Some n ->
      (* FIXME: do better someday *)
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
    (* We embed the hash of the kernel name in the label so that the identifier
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

let cache_tactic_notation tobj =
  let key = tobj.tacobj_key in
  let () = check_key key in
  Tacenv.register_alias key tobj.tacobj_body;
  extend_tactic_grammar key tobj.tacobj_forml tobj.tacobj_tacgram;
  Pptactic.declare_notation_tactic_pprule key (pprule tobj.tacobj_tacgram)

let open_tactic_notation i tobj =
  let key = tobj.tacobj_key in
  if Int.equal i 1 && not tobj.tacobj_local then
    extend_tactic_grammar key tobj.tacobj_forml tobj.tacobj_tacgram

let load_tactic_notation i tobj =
  let key = tobj.tacobj_key in
  let () = check_key key in
  (* Only add the printing and interpretation rules. *)
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

let classify_tactic_notation tacobj = Substitute

let ltac_notation_cat = Libobject.create_category "ltac.notations"

let inTacticGrammar : tactic_grammar_obj -> obj =
  declare_object {(default_object "TacticGrammar") with
       open_function = simple_open ~cat:ltac_notation_cat open_tactic_notation;
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
  Lib.add_leaf (inTacticGrammar tacobj)

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
    | _ -> assert false (* Not handled by the ML extension syntax *)
    in
    let empty_value = function
    | TacTerm s -> raise NonEmptyArgument
    | TacNonTerm (_, (symb, _)) ->
      let EntryName (typ, e) = prod_item_of_symbol 0 symb in
      let Genarg.Rawwit wit = typ in
      let inj x = CAst.make @@ TacArg ( TacGeneric (None, Genarg.in_gen typ x)) in
      let default = epsilon_value inj e in
      match default with
      | None -> raise NonEmptyArgument
      | Some def -> Tacintern.intern_tactic_or_tacarg (Genintern.empty_glob_sign Environ.empty_env) def
    in
    try Some (hd, List.map empty_value rem) with NonEmptyArgument -> None
  in
  let entries = List.map map_prod entries in
  let add_atomic i args = match args with
  | None -> ()
  | Some (id, args) ->
    let args = List.map (fun a -> Tacexp a) args in
    let entry = { mltac_name = name; mltac_index = i } in
    let body = CAst.make (TacML (entry, args)) in
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
    let tac = CAst.make (TacML (entry, List.map map ids)) in
    add_glob_tactic_notation false ~level ?deprecation prods true ids tac
  in
  List.iteri iter (List.rev prods);
  (* We call [extend_atomic_tactic] only for "basic tactics" (the ones
     at ltac_expr level 0) *)
  if Int.equal level 0 then extend_atomic_tactic name prods

(**********************************************************************)
(** Ltac quotations                                                   *)

let ltac_quotations = ref String.Set.empty

let () =
  Pcoq.grammar_extend Pltac.tactic_value (Pcoq.Fresh (Gramlib.Gramext.First, [None, None, []]))

let create_ltac_quotation name cast (e, l) =
  let () =
    if String.Set.mem name !ltac_quotations then
      failwith ("Ltac quotation " ^ name ^ " already registered")
  in
  let () = ltac_quotations := String.Set.add name !ltac_quotations in
  let entry = match l with
  | None -> Pcoq.Symbol.nterm e
  | Some l -> Pcoq.Symbol.nterml e (string_of_int l)
  in
  let rule =
    Pcoq.(
      Rule.next
        (Rule.next
           (Rule.next
              (Rule.next
                 (Rule.next
                    Rule.stop
                    (Symbol.token (CLexer.terminal name)))
                 (Symbol.token (CLexer.terminal ":")))
              (Symbol.token (CLexer.terminal "(")))
           entry)
        (Symbol.token (CLexer.terminal ")")))
  in
  let action _ v _ _ _ loc = cast (Some loc, v) in
  let gram = [Pcoq.Production.make rule action] in
  Pcoq.grammar_extend Pltac.tactic_value (Pcoq.Reuse (None, gram))

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
            | { CAst.v=(Tacexpr.TacArg _) } -> false
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
    (* Register locally the tactic to handle recursivity. This
       function affects the whole environment, so that we transactify
       it afterwards. *)
    let iter_rec (sp, kn) = Tacenv.push_tactic (Nametab.Until 1) sp kn in
    let () = List.iter iter_rec recvars in
    List.map map rfun
  in
  (* STATE XXX: Review what is going on here. Why does this needs
     protection? Why is not the STM level protection enough? Fishy *)
  let defs = Vernacstate.System.protect defs () in
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
    | {CAst.v=(Tacexpr.TacFun (l, t))} -> (l, t)
    | _ -> ([], body)
    in
    let pr_ltac_fun_arg n = spc () ++ Name.print n in
    hov 2 (pr_qualid qid ++ prlist pr_ltac_fun_arg l)
  in
  Feedback.msg_notice (prlist_with_sep fnl pr_entry entries)

let locatable_ltac = "Ltac"

let split_ltac_fun = function
  | {CAst.v=(Tacexpr.TacFun (l, t))} -> (l,t)
  | t -> ([],t)

let pr_ltac_fun_arg n = spc () ++ Name.print n

let print_ltac_body qid tac =
  let filter mp =
    try Some (Nametab.shortest_qualid_of_module mp)
    with Not_found -> None
  in
  let mods = List.map_filter filter tac.Tacenv.tac_redef in
  let redefined = match mods with
  | [] -> mt ()
  | mods ->
    let redef = prlist_with_sep fnl pr_qualid mods in
    fnl () ++ str "Redefined by:" ++ fnl () ++ redef
  in
  let l,t = split_ltac_fun tac.Tacenv.tac_body in
  hv 2 (
    hov 2 (str "Ltac" ++ spc() ++ pr_qualid qid ++
           prlist pr_ltac_fun_arg l ++ spc () ++ str ":=")
    ++ spc() ++ Pptactic.pr_glob_tactic (Global.env ()) t) ++ redefined

let () =
  let open Prettyp in
  let locate qid = try Some (qid, Tacenv.locate_tactic qid) with Not_found -> None in
  let locate_all qid = List.map (fun kn -> (qid,kn)) (Tacenv.locate_extended_all_tactic qid) in
  let shortest_qualid (qid,kn) = Tacenv.shortest_qualid_of_tactic kn in
  let name (qid,kn) = str "Ltac" ++ spc () ++ pr_path (Tacenv.path_of_tactic kn) in
  let print (qid,kn) =
    let entries = Tacenv.ltac_entries () in
    let tac = KNmap.find kn entries in
    print_ltac_body qid tac in
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

let print_ltac id =
 try
  let kn = Tacenv.locate_tactic id in
  let entries = Tacenv.ltac_entries () in
  let tac = KNmap.find kn entries in
  print_ltac_body id tac
 with
  Not_found ->
   user_err
    (pr_qualid id ++ spc() ++ str "is not a user defined tactic.")

(** Grammar *)

let () =
  let entries = [
    AnyEntry Pltac.ltac_expr;
    AnyEntry Pltac.binder_tactic;
    AnyEntry Pltac.simple_tactic;
    AnyEntry Pltac.tactic_value;
  ] in
  register_grammars_by_name "tactic" entries

let get_identifier i =
  (* Workaround for badly-designed generic arguments lacking a closure *)
  Names.Id.of_string_soft (Printf.sprintf "$%i" i)

type _ ty_sig =
| TyNil : (Geninterp.interp_sign -> unit Proofview.tactic) ty_sig
| TyIdent : string * 'r ty_sig -> 'r ty_sig
| TyArg : ('a, 'b, 'c) Extend.ty_user_symbol * 'r ty_sig -> ('c -> 'r) ty_sig

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

let rec clause_of_sign : type a. int -> a ty_sig -> Genarg.ArgT.any Extend.user_symbol grammar_tactic_prod_item_expr list =
  fun i sign -> match sign with
  | TyNil -> []
  | TyIdent (s, sig') -> TacTerm s :: clause_of_sign i sig'
  | TyArg (a, sig') ->
    let id = Some (get_identifier i) in
    TacNonTerm (None, (untype_user_symbol a, id)) :: clause_of_sign (i + 1) sig'

let clause_of_ty_ml = function
  | TyML (t,_) -> clause_of_sign 1 t

let rec eval_sign : type a. a ty_sig -> a -> Geninterp.Val.t list -> Geninterp.interp_sign -> unit Proofview.tactic =
  fun sign tac ->
    match sign with
    | TyNil ->
      begin fun vals ist -> match vals with
      | [] -> tac ist
      | _ :: _ -> assert false
      end
    | TyIdent (s, sig') -> eval_sign sig' tac
    | TyArg (a, sig') ->
      let f = eval_sign sig' in
      begin fun tac vals ist -> match vals with
      | [] -> assert false
      | v :: vals ->
        let v' = Taccoerce.Value.cast (topwit (Egramml.proj_symbol a)) v in
        f (tac v') vals ist
      end tac

let eval : ty_ml -> Geninterp.Val.t list -> Geninterp.interp_sign -> unit Proofview.tactic = function
  | TyML (t,tac) -> eval_sign t tac
let eval_of_ty_ml = eval

let is_constr_entry = function
| TUentry a -> Option.has_some @@ genarg_type_eq (ExtraArg a) Stdarg.wit_constr
| _ -> false

let rec only_constr : type a. a ty_sig -> bool = function
| TyNil -> true
| TyIdent(_,_) -> false
| TyArg (u, s) -> if is_constr_entry u then only_constr s else false

let rec mk_sign_vars : type a. int -> a ty_sig -> Name.t list = fun i tu -> match tu with
| TyNil -> []
| TyIdent (_,s) -> mk_sign_vars i s
| TyArg (_, s) -> Name (get_identifier i) :: mk_sign_vars (i + 1) s

let dummy_id = Id.of_string "_"

let lift_constr_tac_to_ml_tac vars tac =
  let tac _ ist = Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
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
    (* The extension is only made of a name followed by constr
       entries: we do not add any grammar nor printing rule and add it
       as a true Ltac definition. *)
    let vars = mk_sign_vars 1 s in
    let ml = { Tacexpr.mltac_name = ml_tactic_name; Tacexpr.mltac_index = 0 } in
    let tac = match s with
    | TyNil -> eval ml_tac
    (* Special handling of tactics without arguments: such tactics do
       not do a Proofview.Goal.nf_enter to compute their arguments. It
       matters for some whole-prof tactics like [shelve_unifiable]. *)
    | _ -> lift_constr_tac_to_ml_tac vars (eval ml_tac)
    in
    (* Arguments are not passed directly to the ML tactic in the TacML
       node, the ML tactic retrieves its arguments in the [ist]
       environment instead.  This is the rôle of the
       [lift_constr_tac_to_ml_tac] function. *)
    let body = CAst.make (Tacexpr.TacFun (vars, CAst.make (Tacexpr.TacML (ml, [])))) in
    let id = Names.Id.of_string name in
    let obj () = Tacenv.register_ltac true false id body ?deprecation in
    let () = Tacenv.register_ml_tactic ml_tactic_name [|tac|] in
    Mltop.declare_cache_obj obj plugin_name
  | _ ->
  let obj () = add_ml_tactic_notation ml_tactic_name ~level ?deprecation (List.map clause_of_ty_ml sign) in
  Tacenv.register_ml_tactic ml_tactic_name @@ Array.of_list (List.map eval sign);
  Mltop.declare_cache_obj obj plugin_name

type (_, 'a) ml_ty_sig =
| MLTyNil : ('a, 'a) ml_ty_sig
| MLTyArg : ('r, 'a) ml_ty_sig -> (Geninterp.Val.t -> 'r, 'a) ml_ty_sig

let rec ml_sig_len : type r a. (r, a) ml_ty_sig -> int = function
| MLTyNil -> 0
| MLTyArg sign -> 1 + ml_sig_len sign

let rec cast_ml : type r a. (r, a) ml_ty_sig -> r -> Geninterp.Val.t list -> a =
  fun sign f ->
  match sign with
  | MLTyNil ->
    begin function
    | [] -> f
    | _ :: _ -> CErrors.anomaly (str "Arity mismatch")
    end
  | MLTyArg sign ->
    function
    | [] -> CErrors.anomaly (str "Arity mismatch")
    | arg :: args -> cast_ml sign (f arg) args

let ml_tactic_extend ~plugin ~name ~local ?deprecation sign tac =
  let open Tacexpr in
  let tac args _ = cast_ml sign tac args in
  let ml_tactic_name = { mltac_tactic = name; mltac_plugin = plugin } in
  let ml = { mltac_name = ml_tactic_name; mltac_index = 0 } in
  let len = ml_sig_len sign in
  let args = List.init len (fun i -> Id.of_string (Printf.sprintf "arg%i" i)) in
  let vars = List.map (fun id -> Name id) args in
  let args = List.map (fun id -> Reference (Locus.ArgVar (CAst.make id))) args in
  let body = CAst.make (Tacexpr.TacFun (vars, CAst.make (Tacexpr.TacML (ml, args)))) in
  let id = Names.Id.of_string name in
  let obj () = Tacenv.register_ltac true local id body ?deprecation in
  let () = Tacenv.register_ml_tactic ml_tactic_name [|tac|] in
  Mltop.declare_cache_obj obj plugin

module MLName =
struct
  open Tacexpr
  type t = ml_tactic_name
  let compare tac1 tac2 =
    let c = String.compare tac1.mltac_tactic tac2.mltac_tactic in
    if c = 0 then String.compare tac1.mltac_plugin tac2.mltac_plugin
    else c
end

module MLTacMap = Map.Make(MLName)

let ml_table : (Geninterp.Val.t list -> Geninterp.Val.t Ftactic.t) MLTacMap.t ref = ref MLTacMap.empty

type ml_ltac_val = {
  tacval_tac : Tacexpr.ml_tactic_name;
  tacval_var : Id.t list;
}

let in_tacval =
(*  This is a hack to emulate value-returning ML-implemented tactics in Ltac.
    We use a dummy generic argument to work around the limitations of the Ltac
    runtime. Indeed, the TacML node needs to return unit values, since it is
    considered a "tactic" in the runtime. Changing it to allow arbitrary values
    would require to toggle this status, and thus to make it a "value" node.
    This would in turn create too much backwards incompatibility. Instead, we
    piggy back on the TacGeneric node, which by construction is used to return
    values.

    The trick is to represent a n-ary application of a ML function as a generic
    argument. We store in the node the name of the tactic and its arity, while
    giving canonical names to the bound variables of the closure. This trick is
    already performed in several external developments for specific calls, we
    make it here generic. The argument should not be used for other purposes, so
    we only export the registering functions.
  *)
  let wit : (Empty.t, ml_ltac_val, Geninterp.Val.t) Genarg.genarg_type =
    Genarg.create_arg "ltac:val"
  in
  (* No need to internalize this ever *)
  let intern_fun _ e = Empty.abort e in
  let subst_fun s v = v in
  let () = Genintern.register_intern0 wit intern_fun in
  let () = Genintern.register_subst0 wit subst_fun in
  (* No need to register a value tag for it via register_val0 since we will
     never access this genarg directly. *)
  let interp_fun ist tac =
    let args = List.map (fun id -> Id.Map.get id ist.Geninterp.lfun) tac.tacval_var in
    let tac = MLTacMap.get tac.tacval_tac !ml_table in
    tac args
  in
  let () = Geninterp.register_interp0 wit interp_fun in
  (fun v -> Genarg.in_gen (Genarg.Glbwit wit) v)


let ml_val_tactic_extend ~plugin ~name ~local ?deprecation sign tac =
  let open Tacexpr in
  let tac args = cast_ml sign tac args in
  let ml_tactic_name = { mltac_tactic = name; mltac_plugin = plugin } in
  let len = ml_sig_len sign in
  let vars = List.init len (fun i -> Id.of_string (Printf.sprintf "arg%i" i)) in
  let body = TacGeneric (None, in_tacval { tacval_tac = ml_tactic_name;  tacval_var = vars }) in
  let vars = List.map (fun id -> Name id) vars in
  let body = CAst.make (Tacexpr.TacFun (vars, CAst.make (Tacexpr.TacArg body))) in
  let id = Names.Id.of_string name in
  let obj () = Tacenv.register_ltac true local id body ?deprecation in
  let () = assert (not @@ MLTacMap.mem ml_tactic_name !ml_table) in
  let () = ml_table := MLTacMap.add ml_tactic_name tac !ml_table in
  Mltop.declare_cache_obj obj plugin

(** ARGUMENT EXTEND *)

open Geninterp

type ('a, 'b, 'c) argument_printer =
  'a Pptactic.raw_extra_genarg_printer *
  'b Pptactic.glob_extra_genarg_printer *
  'c Pptactic.extra_genarg_printer

type ('a, 'b) argument_intern =
| ArgInternFun : ('a, 'b) Genintern.intern_fun -> ('a, 'b) argument_intern
| ArgInternWit : ('a, 'b, 'c) Genarg.genarg_type -> ('a, 'b) argument_intern

type 'b argument_subst =
| ArgSubstFun : 'b Genintern.subst_fun -> 'b argument_subst
| ArgSubstWit : ('a, 'b, 'c) Genarg.genarg_type -> 'b argument_subst

type ('b, 'c) argument_interp =
| ArgInterpRet : ('c, 'c) argument_interp
| ArgInterpFun : ('b, Val.t) interp_fun -> ('b, 'c) argument_interp
| ArgInterpWit : ('a, 'b, 'r) Genarg.genarg_type -> ('b, 'c) argument_interp
| ArgInterpSimple :
  (Geninterp.interp_sign -> Environ.env -> Evd.evar_map -> 'b -> 'c) -> ('b, 'c) argument_interp

type ('a, 'b, 'c) tactic_argument = {
  arg_parsing : 'a Vernacextend.argument_rule;
  arg_tag : 'c Val.tag option;
  arg_intern : ('a, 'b) argument_intern;
  arg_subst : 'b argument_subst;
  arg_interp : ('b, 'c) argument_interp;
  arg_printer : ('a, 'b, 'c) argument_printer;
}

let intern_fun (type a b c) name (arg : (a, b, c) tactic_argument) : (a, b) Genintern.intern_fun =
match arg.arg_intern with
| ArgInternFun f -> f
| ArgInternWit wit ->
  fun ist v ->
    let ans = Genarg.out_gen (glbwit wit) (Tacintern.intern_genarg ist (Genarg.in_gen (rawwit wit) v)) in
    (ist, ans)

let subst_fun (type a b c) (arg : (a, b, c) tactic_argument) : b Genintern.subst_fun =
match arg.arg_subst with
| ArgSubstFun f -> f
| ArgSubstWit wit ->
  fun s v ->
    let ans = Genarg.out_gen (glbwit wit) (Tacsubst.subst_genarg s (Genarg.in_gen (glbwit wit) v)) in
    ans

let interp_fun (type a b c) name (arg : (a, b, c) tactic_argument) (tag : c Val.tag) : (b, Val.t) interp_fun =
match arg.arg_interp with
| ArgInterpRet -> (fun ist v -> Ftactic.return (Geninterp.Val.inject tag v))
| ArgInterpFun f -> f
| ArgInterpWit wit ->
  (fun ist x -> Tacinterp.interp_genarg ist (Genarg.in_gen (glbwit wit) x))
| ArgInterpSimple f ->
  (fun ist v -> Ftactic.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let v = f ist env sigma v in
    Ftactic.return (Geninterp.Val.inject tag v)
  end)

let argument_extend (type a b c) ~name (arg : (a, b, c) tactic_argument) =
  let wit = Genarg.create_arg name in
  let () = Genintern.register_intern0 wit (intern_fun name arg) in
  let () = Genintern.register_subst0 wit (subst_fun arg) in
  let tag = match arg.arg_tag with
  | None ->
    let () = register_val0 wit None in
    val_tag (topwit wit)
  | Some tag ->
    let () = register_val0 wit (Some tag) in
    tag
  in
  let () = register_interp0 wit (interp_fun name arg tag) in
  let entry = match arg.arg_parsing with
  | Vernacextend.Arg_alias e ->
    let () = Pcoq.register_grammar wit e in
    e
  | Vernacextend.Arg_rules rules ->
    let e = Pcoq.create_generic_entry2 name (Genarg.rawwit wit) in
    let () = Pcoq.grammar_extend e (Pcoq.Fresh (Gramlib.Gramext.First, [None, None, rules])) in
    e
  in
  let (rpr, gpr, tpr) = arg.arg_printer in
  let () = Pptactic.declare_extra_genarg_pprule wit rpr gpr tpr in
  let () = create_ltac_quotation name
    (fun (loc, v) -> Tacexpr.TacGeneric (Some name,Genarg.in_gen (Genarg.rawwit wit) v))
    (entry, None)
  in
  (wit, entry)
