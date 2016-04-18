(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Libobject
open Genarg
open Pcoq
open Egramml
open Egramcoq
open Vernacexpr
open Libnames
open Nameops

type 'a grammar_tactic_prod_item_expr =
| TacTerm of string
| TacNonTerm of Loc.t * 'a * Names.Id.t

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
  let open Extend in
  if n = 5 then Aentry (name_of_entry Tactic.binder_tactic)
  else Aentryl (name_of_entry Tactic.tactic_expr, n)

type entry_name = EntryName :
  'a raw_abstract_argument_type * (Tacexpr.raw_tactic_expr, 'a) Extend.symbol -> entry_name

let try_get_entry u s =
  let open Extend in
  (** Order the effects: get_entry can raise Not_found *)
  let TypedEntry (typ, e) = get_entry u s in
  EntryName (typ, Aentry (name_of_entry e))

(** Quite ad-hoc *)
let get_tacentry n m =
  let open Extend in
  let check_lvl n =
    Int.equal m n
    && not (Int.equal m 5) (* Because tactic5 is at binder_tactic *)
    && not (Int.equal m 0) (* Because tactic0 is at simple_tactic *)
  in
  if check_lvl n then EntryName (rawwit Constrarg.wit_tactic, Aself)
  else if check_lvl (n + 1) then EntryName (rawwit Constrarg.wit_tactic, Anext)
  else EntryName (rawwit Constrarg.wit_tactic, atactic n)

let get_separator = function
| None -> error "Missing separator."
| Some sep -> sep

let rec parse_user_entry s sep =
  let open Extend in
  let l = String.length s in
  if l > 8 && coincide s "ne_" 0 && coincide s "_list" (l - 5) then
    let entry = parse_user_entry (String.sub s 3 (l-8)) None in
    Ulist1 entry
  else if l > 12 && coincide s "ne_" 0 &&
                   coincide s "_list_sep" (l-9) then
    let entry = parse_user_entry (String.sub s 3 (l-12)) None in
    Ulist1sep (entry, get_separator sep)
  else if l > 5 && coincide s "_list" (l-5) then
    let entry = parse_user_entry (String.sub s 0 (l-5)) None in
    Ulist0 entry
  else if l > 9 && coincide s "_list_sep" (l-9) then
    let entry = parse_user_entry (String.sub s 0 (l-9)) None in
    Ulist0sep (entry, get_separator sep)
  else if l > 4 && coincide s "_opt" (l-4) then
    let entry = parse_user_entry (String.sub s 0 (l-4)) None in
    Uopt entry
  else if Int.equal l 7 && coincide s "tactic" 0 && '5' >= s.[6] && s.[6] >= '0' then
    let n = Char.code s.[6] - 48 in
    Uentryl ("tactic", n)
  else
    let s = match s with "hyp" -> "var" | _ -> s in
    Uentry s

let arg_list = function Rawwit t -> Rawwit (ListArg t)
let arg_opt = function Rawwit t -> Rawwit (OptArg t)

let interp_entry_name up_level s sep =
  let open Extend in
  let rec eval = function
  | Ulist1 e ->
    let EntryName (t, g) = eval e in
    EntryName (arg_list t, Alist1 g)
  | Ulist1sep (e, sep) ->
    let EntryName (t, g) = eval e in
    EntryName (arg_list t, Alist1sep (g, sep))
  | Ulist0 e ->
    let EntryName (t, g) = eval e in
    EntryName (arg_list t, Alist0 g)
  | Ulist0sep (e, sep) ->
    let EntryName (t, g) = eval e in
    EntryName (arg_list t, Alist0sep (g, sep))
  | Uopt e ->
    let EntryName (t, g) = eval e in
    EntryName (arg_opt t, Aopt g)
  | Uentry s ->
    begin
      try try_get_entry uprim s with Not_found ->
      try try_get_entry uconstr s with Not_found ->
      try try_get_entry utactic s with Not_found ->
      error ("Unknown entry "^s^".")
    end
  | Uentryl (s, n) ->
    (** FIXME: do better someday *)
    assert (String.equal s "tactic");
    get_tacentry n up_level
  in
  eval (parse_user_entry s sep)

(**********************************************************************)
(** Grammar declaration for Tactic Notation (Coq level)               *)

let get_tactic_entry n =
  if Int.equal n 0 then
    Tactic.simple_tactic, None
  else if Int.equal n 5 then
    Tactic.binder_tactic, None
  else if 1<=n && n<5 then
    Tactic.tactic_expr, Some (Extend.Level (string_of_int n))
  else
    error ("Invalid Tactic Notation level: "^(string_of_int n)^".")

(**********************************************************************)
(** State of the grammar extensions                                   *)

type tactic_grammar = {
  tacgram_level : int;
  tacgram_prods : Tacexpr.raw_tactic_expr grammar_prod_item list;
}

(** ML Tactic grammar extensions *)

let add_ml_tactic_entry (name, prods) =
  let entry = Tactic.simple_tactic in
  let mkact i loc l : Tacexpr.raw_tactic_expr =
    let open Tacexpr in
    let entry = { mltac_name = name; mltac_index = i } in
    let map arg = TacGeneric arg in
    TacML (loc, entry, List.map map l)
  in
  let rules = List.map_i (fun i p -> make_rule (mkact i) p) 0 prods in
  synchronize_level_positions ();
  grammar_extend entry None (None, [(None, None, List.rev rules)]);
  1

(* Declaration of the tactic grammar rule *)

let head_is_ident tg = match tg.tacgram_prods with
| GramTerminal _::_ -> true
| _ -> false

(** Tactic grammar extensions *)

let add_tactic_entry (kn, tg) =
  let open Tacexpr in
  let entry, pos = get_tactic_entry tg.tacgram_level in
  let mkact loc l =
    let filter = function
    | GramTerminal _ -> None
    | GramNonTerminal (_, t, _) -> Some (Genarg.unquote t)
    in
    let types = List.map_filter filter tg.tacgram_prods in
    let map arg t =
      (** HACK to handle especially the tactic(...) entry *)
      let wit = Genarg.rawwit Constrarg.wit_tactic in
      if Genarg.argument_type_eq t (Genarg.unquote wit) then
        Tacexp (Genarg.out_gen wit arg)
      else
        TacGeneric arg
    in
    let l = List.map2 map l types in
    (TacAlias (loc,kn,l):raw_tactic_expr)
  in
  let () =
    if Int.equal tg.tacgram_level 0 && not (head_is_ident tg) then
      error "Notation for simple tactic must start with an identifier."
  in
  let rules = make_rule mkact tg.tacgram_prods in
  synchronize_level_positions ();
  grammar_extend entry None (pos, [(None, None, List.rev [rules])]);
  1

let tactic_grammar =
  create_grammar_command "TacticGrammar" add_tactic_entry

let ml_tactic_grammar =
  create_grammar_command "MLTacticGrammar" add_ml_tactic_entry

let extend_tactic_grammar kn ntn = extend_grammar tactic_grammar (kn, ntn)
let extend_ml_tactic_grammar n ntn = extend_grammar ml_tactic_grammar (n, ntn)

(**********************************************************************)
(* Tactic Notation                                                    *)

let interp_prod_item lev = function
  | TacTerm s -> GramTerminal s
  | TacNonTerm (loc, (nt, sep), _) ->
      let EntryName (etyp, e) = interp_entry_name lev nt sep in
      GramNonTerminal (loc, etyp, e)

let make_terminal_status = function
  | GramTerminal s -> Some s
  | GramNonTerminal _ -> None

let make_fresh_key =
  let id = Summary.ref ~name:"TACTIC-NOTATION-COUNTER" 0 in
  fun () ->
    let cur = incr id; !id in
    let lbl = Id.of_string ("_" ^ string_of_int cur) in
    let kn = Lib.make_kn lbl in
    let (mp, dir, _) = KerName.repr kn in
    (** We embed the full path of the kernel name in the label so that the
        identifier should be unique. This ensures that including two modules
        together won't confuse the corresponding labels. *)
    let lbl = Id.of_string_soft (Printf.sprintf "%s#%s#%i"
      (ModPath.to_string mp) (DirPath.to_string dir) cur)
    in
    KerName.make mp dir (Label.of_id lbl)

type tactic_grammar_obj = {
  tacobj_key : KerName.t;
  tacobj_local : locality_flag;
  tacobj_tacgram : tactic_grammar;
  tacobj_tacpp : Pptactic.pp_tactic;
  tacobj_body : Id.t list * Tacexpr.glob_tactic_expr;
}

let check_key key =
  if Tacenv.check_alias key then
    error "Conflicting tactic notations keys. This can happen when including \
    twice the same module."

let cache_tactic_notation (_, tobj) =
  let key = tobj.tacobj_key in
  let () = check_key key in
  Tacenv.register_alias key tobj.tacobj_body;
  extend_tactic_grammar key tobj.tacobj_tacgram;
  Pptactic.declare_notation_tactic_pprule key tobj.tacobj_tacpp

let open_tactic_notation i (_, tobj) =
  let key = tobj.tacobj_key in
  if Int.equal i 1 && not tobj.tacobj_local then
    extend_tactic_grammar key tobj.tacobj_tacgram

let load_tactic_notation i (_, tobj) =
  let key = tobj.tacobj_key in
  let () = check_key key in
  (** Only add the printing and interpretation rules. *)
  Tacenv.register_alias key tobj.tacobj_body;
  Pptactic.declare_notation_tactic_pprule key tobj.tacobj_tacpp;
  if Int.equal i 1 && not tobj.tacobj_local then
    extend_tactic_grammar key tobj.tacobj_tacgram

let subst_tactic_notation (subst, tobj) =
  let (ids, body) = tobj.tacobj_body in
  { tobj with
    tacobj_key = Mod_subst.subst_kn subst tobj.tacobj_key;
    tacobj_body = (ids, Tacsubst.subst_tactic subst body);
  }

let classify_tactic_notation tacobj = Substitute tacobj

let inTacticGrammar : tactic_grammar_obj -> obj =
  declare_object {(default_object "TacticGrammar") with
       open_function = open_tactic_notation;
       load_function = load_tactic_notation;
       cache_function = cache_tactic_notation;
       subst_function = subst_tactic_notation;
       classify_function = classify_tactic_notation}

let rec safe_printing_level n prods =
  match List.last prods with
  | TacTerm _ -> n
  | TacNonTerm (_, (nt, sep), _) ->
     let level = match parse_user_entry nt sep with
     | Extend.Uentryl ("tactic",n') -> Some n'
     | Extend.Uentry ("tactic") -> Some 5
     | Extend.Uentry ("binder_tactic") -> Some 5
     | _ -> None in
     match level with
     | Some n' when n' > n ->
         msg_warning (strbrk "Notation ends with a tactic at a level "
           ++ strbrk "higher than the tactic itself. Using this level "
           ++ strbrk "for ensuring correct parenthesizing when printing.");
         n'
     | _ -> n

let cons_production_parameter = function
| TacTerm _ -> None
| TacNonTerm (_, _, id) -> Some id

let add_tactic_notation (local,n,prods,e) =
  let ids = List.map_filter cons_production_parameter prods in
  let printing_level = safe_printing_level n prods in
  let prods = List.map (interp_prod_item n) prods in
  let pprule = {
    Pptactic.pptac_level = printing_level;
    pptac_prods = prods;
  } in
  let tac = Tacintern.glob_tactic_env ids (Global.env()) e in
  let parule = {
    tacgram_level = n;
    tacgram_prods = prods;
  } in
  let tacobj = {
    tacobj_key = make_fresh_key ();
    tacobj_local = local;
    tacobj_tacgram = parule;
    tacobj_tacpp = pprule;
    tacobj_body = (ids, tac);
  } in
  Lib.add_anonymous_leaf (inTacticGrammar tacobj)

(**********************************************************************)
(* ML Tactic entries                                                  *)

type ml_tactic_grammar_obj = {
  mltacobj_name : Tacexpr.ml_tactic_name;
  (** ML-side unique name *)
  mltacobj_prod : Tacexpr.raw_tactic_expr grammar_prod_item list list;
  (** Grammar rules generating the ML tactic. *)
}

exception NonEmptyArgument

(** ML tactic notations whose use can be restricted to an identifier are added
    as true Ltac entries. *)
let extend_atomic_tactic name entries =
  let open Tacexpr in
  let map_prod prods =
    let (hd, rem) = match prods with
    | GramTerminal s :: rem -> (s, rem)
    | _ -> assert false (** Not handled by the ML extension syntax *)
    in
    let empty_value = function
    | GramTerminal s -> raise NonEmptyArgument
    | GramNonTerminal (_, typ, e) ->
      let Genarg.Rawwit wit = typ in
      let inj x = TacArg (Loc.ghost, TacGeneric (Genarg.in_gen typ x)) in
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
    let body = TacML (Loc.ghost, entry, args) in
    Tacenv.register_ltac false false (Names.Id.of_string id) body
  in
  List.iteri add_atomic entries

let cache_ml_tactic_notation (_, obj) =
  extend_ml_tactic_grammar obj.mltacobj_name obj.mltacobj_prod

let open_ml_tactic_notation i obj =
  if Int.equal i 1 then cache_ml_tactic_notation obj

let inMLTacticGrammar : ml_tactic_grammar_obj -> obj =
  declare_object { (default_object "MLTacticGrammar") with
    open_function = open_ml_tactic_notation;
    cache_function = cache_ml_tactic_notation;
    classify_function = (fun o -> Substitute o);
    subst_function = (fun (_, o) -> o);
  }

let add_ml_tactic_notation name prods =
  let obj = {
    mltacobj_name = name;
    mltacobj_prod = prods;
  } in
  Lib.add_anonymous_leaf (inMLTacticGrammar obj);
  extend_atomic_tactic name prods

(**********************************************************************)
(** Ltac quotations                                                   *)

let ltac_quotations = ref String.Set.empty

let create_ltac_quotation name cast (e, l) =
  let open Extend in
  let () =
    if String.Set.mem name !ltac_quotations then
      failwith ("Ltac quotation " ^ name ^ " already registered")
  in
  let () = ltac_quotations := String.Set.add name !ltac_quotations in
  let entry = match l with
  | None -> Aentry (name_of_entry e)
  | Some l -> Aentryl (name_of_entry e, l)
  in
(*   let level = Some "1" in *)
  let level = None in
  let assoc = None in
  let rule =
    Next (Next (Next (Next (Next (Stop,
      Atoken (Lexer.terminal name)),
      Atoken (Lexer.terminal ":")),
      Atoken (Lexer.terminal "(")),
      entry),
      Atoken (Lexer.terminal ")"))
  in
  let action _ v _ _ _ loc = cast (loc, v) in
  let gram = (level, assoc, [Rule (rule, action)]) in
  Pcoq.grammar_extend Tactic.tactic_arg None (None, [gram])

(** Command *)


type tacdef_kind =
  | NewTac of Id.t
  | UpdateTac of Nametab.ltac_constant

let is_defined_tac kn =
  try ignore (Tacenv.interp_ltac kn); true with Not_found -> false

let register_ltac local tacl =
  let map tactic_body =
    match tactic_body with
    | TacticDefinition ((loc,id), body) ->
        let kn = Lib.make_kn id in
        let id_pp = pr_id id in
        let () = if is_defined_tac kn then
          Errors.user_err_loc (loc, "",
            str "There is already an Ltac named " ++ id_pp ++ str".")
        in
        let is_primitive =
          try
            match Pcoq.parse_string Pcoq.Tactic.tactic (Id.to_string id) with
            | Tacexpr.TacArg _ -> false
            | _ -> true (* most probably TacAtom, i.e. a primitive tactic ident *)
          with e when Errors.noncritical e -> true (* prim tactics with args, e.g. "apply" *)
        in
        let () = if is_primitive then
          msg_warning (str "The Ltac name " ++ id_pp ++
            str " may be unusable because of a conflict with a notation.")
        in
        NewTac id, body
    | TacticRedefinition (ident, body) ->
        let loc = loc_of_reference ident in
        let kn =
          try Nametab.locate_tactic (snd (qualid_of_reference ident))
          with Not_found ->
            Errors.user_err_loc (loc, "",
                        str "There is no Ltac named " ++ pr_reference ident ++ str ".")
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
    let iter_rec (sp, kn) = Nametab.push_tactic (Nametab.Until 1) sp kn in
    let () = List.iter iter_rec recvars in
    List.map map rfun
  in
  let defs = Future.transactify defs () in
  let iter (def, tac) = match def with
  | NewTac id ->
    Tacenv.register_ltac false local id tac;
    Flags.if_verbose msg_info (Nameops.pr_id id ++ str " is defined")
  | UpdateTac kn ->
    Tacenv.redefine_ltac local kn tac;
    let name = Nametab.shortest_qualid_of_tactic kn in
    Flags.if_verbose msg_info (Libnames.pr_qualid name ++ str " is redefined")
  in
  List.iter iter defs
