(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Coqpp_parser
open Coqpp_ast

let exit_code = ref 0
let show_warn = ref true

let fprintf = Printf.fprintf

let error s =
  exit_code := 1;
  Printf.eprintf "Error: ";
  Printf.eprintf s

(* todo: checking if !show_warn is true here gives a compilation error *)
let warn s =
  Printf.eprintf "Warning: ";
  Printf.eprintf s

type args = {
  mlg_files : string list;
  rst_files : string list;
  fullGrammar : bool;
  check_tacs : bool;
  check_cmds : bool;
  show_warn : bool;
  verbose : bool;
  verify : bool;
}

let default_args = {
  mlg_files = [];
  rst_files = [];
  fullGrammar = false;
  check_tacs = false;
  check_cmds = false;
  show_warn = true;
  verbose = false;
  verify = false;
}

(* translated symbols *)

type doc_symbol =
| Sterm of string
| Snterm of string
| Slist1 of doc_symbol
| Slist1sep of doc_symbol * doc_symbol
| Slist0 of doc_symbol
| Slist0sep of doc_symbol * doc_symbol
| Sopt of doc_symbol
| Sparen of doc_symbol list (* for GRAMMAR EXTEND *)
| Sprod of doc_symbol list list (* for GRAMMAR EXTEND *)
  (* editing operations *)
| Sedit of string
| Sedit2 of string * string

(* nonterminals to rename or delete *)
module StringMap = Map.Make(String)
module NTMap = StringMap
module StringSet = Set.Make(String)

type gram = {
  (* map from nonterminal name to a list of prods *)
  (* each production is a list of doc_symbol *)
  map: doc_symbol list list NTMap.t;
  (* specifies the order for nt's *)
  order: string list;
}

module DocGram = struct
  (* these guarantee that order and map have a 1-1 relationship
     on the nt name.  They don't guarantee that nts on rhs of a production
     are defined, nor do they prohibit duplicate productions *)

  exception Duplicate
  exception Invalid

  (* add an nt at the end (if not already present) then set its prods *)
  let g_maybe_add g nt prods =
    if not (NTMap.mem nt !g.map) then
      g := { !g with order = !g.order @ [nt] };
    g := { !g with map = NTMap.add nt prods !g.map }

  (* add an nt at the beginning (if not already present) then set its prods *)
  let g_maybe_add_begin g nt prods =
    if not (NTMap.mem nt !g.map) then
      g := { !g with order = nt :: !g.order };
    g := { !g with map = NTMap.add nt prods !g.map }

  (* reverse the order of the grammar *)
  let g_reverse g =
    g := { !g with order = List.rev !g.order }

  (* update the productions of an existing nt *)
  let g_update_prods g nt prods =
    ignore (NTMap.find nt !g.map);  (* don't add the nt if it's not present *)
    g := { !g with map = NTMap.add nt prods !g.map }

  (* remove a non-terminal *)
  let g_remove g nt =
    g := { map = NTMap.remove nt !g.map;
           order = List.filter (fun elt -> elt <> nt) !g.order }

  (* rename an nt and update its prods, keeping its original position.
     If the new name already exists, include its prods *)
  let g_rename_merge g nt nt' nprods =
    let oprods =
      try
        let oprods = NTMap.find nt' !g.map in
        g := { !g with order = List.filter (fun elt -> elt <> nt') !g.order };
        oprods
      with Not_found ->
       g := { !g with map = NTMap.add nt' [] !g.map };
       []
    in
    g := { map = NTMap.remove nt !g.map;
           order = List.map (fun n -> if n = nt then nt' else n) !g.order };
    g_update_prods g nt' (oprods @ nprods)

  (* add a new nonterminal after "ins_after" None means insert at the beginning *)
  let g_add_after g ins_after nt prods =
    if NTMap.mem nt !g.map then raise Duplicate;  (* don't update the nt if it's already present *)
    let rec insert_nt order res =
      match ins_after, order with
      | None, _ -> nt :: order
      | Some _, [] -> raise Not_found
      | Some ins_after_nt, hd :: tl ->
        if hd = ins_after_nt then
          (List.rev res) @ (hd :: nt :: tl)
        else
          insert_nt tl (hd :: res)
    in
    g := { order = insert_nt !g.order [];
           map = NTMap.add nt prods !g.map }

  (* replace the map and order *)
  let g_reorder g map order =
    let order_nts = StringSet.of_list order in
    let map_nts = List.fold_left (fun res b -> let (nt, _) = b in StringSet.add nt res)
      StringSet.empty (NTMap.bindings map) in
    if List.length order <> NTMap.cardinal map ||
      not (StringSet.equal order_nts map_nts) then raise Invalid;
    g := { order = order; map = map }

end
open DocGram

(*** Print routines ***)

let sprintf = Printf.sprintf

let map_and_concat f ?(delim="") l =
  String.concat delim (List.map f l)

let rec db_output_prodn = function
  | Sterm s -> sprintf "(Sterm %s) " s
  | Snterm s -> sprintf "(Snterm %s) " s
  | Slist1 sym -> sprintf "(Slist1 %s) " (db_output_prodn sym)
  | Slist1sep (sym, sep) -> sprintf "(Slist1sep %s %s) " (db_output_prodn sep) (db_output_prodn sym)
  | Slist0 sym -> sprintf "(Slist0 %s) " (db_output_prodn sym)
  | Slist0sep (sym, sep) -> sprintf "(Slist0sep %s %s)  " (db_output_prodn sep) (db_output_prodn sym)
  | Sopt sym -> sprintf "(Sopt %s) " (db_output_prodn sym)
  | Sparen prod -> sprintf "(Sparen %s) " (db_out_list prod)
  | Sprod prods -> sprintf "(Sprod %s) " (db_out_prods prods)
  | Sedit s -> sprintf "(Sedit %s) " s
  | Sedit2 (s, s2) -> sprintf "(Sedit2 %s %s) " s s2
and db_out_list prod = sprintf "(%s)" (map_and_concat db_output_prodn prod)
and db_out_prods prods = sprintf "( %s )" (map_and_concat ~delim:" | " db_out_list prods)

let rec output_prod plist need_semi = function
    | Sterm s -> if plist then sprintf "%s" s else sprintf "\"%s\"" s
    | Snterm s ->
        if plist then sprintf "`%s`" s else
          sprintf "%s%s" s (if s = "IDENT" && need_semi then ";" else "")
    | Slist1 sym -> sprintf "LIST1 %s" (prod_to_str ~plist [sym])
    | Slist1sep (sym, sep) -> sprintf "LIST1 %s SEP %s" (prod_to_str ~plist [sym]) (prod_to_str ~plist [sep])
    | Slist0 sym -> sprintf "LIST0 %s" (prod_to_str ~plist [sym])
    | Slist0sep (sym, sep) -> sprintf "LIST0 %s SEP %s" (prod_to_str ~plist [sym]) (prod_to_str ~plist [sep])
    | Sopt sym -> sprintf "OPT %s" (prod_to_str ~plist [sym])
    | Sparen sym_list -> sprintf "( %s )" (prod_to_str sym_list)
    | Sprod sym_list ->
      sprintf "[ %s ]" (String.concat " " (List.mapi (fun i r ->
          let prod = (prod_to_str r) in
          let sep = if i = 0 then "" else
              if prod <> "" then "| " else "|" in
          sprintf "%s%s" sep prod)
        sym_list))
    | Sedit s -> sprintf "%s" s
    (* todo: make PLUGIN info output conditional on the set of prods? *)
    | Sedit2 ("PLUGIN", plugin) ->
      if plist then
        sprintf "     (%s plugin)" plugin
      else
        sprintf "     (* %s plugin *)" plugin
    | Sedit2 ("FILE", file) ->
      let file_suffix_regex = Str.regexp ".*/\\([a-zA-Z0-9_\\.]+\\)" in
      let suffix = if Str.string_match file_suffix_regex file 0 then Str.matched_group 1 file else file in
      if plist then
        sprintf "     (%s)" suffix
      else
        sprintf "     (* %s *)" suffix
    | Sedit2 (s, s2) -> sprintf "%s \"%s\"" s s2

and prod_to_str_r plist prod =
  match prod with
  | p :: tl ->
    let need_semi =
      match prod with
      | Snterm "IDENT" :: Sterm _ :: _
      | Snterm "IDENT" :: Sprod _ :: _ -> true
      | _ -> false in
    (output_prod plist need_semi p) :: (prod_to_str_r plist tl)
  | [] -> []

and prod_to_str ?(plist=false) prod =
  String.concat " " (prod_to_str_r plist prod)


let rec output_prodn = function
  | Sterm s -> let s = if List.mem s ["{"; "{|"; "|"; "}"] then "%" ^ s else s in
    sprintf "%s" s
  | Snterm s -> sprintf "@%s" s
  | Slist1 sym -> sprintf "{+ %s }" (output_prodn sym)
  | Slist1sep (sym, sep) -> sprintf "{+%s %s }" (output_sep sep) (output_prodn sym)
  | Slist0 sym -> sprintf "{* %s }" (output_prodn sym)
  | Slist0sep (sym, sep) -> sprintf "{*%s %s }" (output_sep sep) (output_prodn sym)
  | Sopt sym -> sprintf "{? %s }" (output_prodn sym)
  | Sparen sym_list -> sprintf "%s" (prod_to_prodn sym_list)
  | Sprod sym_list ->
    let lcurly, rcurly = if List.length sym_list = 1 then "", "" else "{| ", " }" in
    sprintf "%s%s%s"
      lcurly
      (String.concat " " (List.mapi (fun i r ->
          let prod = (prod_to_prodn r) in
          let sep = if i = 0 then "" else
              if prod <> "" then "| " else "|" in
          sprintf "%s%s" sep prod)
        sym_list))
      rcurly
  | Sedit s -> sprintf "%s" s
  | Sedit2 ("PLUGIN", s2) -> ""
  | Sedit2 (s, s2) -> sprintf "%s \"%s\"" s s2

and output_sep sep =
  match sep with
  | Sterm s -> sprintf "%s" s  (* avoid escaping separator *)
  | _ -> output_prodn sep

and prod_to_prodn prod = String.concat " " (List.map output_prodn prod)

type fmt = [`MLG | `PRODLIST | `PRODN ]

(* print a subset of the grammar with nts in the specified order *)
let print_in_order out g fmt nt_order hide =
  List.iter (fun nt ->
      if not (StringSet.mem nt hide) then
        try
          let prods = NTMap.find nt !g.map in
          match fmt with
          | `MLG ->
            fprintf out "%s: [\n" nt;
            List.iter (fun prod ->
                let str = prod_to_str ~plist:false prod in
                let pfx = if str = "" then "|" else "| " in
                fprintf out "%s%s\n" pfx str)
              prods;
            fprintf out "]\n\n"
          | `PRODLIST ->
            fprintf out "%s :" nt;
            List.iteri (fun i prod ->
                if i > 0 then
                  fprintf out "%s :" (String.make (String.length nt) ' ');
                let str = prod_to_str ~plist:true prod in
                let pfx = if str = "" then "" else " " in
                fprintf out "%s%s\n" pfx str)
              prods;
          | `PRODN ->
            fprintf out "\n%s:\n" nt;
            List.iter (fun prod ->
                let str = prod_to_prodn prod in
                let pfx = if str = "" then "" else " " in
                fprintf out "%s%s\n" pfx str)
              prods;
        with Not_found -> error "Missing nt '%s' in print_in_order\n" nt)
    nt_order


(*** Read grammar routines ***)

let cvt_ext prod =
  let rec to_doc_sym = function
    | Ulist1 sym -> Slist1 (to_doc_sym sym)
    | Ulist1sep (sym, s) -> Slist1sep ((to_doc_sym sym), Sterm s)
    | Ulist0 sym -> Slist0 (to_doc_sym sym)
    | Ulist0sep (sym, s) -> Slist0sep ((to_doc_sym sym), Sterm s)
    | Uopt sym -> Sopt (to_doc_sym sym)
    | Uentry s -> Snterm s
    | Uentryl (s, i) -> Snterm (s ^ (string_of_int i))
 in
 let from_ext = function
   | ExtTerminal s -> Sterm s
   | ExtNonTerminal (s, _) -> to_doc_sym s
 in
 List.map from_ext prod

let rec cvt_gram_sym = function
  | GSymbString s -> Sterm s
  | GSymbQualid (s, level) ->
    Snterm (match level with
           | Some str -> s ^ str
           | None -> s)
  | GSymbParen l -> Sparen (cvt_gram_sym_list l)
  | GSymbProd ll ->
    let cvt = List.map cvt_gram_prod ll in
    (match cvt with
    | (Snterm x :: []) :: [] -> Snterm x
    | (Sterm x :: []) :: []  -> Sterm x
    | _ -> Sprod cvt)

and cvt_gram_sym_list l =
  let get_sym = function
    | GSymbQualid (s, level) -> s
    | _ -> ""
  in

  match l with
  | GSymbQualid ("LIST0", _) :: s :: GSymbQualid ("SEP", _) :: sep :: tl ->
    Slist0sep (cvt_gram_sym s, cvt_gram_sym sep) :: cvt_gram_sym_list tl
  | GSymbQualid ("LIST1", _) :: s :: GSymbQualid ("SEP", _) :: sep :: tl ->
    Slist1sep (cvt_gram_sym s, cvt_gram_sym sep) :: cvt_gram_sym_list tl
  | GSymbQualid ("LIST0", _) :: s :: tl ->
    Slist0 (cvt_gram_sym s) :: cvt_gram_sym_list tl
  | GSymbQualid ("LIST1", _) :: s :: tl ->
    Slist1 (cvt_gram_sym s) :: cvt_gram_sym_list tl
  | GSymbQualid ("OPT", _) :: s :: tl ->
    Sopt (cvt_gram_sym s) :: cvt_gram_sym_list tl
  | GSymbQualid ("IDENT", _) :: s2 :: tl when get_sym s2 = "" ->
    cvt_gram_sym s2 :: cvt_gram_sym_list tl
  | GSymbQualid ("ADD_OPT", _) :: tl ->
    (Sedit "ADD_OPT") :: cvt_gram_sym_list tl
  | GSymbQualid ("NOTE", _) :: GSymbQualid (s2, l) :: tl ->
    (Sedit2 ("NOTE", s2)) :: cvt_gram_sym_list tl
  | GSymbQualid ("USE_NT", _) :: GSymbQualid (s2, l) :: tl ->
    (Sedit2 ("USE_NT", s2)) :: cvt_gram_sym_list tl
  | hd :: tl ->
    cvt_gram_sym hd :: cvt_gram_sym_list tl
  | [] -> []

and cvt_gram_prod p =
 List.concat (List.map (fun x -> let _, gs = x in cvt_gram_sym_list gs)  p.gprod_symbs)


let add_symdef nt file symdef_map =
  let ent =
    try
      StringMap.find nt !symdef_map
    with Not_found -> []
  in
  symdef_map := StringMap.add nt (Filename.basename file::ent) !symdef_map

let rec edit_SELF nt cur_level next_level right_assoc prod =
  let len = List.length prod in
  List.mapi (fun i sym ->
    match sym with
    | Snterm s -> begin match s with
      | s when s = nt || s = "SELF" ->
        if i = 0 then Snterm next_level
        else if i+1 < len then sym
        else if right_assoc then Snterm cur_level else Snterm next_level
      | "NEXT" -> Snterm next_level
      | _ -> sym
    end
    | Slist1 sym -> Slist1 (List.hd (edit_SELF nt cur_level next_level right_assoc [sym]))
    | Slist0 sym -> Slist0 (List.hd (edit_SELF nt cur_level next_level right_assoc [sym]))
    | x -> x)
  prod


let autoloaded_mlgs = [ (* in the order they are loaded by Coq *)
 "parsing/g_constr.mlg";
 "parsing/g_prim.mlg";
 "vernac/g_vernac.mlg";
 "vernac/g_proofs.mlg";
 "toplevel/g_toplevel.mlg";
 "plugins/ltac/extraargs.mlg";
 "plugins/ltac/g_obligations.mlg";
 "plugins/ltac/coretactics.mlg";
 "plugins/ltac/extratactics.mlg";
 "plugins/ltac/profile_ltac_tactics.mlg";
 "plugins/ltac/g_auto.mlg";
 "plugins/ltac/g_class.mlg";
 "plugins/ltac/g_rewrite.mlg";
 "plugins/ltac/g_eqdecide.mlg";
 "plugins/ltac/g_tactic.mlg";
 "plugins/ltac/g_ltac.mlg";
 "plugins/syntax/g_string.mlg";
 "plugins/btauto/g_btauto.mlg";
 "plugins/rtauto/g_rtauto.mlg";
 "plugins/cc/g_congruence.mlg";
 "plugins/firstorder/g_ground.mlg";
 "plugins/syntax/g_numeral.mlg";
]


let ematch prod edit =
  let rec ematchr prod edit =
    (*Printf.printf "%s and\n  %s\n\n" (prod_to_str prod) (prod_to_str edit);*)
    match (prod, edit) with
    | (_, Sedit _ :: tl)
    | (_, Sedit2 _ :: tl)
      -> ematchr prod tl
    | (Sedit _ :: tl, _)
    | (Sedit2 _ :: tl, _)
      -> ematchr tl edit
    | (phd :: ptl, hd :: tl) ->
      let m = match (phd, hd) with
        | (Slist1 psym, Slist1 sym)
        | (Slist0 psym, Slist0 sym)
        | (Sopt psym, Sopt sym)
          -> ematchr [psym] [sym]
        | (Slist1sep (psym, psep), Slist1sep (sym, sep))
        | (Slist0sep (psym, psep), Slist0sep (sym, sep))
          -> ematchr [psym] [sym] && ematchr [psep] [sep]
        | (Sparen psyml, Sparen syml)
          -> ematchr psyml syml
        | (Sprod psymll, Sprod symll)
          -> List.fold_left (&&) true (List.map2 ematchr psymll symll)
        | _, _ -> phd = hd
      in
      m && ematchr ptl tl
    | ([], hd :: tl) -> false
    | (phd :: ptl, []) -> false
    | ([], []) -> true
in
  (*Printf.printf "\n";*)
  let rv = ematchr prod edit in
  (*Printf.printf "%b\n" rv;*)
  rv

let has_match p prods = List.exists (fun p2 -> ematch p p2) prods

let plugin_regex = Str.regexp "^plugins/\\([a-zA-Z0-9_]+\\)/"

let read_mlg is_edit ast file level_renames symdef_map =
  let res = ref [] in
  let add_prods nt prods =
    if not is_edit then
      add_symdef nt file symdef_map;
    let prods = if not is_edit &&
        not (List.mem file autoloaded_mlgs) &&
        Str.string_match plugin_regex file 0 then
      let plugin = Str.matched_group 1 file in
      List.map (fun p -> p @ [Sedit2 ("PLUGIN", plugin)]) prods
    else
      prods
    in
    (* todo: doesn't yet work perfectly with SPLICE *)
(*    let prods = if not is_edit then List.map (fun p -> p @ [Sedit2 ("FILE", file)]) prods else prods in*)
    res := (nt, prods) :: !res
  in
  let prod_loop = function
    | GramExt grammar_ext ->
      let get_label = function
        | Some s -> s
        | None -> ""
      in
      List.iter (fun ent ->
          let len = List.length ent.gentry_rules in
          List.iteri (fun i rule ->
              let nt = ent.gentry_name in
              let level = (get_label rule.grule_label) in
              let level = if level <> "" then level else
                match ent.gentry_pos with
                | Some Level lev
                | Some Before lev
                | Some After lev
                  -> lev
                (* Looks like FIRST/LAST can be ignored for documenting the current grammar *)
                | _ -> "" in
              let cur_level = nt ^ level in
              let next_level = nt ^
                  if i+1 < len then (get_label (List.nth ent.gentry_rules (i+1)).grule_label) else "" in
              let right_assoc = (rule.grule_assoc = Some RightA) in

              if i = 0 && cur_level <> nt && not (StringMap.mem nt !level_renames) then begin
                level_renames := StringMap.add nt cur_level !level_renames;
              end;
              let cvted = List.map cvt_gram_prod rule.grule_prods in
              (* edit names for levels *)
              (* See https://camlp5.github.io/doc/html/grammars.html#b:Associativity *)
              let edited = List.map (edit_SELF nt cur_level next_level right_assoc) cvted in
              let prods_to_add =
                if cur_level <> nt && i+1 < len then
                  edited @ [[Snterm next_level]]
                else
                  edited in
              add_prods cur_level prods_to_add)
            ent.gentry_rules
        ) grammar_ext.gramext_entries

    | VernacExt vernac_ext ->
      let node = match vernac_ext.vernacext_entry with
      | None -> "command"
      | Some c -> String.trim c.code
      in
      add_prods node
        (List.map (fun r -> cvt_ext r.vernac_toks) vernac_ext.vernacext_rules)
    | VernacArgumentExt vernac_argument_ext ->
      add_prods vernac_argument_ext.vernacargext_name
        (List.map (fun r -> cvt_ext r.tac_toks) vernac_argument_ext.vernacargext_rules)
    | TacticExt tactic_ext ->
      add_prods "simple_tactic"
        (List.map (fun r -> cvt_ext r.tac_toks) tactic_ext.tacext_rules)
    | ArgumentExt argument_ext ->
      add_prods argument_ext.argext_name
        (List.map (fun r -> cvt_ext r.tac_toks) argument_ext.argext_rules)
    | _ -> ()
  in

  List.iter prod_loop ast;
  List.rev !res

let dir s = "doc/tools/docgram/" ^ s

let read_mlg_edit file =
  let fdir = dir file in
  let level_renames = ref StringMap.empty in (* ignored *)
  let symdef_map = ref StringMap.empty in (* ignored *)
  read_mlg true (parse_file fdir) fdir level_renames symdef_map

let add_rule g nt prods file =
  let ent = try NTMap.find nt !g.map with Not_found -> [] in
  let nodups = List.concat (List.map (fun prod ->
      if has_match prod ent then begin
        if !show_warn then
          warn "%s: Duplicate production '%s: %s'\n" file nt (prod_to_str prod);
        []
      end else
        [prod])
    prods) in
  g_maybe_add_begin g nt (ent @ nodups)

let read_mlg_files g args symdef_map =
  let level_renames = ref StringMap.empty in
  let last_autoloaded = List.hd (List.rev autoloaded_mlgs) in
  List.iter (fun file ->
    (* does nt renaming, deletion and splicing *)
    let rules = read_mlg false (parse_file file) file level_renames symdef_map in
    let numprods = List.fold_left (fun num rule ->
        let nt, prods = rule in
        add_rule g nt prods file;
        num + List.length prods)
      0 rules
    in
    if args.verbose then begin
      Printf.eprintf "%s:  %d nts,  %d prods\n" file (List.length rules) numprods;
      if file = last_autoloaded then
        Printf.eprintf "  Optionally loaded plugins:\n"
    end
  ) args.mlg_files;
  g_reverse g;
  !level_renames


(*** global editing ops ***)

let create_edit_map edits =
  let rec aux edits map =
    match edits with
    | [] -> map
    | edit :: tl ->
      let (key, binding) = edit in
      aux tl (StringMap.add key binding map)
  in
  aux edits StringMap.empty

(* edit a production: rename nonterminals, drop nonterminals, substitute nonterminals *)
let rec edit_prod g top edit_map prod =
  let edit_nt edit_map sym0 nt =
    try
      let binding = StringMap.find nt edit_map in
      match binding with
      | "DELETE" -> []
      | "SPLICE" ->
        begin
          try let splice_prods = NTMap.find nt !g.map in
            match splice_prods with
            | [] -> assert false
            | [p] -> List.rev p
            | _ -> [Sprod splice_prods]
          with Not_found -> error "Missing nt '%s' for splice\n" nt; [Snterm nt]
        end
      | _ -> [Snterm binding]
    with Not_found -> [sym0]
  in

  let rec edit_symbol sym0 =
    match sym0 with
      | Sterm s -> [sym0]
      | Snterm s -> edit_nt edit_map sym0 s
      | Slist1 sym -> [Slist1 (List.hd (edit_symbol sym))]
      (* you'll get a run-time failure deleting a SEP symbol *)
      | Slist1sep (sym, sep) -> [Slist1sep (List.hd (edit_symbol sym), (List.hd (edit_symbol sep)))]
      | Slist0 sym -> [Slist0 (List.hd (edit_symbol sym))]
      | Slist0sep (sym, sep) -> [Slist0sep (List.hd (edit_symbol sym), (List.hd (edit_symbol sep)))]
      | Sopt sym -> [Sopt (List.hd (edit_symbol sym))]
      | Sparen slist -> [Sparen (List.hd (edit_prod g false edit_map slist))]
      | Sprod slistlist -> let (_, prods) = edit_rule g edit_map "" slistlist in
                           [Sprod prods]
      | Sedit _
      | Sedit2 _ -> [sym0] (* these constructors not used here *)
  in
  let is_splice nt =
    try
      StringMap.find nt edit_map = "SPLICE"
    with Not_found -> false
  in
  let get_splice_prods nt =
    try NTMap.find nt !g.map
    with Not_found -> (error "Missing nt '%s' for splice\n" nt; [])
  in

  (* special case splice creating multiple new productions *)
  let splice_prods = match prod with
    | Snterm nt :: [] when is_splice nt ->
      get_splice_prods nt
    | _ -> []
  in
  if top && splice_prods <> [] then
    splice_prods
  else
    [List.rev (List.concat (List.rev (List.map (fun sym -> edit_symbol sym) prod)))]

and edit_rule g edit_map nt rule =
  let nt =
    try let new_name = StringMap.find nt edit_map in
      match new_name with
      | "SPLICE" -> nt
      | "DELETE" -> ""
      | _ -> new_name
    with Not_found -> nt
  in
  (nt, (List.concat (List.map (edit_prod g true edit_map) rule)))

(*** splice: replace a reference to a nonterminal with its definition ***)

(* todo: create a better splice routine, handle recursive case *)
let apply_splice g splice_map =
  StringMap.iter (fun nt b ->
      if not (NTMap.mem nt !g.map) then
        error "Unknown nt '%s' for apply_splice\n" nt)
    splice_map;
  List.iter (fun b ->
      let (nt, prods) = b in
      let (nt', prods) = edit_rule g splice_map nt prods in
      g_update_prods g nt' prods)
    (NTMap.bindings !g.map);
  List.iter (fun b ->
      let (nt, op) = b in
      match op with
      | "DELETE"
      | "SPLICE" ->
        g_remove g nt;
      | _ -> ())
    (StringMap.bindings splice_map)

let find_first edit prods nt =
  let rec find_first_r edit prods nt i =
    match prods with
    | [] ->
      error "Can't find '%s' in REPLACE for '%s'\n" (prod_to_str edit) nt;
      raise Not_found
    | prod :: tl ->
      if ematch prod edit then i
      else find_first_r edit tl nt (i+1)
  in
  find_first_r edit prods nt 0

let remove_prod edit prods nt =
  let res, got_first = List.fold_left (fun args prod ->
      let res, got_first = args in
      if not got_first && ematch prod edit then
        res, true
      else
        prod :: res, got_first)
    ([], false) prods in
  if not got_first then
    error "Can't find '%s' to DELETE for '%s'\n" (prod_to_str edit) nt;
  List.rev res

let insert_after posn insert prods =
  List.concat (List.mapi (fun i prod ->
      if i = posn then prod :: insert else [prod])
    prods)

(*** replace LIST*, OPT with new nonterminals ***)

(* generate a non-terminal name for a replacement *)
let nt_regex = Str.regexp "^[a-zA-Z_][a-zA-Z0-9_\\.]*$"
let good_name name = if Str.string_match nt_regex name 0 then name else ""
let map_name s =
  let s = match s with
  | "|" -> "or"
  | "!" -> "exclam"
  | ">" -> "gt"
  | "<" -> "lt"
  | "+" -> "plus"
  | "?" -> "qmark"
  | "}" -> "rbrace"
  | "," -> "comma"
  | ";" -> "semi"
  | _ -> s
  in
  good_name s

let rec gen_nt_name sym =
  let name_from_prod prod =
    let rec aux name sterm_name prod =
      if name <> "" then name else
        match prod with
        | [] -> sterm_name
        | Sterm s :: tl
        | Snterm s :: tl ->
          if good_name s <> "" then
            aux (map_name s) sterm_name tl
          else
            aux name (map_name s) tl;
        | sym :: tl->
          aux (gen_nt_name sym) sterm_name tl
    in
    aux "" "" prod
  in

  let name = match sym with
    | Sterm s -> map_name s
    | Snterm s -> s
    | Slist1 sym
    | Slist1sep (sym, _)
    | Slist0 sym
    | Slist0sep (sym, _)
    | Sopt sym ->
      gen_nt_name sym
    | Sparen slist ->
      name_from_prod slist
    | Sprod slistlist ->
      name_from_prod (List.hd slistlist)
    | _ -> ""
  in
  good_name name

(* create a new nt for LIST* or OPT with the specified name *)
let rec maybe_add_nt g insert_after name sym queue =
  let empty = [Snterm "empty"] in
  let maybe_unwrap ?(multi=false) sym =
    match sym with
    | Sprod slist when List.length slist = 1 || multi
                   ->    slist
    | Sparen slist -> [ slist ]
    | _ ->            [ [sym] ]
  in
  let unw sym = List.hd (maybe_unwrap sym) in
  let get_prods nt =
    match sym with
    | Slist1 sym ->           let sym' = unw sym in
                              [ [Snterm nt] @ sym';           sym' ]
    | Slist1sep (sym, sep)
    | Slist0sep (sym, sep) -> let sym' = unw sym in
                              [ [Snterm nt; sep] @ sym';      sym' ]
    | Slist0 sym ->           [ [Snterm nt] @ (unw sym);      empty ]
    | Sopt sym ->             (maybe_unwrap ~multi:true sym) @ [ empty ]
    | Sprod slistlist ->      slistlist
    | _ -> []
  in

  let is_slist0sep sym =
    match sym with
    | Slist0sep _ -> true
    | _ -> false
  in

  (* find an existing nt with an identical definition, or generate an unused nt name *)
  let rec find_name nt i =
    let trial_name = sprintf "%s%s" nt (if i = 1 then "" else string_of_int i) in
    try
      if NTMap.find trial_name !g.map = get_prods trial_name then
        trial_name
      else
        find_name nt (succ i)
    with Not_found -> trial_name
  in
  let list_name sep =
    match sep with
      | Sterm s ->
        let name = map_name s in
        if name = s then "_list" else "_list_" ^ name
      | _ -> "_list"
  in
  let nt = name ^ match sym with
    | Slist1 sym ->           "_list"
    | Slist1sep (sym, sep) -> list_name sep
    | Slist0 sym ->           "_list_opt"
    | Slist0sep (sym, sep) -> list_name sep   (* special handling *)
    | Sopt sym ->             "_opt"
    | Sprod slistlist ->      "_alt"
    | _ -> (error "Invalid symbol for USE_NT for nt '%s'\n" name; "ERROR")
  in
  let base_nt = find_name nt 1 in
  let new_nt = if is_slist0sep sym then base_nt ^ "_opt" else base_nt in
  if not (NTMap.mem new_nt !g.map) then begin
    let prods = if is_slist0sep sym then [ [Snterm base_nt]; empty ] else get_prods base_nt in
    g_add_after g (Some !insert_after) new_nt prods;
    insert_after := new_nt;
    Queue.add new_nt queue
  end;
  if is_slist0sep sym && not (NTMap.mem base_nt !g.map) then begin
    match sym with
    | Slist0sep (sym, sep) ->
      let prods = get_prods base_nt in
      g_add_after g (Some !insert_after) base_nt prods;
      insert_after := base_nt;
      Queue.add base_nt queue
    | _ -> ()
  end;
  new_nt

(* expand LIST*, OPT and add "empty" *)
(* todo: doesn't handle recursive expansions well, such as syntax_modifier_opt *)
and expand_rule g edited_nt queue =
  let rule = NTMap.find edited_nt !g.map in
  let insert_after = ref edited_nt in
  let rec expand rule =
    let rec aux syms res =
      match syms with
      | [] -> res
      | sym0 :: tl ->
        let new_sym = match sym0 with
          | Sterm _
          | Snterm _ ->
            sym0
          | Slist1 sym
          | Slist1sep (sym, _)
          | Slist0 sym
          | Slist0sep (sym, _)
          | Sopt sym ->
            let name = gen_nt_name sym in
            if name <> "" then begin
              let new_nt = maybe_add_nt g insert_after name sym0 queue in
              Snterm new_nt
            end else sym0
          | Sparen slist -> Sparen (expand slist)
          | Sprod slistlist ->
            let has_empty = List.length (List.hd (List.rev slistlist)) = 0 in
            let name = gen_nt_name sym0 in
            if name <> "" then begin
              let new_nt = maybe_add_nt g insert_after name
                  (if has_empty then (Sopt (Sprod (List.rev (List.tl (List.rev slistlist))) ))
                  else sym0) queue
              in
              Snterm new_nt
            end else
              Sprod (List.map expand slistlist)
          | Sedit _
          | Sedit2 _ ->
            sym0 (* these constructors not used here *)
        in
        aux tl (new_sym :: res)
    in
    List.rev (aux rule (if edited_nt <> "empty" && ematch rule [] then [Snterm "empty"] else []))
  in
  let rule' = List.map expand rule in
  g_update_prods g edited_nt rule'

let expand_lists g =
  (* todo: use Queue.of_seq w OCaml 4.07+ *)
  let queue = Queue.create () in
  List.iter (fun nt -> Queue.add nt queue) !g.order;
  try
    while true do
      let nt = Queue.pop queue in
      expand_rule g nt queue
    done
  with
  | Queue.Empty -> ()

let edit_all_prods g op eprods =
  let do_it op eprods num =
    let rec aux eprods res =
      match eprods with
      | [] -> res
      | [Snterm old_nt; Snterm new_nt] :: tl when num = 2 ->
        aux tl ((old_nt, new_nt) :: res)
      | [Snterm old_nt] :: tl when num = 1 ->
        aux tl ((old_nt, op) :: res)
      | eprod :: tl ->
        error "Production '%s: %s' must have only %d nonterminal(s)\n"
            op (prod_to_str eprod) num;
        aux tl res
    in
    let map = create_edit_map (aux eprods []) in
    if op = "SPLICE" then
      apply_splice g map
    else (* RENAME/DELETE *)
      List.iter (fun b -> let (nt, _) = b in
          let prods = try NTMap.find nt !g.map  with Not_found -> [] in
          let (nt', prods') = edit_rule g map nt prods in
          if nt' = "" then
            g_remove g nt
          else if nt <> nt' then
            g_rename_merge g nt nt' prods'
          else
            g_update_prods g nt prods')
        (NTMap.bindings !g.map);
  in
  match op with
  | "RENAME" -> do_it op eprods 2; true
  | "DELETE" -> do_it op eprods 1; true
  | "SPLICE" -> do_it op eprods 1; true
  | "EXPAND" ->
    if List.length eprods > 1 || List.length (List.hd eprods) <> 0 then
      error "'EXPAND:' expects a single empty production\n";
    expand_lists g; true
  | _ -> false

let edit_single_prod g edit0 prods nt =
  let rec edit_single_prod_r edit prods nt seen =
    match edit with
    | [] -> prods
    | Sedit "ADD_OPT" :: sym :: tl ->
      let prods' = (try
          let pfx = List.rev seen in
          let posn = find_first edit0 prods nt in
          let prods = insert_after posn [pfx @ (Sopt sym :: tl)] prods in
          let prods = remove_prod (pfx @ (sym :: tl)) prods nt in
          remove_prod (pfx @ tl) prods nt
        with Not_found -> prods) in
        edit_single_prod_r tl prods' nt seen
    | Sedit "ADD_OPT" :: [] -> error "Bad position for ADD_OPT\n"; prods
    | Sedit2 ("USE_NT", name) :: sym :: tl ->
      let prods' = (try
        let nt = maybe_add_nt g (ref nt) name sym (Queue.create ()) in
        let pfx = List.rev seen in
        let posn = find_first edit0 prods nt in
        let prods = insert_after posn [pfx @ (Snterm nt :: tl)] prods in
        remove_prod (pfx @ (sym :: tl)) prods nt
      with Not_found -> prods) in
      edit_single_prod_r tl prods' nt seen
    | Sedit2 ("USE_NT", _) :: [] -> error "Bad position for USE_NT\n"; prods
    | sym :: tl ->
      edit_single_prod_r tl prods nt (sym :: seen)
  in
  edit_single_prod_r edit0 prods nt []

let apply_edit_file g edits =
  List.iter (fun b ->
      let (nt, eprod) = b in
      if not (edit_all_prods g nt eprod) then begin
        let rec aux eprod prods add_nt =
          match eprod with
          | [] -> prods, add_nt
          | (Snterm "DELETE" :: oprod) :: tl ->
            aux tl (remove_prod oprod prods nt) add_nt
          | (Snterm "DELETENT" :: _) :: tl ->  (* note this doesn't remove references *)
            g_remove g nt;
            aux tl prods false
          | (Snterm "EDIT" :: oprod) :: tl ->
            aux tl (edit_single_prod g oprod prods nt) add_nt
          | (Snterm "REPLACE" :: oprod) :: (Snterm "WITH" :: rprod) :: tl ->
            let prods' = (try
              let posn = find_first oprod prods nt in
              let prods = insert_after posn [rprod] prods in  (* insert new prod *)
              remove_prod oprod prods nt      (* remove orig prod *)
              with Not_found -> prods)
            in
            aux tl prods' add_nt
          | (Snterm "REPLACE" :: _ as eprod) :: tl ->
            error "Missing WITH after '%s' in '%s'\n" (prod_to_str eprod) nt;
            aux tl prods add_nt
          | prod :: tl ->
            (* add a production *)
            if has_match prod prods then
              error "Duplicate production '%s' for %s\n" (prod_to_str prod) nt;
            aux tl (prods @ [prod]) add_nt
        in
        let prods, add_nt =
          aux eprod (try NTMap.find nt !g.map with Not_found -> []) true in
        if add_nt then
          g_maybe_add g nt prods
      end)
    edits


(*** main routines ***)

 (* get the nt's in the production, preserving order, don't worry about dups *)
 let nts_in_prod prod =
  let rec traverse = function
  | Sterm s -> []
  | Snterm s -> [s]
  | Slist1 sym
  | Slist0 sym
  | Sopt sym
    -> traverse sym
  | Slist1sep (sym, sep)
  | Slist0sep (sym, sep)
    -> traverse sym @ (traverse sep)
  | Sparen sym_list -> List.concat (List.map traverse sym_list)
  | Sprod sym_list_list -> List.concat (List.map (fun l -> List.concat (List.map traverse l)) sym_list_list)
  | Sedit _
  | Sedit2 _ -> []
  in
  List.rev (List.concat (List.map traverse prod))

  (* get the special tokens in the grammar *)
let print_special_tokens g =
  let rec traverse set = function
  | Sterm s ->
    let c = s.[0] in
    if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') then set
    else StringSet.add s set
  | Snterm s -> set
  | Slist1 sym
  | Slist0 sym
  | Sopt sym
    -> traverse set sym
  | Slist1sep (sym, sep)
  | Slist0sep (sym, sep)
    -> traverse (traverse set sym) sep
  | Sparen sym_list -> traverse_prod set sym_list
  | Sprod sym_list_list -> traverse_prods set sym_list_list
  | Sedit _
  | Sedit2 _ -> set
  and traverse_prod set prod = List.fold_left traverse set prod
  and traverse_prods set prods = List.fold_left traverse_prod set prods
  in
  let spec_toks = List.fold_left (fun set b ->
      let nt, prods = b in
      traverse_prods set prods)
    StringSet.empty (NTMap.bindings !g.map)
  in
  Printf.printf "Special tokens:";
  StringSet.iter (fun t -> Printf.printf " %s" t) spec_toks;
  Printf.printf "\n\n"

(* get the transitive closure of a non-terminal excluding "stops" symbols.
   Preserve ordering to the extent possible *)
(* todo: at the moment, the code doesn't use the ordering; consider switching to using
sets instead of lists *)
let nt_closure g start stops =
  let stop_set = StringSet.of_list stops in
  let rec nt_closure_r res todo =
    match todo with
    | [] -> res
    | nt :: tl ->
      if List.mem nt res || StringSet.mem nt stop_set then
        nt_closure_r res tl
      else begin
        let more_to_do =
          try
            let prods = NTMap.find nt !g.map in
            tl @ (List.concat (List.map nts_in_prod prods))
          with Not_found -> tl in
        nt_closure_r (nt :: res) more_to_do
      end
  in
  List.rev (nt_closure_r [] [start])

let header = "--------------------------------------------"
let nt_subset_in_orig_order g nts =
  let subset = StringSet.of_list nts in
  List.filter (fun nt -> StringSet.mem nt subset) !g.order

let print_chunk out g seen fmt title starts ends =
  fprintf out "\n\n%s:\n%s\n" title header;
  List.iter (fun start ->
      let nts = (nt_closure g start ends) in
      print_in_order out g fmt (nt_subset_in_orig_order g nts) !seen;
      seen := StringSet.union !seen (StringSet.of_list nts))
    starts

let print_chunks g out fmt () =
  let seen = ref StringSet.empty in
  print_chunk out g seen fmt "lconstr" ["lconstr"] ["binder_constr"; "tactic_expr5"];
  print_chunk out g seen fmt "Gallina syntax of terms" ["binder_constr"] ["tactic_expr5"];
  print_chunk out g seen fmt "Gallina The Vernacular" ["gallina"] ["tactic_expr5"];
  print_chunk out g seen fmt "intropattern_list_opt" ["intropattern_list"; "or_and_intropattern_loc"] ["operconstr"; "tactic_expr5"];
  print_chunk out g seen fmt "simple_tactic" ["simple_tactic"]
    ["tactic_expr5"; "tactic_expr3"; "tactic_expr2"; "tactic_expr1"; "tactic_expr0"];

  (*print_chunk out g seen fmt "Ltac" ["tactic_expr5"] [];*)
  print_chunk out g seen fmt "Ltac" ["tactic_expr5"] ["tactic_expr4"];
  print_chunk out g seen fmt "Ltac 4" ["tactic_expr4"] ["tactic_expr3"; "tactic_expr2"];
  print_chunk out g seen fmt "Ltac 3" ["tactic_expr3"] ["tactic_expr2"];
  print_chunk out g seen fmt "Ltac 2" ["tactic_expr2"] ["tactic_expr1"];
  print_chunk out g seen fmt "Ltac 1" ["tactic_expr1"] ["tactic_expr0"];
  print_chunk out g seen fmt "Ltac 0" ["tactic_expr0"] [];


  print_chunk out g seen fmt "command" ["command"] [];
  print_chunk out g seen fmt "vernac_toplevel" ["vernac_toplevel"] [];
  print_chunk out g seen fmt "vernac_control" ["vernac_control"] []

  (*
    let ssr_tops = ["ssr_dthen"; "ssr_else"; "ssr_mpat"; "ssr_rtype"] in
    seen := StringSet.union !seen (StringSet.of_list ssr_tops);

    print_chunk out g seen fmt "ssrindex" ["ssrindex"] [];
    print_chunk out g seen fmt "command" ["command"] [];
    print_chunk out g seen fmt "binder_constr" ["binder_constr"] [];
    (*print_chunk out g seen fmt "closed_binder" ["closed_binder"] [];*)
    print_chunk out g seen fmt "gallina_ext" ["gallina_ext"] [];
    (*print_chunk out g seen fmt "hloc" ["hloc"] [];*)
    (*print_chunk out g seen fmt "hypident" ["hypident"] [];*)
    print_chunk out g seen fmt "simple_tactic" ["simple_tactic"] [];
    print_chunk out g seen fmt "tactic_expr" ["tactic_expr4"; "tactic_expr1"; "tactic_expr0"] [];
    fprintf out "\n\nRemainder:\n";
    print_in_order g (List.filter (fun x -> not (StringSet.mem x !seen)) !g.order) StringSet.empty;
  *)


    (*seen := StringSet.diff !seen (StringSet.of_list ssr_tops);*)
    (*print_chunk out g seen fmt "vernac_toplevel" ["vernac_toplevel"] [];*)

let start_symbols = ["vernac_toplevel"]
(* don't report tokens as undefined *)
let tokens = [ "bullet"; "field"; "ident"; "int"; "num"; "numeral"; "string" ]

let report_bad_nts g file =
  let rec get_nts refd defd bindings =
    match bindings with
    | [] -> refd, defd
    | (nt, prods) :: tl ->
      get_nts (List.fold_left (fun res prod ->
                  StringSet.union res (StringSet.of_list (nts_in_prod prod)))
                refd prods)
        (StringSet.add nt defd) tl
  in
  let all_nts_ref, all_nts_def =
    get_nts (StringSet.of_list tokens) (StringSet.of_list tokens) (NTMap.bindings !g.map) in

  let undef = StringSet.diff all_nts_ref all_nts_def in
  List.iter (fun nt -> warn "%s: Undefined symbol '%s'\n" file nt) (StringSet.elements undef);

  let reachable =
    List.fold_left (fun res sym ->
        StringSet.union res (StringSet.of_list (nt_closure g sym [])))
      StringSet.empty start_symbols
  in
  let unreachable = List.filter (fun nt -> not (StringSet.mem nt reachable)) !g.order in
  List.iter (fun nt -> warn "%s: Unreachable symbol '%s'\n" file nt) unreachable


let report_info g symdef_map =
  let num_prods = List.fold_left (fun sum nt -> let prods = NTMap.find nt !g.map in sum + (List.length prods))
    0 !g.order
  in

  Printf.eprintf "\nstart symbols: %s\n" (String.concat " " start_symbols);
  Printf.eprintf "%d nonterminals defined, %d productions\n" (NTMap.cardinal !g.map) num_prods;
  Printf.eprintf "%d terminals\n" (List.length tokens);

  Printf.eprintf "\nSymbols with multiple definition points in *.mlg:\n";
  let bindings = List.sort (fun a b -> let (ak, _) = a and (bk, _) = b in
                            String.compare ak bk) (StringMap.bindings symdef_map) in
  List.iter (fun b ->
      let (k, v) = b in
      if List.length v > 1 then begin
        Printf.eprintf "  %s:  " k;
        List.iter (fun f -> Printf.eprintf "%s " f) v;
        Printf.eprintf "\n"
      end)
    bindings;
  Printf.eprintf "\n"



[@@@ocaml.warning "-32"]
let rec dump prod =
  match prod with
  | hd :: tl -> let s = (match hd with
    | Sterm s -> sprintf "Sterm %s" s
    | Snterm s -> sprintf "Snterm \"%s\"" s
    | Slist1 sym -> "Slist1"
    | Slist0 sym -> "Slist0"
    | Sopt sym -> "Sopt"
    | Slist1sep _ -> "Slist1sep"
    | Slist0sep _ -> "Slist0sep"
    | Sparen sym_list -> "Sparen"
    | Sprod sym_list_list -> "Sprod"
    | Sedit _ -> "Sedit"
    | Sedit2 _ -> "Sedit2") in
    Printf.printf "%s " s;
    dump tl
  | [] -> Printf.printf "\n"
[@@@ocaml.warning "+32"]

let reorder_grammar eg reordered_rules file =
  let og = ref { map = NTMap.empty; order = [] } in
  List.iter (fun rule ->
      let nt, prods = rule in
      try
        (* only keep nts and prods in common with editedGrammar *)
        let eg_prods = NTMap.find nt !eg.map in
        let prods = List.filter (fun prod -> (has_match prod eg_prods)) prods in
        if NTMap.mem nt !og.map then
          warn "%s: Duplicate nonterminal '%s'\n" file nt;
        add_rule og nt prods file
      with Not_found -> ())
    reordered_rules;
  g_reverse og;

  (* insert a prod in a list after prev_prod (None=at the beginning) *)
  let rec insert_prod prev_prod prod prods res =
    match prev_prod, prods with
    | None, _ -> prod :: prods
    | Some _, [] -> raise Not_found
    | Some ins_after_prod, hd :: tl ->
      if ematch hd ins_after_prod then
        (List.rev res) @ (hd :: prod :: tl)
      else
        insert_prod prev_prod prod tl (hd :: res)
  in

  (* insert prods that are not already in og_prods *)
  let rec upd_prods prev_prod eg_prods og_prods =
    match eg_prods with
    | [] -> og_prods
    | prod :: tl ->
      let og_prods =
        if has_match prod og_prods then
          List.map (fun p -> if ematch p prod then prod else p) og_prods
        else
          insert_prod prev_prod prod og_prods [] in
      upd_prods (Some prod) tl og_prods
  in

  (* add nts and prods not present in orderedGrammar *)
  let _ = List.fold_left (fun prev_nt nt ->
      let e_prods = NTMap.find nt !eg.map in
      if not (NTMap.mem nt !og.map) then
        g_add_after og prev_nt nt e_prods
      else
        g_update_prods og nt (upd_prods None e_prods (NTMap.find nt !og.map));
      Some nt)
    None !eg.order in
  g_reorder eg !og.map !og.order


let finish_with_file old_file verify =
  let files_eq f1 f2 =
    let chunksize = 8192 in
    (try
      let ofile = open_in_bin f1 in
      let nfile = open_in_bin f2 in
      let rv = if (in_channel_length ofile) <> (in_channel_length nfile) then false
        else begin
        let obuf = Bytes.create chunksize in
        Bytes.fill obuf 0 chunksize '\x00';
        let nbuf = Bytes.create chunksize in
        Bytes.fill nbuf 0 chunksize '\x00';
        let rec read () =
          let olen = input ofile obuf 0 chunksize in
          let _ = input nfile nbuf 0 chunksize in
          if obuf <> nbuf then
            false
          else if olen = 0 then
            true
          else
            read ()
        in
        read ()
        end
      in
      close_in ofile;
      close_in nfile;
      rv
    with Sys_error _ -> false)
  in

  let temp_file = (old_file ^ "_temp") in
  if verify then
    if (files_eq old_file temp_file || !exit_code <> 0) then
      Sys.remove temp_file
    else
      error "%s is not current\n" old_file
  else
    Sys.rename temp_file old_file

let open_temp_bin file =
  open_out_bin (sprintf "%s_temp" file)

let find_longest_match prods str =
  (* todo: require a minimum length? *)
  let common_prefix_len s1 s2 =
    let limit = min (String.length s1) (String.length s2) in
    let rec aux off =
      if off = limit then off
      else if s1.[off] = s2.[off] then aux (succ off)
      else off
    in
    aux 0
  in

  let slen = String.length str in
  let rec longest best multi best_len prods =
    match prods with
    | [] -> best, multi, best_len
    | prod :: tl ->
      let pstr = String.trim (prod_to_prodn prod) in
      let clen = common_prefix_len str pstr in
      if clen = slen && slen = String.length pstr then
        pstr, false, clen  (* exact match *)
      else if clen > best_len then
        longest pstr false clen tl  (* better match *)
      else if clen = best_len then
        longest best true best_len tl  (* 2nd match with same length *)
      else
        longest best multi best_len tl  (* worse match *)
  in
  longest "" false 0 prods

type seen = {
  nts: (string * int) NTMap.t;
  tacs: (string * int) NTMap.t;
  cmds: (string * int) NTMap.t;
}

let process_rst g file args seen tac_prods cmd_prods =
  let old_rst = open_in file in
  let new_rst = open_temp_bin file in
  let linenum = ref 0 in
  let dir_regex = Str.regexp "^\\([ \t]*\\)\\.\\.[ \t]*\\([a-zA-Z0-9:]*\\)\\(.*\\)" in
  let ig_args_regex = Str.regexp "^[ \t]*\\([a-zA-Z0-9_\\.]*\\)[ \t]*\\([a-zA-Z0-9_\\.]*\\)" in
  let blank_regex = Str.regexp "^[ \t]*$" in
  let end_prodlist_regex = Str.regexp "^[ \t]*$" in
  let rec index_of_r str list index =
    match list with
    | [] -> None
    | hd :: list ->
      if hd = str then Some index
      else index_of_r str list (index+1)
  in
  let index_of str list = index_of_r str list 0 in
  let getline () =
    let line = input_line old_rst in
    incr linenum;
    line
  in
  let output_insertgram start_index end_ indent is_coq_group =
    let rec nthcdr n list = if n = 0 then list else nthcdr (n-1) (List.tl list) in
    let rec copy_prods list =
      match list with
      | [] -> ()
      | nt :: tl ->
        (try
          let (prev_file, prev_linenum) = NTMap.find nt !seen.nts in
          warn "%s line %d: '%s' already included at %s line %d\n"
              file !linenum nt prev_file prev_linenum;
        with Not_found ->
          if is_coq_group then
            seen := { !seen with nts = (NTMap.add nt (file, !linenum) !seen.nts)} );
        let prods = NTMap.find nt !g.map in
        List.iteri (fun i prod ->
            let rhs = String.trim (sprintf ": %s" (prod_to_str ~plist:true prod)) in
            fprintf new_rst "%s   %s %s\n" indent (if i = 0 then nt else String.make (String.length nt) ' ') rhs)
          prods;
        if nt <> end_ then copy_prods tl
    in
    copy_prods (nthcdr start_index !g.order)
  in

  let process_insertgram line rhs =
    if not (Str.string_match ig_args_regex rhs 0) then
      error "%s line %d: bad arguments '%s' for 'insertgram'\n" file !linenum rhs
    else begin
      let start = Str.matched_group 1 rhs in
      let end_ = Str.matched_group 2 rhs in
      let start_index = index_of start !g.order in
      let end_index = index_of end_ !g.order in
      if start_index = None then
        error "%s line %d: '%s' is undefined\n" file !linenum start;
      if end_index = None then
        error "%s line %d: '%s' is undefined\n" file !linenum end_;
      match start_index, end_index with
      | Some start_index, Some end_index ->
        if start_index > end_index then
          error "%s line %d: '%s' must appear before '%s' in .../orderedGrammar\n" file !linenum start end_
        else begin
          try
            let line2 = getline() in
            if not (Str.string_match blank_regex line2 0) then
              error "%s line %d: expecting a blank line after 'insertgram'\n" file !linenum
            else begin
              let line3 = getline() in
              if not (Str.string_match dir_regex line3 0) || (Str.matched_group 2 line3) <> "productionlist::" then
                error "%s line %d: expecting 'productionlist' after 'insertgram'\n" file !linenum
              else begin
                let indent = Str.matched_group 1 line3 in
                let is_coq_group = ("coq" = String.trim (Str.matched_group 3 line3)) in
                let rec skip_to_end () =
                  let endline = getline() in
                  if Str.string_match end_prodlist_regex endline 0 then begin
                    fprintf new_rst "%s\n\n%s\n" line line3;
                    output_insertgram start_index end_ indent is_coq_group;
                    fprintf new_rst "%s\n" endline
                  end else
                    skip_to_end ()
                in
                skip_to_end ()
              end
            end
          with End_of_file -> error "%s line %d: unexpected end of file\n" file !linenum;
        end
      | _ -> ()
    end

  in
  try
    while true do
      let line = getline() in
      if Str.string_match dir_regex line 0 then begin
        let dir = Str.matched_group 2 line in
        let rhs = String.trim (Str.matched_group 3 line) in
        match dir with
        | "productionlist::" ->
          if rhs = "coq" then
            warn "%s line %d: Missing 'insertgram' before 'productionlist:: coq'\n" file !linenum;
          fprintf new_rst "%s\n" line;
        | "tacn::" when args.check_tacs ->
          if not (StringSet.mem rhs tac_prods) then
            warn "%s line %d: Unknown tactic: '%s'\n" file !linenum rhs;
          if NTMap.mem rhs !seen.tacs then
            warn "%s line %d: Repeated tactic: '%s'\n" file !linenum rhs;
          seen := { !seen with tacs = (NTMap.add rhs (file, !linenum) !seen.tacs)};
          fprintf new_rst "%s\n" line
        | "cmd::" when args.check_cmds ->
          if not (StringSet.mem rhs cmd_prods) then
            warn "%s line %d: Unknown command: '%s'\n" file !linenum rhs;
          if NTMap.mem rhs !seen.cmds then
            warn "%s line %d: Repeated command: '%s'\n" file !linenum rhs;
          seen := { !seen with cmds = (NTMap.add rhs (file, !linenum) !seen.cmds)};
          fprintf new_rst "%s\n" line
        | "insertgram" ->
          process_insertgram line rhs
        | _ -> fprintf new_rst "%s\n" line
      end else
        fprintf new_rst "%s\n" line;
    done
  with End_of_file -> ();
  close_in old_rst;
  close_out new_rst;
  finish_with_file file args.verify

let report_omitted_prods entries seen label split =
  let maybe_warn first last n =
    if first <> "" then begin
      if first <> last then
        warn "%ss '%s' to %s'%s' not included in .rst files (%d)\n" label first split last n
      else
        warn "%s %s not included in .rst files\n" label first;
    end
  in

  let first, last, n = List.fold_left (fun missing nt ->
      let first, last, n = missing in
      if NTMap.mem nt seen then begin
        maybe_warn first last n;
        "", "", 0
      end else
        (if first = "" then nt else first), nt, n + 1)
    ("", "", 0) entries in
  maybe_warn first last n

let process_grammar args =
  let symdef_map = ref StringMap.empty in
  let g = ref { map = NTMap.empty; order = [] } in

  let level_renames = read_mlg_files g args symdef_map in

  (* rename nts with levels *)
  List.iter (fun b -> let (nt, prod) = b in
      let (_, prod) = edit_rule g level_renames nt prod in
      g_update_prods g nt prod)
    (NTMap.bindings !g.map);

  (* print the full grammar with minimal editing *)
  let out = open_temp_bin (dir "fullGrammar") in
  fprintf out "%s\n%s\n\n"
      "(* Coq grammar generated from .mlg files.  Do not edit by hand.  Not compiled into Coq *)"
      "DOC_GRAMMAR";
  print_in_order out g `MLG !g.order StringSet.empty;
  close_out out;
  finish_with_file (dir "fullGrammar") args.verify;
  if args.verbose then
    print_special_tokens g;

  if not args.fullGrammar then begin
    (* do shared edits *)
    if !exit_code = 0 then begin
      let common_edits = read_mlg_edit "common.edit_mlg" in
      apply_edit_file g common_edits
    end;
    let prodn_gram = ref { map = !g.map; order = !g.order } in

    if !exit_code = 0 && not args.verify then begin
      let prodlist_edits = read_mlg_edit "productionlist.edit_mlg" in
      apply_edit_file g prodlist_edits;
      let out = open_temp_bin (dir "productionlistGrammar") in
      if args.verbose then
        report_info g !symdef_map;
      print_in_order out g `PRODLIST !g.order StringSet.empty;
      (*print_chunks g out `PRODLIST ();*)
      close_out out;
      finish_with_file (dir "productionlistGrammar") args.verify;
    end;

    if !exit_code = 0 && not args.verify then begin
      let out = open_temp_bin (dir "editedGrammar") in
      fprintf out "%s\n%s\n\n"
          "(* Edited Coq grammar generated from .mlg files.  Do not edit by hand.  Not compiled into Coq *)"
          "DOC_GRAMMAR";
      print_in_order out g `MLG !g.order StringSet.empty;
      close_out out;
      finish_with_file (dir "editedGrammar") args.verify;
      report_bad_nts g "editedGrammar"
    end;

    if !exit_code = 0 then begin
      let ordered_grammar = read_mlg_edit "orderedGrammar" in
      let out = open_temp_bin (dir "orderedGrammar") in
      fprintf out "%s\n%s\n\n"
          ("(* Defines the order to apply to editedGrammar to get productionlistGrammar.\n" ^
          "doc_grammar will modify this file to add/remove nonterminals and productions\n" ^
           "to match editedGrammar, which will remove comments.  Not compiled into Coq *)")
          "DOC_GRAMMAR";
      reorder_grammar g ordered_grammar "orderedGrammar";
      print_in_order out g `MLG !g.order StringSet.empty;
      close_out out;
      finish_with_file (dir "orderedGrammar") args.verify;
    end;

    if !exit_code = 0 then begin
      let plist nt =
        let list = (List.map (fun t -> String.trim (prod_to_prodn t))
          (NTMap.find nt !g.map)) in
        list, StringSet.of_list list in
      let tac_list, tac_prods = plist "simple_tactic" in
      let cmd_list, cmd_prods = plist "command" in
      let seen = ref { nts=NTMap.empty; tacs=NTMap.empty; cmds=NTMap.empty } in
      List.iter (fun file -> process_rst g file args seen tac_prods cmd_prods) args.rst_files;
      report_omitted_prods !g.order !seen.nts "Nonterminal" "";
      if args.check_tacs then
        report_omitted_prods tac_list !seen.tacs "Tactic" "\n                 ";
      if args.check_cmds then
        report_omitted_prods cmd_list !seen.cmds "Command" "\n                  "
    end;

    (* generate output for prodn: simple_tactic, command, also for Ltac?? *)
    if !exit_code = 0 && not args.verify then begin
      let prodn_edits = read_mlg_edit "prodn.edit_mlg" in
      apply_edit_file prodn_gram prodn_edits;
      let out = open_temp_bin (dir "prodnGrammar") in
      print_in_order out prodn_gram `PRODN !prodn_gram.order StringSet.empty;
      close_out out;
      finish_with_file (dir "prodnGrammar") args.verify
    end
  end

let parse_args () =
  let suffix_regex = Str.regexp ".*\\.\\([a-z]+\\)$" in
  let args =
    List.fold_left (fun args arg ->
        match arg with
        | "-check-cmds" -> { args with check_cmds = true }
        | "-check-tacs" -> { args with check_tacs = true }
        | "-no-warn" -> show_warn := false; { args with show_warn = true }
        | "-short" -> { args with fullGrammar = true }
        | "-verbose" -> { args with verbose = true }
        | "-verify" -> { args with verify = true }
        | arg when Str.string_match suffix_regex arg 0 ->
            (match Str.matched_group 1 arg with
            | "mlg" -> { args with mlg_files = (arg :: args.mlg_files) }
            | "rst" -> { args with rst_files = (arg :: args.rst_files) }
            | _ -> error "Unknown command line argument '%s'\n" arg; args)
        | arg -> error "Unknown command line argument '%s'\n" arg; args)
      default_args (List.tl (Array.to_list Sys.argv)) in
  { args with mlg_files = (List.rev args.mlg_files); rst_files = (List.rev args.rst_files)}

let () =
  (*try*)
    Printexc.record_backtrace true;
    let args = parse_args () in
    if !exit_code = 0 then begin
      process_grammar args
    end;
    exit !exit_code
  (*with _ -> Printexc.print_backtrace stdout; exit 1*)
