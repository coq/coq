(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
  no_update: bool;
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
  no_update = false;
  show_warn = true;
  verbose = false;
  verify = false;
}

let start_symbols = ["document"]
let tokens = [ "bullet"; "string"; "unicode_id_part"; "unicode_letter" ]

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
  let g_add_after g ?(update=true) ins_after nt prods =
    if (not update) && NTMap.mem nt !g.map then raise Duplicate;  (* don't update the nt if it's already present *)
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

  let g_add_prod_after g ins_after nt prod =
    let prods = try NTMap.find nt !g.map with Not_found -> [] in
    if prods <> [] then
      g_update_prods g nt (prods @ [prod])
    else
      g_add_after g ~update:true ins_after nt [prod]

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

(* identify special chars that don't get a trailing space in output *)
let omit_space s = List.mem s ["?"; "."; "#"]

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
    | Sprod sym_list_list ->
      sprintf "[ %s ]" (String.concat " " (List.mapi (fun i r ->
          let prod = (prod_to_str r) in
          let sep = if i = 0 then "" else
              if prod <> "" then "| " else "|" in
          sprintf "%s%s" sep prod)
        sym_list_list))
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
  | Sterm s :: Snterm "ident" :: tl when omit_space s && plist ->
    (sprintf "%s`ident`" s) :: (prod_to_str_r plist tl)
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
  | Sterm s ->
    let s = match s with
            | "|}" -> "%|%}"
            | "{|" -> "%{%|"
            | "`{" -> "`%{"
            | "@{" -> "@%{"
            | "{"
            | "}"
            | "|" -> "%" ^ s
            | _ -> s
    in
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

and prod_to_prodn_r prod =
  match prod with
  | Sterm s :: Snterm "ident" :: tl when omit_space s ->
    (sprintf "%s@ident" s) :: (prod_to_prodn_r tl)
  | p :: tl -> (output_prodn p) :: (prod_to_prodn_r tl)
  | [] -> []

and prod_to_prodn prod = String.concat " " (prod_to_prodn_r prod)

let pr_prods nt prods = (* duplicative *)
  Printf.printf "%s: [\n" nt;
  List.iter (fun prod ->
      let str = prod_to_str ~plist:false prod in
      let pfx = if str = "" then "|" else "| " in
      Printf.printf "%s%s\n" pfx str)
    prods;
  Printf.printf "]\n\n"

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
            fprintf out "\n%s:\n%s " nt nt;
            List.iteri (fun i prod ->
                let str = prod_to_prodn prod in
                let op = if i = 0 then "::=" else "+=" in
                fprintf out "%s %s\n" op str)
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

(*todo: couldn't get linker to see Stats*)
(*open Stats*)
type pid = {
  file : string;
  char : int;
}

let pid_compare pid1 pid2 =
  let scmp = String.compare pid1.file pid2.file in
  if scmp <> 0 then scmp else compare pid1.char pid2.char

module PidOrd = struct type t = pid let compare = pid_compare end
module ProdMap = Map.Make(PidOrd)

let prod_map = ref ProdMap.empty

let add_to_prod_map loc nt prod =
  let open Lexing in
  let loc = loc.loc_start in
  let key = { file=loc.pos_fname; char=loc.pos_cnum } in
  let value = Printf.sprintf "%s:  %s" nt (prod_to_str prod) in
  prod_map := ProdMap.add key value !prod_map;
  key

type extid = {
  plugin : string;
  etype : string;  (* use defined const *)
  ename : string;
  num : int;
}

let extid_compare extid1 extid2 =
  let scmp = String.compare extid1.plugin extid2.plugin in
  if scmp <> 0 then scmp else begin
    let scmp = String.compare extid1.etype extid2.etype in
    if scmp <> 0 then scmp else begin
      let scmp = String.compare extid1.ename extid2.ename in
      if scmp <> 0 then scmp else compare extid1.num extid2.num
    end
  end

module ExtOrd = struct type t = extid let compare = extid_compare end
module ExtMap = Map.Make(ExtOrd)

let ext_map = ref ExtMap.empty

let add_to_ext_map plugin etype ename num loc prod_map_key = (* todo: remove loc? *)
(*  let open Lexing in*)
(*  Printf.printf "ext: '%s' %s %s %d line %d\n" !plugin etype ename num loc.loc_start.pos_lnum;*)
  let (as_is, no_plugin_name) = match etype with
  | "C" -> false, true
  | "T" -> true, num = 0
  | _ -> true, false
  in
  if as_is then
    ext_map := ExtMap.add { plugin=(!plugin); etype; ename; num } prod_map_key !ext_map;
  if no_plugin_name then
    ext_map := ExtMap.add { plugin=""; etype; ename; num } prod_map_key !ext_map

let dir s = "doc/tools/docgram/" ^ s

let save_prod_maps () =
  let outch = open_out_bin (dir "prodmap") in
  Marshal.to_channel outch !prod_map [];
  Marshal.to_channel outch !ext_map [];
  close_out outch

let keywords = ref StringSet.empty

let rec cvt_gram_sym nt = function
  | GSymbString s -> Sterm s
  | GSymbQualid (s, level) ->
    Snterm (match level with
           | Some str -> s ^ str
           | None -> s)
  | GSymbParen l -> Sparen (cvt_gram_sym_list nt l)
  | GSymbProd ll ->
    let cvt = List.map (fun p ->
        let loc = p.gprod_body.loc.loc_start in
        let open Lexing in
        let label = Printf.sprintf "(%s : %d)" nt loc.pos_lnum in
        cvt_gram_prod label p)
      ll in
    (match cvt with
    | (Snterm x :: []) :: [] -> Snterm x
    | (Sterm x :: []) :: []  -> Sterm x
    | _ -> Sprod cvt)

and cvt_gram_sym_list nt l =
  let get_sym = function
    | GSymbQualid (s, level) -> s
    | _ -> ""
  in

  match l with
  | GSymbQualid ("LIST0", _) :: s :: GSymbQualid ("SEP", _) :: sep :: tl ->
    Slist0sep (cvt_gram_sym nt s, cvt_gram_sym nt sep) :: cvt_gram_sym_list nt tl
  | GSymbQualid ("LIST1", _) :: s :: GSymbQualid ("SEP", _) :: sep :: tl ->
    Slist1sep (cvt_gram_sym nt s, cvt_gram_sym nt sep) :: cvt_gram_sym_list nt tl
  | GSymbQualid ("LIST0", _) :: s :: tl ->
    Slist0 (cvt_gram_sym nt s) :: cvt_gram_sym_list nt tl
  | GSymbQualid ("LIST1", _) :: s :: tl ->
    Slist1 (cvt_gram_sym nt s) :: cvt_gram_sym_list nt tl
  | GSymbQualid ("OPT", _) :: s :: tl ->
    Sopt (cvt_gram_sym nt s) :: cvt_gram_sym_list nt tl
  | GSymbQualid ("IDENT", _) :: s2 :: tl when get_sym s2 = "" ->
    cvt_gram_sym nt s2 :: cvt_gram_sym_list nt tl
  | GSymbQualid ("ADD_OPT", _) :: tl ->
    (Sedit "ADD_OPT") :: cvt_gram_sym_list nt tl
  | GSymbQualid ("NOTE", _) :: GSymbQualid (s2, l) :: tl ->
    (Sedit2 ("NOTE", s2)) :: cvt_gram_sym_list nt tl
  | GSymbQualid ("USE_NT", _) :: GSymbQualid (s2, l) :: tl ->
    (Sedit2 ("USE_NT", s2)) :: cvt_gram_sym_list nt tl
  | GSymbString s :: tl ->
    (* todo: not seeing "(bfs)" here for some reason *)
    keywords := StringSet.add s !keywords;
    cvt_gram_sym nt (GSymbString s) :: cvt_gram_sym_list nt tl
  | hd :: tl ->
    cvt_gram_sym nt hd :: cvt_gram_sym_list nt tl
  | [] -> []

and cvt_gram_prod nt p =
  let rv = List.concat (List.map (fun x -> let _, gs = x in cvt_gram_sym_list nt gs)  p.gprod_symbs) in
  ignore @@ add_to_prod_map p.gprod_body.loc nt rv;
  rv


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
        | (Sprod psymll, Sprod symll) ->
          if List.compare_lengths psymll symll != 0 then false
          else
            List.fold_left (&&) true (List.map2 ematchr psymll symll)
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
  let locals = ref StringSet.empty in
  let plugin_name = ref "" in
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
              if not (List.mem nt grammar_ext.gramext_globals) then
                locals := StringSet.add nt !locals;
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
              let cvted = List.map (fun p -> cvt_gram_prod cur_level p) rule.grule_prods in
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

    | DeclarePlugin plugin ->
      plugin_name := plugin
    | VernacExt vernac_ext ->
      let node = match vernac_ext.vernacext_entry with
      | None -> "command"
      | Some c -> String.trim c.code
      in
      add_prods node
        (List.mapi (fun n r ->
            let rv = cvt_ext r.vernac_toks in
            add_to_ext_map plugin_name "C" vernac_ext.vernacext_name n r.vernac_body.loc
              (add_to_prod_map r.vernac_body.loc node rv);
            rv)
           vernac_ext.vernacext_rules)
    | VernacArgumentExt vernac_argument_ext ->
      add_prods vernac_argument_ext.vernacargext_name
        (List.mapi (fun n r ->
            let rv = cvt_ext r.tac_toks in
            add_to_ext_map plugin_name "A" vernac_argument_ext.vernacargext_name n r.tac_body.loc
              (add_to_prod_map r.tac_body.loc vernac_argument_ext.vernacargext_name rv);
            rv)
          vernac_argument_ext.vernacargext_rules)
    | TacticExt tactic_ext ->
      add_prods "simple_tactic"
        (List.mapi (fun n r ->
            let rv = cvt_ext r.tac_toks in
            add_to_ext_map plugin_name "T" tactic_ext.tacext_name n r.tac_body.loc
              (add_to_prod_map r.tac_body.loc "simple_tactic" rv);
            rv)
          tactic_ext.tacext_rules)
    | ArgumentExt argument_ext ->
      add_prods argument_ext.argext_name
        (List.mapi (fun n r ->
            let rv = cvt_ext r.tac_toks in
            ignore @@ add_to_prod_map r.tac_body.loc argument_ext.argext_name rv;
            rv)
          argument_ext.argext_rules)
    | _ -> ()
  in

  List.iter prod_loop ast;
  List.rev !res, !locals

let read_mlg_edit file =
  let fdir = dir file in
  let level_renames = ref StringMap.empty in (* ignored *)
  let symdef_map = ref StringMap.empty in (* ignored *)
  let prods, _ = read_mlg true (parse_file fdir) fdir level_renames symdef_map in
  prods

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
    let rules, locals = read_mlg false (parse_file file) file level_renames symdef_map in
    let numprods = List.fold_left (fun num rule ->
        let nt, prods = rule in
        if NTMap.mem nt !g.map && (StringSet.mem nt locals) &&
            StringSet.cardinal (StringSet.of_list (StringMap.find nt !symdef_map)) > 1 then
          warn "%s: local nonterminal '%s' already defined\n" file nt;
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


 (* get the nt's in the production, preserving order, don't worry about dups *)
 let nts_in_prod prod =
  let rec traverse = function
  | Sterm s -> []
  | Snterm s -> if List.mem s tokens then [] else [s]
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

let get_refdef_nts g =
  let rec get_nts_r refd defd bindings =
    match bindings with
    | [] -> refd, defd
    | (nt, prods) :: tl ->
      get_nts_r (List.fold_left (fun res prod ->
                  StringSet.union res (StringSet.of_list (nts_in_prod prod)))
                refd prods)
        (StringSet.add nt defd) tl
   in
   let toks = StringSet.of_list tokens in
   get_nts_r toks toks (NTMap.bindings !g.map)


(*** global editing ops ***)

let create_edit_map g op edits =
  let rec aux edits map =
    match edits with
    | [] -> map
    | edit :: tl ->
      let (key, binding) = edit in
      let all_nts_ref, all_nts_def = get_refdef_nts g in
      (match op with
      (* todo: messages should tell you which edit file causes the error *)
      | "SPLICE" ->
        if not (StringSet.mem key all_nts_def) then
          error "Undefined nt `%s` in SPLICE\n" key
      | "DELETE" ->
        if not (StringSet.mem key all_nts_ref || (StringSet.mem key all_nts_def)) then
          error "Unused/undefined nt `%s` in DELETE\n" key;
      | "RENAME" ->
        if not (StringSet.mem key all_nts_ref || (StringSet.mem key all_nts_def)) then
          error "Unused/undefined  nt `%s` in RENAME\n" key;
(*      todo: could not get the following codeto type check
        (match binding with
        | _ :: Snterm new_nt :: _ ->
          if not (StringSet.mem new_nt all_nts_ref) then
            error "nt `%s` already exists in %s\n" new_nt op
        | _ -> ())
*)
      | _ -> ());
      aux tl (StringMap.add key binding map)
  in
  aux edits StringMap.empty

let remove_Sedit2 p =
  List.filter (fun sym -> match sym with | Sedit2 _ -> false | _ -> true) p

(* don't deal with Sedit, Sedit2 yet (ever?) *)
let rec pmatch fullprod fullpat repl =
  let map_prod prod = List.concat (List.map (fun s -> pmatch [s] fullpat repl) prod) in
  let pmatch_wrap sym =
    let r = pmatch [sym] fullpat repl in
    match r with
    | a :: b :: tl -> Sparen r
    | [a] -> a
    | x -> error "pmatch: should not happen"; Sterm "??"
  in

  let symmatch_r s =
  let res = match s with
  | Slist1 sym -> Slist1 (pmatch_wrap sym)
  | Slist1sep (sym, sep) -> Slist1sep (pmatch_wrap sym, sep)
  | Slist0 sym -> Slist0 (pmatch_wrap sym)
  | Slist0sep (sym, sep) -> Slist0sep (pmatch_wrap sym, sep)
  | Sopt sym -> Sopt (pmatch_wrap sym)
  | Sparen prod -> Sparen (map_prod prod)
  | Sprod prods -> Sprod (List.map map_prod prods)
  | sym -> sym
  in
(*  Printf.printf "symmatch of %s gives %s\n" (prod_to_str [s]) (prod_to_str [res]);*)
  res
  in

  let rec pmatch_r prod pat match_start start_res res =
(*    Printf.printf "pmatch_r: prod = %s;  pat = %s;  res = %s\n" (prod_to_str prod) (prod_to_str pat) (prod_to_str res);*)
    match prod, pat with
    | _, [] ->
      let new_res = (List.rev repl) @ res in
      pmatch_r prod fullpat prod new_res new_res (* subst and continue *)
    | [], _ -> (List.rev ((List.rev match_start) @ res)) (* leftover partial match *)
    | hdprod :: tlprod, hdpat :: tlpat ->
      if hdprod = hdpat then
        pmatch_r tlprod tlpat match_start start_res res
      else
        (* match from the next starting position *)
        match match_start with
        | hd :: tl ->
          let new_res = (symmatch_r hd) :: start_res in
          pmatch_r tl fullpat tl new_res new_res
        | [] -> List.rev res (* done *)
  in
  pmatch_r fullprod fullpat fullprod [] []

(* global replace of production substrings, rhs only *)
let global_repl g pat repl =
  List.iter (fun nt ->
      g_update_prods g nt (List.map (fun prod -> pmatch prod pat repl) (NTMap.find nt !g.map))
  ) !g.order

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
            | [p] -> List.rev (remove_Sedit2 p)
            | _ -> [Sprod (List.map remove_Sedit2 splice_prods)]
          with Not_found -> error "Missing nt '%s' for splice\n" nt; [Snterm nt]
        end
      | _ -> [Snterm binding]
    with Not_found -> [sym0]
  in
  let maybe_wrap syms =
    match syms with
    | s :: [] -> List.hd syms
    | s -> Sparen (List.rev syms)
  in

  let rec edit_symbol sym0 =
    match sym0 with
      | Sterm s -> [sym0]
      | Snterm s -> edit_nt edit_map sym0 s
      | Slist1 sym -> [Slist1 (maybe_wrap (edit_symbol sym))]
      (* you'll get a run-time failure deleting a SEP symbol *)
      | Slist1sep (sym, sep) -> [Slist1sep (maybe_wrap (edit_symbol sym), (List.hd (edit_symbol sep)))]
      | Slist0 sym -> [Slist0 (maybe_wrap (edit_symbol sym))]
      | Slist0sep (sym, sep) -> [Slist0sep (maybe_wrap (edit_symbol sym), (List.hd (edit_symbol sep)))]
      | Sopt sym -> [Sopt (maybe_wrap (edit_symbol sym))]
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

(* todo: create a better splice routine *)
let apply_splice g splice_map =
  List.iter (fun b ->
      let (nt0, prods0) = b in
      let rec splice_loop nt prods cnt =
        let max_cnt = 10 in
        let (nt', prods') = edit_rule g splice_map nt prods in
        if cnt > max_cnt then
          error "Splice for '%s' not done after %d iterations\n" nt0 max_cnt;
        if nt' = nt && prods' = prods then
          (nt', prods')
        else
          splice_loop nt' prods' (cnt+1)
      in
      let (nt', prods') = splice_loop nt0 prods0 0 in
      g_update_prods g nt' prods')
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
      error "Can't find '%s' in edit for '%s'\n" (prod_to_str edit) nt;
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
    let map = create_edit_map g op (aux eprods []) in
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

let report_undef_nts g prod rec_nt =
  let nts = nts_in_prod prod in
  List.iter (fun nt ->
      if not (NTMap.mem nt !g.map) && not (List.mem nt tokens) && nt <> rec_nt then
        error "Undefined nonterminal `%s` in edit: %s\n" nt (prod_to_str prod))
    nts

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
            if not (NTMap.mem nt !g.map) then
              error "DELETENT for undefined nonterminal `%s`\n" nt;
            g_remove g nt;
            aux tl prods false
          | (Snterm "MOVETO" :: Snterm nt2 :: oprod) :: tl ->
            g_add_prod_after g (Some nt) nt2 oprod;
            let prods' = (try
              let posn = find_first oprod prods nt in
              let prods = if List.mem [Snterm nt2] prods then prods
                else insert_after posn [[Snterm nt2]] prods (* insert new prod *)
              in
              remove_prod oprod prods nt      (* remove orig prod *)
              with Not_found -> prods)
            in
            aux tl prods' add_nt
          | (Snterm "OPTINREF" :: _) :: tl ->
            if not (has_match [] prods) then
              error "OPTINREF but no empty production for %s\n" nt;
            global_repl g [(Snterm nt)] [(Sopt (Snterm nt))];
            aux tl (remove_prod [] prods nt) add_nt
          | (Snterm "INSERTALL" :: syms) :: tl ->
            aux tl (List.map (fun p -> syms @ p) prods) add_nt
          | (Snterm "PRINT" :: _) :: tl ->
            pr_prods nt prods;
            aux tl prods add_nt
          | (Snterm "EDIT" :: oprod) :: tl ->
            aux tl (edit_single_prod g oprod prods nt) add_nt
          | (Snterm "REPLACE" :: oprod) :: (Snterm "WITH" :: rprod) :: tl ->
            report_undef_nts g rprod "";
            (* todo: check result not already present *)
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
          (* todo: check for unmatched editing keywords here *)
          | prod :: tl ->
            (* add a production *)
            if has_match prod prods then
              error "Duplicate production '%s' for %s\n" (prod_to_str prod) nt;
            report_undef_nts g prod nt;
            aux tl (prods @ [prod]) add_nt
        in
        let prods, add_nt =
          aux eprod (try NTMap.find nt !g.map with Not_found -> []) true in
        if add_nt then
          g_maybe_add g nt prods
      end)
    edits


(*** main routines ***)

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
let index_of str list =
  let rec index_of_r str list index =
    match list with
    | [] -> None
    | hd :: list ->
      if hd = str then Some index
      else index_of_r str list (index+1)
  in
  index_of_r str list 0

exception IsNone

(* todo: raise exception for bad n? *)
let rec nthcdr n list = if n <= 0 then list else nthcdr (n-1) (List.tl list)

let pfx n list =
  let rec pfx_r n res = function
    | item :: tl -> if n < 0 then res else pfx_r (n-1) (item :: res) tl
    | [] -> res
  in
  List.rev (pfx_r n [] list)

(* todo: adjust Makefile to include Option.ml/mli *)
let get_opt = function
  | Some y -> y
  | _ -> raise IsNone

let get_range g start end_ =
  let starti, endi = get_opt (index_of start !g.order), get_opt (index_of end_ !g.order) in
  pfx (endi - starti) (nthcdr starti !g.order)

let get_rangeset g start end_ = StringSet.of_list (get_range g start end_)

let print_dominated g =
  let info nt rangeset exclude =
    let reachable = StringSet.of_list (nt_closure g nt exclude) in
    let unreachable = StringSet.of_list (nt_closure g (List.hd start_symbols) (nt::exclude)) in
    let dominated = StringSet.diff reachable unreachable in
    Printf.printf "For %s, 'attribute' is: reachable = %b, unreachable = %b, dominated = %b\n" nt
        (StringSet.mem "attribute" reachable)
        (StringSet.mem "attribute" unreachable)
        (StringSet.mem "attribute" dominated);
    Printf.printf "  rangeset = %b excluded = %b\n"
        (StringSet.mem "attribute" rangeset)
        (List.mem "attribute" exclude);
    reachable, dominated
  in
  let pr3 nt rangeset reachable dominated =
    let missing = StringSet.diff dominated rangeset in
    if not (StringSet.is_empty missing) then begin
      Printf.printf "\nMissing in range for '%s':\n" nt;
      StringSet.iter (fun nt -> Printf.printf "  %s\n" nt) missing
    end;

    let unneeded = StringSet.diff rangeset reachable in
    if not (StringSet.is_empty unneeded) then begin
      Printf.printf "\nUnneeded in range for '%s':\n" nt;
      StringSet.iter (fun nt -> Printf.printf "  %s\n" nt) unneeded
    end;
  in
  let pr2 nt rangeset exclude =
    let reachable, dominated = info nt rangeset exclude in
    pr3 nt rangeset reachable dominated
  in
  let pr nt end_ = pr2 nt (get_rangeset g nt end_) [] in

  let ssr_ltac = ["ssr_first_else"; "ssrmmod"; "ssrdotac"; "ssrortacarg";
      "ssrparentacarg"] in
  let ssr_tac = ["ssrintrosarg"; "ssrhintarg"; "ssrtclarg"; "ssrseqarg"; "ssrmovearg";
      "ssrrpat"; "ssrclauses"; "ssrcasearg"; "ssrarg"; "ssrapplyarg"; "ssrexactarg";
      "ssrcongrarg"; "ssrterm"; "ssrrwargs"; "ssrunlockargs"; "ssrfixfwd"; "ssrcofixfwd";
      "ssrfwdid"; "ssrposefwd"; "ssrsetfwd"; "ssrdgens"; "ssrhavefwdwbinders"; "ssrhpats_nobs";
      "ssrhavefwd"; "ssrsufffwd"; "ssrwlogfwd"; "ssrhint"; "ssrclear"; "ssr_idcomma";
      "ssrrwarg"; "ssrintros_ne"; "ssrhint3arg" ] @ ssr_ltac in
  let ssr_cmd = ["ssr_modlocs"; "ssr_search_arg"; "ssrhintref"; "ssrhintref_list";
      "ssrviewpos"; "ssrviewposspc"] in
  let ltac = ["ltac_expr"; "ltac_expr0"; "ltac_expr1"; "ltac_expr2"; "ltac_expr3"] in
  let term = ["term"; "term0"; "term1"; "term10"; "term100"; "term9";
      "pattern"; "pattern0"; "pattern1"; "pattern10"] in

  pr "term" "constr";

  let ltac_rangeset = List.fold_left StringSet.union StringSet.empty
                            [(get_rangeset g "ltac_expr" "tactic_atom");
                            (get_rangeset g "toplevel_selector" "range_selector");
                            (get_rangeset g "ltac_match_term" "match_pattern");
                            (get_rangeset g "ltac_match_goal" "match_pattern_opt")] in
  pr2 "ltac_expr" ltac_rangeset ("simple_tactic" :: ssr_tac);

  let dec_vern_rangeset = get_rangeset g "decorated_vernac" "opt_coercion" in
  let dev_vern_excl =
      ["gallina_ext"; "command"; "tactic_mode"; "syntax"; "command_entry"] @ term @ ltac @ ssr_tac in
  pr2 "decorated_vernac" dec_vern_rangeset dev_vern_excl;

  let simp_tac_range = get_rangeset g "simple_tactic" "hypident_occ_list_comma" in
  let simp_tac_excl = ltac @ ssr_tac in
  pr2 "simple_tactic" simp_tac_range simp_tac_excl;

  let cmd_range = get_rangeset g "command" "int_or_id_list_opt" in
  let cmd_excl = ssr_tac @ ssr_cmd in
  pr2 "command" cmd_range cmd_excl;

  let syn_range = get_rangeset g "syntax" "constr_as_binder_kind" in
  let syn_excl = ssr_tac @ ssr_cmd in
  pr2 "syntax" syn_range syn_excl;

  let gext_range = get_rangeset g "gallina_ext" "Structure_opt" in
  let gext_excl = ssr_tac @ ssr_cmd in
  pr2 "gallina_ext" gext_range gext_excl;

  let qry_range = get_rangeset g "query_command" "searchabout_query_list" in
  let qry_excl = ssr_tac @ ssr_cmd in
  pr2 "query_command" qry_range qry_excl

  (* todo: tactic_mode *)

let check_range_consistency g start end_ =
  let defined_list = get_range g start end_ in
  let defined = StringSet.of_list defined_list in
  let referenced = List.fold_left (fun set nt ->
      let prods = NTMap.find nt !g.map in
      let refs = List.concat (List.map nts_in_prod prods) in
      StringSet.union set (StringSet.of_list refs))
    StringSet.empty defined_list
  in
  let undef = StringSet.diff referenced defined in
  let unused = StringSet.diff defined referenced in
  if StringSet.cardinal unused > 0 || (StringSet.cardinal undef > 0) then begin
    Printf.printf "\nFor range '%s' to '%s':\n  External reference:" start end_;
    StringSet.iter (fun nt -> Printf.printf " %s" nt) undef;
    Printf.printf "\n";
    if StringSet.cardinal unused > 0 then begin
      Printf.printf "  Unreferenced:";
      StringSet.iter (fun nt -> Printf.printf " %s" nt) unused;
      Printf.printf "\n"
    end
  end

(* print info on symbols with a single production of a single nonterminal *)
let check_singletons g =
  NTMap.iter (fun nt prods ->
      if List.length prods = 1 then
        if List.length (remove_Sedit2 (List.hd prods)) = 1 then
          warn "Singleton non-terminal, maybe SPLICE?: %s\n" nt
        else
          (*warn "Single production, maybe SPLICE?: %s\n" nt*) ())
    !g.map

let report_bad_nts g file =
  let all_nts_ref, all_nts_def = get_refdef_nts g in
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


let finish_with_file old_file args =
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

  let temp_file = (old_file ^ ".new") in
  if !exit_code <> 0 then
    Sys.remove temp_file
  else if args.verify then begin
    if not (files_eq old_file temp_file) then
      error "%s is not current\n" old_file;
    Sys.remove temp_file
  end else if not args.no_update then
    Sys.rename temp_file old_file

let open_temp_bin file =
  open_out_bin (sprintf "%s.new" file)

let match_cmd_regex = Str.regexp "[a-zA-Z0-9_ ]+"
let match_subscripts = Str.regexp "__[a-zA-Z0-9]+"

let find_longest_match prods str =
  let get_pfx str = String.trim (if Str.string_match match_cmd_regex str 0 then Str.matched_string str else "") in
  let prods = StringSet.fold (fun a lst -> a :: lst) prods [] in  (* todo: wasteful! *)
  let common_prefix_len s1 s2 =
    let limit = min (String.length s1) (String.length s2) in
    let rec aux off =
      if off = limit then off
      else if s1.[off] = s2.[off] then aux (succ off)
      else off
    in
    aux 0
  in
  let remove_subscrs str = Str.global_replace match_subscripts "" str in

  let slen = String.length str in
  let str_pfx = get_pfx str in
  let no_subscrs = remove_subscrs str in
  let has_subscrs = no_subscrs <> str in
  let rec longest best multi best_len prods =
    match prods with
    | [] -> best, multi, best_len
    | prod :: tl ->
      let pstr = String.trim prod in  (* todo: should be pretrimmed *)
      let clen = common_prefix_len str pstr in
      if has_subscrs && no_subscrs = pstr then
        str, false, clen (* exact match ignoring subscripts *)
      else if pstr = str then
        pstr, false, clen  (* exact match of full line *)
      else if str_pfx = "" || str_pfx <> get_pfx pstr then
        longest best multi best_len tl  (* prefixes don't match *)
      else if clen = slen && slen = String.length pstr then
        pstr, false, clen  (* exact match on prefix *)
      else if clen > best_len then
        longest pstr false clen tl  (* better match *)
      else if clen = best_len then
        longest best true best_len tl  (* 2nd match with same length *)
      else
        longest best multi best_len tl  (* worse match *)
  in
  let mtch, multi, _ = longest "" false 0 prods in
  if has_subscrs && mtch <> str then
    "", multi, mtch (* no match for subscripted entry *)
  else
    mtch, multi, ""

type seen = {
  nts: (string * int) NTMap.t;
  tacs: (string * int) NTMap.t;
  tacvs: (string * int) NTMap.t;
  cmds: (string * int) NTMap.t;
  cmdvs: (string * int) NTMap.t;
}

let process_rst g file args seen tac_prods cmd_prods =
  let old_rst = open_in file in
  let new_rst = open_temp_bin file in
  let linenum = ref 0 in
  let dir_regex = Str.regexp "^\\([ \t]*\\)\\.\\.[ \t]*\\([a-zA-Z0-9:]* *\\)\\(.*\\)" in
  let contin_regex = Str.regexp "^\\([ \t]*\\)\\(.*\\)" in
  let ip_args_regex = Str.regexp "^[ \t]*\\([a-zA-Z0-9_\\.]*\\)[ \t]*\\([a-zA-Z0-9_\\.]*\\)" in
  let blank_regex = Str.regexp "^[ \t]*$" in
  let end_prodlist_regex = Str.regexp "^[ \t]*$" in
  let getline () =
    let line = input_line old_rst in
    incr linenum;
    line
  in
  (* todo: maybe pass end_index? *)
  let output_insertprodn start_index end_ indent =
    let rec copy_prods list =
      match list with
      | [] -> ()
      | nt :: tl ->
        (try
          let (prev_file, prev_linenum) = NTMap.find nt !seen.nts in
          warn "%s line %d: '%s' already included at %s line %d\n"
              file !linenum nt prev_file prev_linenum;
        with Not_found ->
          seen := { !seen with nts = (NTMap.add nt (file, !linenum) !seen.nts)} );
        let prods = NTMap.find nt !g.map in
        List.iteri (fun i prod ->
            let rhs = String.trim (prod_to_prodn prod) in
            let sep = if i = 0 then " ::=" else "|" in
            fprintf new_rst "%s   %s%s %s\n" indent (if i = 0 then nt else "") sep rhs)
          prods;
        if nt <> end_ then copy_prods tl
    in
    copy_prods (nthcdr start_index !g.order)
  in

  let process_insertprodn line rhs =
    if not (Str.string_match ip_args_regex rhs 0) then
      error "%s line %d: bad arguments '%s' for 'insertprodn'\n" file !linenum rhs
    else begin
      let start = Str.matched_group 1 rhs in
      let end_ = Str.matched_group 2 rhs in
      let start_index = index_of start !g.order in
      let end_index = index_of end_ !g.order in
      if start_index = None then
        error "%s line %d: '%s' is undefined in insertprodn\n" file !linenum start;
      if end_index = None then
        error "%s line %d: '%s' is undefined in insertprodn\n" file !linenum end_;
(*      if start_index <> None && end_index <> None then*)
(*        check_range_consistency g start end_;*)
      match start_index, end_index with
      | Some start_index, Some end_index ->
        if start_index > end_index then
          error "%s line %d: '%s' must appear before '%s' in orderedGrammar\n" file !linenum start end_
        else begin
          try
            let line2 = getline() in
            if not (Str.string_match blank_regex line2 0) then
              error "%s line %d: expecting a blank line after 'insertprodn'\n" file !linenum
            else begin
              let line3 = getline() in
              if not (Str.string_match dir_regex line3 0) || (String.trim (Str.matched_group 2 line3)) <> "prodn::" then
                error "%s line %d: expecting '.. prodn::' after 'insertprodn'\n" file !linenum
              else begin
                let indent = Str.matched_group 1 line3 in
                let rec skip_to_end () =
                  let endline = getline() in
                  if Str.string_match end_prodlist_regex endline 0 then begin
                    fprintf new_rst "%s\n\n%s\n" line line3;
                    output_insertprodn start_index end_ indent;
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

(*  let skip_files = ["doc/sphinx/proof-engine/ltac.rst"; "doc/sphinx/proof-engine/ltac2.rst";*)
(*    "doc/sphinx/proof-engine/ssreflect-proof-language.rst"]*)
(*  in*)

  let cmd_replace_files = [
    "doc/sphinx/language/core/records.rst";
    "doc/sphinx/language/core/sections.rst";
    "doc/sphinx/language/extensions/implicit-arguments.rst";
    "doc/sphinx/language/extensions/arguments-command.rst";
    "doc/sphinx/language/using/libraries/funind.rst";

    "doc/sphinx/language/gallina-specification-language.rst";
    "doc/sphinx/language/gallina-extensions.rst";
    "doc/sphinx/proof-engine/vernacular-commands.rst";
    "doc/sphinx/user-extensions/syntax-extensions.rst"
  ]
  in

  let save_n_get_more direc pfx first_rhs seen_map prods =
    let replace rhs prods =
      if StringSet.is_empty prods || not (List.mem file cmd_replace_files) then
        rhs (* no change *)
      else
        let mtch, multi, best = find_longest_match prods rhs in
(*        Printf.printf "mtch = '%s'  rhs = '%s'\n" mtch rhs;*)
        if mtch = rhs then
          rhs (* no change *)
        else if mtch = "" then begin
          warn "%s line %d: NO MATCH `%s`\n" file !linenum rhs;
          if best <> "" then
            warn "%s line %d: BEST `%s`\n" file !linenum best;
          rhs
        end else if multi then begin
          warn "%s line %d: MULTIMATCH `%s`\n" file !linenum rhs;
          rhs
        end else
          mtch (* update cmd/tacn *)
    in
    let map = ref seen_map in
    if NTMap.mem first_rhs !map then
      warn "%s line %d: Repeated %s: '%s'\n" file !linenum direc first_rhs;
(*    if not (StringSet.mem rhs seen_map) then*)
(*      warn "%s line %d: Unknown tactic: '%s'\n" file !linenum rhs;*)

    fprintf new_rst "%s%s\n" pfx (replace first_rhs prods);

    map := NTMap.add first_rhs (file, !linenum) !map;
    while
      let nextline = getline() in
      ignore (Str.string_match contin_regex nextline 0);
      let indent = Str.matched_group 1 nextline in
      let rhs = Str.matched_group 2 nextline in
      let replaceable = rhs <> "" && rhs.[0] <> ':' in
      let upd_rhs = if replaceable then (replace rhs prods) else rhs in
      fprintf new_rst "%s%s\n" indent upd_rhs;
      if replaceable then begin
        map := NTMap.add rhs (file, !linenum) !map
      end;
      rhs <> ""
    do
      ()
    done;
    !map
  in

  try
    while true do
      let line = getline() in
      if Str.string_match dir_regex line 0 then begin
        let dir = String.trim (Str.matched_group 2 line) in
        let rhs = Str.matched_group 3 line in
        let pfx = String.sub line 0 (Str.group_end 2) in
        match dir with
        | "prodn::" ->
          if rhs = "coq" then
            warn "%s line %d: Missing 'insertprodn' before 'prodn:: coq'\n" file !linenum;
          fprintf new_rst "%s\n" line;
        | "tacn::" when args.check_tacs ->
          seen := { !seen with tacs = save_n_get_more "tacn" pfx rhs !seen.tacs tac_prods }
        | "tacv::" when args.check_tacs ->
          seen := { !seen with tacvs = save_n_get_more "tacv" pfx rhs !seen.tacvs StringSet.empty }
        | "cmd::" when args.check_cmds ->
          seen := { !seen with cmds = save_n_get_more "cmd" pfx rhs !seen.cmds cmd_prods }
        | "cmdv::" when args.check_cmds ->
          seen := { !seen with cmdvs = save_n_get_more "cmdv" pfx rhs !seen.cmdvs StringSet.empty }
        | "insertprodn" ->
          process_insertprodn line rhs
        | _ -> fprintf new_rst "%s\n" line
      end else
        fprintf new_rst "%s\n" line;
    done
  with End_of_file -> ();
  close_in old_rst;
  close_out new_rst;
  finish_with_file file args

let report_omitted_prods entries seen label split =
  let maybe_warn first last n =
    if first <> "" then begin
      if first <> last then
        warn "%ss '%s' to %s'%s' not included in .rst files (%d)\n" label first split last n
      else
        warn "%s %s not included in .rst files\n" label first;
    end
  in

  let first, last, n, total = List.fold_left (fun missing nt ->
      let first, last, n, total = missing in
      if NTMap.mem nt seen then begin
        maybe_warn first last n;
        "", "", 0, total
      end else
        (if first = "" then nt else first), nt, n + 1, total + 1)
    ("", "", 0, 0) entries in
  maybe_warn first last n;
  if total <> 0 then
    Printf.eprintf "TOTAL %ss not included = %d\n" label total

let process_grammar args =
  let symdef_map = ref StringMap.empty in
  let g = ref { map = NTMap.empty; order = [] } in

  let level_renames = read_mlg_files g args symdef_map in
  if args.verbose then begin
    Printf.printf "Keywords:\n";
    StringSet.iter (fun kw -> Printf.printf "%s " kw) !keywords;
    Printf.printf "\n\n";
  end;
  save_prod_maps ();

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
  finish_with_file (dir "fullGrammar") args;
  if args.verbose then
    print_special_tokens g;

  if not args.fullGrammar then begin
    (* do shared edits *)
    if !exit_code = 0 then begin
      let common_edits = read_mlg_edit "common.edit_mlg" in
      apply_edit_file g common_edits
    end;
    let prodn_gram = ref { map = !g.map; order = !g.order } in  (* todo: should just be 'g', right? *)

    if !exit_code = 0 && not args.verify then begin
      let out = open_temp_bin (dir "editedGrammar") in
      fprintf out "%s\n%s\n\n"
          "(* Edited Coq grammar generated from .mlg files.  Do not edit by hand.  Not compiled into Coq *)"
          "DOC_GRAMMAR";
      print_in_order out g `MLG !g.order StringSet.empty;
      close_out out;
      finish_with_file (dir "editedGrammar") args;
      report_bad_nts g "editedGrammar"
    end;

    if !exit_code = 0 then begin
      let ordered_grammar = read_mlg_edit "orderedGrammar" in
      let out = open_temp_bin (dir "orderedGrammar") in
      fprintf out "%s\n%s\n\n"
          ("(* Defines the order to apply to editedGrammar to get the final grammar for the doc.\n" ^
          "doc_grammar will modify this file to add/remove nonterminals and productions\n" ^
           "to match editedGrammar, which will remove comments.  Not compiled into Coq *)")
          "DOC_GRAMMAR";
      reorder_grammar g ordered_grammar "orderedGrammar";
      print_in_order out g `MLG !g.order StringSet.empty;
      close_out out;
      finish_with_file (dir "orderedGrammar") args;
      check_singletons g
(*      print_dominated g*)
    end;

    let seen = ref { nts=NTMap.empty; tacs=NTMap.empty; tacvs=NTMap.empty; cmds=NTMap.empty; cmdvs=NTMap.empty } in
    let args = { args with no_update = false } in (* always update rsts in place for now *)
    if !exit_code = 0 then begin
      let plist nt =
        let list = (List.map (fun t -> String.trim (prod_to_prodn t))
          (NTMap.find nt !g.map)) in
        list, StringSet.of_list list in
      let tac_list, tac_prods = plist "simple_tactic" in
      let cmd_list, cmd_prods = plist "command" in
      List.iter (fun file -> process_rst g file args seen tac_prods cmd_prods) args.rst_files;
      report_omitted_prods !g.order !seen.nts "Nonterminal" "";
      let out = open_out (dir "updated_rsts") in
      close_out out;
    end;

(*
      if args.check_tacs then
        report_omitted_prods tac_list !seen.tacs "Tactic" "\n                 ";
      if args.check_cmds then
        report_omitted_prods cmd_list !seen.cmds "Command" "\n                  ";
*)

    if !exit_code = 0 then begin
      (* generate report on cmds or tacs *)
      let cmdReport outfile cmdStr cmd_nts cmds cmdvs =
        let rstCmds = StringSet.of_list (List.map (fun b -> let c, _ = b in c) (NTMap.bindings cmds)) in
        let rstCmdvs = StringSet.of_list (List.map (fun b -> let c, _ = b in c) (NTMap.bindings cmdvs)) in
        let gramCmds = List.fold_left (fun set nt ->
            StringSet.union set (StringSet.of_list (List.map (fun p -> String.trim (prod_to_prodn p)) (NTMap.find nt !prodn_gram.map)))
          ) StringSet.empty cmd_nts in
        let allCmds = StringSet.union rstCmdvs (StringSet.union rstCmds gramCmds) in
        let out = open_temp_bin (dir outfile) in
        StringSet.iter (fun c ->
            let rsts = StringSet.mem c rstCmds in
            let gram = StringSet.mem c gramCmds in
            let pfx = match rsts, gram with
            | true, false -> "+"
            | false, true -> "-"
            | false, false -> "?"
            | _, _ -> " "
            in
            let var = if StringSet.mem c rstCmdvs then "v" else " " in
            fprintf out "%s%s  %s\n" pfx var c)
          allCmds;
        close_out out;
        finish_with_file (dir outfile) args;
        Printf.printf "# %s in rsts, gram, total = %d %d %d\n" cmdStr (StringSet.cardinal gramCmds)
          (StringSet.cardinal rstCmds) (StringSet.cardinal allCmds);
      in

      let cmd_nts = ["command"] in
      (* TODO: need to handle tactic_mode (overlaps with query_command) and subprf *)
      cmdReport "prodnCommands" "cmds" cmd_nts !seen.cmds !seen.cmdvs;

      let tac_nts = ["simple_tactic"] in
      cmdReport "prodnTactics" "tacs" tac_nts !seen.tacs !seen.tacvs
    end;

    (* generate prodnGrammar for reference *)
    if !exit_code = 0 && not args.verify then begin
      let out = open_temp_bin (dir "prodnGrammar") in
      print_in_order out prodn_gram `PRODN !prodn_gram.order StringSet.empty;
      close_out out;
      finish_with_file (dir "prodnGrammar") args
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
        | "-no-update" -> { args with no_update = true }
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
