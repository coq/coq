(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
let error_count = ref 0
let show_warn = ref true

let fprintf = Printf.fprintf

let error s =
  exit_code := 1;
  incr error_count;
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
  update: bool;
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
  update = true;
  show_warn = true;
  verbose = false;
  verify = false;
}

let start_symbols = ["document"; "REACHABLE"]
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


(*** Print routines ***)

let sprintf = Printf.sprintf

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
    (* todo: make TAG info output conditional on the set of prods? *)
    | Sedit2 ("TAG", plugin) ->
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

(* Determine if 2 productions are equal ignoring Sedit and Sedit2 *)
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

let get_first m_prod prods =
  let rec find_first_r prods i =
    match prods with
    | [] ->
      raise Not_found
    | prod :: tl ->
      if ematch prod m_prod then i
      else find_first_r tl (i+1)
  in
  find_first_r prods 0

let find_first edit prods nt =
  try
    get_first edit prods
  with Not_found ->
    error "Can't find '%s' in edit for '%s'\n" (prod_to_str edit) nt;
    raise Not_found

module DocGram = struct
  (* these guarantee that order and map have a 1-1 relationship
     on the nt name.  They don't guarantee that nts on rhs of a production
     are defined, nor do they prohibit duplicate productions *)

  exception Duplicate
  exception Invalid

  let g_empty () = ref { map = NTMap.empty; order = [] }

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

let remove_Sedit2 p =
  List.filter (fun sym -> match sym with | Sedit2 _ -> false | _ -> true) p

let rec output_prodn = function
  | Sterm s ->
    let s = match s with
            | "|}" -> "%|%}"
            | "{|" -> "%{%|"
            | "`{" -> "`%{"
            | "@{" -> "@%{"
            | "|-" -> "%|-"
            | "|->" -> "%|->"
            | "||" -> "%||"
            | "|||" -> "%|||"
            | "||||" -> "%||||"
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
  | Sedit2 ("TAG", s2) -> ""
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

and prod_to_prodn prod = String.concat " " (prod_to_prodn_r (remove_Sedit2 prod))

let get_tag file prod =
  List.fold_left (fun rv sym ->
      match sym with
        (* todo: only Ltac2 and SSR for now, outside of their main chapters *)
      | Sedit2 ("TAG", "Ltac2") when file <> "doc/sphinx/proof-engine/ltac2.rst" -> "   Ltac2"
      | Sedit2 ("TAG", "SSR") when file <> "doc/sphinx/proof-engine/ssreflect-proof-language.rst" -> "   SSR"
      | _ -> rv
    ) "" prod

let pr_prods nt prods = (* duplicative *)
  Printf.printf "%s: [\n" nt;
  List.iter (fun prod ->
      let str = prod_to_str ~plist:false prod in
      let pfx = if str = "" then "|" else "| " in
      Printf.printf "%s%s\n" pfx str)
    prods;
  Printf.printf "]\n\n"

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

let keywords = ref StringSet.empty

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
  | GSymbQualid ("TAG", _) :: GSymbQualid (s2, l) :: tl ->
    (Sedit2 ("TAG", s2)) :: cvt_gram_sym_list tl
  | GSymbQualid ("TAG", _) :: GSymbString (s2) :: tl ->
    (Sedit2 ("TAG", s2)) :: cvt_gram_sym_list tl
  | GSymbString s :: tl ->
    (* todo: not seeing "(bfs)" here for some reason *)
    keywords := StringSet.add s !keywords;
    cvt_gram_sym (GSymbString s) :: cvt_gram_sym_list tl
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

let rec edit_SELF nt cur_level next_level right_assoc inner prod =
  let subedit sym = List.hd (edit_SELF nt cur_level next_level right_assoc true [sym]) in
  let len = List.length prod in
  List.mapi (fun i sym ->
    match sym with
    | Sterm _ -> sym

    | Snterm s when s = nt || s = "SELF"->
      if inner then
        Snterm nt (* first level *)
      else if i = 0 then
        Snterm next_level
      else if i + 1 = len then
        (if right_assoc then Snterm cur_level else Snterm next_level)
      else
        Snterm nt
    | Snterm "NEXT" -> Snterm next_level
    | Snterm _ -> sym

    | Slist1 sym -> Slist1 (subedit sym)
    | Slist0 sym -> Slist0 (subedit sym)
    | Slist1sep (sym, sep) -> Slist1sep ((subedit sym), (subedit sep))
    | Slist0sep (sym, sep) -> Slist0sep ((subedit sym), (subedit sep))
    | Sopt sym -> Sopt (subedit sym)
    | Sparen syms -> Sparen (List.map (fun sym -> subedit sym) syms)
    | Sprod prods -> Sprod (List.map (fun prod -> edit_SELF nt cur_level next_level right_assoc true prod) prods)
    | Sedit _ -> sym
    | Sedit2 _ -> sym)
  prod


let autoloaded_mlgs = [ (* productions from other mlgs are marked with TAGs *)
 "parsing/g_constr.mlg";
 "parsing/g_prim.mlg";
 "plugins/btauto/g_btauto.mlg";
 "plugins/cc/g_congruence.mlg";
 "plugins/firstorder/g_ground.mlg";
 "plugins/ltac/coretactics.mlg";
 "plugins/ltac/extraargs.mlg";
 "plugins/ltac/extratactics.mlg";
 "plugins/ltac/g_auto.mlg";
 "plugins/ltac/g_class.mlg";
 "plugins/ltac/g_eqdecide.mlg";
 "plugins/ltac/g_ltac.mlg";
 "plugins/ltac/g_obligations.mlg";
 "plugins/ltac/g_rewrite.mlg";
 "plugins/ltac/g_tactic.mlg";
 "plugins/ltac/profile_ltac_tactics.mlg";
 "plugins/rtauto/g_rtauto.mlg";
 "plugins/syntax/g_number_string.mlg";
 "toplevel/g_toplevel.mlg";
 "vernac/g_proofs.mlg";
 "vernac/g_vernac.mlg";
]


let has_match p prods = List.exists (fun p2 -> ematch p p2) prods

let plugin_regex = Str.regexp "^plugins/\\([a-zA-Z0-9_]+\\)/"
let level_regex = Str.regexp "[a-zA-Z0-9_]*$"

let get_plugin_name file =
  if Str.string_match plugin_regex file 0 then
    let s = Str.matched_group 1 file in
    if List.mem s ["ssr"; "ssrmatching"] then "SSR"
    else s
  else
    ""

let read_mlg g is_edit ast file level_renames symdef_map =
  let res = ref [] in
  let locals = ref StringSet.empty in
  let dup_renames = ref StringMap.empty in
  let add_prods nt prods gramext_globals =
    if not is_edit then
      if NTMap.mem nt !g.map && not (List.mem nt gramext_globals) && nt <> "command" && nt <> "simple_tactic" then begin
        let new_name = String.uppercase_ascii (Filename.remove_extension (Filename.basename file)) ^ "_" ^ nt in
        dup_renames := StringMap.add nt new_name !dup_renames;
        if false then Printf.printf "** dup local sym %s -> %s in %s\n" nt new_name file
      end;
      add_symdef nt file symdef_map;
    let plugin = get_plugin_name file in
    let prods = if not is_edit &&
        not (List.mem file autoloaded_mlgs) &&
        plugin <> "" then
      List.map (fun p -> p @ [Sedit2 ("TAG", plugin)]) prods
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
      let gramext_globals = ref grammar_ext.gramext_globals in
      List.iter (fun ent ->
          let pos, rules = match ent.gentry_rules with
          | GDataFresh (pos, r) -> (pos, r)
          | GDataReuse (lbl, r) ->
            let r = {
              grule_label = lbl;
              grule_assoc = None;
              grule_prods = r;
            } in
            (None, [r])
          in
          let len = List.length rules in
          List.iteri (fun i rule ->
              let nt = ent.gentry_name in
              if not (List.mem nt !gramext_globals) then
                locals := StringSet.add nt !locals;
              let level = (get_label rule.grule_label) in
              let level = if level <> "" then level else
                match pos with
                | Some (Before lev)
                | Some (After lev)
                  -> lev
                (* Looks like FIRST/LAST can be ignored for documenting the current grammar *)
                | _ -> "" in
              if len > 1 && level = "" then
                error "Missing level string for '%s'\n" nt
              else if not (Str.string_match level_regex level 0) then
                error "Invalid level string '%s' for '%s'\n" level nt;
              let cur_level = nt ^ level in
              let next_level = nt ^
                  if i+1 < len then (get_label (List.nth rules (i+1)).grule_label) else "" in
              let right_assoc = (rule.grule_assoc = Some RightA) in

              if i = 0 && cur_level <> nt && not (StringMap.mem nt !level_renames) then begin
                level_renames := StringMap.add nt cur_level !level_renames;
              end;
              let cvted = List.map cvt_gram_prod rule.grule_prods in
              (* edit names for levels *)
              (* See https://camlp5.github.io/doc/html/grammars.html#b:Associativity *)
              let edited = List.map (edit_SELF nt cur_level next_level right_assoc false) cvted in
              let prods_to_add =
                if cur_level <> nt && i+1 < len then
                  edited @ [[Snterm next_level]]
                else
                  edited
              in
              if cur_level <> nt && List.mem nt !gramext_globals then
                gramext_globals := cur_level :: !gramext_globals;
              add_prods cur_level prods_to_add !gramext_globals)
            rules
        ) grammar_ext.gramext_entries

    | VernacExt vernac_ext ->
      let node = match vernac_ext.vernacext_entry with
      | None -> "command"
      | Some c -> String.trim c.code
      in
      add_prods node
        (List.map (fun r -> cvt_ext r.vernac_toks) vernac_ext.vernacext_rules) []
    | VernacArgumentExt vernac_argument_ext ->
      add_prods vernac_argument_ext.vernacargext_name
        (List.map (fun r -> cvt_ext r.tac_toks) vernac_argument_ext.vernacargext_rules) []
    | TacticExt tactic_ext ->
      add_prods "simple_tactic"
        (List.map (fun r -> cvt_ext r.tac_toks) tactic_ext.tacext_rules) []
    | ArgumentExt argument_ext ->
      add_prods argument_ext.argext_name
        (List.map (fun r -> cvt_ext r.tac_toks) argument_ext.argext_rules) []
    | _ -> ()
  in

  List.iter prod_loop ast;
  List.rev !res, !locals, !dup_renames

let dir s = "doc/tools/docgram/" ^ s

let read_mlg_edit file =
  let fdir = dir file in
  let level_renames = ref StringMap.empty in (* ignored *)
  let symdef_map = ref StringMap.empty in (* ignored *)
  let prods, _, _ = read_mlg (g_empty ()) true (parse_file fdir) fdir level_renames symdef_map in
  prods

let add_rule g nt prods file =
  let ent = try NTMap.find nt !g.map with Not_found -> [] in
  let nodups = List.concat (List.map (fun prod ->
      if has_match prod ent then begin
        if !show_warn then
          warn "%s: Duplicate production '%s -> %s'\n" file nt (prod_to_str prod);
        []
      end else
        [prod])
    prods) in
  g_maybe_add_begin g nt (ent @ nodups)


let remove_Sedit2 p =
  List.filter (fun sym -> match sym with | Sedit2 _ -> false | _ -> true) p

let check_for_duplicates cause rule oldrule nt =
  let prods = List.map (fun p -> prod_to_str p) rule in
  let sorted = List.sort String.compare prods in
  let rec aux prev = function
    | hd :: tl -> if hd = prev then begin
        if (List.length (List.filter (fun p -> (prod_to_str p) = hd) rule)) <>
          (List.length (List.filter (fun p -> (prod_to_str p) = hd) oldrule)) then
          error "Duplicate production '%s -> %s' %s\n%!" nt hd cause
      end;
      aux hd tl
    | [] -> ()
  in
  aux " x " sorted

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
            | [] -> error "Empty splice for '%s'\n" nt; []
            | [p] -> List.rev (remove_Sedit2 p)
            | _ -> [Sprod (List.map remove_Sedit2 splice_prods)] (* todo? check if we create a dup *)
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
    | Snterm nt :: Sedit2 ("TAG", _) :: [] when is_splice nt ->
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

let read_mlg_files g args symdef_map =
  let level_renames = ref StringMap.empty in
  let last_autoloaded = List.hd (List.rev autoloaded_mlgs) in
  List.iter (fun file ->
    (* todo: ??? does nt renaming, deletion and splicing *)
    let rules, locals, dup_renames = read_mlg g false (parse_file file) file level_renames symdef_map in
    let numprods = List.fold_left (fun num rule ->
        let nt, prods = rule in
        (* rename local duplicates *)
        let prods = List.map (fun prod -> List.hd (edit_prod g true dup_renames prod)) prods in
        let nt = try StringMap.find nt dup_renames with Not_found -> nt in
(*        if NTMap.mem nt !g.map && (StringSet.mem nt locals) &&*)
(*            StringSet.cardinal (StringSet.of_list (StringMap.find nt !symdef_map)) > 1 then*)
(*          warn "%s: local nonterminal '%s' already defined\n" file nt;  (* todo: goes away *)*)
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
          error "Undefined nt '%s' in SPLICE\n" key
      | "DELETE" ->
        if not (StringSet.mem key all_nts_ref || (StringSet.mem key all_nts_def)) then
          error "Unused/undefined nt '%s' in DELETE\n" key;
      | "RENAME" ->
        if not (StringSet.mem key all_nts_ref || (StringSet.mem key all_nts_def)) then
          error "Unused/undefined  nt '%s' in RENAME\n" key;
      | _ -> ());
      aux tl (StringMap.add key binding map)
  in
  aux edits StringMap.empty

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

(*** splice: replace a reference to a nonterminal with its definition ***)

(* todo: create a better splice routine *)
(* todo: remove extraneous "(* ltac2 plugin *)" in Ltac2 Notation cmd *)
let apply_splice g edit_map =
  List.iter (fun b ->
      let (nt0, prods0) = b in
      let rec splice_loop nt prods cnt =
        if cnt >= 10 then begin
          error "Splice for '%s' not done after %d iterations.  Current value is:\n" nt0 cnt;
          List.iter (fun prod -> Printf.eprintf "  %s\n" (prod_to_str prod)) prods;
          (nt, prods)
        end else begin
          let (nt', prods') = edit_rule g edit_map nt prods in
          if nt' = nt && prods' = prods then
            (nt, prods)
          else
            splice_loop nt' prods' (cnt+1)
        end
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
    (StringMap.bindings edit_map)


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

(* create a new nt for LIST* or OPT with the specified name *)
let maybe_add_nt g insert_after name sym queue =
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

let apply_rename_delete g edit_map =
  List.iter (fun b -> let (nt, _) = b in
      let prods = try NTMap.find nt !g.map  with Not_found -> [] in
      let (nt', prods') = edit_rule g edit_map nt prods in
      if nt' = "" then
        g_remove g nt
      else if nt <> nt' then
        g_rename_merge g nt nt' prods'
      else
        g_update_prods g nt prods')
    (NTMap.bindings !g.map)

let edit_all_prods g op eprods =
  let g_old_map = !g.map in
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
    let edit_map = create_edit_map g op (aux eprods []) in
    match op with
    | "SPLICE" ->
      let rv = apply_splice g edit_map in
      let cause = Printf.sprintf "from SPLICE of '%s'" (prod_to_str (List.hd eprods)) in
      NTMap.iter (fun nt rule -> check_for_duplicates cause rule (NTMap.find nt g_old_map) nt) !g.map;
      rv
    | "RENAME"
    | "DELETE" -> apply_rename_delete g edit_map
    | _ -> ()

  in
  match op with
  | "RENAME" -> do_it op eprods 2; true
  | "DELETE" -> do_it op eprods 1; true
  | "SPLICE" ->
    (* iterate to give precise error messages *)
    List.iter (fun prod -> do_it op [ prod ] 1) eprods; true
  | "OPTINREF" ->
      List.iter (fun nt ->
        let prods = NTMap.find nt !g.map in
        if has_match [] prods then begin
          let prods' = remove_prod [] prods nt in
          g_update_prods g nt prods';
          global_repl g [(Snterm nt)] [(Sopt (Snterm nt))]
        end)
      !g.order; true
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
        error "Undefined nonterminal '%s' in edit: %s\n" nt (prod_to_str prod))
    nts

let apply_edit_file g edits =
  let moveto src_nt dest_nt oprod prods =
    g_add_prod_after g (Some src_nt) dest_nt oprod;
    remove_prod oprod prods src_nt      (* remove orig prod *)
  in
  List.iter (fun b ->
      let (nt, eprod) = b in
      if not (edit_all_prods g nt eprod) then begin
        let rec aux eprod prods add_nt =
          let g_old_map = !g.map in
          let rv = match eprod with
          | [] -> prods, add_nt
          | (Snterm "DELETE" :: oprod) :: tl ->
            aux tl (remove_prod oprod prods nt) add_nt
          | (Snterm "DELETENT" :: _) :: tl ->  (* note this doesn't remove references *)
            if not (NTMap.mem nt !g.map) then
              error "DELETENT for undefined nonterminal '%s'\n" nt;
            g_remove g nt;
            aux tl prods false
          | (Snterm "MOVETO" :: Snterm dest_nt :: oprod) :: tl ->
            let prods = try (* add "nt -> dest_nt" production *)
              let posn = find_first oprod prods nt in
              if List.mem [Snterm dest_nt] prods then prods
                else insert_after posn [[Snterm dest_nt]] prods (* insert new prod *)
            with Not_found -> prods in
            let prods' = moveto nt dest_nt oprod prods in
            aux tl prods' add_nt
          | [Snterm "COPYALL"; Snterm dest_nt] :: tl ->
            if NTMap.mem dest_nt !g.map then
              error "COPYALL target nonterminal '%s' already exists\n" dest_nt;
            g_maybe_add g dest_nt prods;
            aux tl prods add_nt
          | [Snterm "MOVEALLBUT"; Snterm dest_nt] :: tl ->
            List.iter (fun tlprod ->
                if not (List.mem tlprod prods) then
                  error "MOVEALLBUT for %s can't find '%s'\n" nt (prod_to_str tlprod))
              tl;
            let prods' = List.fold_left (fun prods oprod ->
                if not (List.mem oprod tl) then begin
                  moveto nt dest_nt oprod prods
                end else
                  prods)
              prods prods in
            prods', add_nt
          | (Snterm "OPTINREF" :: _) :: tl ->
            if not (has_match [] prods) then
              error "OPTINREF but no empty production for %s\n" nt;
            global_repl g [(Snterm nt)] [(Sopt (Snterm nt))];
            aux tl (remove_prod [] prods nt) add_nt
          | (Snterm "INSERTALL" :: syms) :: tl ->
            aux tl (List.map (fun p -> syms @ p) prods) add_nt
          | (Snterm "APPENDALL" :: syms) :: tl ->
            aux tl (List.map (fun p -> p @ syms) prods) add_nt
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
              error "Duplicate production '%s -> %s'\n" nt (prod_to_str prod);
            report_undef_nts g prod nt;
            aux tl (prods @ [prod]) add_nt
          in
          if eprod <> [] then begin
            let cause = Printf.sprintf "from '%s'" (prod_to_str (List.hd eprod)) in
            NTMap.iter (fun nt rule ->
              let old_rule = try NTMap.find nt g_old_map with Not_found -> [] in
              check_for_duplicates cause rule old_rule nt) !g.map;
          end;
          rv
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

let index_of str list =
  let rec index_of_r str list index =
    match list with
    | [] -> None
    | hd :: list ->
      if hd = str then Some index
      else index_of_r str list (index+1)
  in
  index_of_r str list 0

(* todo: raise exception for bad n? *)
let rec nthcdr n list = if n <= 0 then list else nthcdr (n-1) (List.tl list)

let report_bad_nts g file =
  let all_nts_ref, all_nts_def = get_refdef_nts g in
  let undef = StringSet.diff all_nts_ref all_nts_def in
  if !show_warn then
    List.iter (fun nt -> warn "%s: Undefined symbol '%s'\n" file nt) (StringSet.elements undef);

  let reachable =
    List.fold_left (fun res sym ->
        StringSet.union res (StringSet.of_list (nt_closure g sym [])))
      StringSet.empty start_symbols
  in
  let unreachable = List.filter (fun nt -> not (StringSet.mem nt reachable)) !g.order in
  if !show_warn then
    List.iter (fun nt -> warn "%s: Unreachable symbol '%s'\n" file nt) unreachable

let reorder_grammar eg reordered_rules file =
  let og = g_empty () in
  List.iter (fun rule ->
      let nt, prods = rule in
      try
        (* only keep nts and prods in common with editedGrammar *)
        let eg_prods = NTMap.find nt !eg.map in
        let prods = List.filter (fun prod -> (has_match prod eg_prods)) prods in
        if NTMap.mem nt !og.map && !show_warn then
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
    if not (files_eq old_file temp_file) then begin
      error "%s is not current\n" old_file;
      ignore (CUnix.sys_command "diff" [ "-u" ; old_file ; old_file ^ ".new"])
    end;
    Sys.remove temp_file
  end else if args.update then
    Sys.rename temp_file old_file

let open_temp_bin file =
  open_out_bin (sprintf "%s.new" file)

let match_cmd_regex = Str.regexp "[a-zA-Z0-9_ ]+"
let match_subscripts = Str.regexp "__[a-zA-Z0-9]+"
let remove_subscrs str = Str.global_replace match_subscripts "" str

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

(* Sphinx notations can't handle empty productions *)
let has_empty_prod rhs =
  let rec has_empty_prod_r rhs =
    match rhs with
      | [] -> false
      | Sterm _ :: tl
      | Snterm _ :: tl
      | Sedit _ :: tl
      | Sedit2 (_, _) :: tl ->  has_empty_prod_r tl

      | Slist1 sym :: tl
      | Slist0 sym :: tl
      | Slist1sep (sym, _) :: tl
      | Slist0sep (sym, _) :: tl
      | Sopt sym :: tl ->  has_empty_prod_r [ sym ] ||  has_empty_prod_r tl

      | Sparen prod :: tl -> List.length prod = 0 || has_empty_prod_r tl
      | Sprod prods :: tl -> List.fold_left
          (fun rv prod -> List.length prod = 0 || has_empty_prod_r tl || rv) false prods
  in
  List.length rhs = 0 || has_empty_prod_r rhs

let process_rst g file args seen tac_prods cmd_prods =
  let old_rst = open_in file in
  let new_rst = open_temp_bin file in
  let linenum = ref 0 in
  let dir_regex = Str.regexp "^\\([ \t]*\\)\\.\\.[ \t]*\\([a-zA-Z0-9:]* *\\)\\(.*\\)" in
  let contin_regex = Str.regexp "^\\([ \t]*\\)\\(.*\\)" in
  let ip_args_regex = Str.regexp "^[ \t]*\\([a-zA-Z0-9_\\.]+\\)[ \t]+\\([a-zA-Z0-9_\\.]+\\)" in
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
          if !show_warn then
            warn "%s line %d: '%s' already included at %s line %d\n"
                file !linenum nt prev_file prev_linenum;
        with Not_found ->
          seen := { !seen with nts = (NTMap.add nt (file, !linenum) !seen.nts)} );
        let prods = NTMap.find nt !g.map in
        List.iteri (fun i prod ->
            let rhs = String.trim (prod_to_prodn prod) in
            let tag = get_tag file prod in
            let sep = if i = 0 then " ::=" else "|" in
            if has_empty_prod prod then
              error "%s line %d: Empty (sub-)production for %s, edit to remove: '%s %s'\n"
                file !linenum nt sep rhs;
            fprintf new_rst "%s   %s%s %s%s\n" indent (if i = 0 then nt else "") sep rhs tag)
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

  let save_n_get_more direc pfx first_rhs seen_map prods =
    let replace rhs prods =
      if StringSet.is_empty prods then
        rhs (* no change *)
      else
        let mtch, multi, best = find_longest_match prods rhs in
(*        Printf.printf "mtch = '%s'  rhs = '%s'\n" mtch rhs;*)
        if mtch = rhs then
          rhs (* no change *)
        else if mtch = "" then begin
          error "%s line %d: NO MATCH for '%s'\n" file !linenum rhs;
          if best <> "" then begin
            Printf.eprintf "    closest match is: '%s'\n" best;
            Printf.eprintf "    Please update the rst manually while preserving any subscripts, e.g. 'NT__sub'\n"
          end;
          rhs
        end else if multi then begin
          error "%s line %d: MULTIPLE MATCHES for '%s'\n" file !linenum rhs;
          Printf.eprintf "    Please update the rst manually while preserving any subscripts, e.g. 'NT__sub'\n";
          rhs
        end else
          mtch (* update cmd/tacn *)
    in
    let map = ref seen_map in
    if NTMap.mem first_rhs !map && !show_warn then
      warn "%s line %d: Repeated %s: '%s'\n" file !linenum direc first_rhs;
(*    if not (StringSet.mem rhs seen_map) then*)
(*      warn "%s line %d: Unknown tactic: '%s'\n" file !linenum rhs;*)

    fprintf new_rst "%s%s\n" pfx (replace first_rhs prods);

    map := NTMap.add (remove_subscrs first_rhs) (file, !linenum) !map;
    while
      try
        let nextline = getline() in
        ignore (Str.string_match contin_regex nextline 0);
        let indent = Str.matched_group 1 nextline in
        let rhs = Str.matched_group 2 nextline in
        let replaceable = rhs <> "" && rhs.[0] <> ':' in
        let upd_rhs = if replaceable then (replace rhs prods) else rhs in
        fprintf new_rst "%s%s\n" indent upd_rhs;
        if replaceable then begin
          map := NTMap.add (remove_subscrs rhs) (file, !linenum) !map
        end;
        rhs <> ""
      with End_of_file -> false
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
          if rhs = "coq" && !show_warn then
            warn "%s line %d: Missing 'insertprodn' before 'prodn:: coq'\n" file !linenum;
          fprintf new_rst "%s\n" line;
        | "tacn::" ->
          seen := { !seen with tacs = save_n_get_more "tacn" pfx rhs !seen.tacs tac_prods }
        | "tacv::" ->
          seen := { !seen with tacvs = save_n_get_more "tacv" pfx rhs !seen.tacvs StringSet.empty }
        | "cmd::" ->
          seen := { !seen with cmds = save_n_get_more "cmd" pfx rhs !seen.cmds cmd_prods }
        | "cmdv::" ->
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

let report_omitted_prods g seen label split =
  if !show_warn then begin
    let included = try
        List.map (fun prod ->
          match prod with
          | Snterm nt :: tl -> nt
          | _ -> "") (NTMap.find "NOTINRSTS" !g.map)
      with Not_found -> []
    in
    Printf.printf "\n\n";
    let missing = NTMap.filter (fun nt _ ->
        not (NTMap.mem nt seen || (List.mem nt included)))
      !g.map in
    NTMap.iter (fun nt _ ->
        warn "%s %s not included in .rst files\n" "Nonterminal" nt)
      missing;
    let total = NTMap.cardinal missing in
    if total <> 0 then
      Printf.eprintf "TOTAL %ss not included = %d\n" label total
  end

let process_grammar args =
  let symdef_map = ref StringMap.empty in
  let g = g_empty () in

  let level_renames = read_mlg_files g args symdef_map in
  if args.verbose then begin
    Printf.printf "Keywords:\n";
    StringSet.iter (fun kw -> Printf.printf "%s " kw) !keywords;
    Printf.printf "\n\n";
  end;

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
(*      check_singletons g*)

      let seen = ref { nts=NTMap.empty; tacs=NTMap.empty; tacvs=NTMap.empty; cmds=NTMap.empty; cmdvs=NTMap.empty } in
      let plist nt =
        let list = (List.map (fun t -> String.trim (prod_to_prodn t))
          (NTMap.find nt !g.map)) in
        list, StringSet.of_list list in
      let tac_list, tac_prods = plist "simple_tactic" in
      let cmd_list, cmd_prods = plist "command" in
      List.iter (fun file -> process_rst g file args seen tac_prods cmd_prods) args.rst_files;
      report_omitted_prods g !seen.nts "Nonterminal" "";
      let out = open_out (dir "updated_rsts") in
      close_out out;

      (* generate report on cmds or tacs *)
      let cmdReport outfile cmdStr itemName cmd_nts cmds cmdvs =
        let rstCmds = StringSet.of_list (List.map (fun b -> let c, _ = b in c) (NTMap.bindings cmds)) in
        let rstCmdvs = StringSet.of_list (List.map (fun b -> let c, _ = b in c) (NTMap.bindings cmdvs)) in
        let gramCmds = List.fold_left (fun set nt ->
            StringSet.union set (StringSet.of_list (List.map (fun p -> String.trim (prod_to_prodn p)) (NTMap.find nt !prodn_gram.map)))
          ) StringSet.empty cmd_nts in
        let allCmds = StringSet.union rstCmdvs (StringSet.union rstCmds gramCmds) in
        let out = open_out_bin (dir outfile) in
        StringSet.iter (fun c ->
            let rsts = StringSet.mem c rstCmds in
            let gram = StringSet.mem c gramCmds in
            let pfx = match rsts, gram with
            | true, false -> error "%s not in grammar: %s\n" itemName c; "+"
            | false, true -> error "%s not in doc: %s\n" itemName c; "-"
            | false, false -> "?"
            | _, _ -> " "
            in
            let var = if StringSet.mem c rstCmdvs then "v" else " " in
            fprintf out "%s%s  %s\n" pfx var c)
          allCmds;
        close_out out;
        Printf.printf "# %s in rsts, gram, total = %d %d %d\n" cmdStr (StringSet.cardinal gramCmds)
          (StringSet.cardinal rstCmds) (StringSet.cardinal allCmds);
      in

      let cmd_nts = ["command"] in
      (* TODO: need to handle tactic_mode (overlaps with query_command) and subprf *)
      if args.check_cmds then
        cmdReport "prodnCommands" "cmds" "Command" cmd_nts !seen.cmds !seen.cmdvs;

      let tac_nts = ["simple_tactic"] in
      if args.check_tacs then
        cmdReport "prodnTactics" "tacs" "Tactic" tac_nts !seen.tacs !seen.tacvs;

      (* generate prodnGrammar for reference *)
      if not args.verify then begin
        let out = open_out_bin (dir "prodnGrammar") in
        print_in_order out prodn_gram `PRODN !prodn_gram.order StringSet.empty;
        close_out out;
      end
    end (* if !exit_code = 0 *)
  end (* if not args.fullGrammar *)

let parse_args () =
  let suffix_regex = Str.regexp ".*\\.\\([a-z]+\\)$" in
  let args =
    List.fold_left (fun args arg ->
        match arg with
        | "-check-cmds" -> { args with check_cmds = true }
        | "-check-tacs" -> { args with check_tacs = true }
        | "-no-warn" -> show_warn := false; { args with show_warn = false }
        | "-no-update" -> { args with update = false }
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
    if !error_count > 0 then
      Printf.eprintf "%d error(s)\n" !error_count;
    exit !exit_code
  (*with _ -> Printexc.print_backtrace stdout; exit 1*)
