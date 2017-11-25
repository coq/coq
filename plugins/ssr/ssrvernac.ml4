(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Names
module CoqConstr = Constr
open CoqConstr
open Termops
open Constrexpr
open Constrexpr_ops
open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Pvernac.Vernac_
open Ltac_plugin
open Notation_ops
open Notation_term
open Glob_term
open Stdarg
open Genarg
open Decl_kinds
open Pp
open Ppconstr
open Printer
open Util
open Extraargs
open Evar_kinds
open Ssrprinters
open Ssrcommon
open Ssrparser
DECLARE PLUGIN "ssreflect_plugin"

let (!@) = Pcoq.to_coqloc

(* Defining grammar rules with "xx" in it automatically declares keywords too,
 * we thus save the lexer to restore it at the end of the file *)
let frozen_lexer = CLexer.get_keyword_state () ;;

(* global syntactic changes and vernacular commands *)

(** Alternative notations for "match" and anonymous arguments. *)(* {{{ ************)

(* Syntax:                                                        *)
(*  if <term> is <pattern> then ... else ...                      *)
(*  if <term> is <pattern> [in ..] return ... then ... else ...   *)
(*  let: <pattern> := <term> in ...                               *)
(*  let: <pattern> [in ...] := <term> return ... in ...           *)
(* The scope of a top-level 'as' in the pattern extends over the  *)
(* 'return' type (dependent if/let).                              *)
(* Note that the optional "in ..." appears next to the <pattern>  *)
(* rather than the <term> in then "let:" syntax. The alternative  *)
(* would lead to ambiguities in, e.g.,                            *)
(* let: p1 := (*v---INNER LET:---v *)                             *)
(*   let: p2 := let: p3 := e3 in k return t in k2 in k1 return t' *)
(* in b       (*^--ALTERNATIVE INNER LET--------^ *)              *)

(* Caveat : There is no pretty-printing support, since this would *)
(* require a modification to the Coq kernel (adding a new match   *)
(* display style -- why aren't these strings?); also, the v8.1    *)
(* pretty-printer only allows extension hooks for printing        *)
(* integer or string literals.                                    *)
(*   Also note that in the v8 grammar "is" needs to be a keyword; *)
(* as this can't be done from an ML extension file, the new       *)
(* syntax will only work when ssreflect.v is imported.            *)

let no_ct = None, None and no_rt = None in 
let aliasvar = function
  | [[{ CAst.v = CPatAlias (_, na); loc }]] -> Some na
  | _ -> None in
let mk_cnotype mp = aliasvar mp, None in
let mk_ctype mp t = aliasvar mp, Some t in
let mk_rtype t = Some t in
let mk_dthen ?loc (mp, ct, rt) c = (CAst.make ?loc (mp, c)), ct, rt in
let mk_let ?loc rt ct mp c1 =
  CAst.make ?loc @@ CCases (LetPatternStyle, rt, ct, [CAst.make ?loc (mp, c1)]) in
let mk_pat c (na, t) = (c, na, t) in
GEXTEND Gram
  GLOBAL: binder_constr;
  ssr_rtype: [[ "return"; t = operconstr LEVEL "100" -> mk_rtype t ]];
  ssr_mpat: [[ p = pattern -> [[p]] ]];
  ssr_dpat: [
    [ mp = ssr_mpat; "in"; t = pattern; rt = ssr_rtype -> mp, mk_ctype mp t, rt
    | mp = ssr_mpat; rt = ssr_rtype -> mp, mk_cnotype mp, rt
    | mp = ssr_mpat -> mp, no_ct, no_rt
  ] ];
  ssr_dthen: [[ dp = ssr_dpat; "then"; c = lconstr -> mk_dthen ~loc:!@loc dp c ]];
  ssr_elsepat: [[ "else" -> [[CAst.make ~loc:!@loc @@ CPatAtom None]] ]];
  ssr_else: [[ mp = ssr_elsepat; c = lconstr -> CAst.make ~loc:!@loc (mp, c) ]];
  binder_constr: [
    [ "if"; c = operconstr LEVEL "200"; "is"; db1 = ssr_dthen; b2 = ssr_else ->
      let b1, ct, rt = db1 in CAst.make ~loc:!@loc @@ CCases (MatchStyle, rt, [mk_pat c ct], [b1; b2])
    | "if"; c = operconstr LEVEL "200";"isn't";db1 = ssr_dthen; b2 = ssr_else ->
      let b1, ct, rt = db1 in 
      let b1, b2 = let open CAst in
        let {loc=l1; v=(p1, r1)}, {loc=l2; v=(p2, r2)} = b1, b2 in
        (make ?loc:l1 (p1, r2), make ?loc:l2 (p2, r1))
      in
      CAst.make ~loc:!@loc @@ CCases (MatchStyle, rt, [mk_pat c ct], [b1; b2])
    | "let"; ":"; mp = ssr_mpat; ":="; c = lconstr; "in"; c1 = lconstr ->
      mk_let ~loc:!@loc no_rt [mk_pat c no_ct] mp c1
    | "let"; ":"; mp = ssr_mpat; ":="; c = lconstr;
      rt = ssr_rtype; "in"; c1 = lconstr ->
      mk_let ~loc:!@loc rt [mk_pat c (mk_cnotype mp)] mp c1
    | "let"; ":"; mp = ssr_mpat; "in"; t = pattern; ":="; c = lconstr;
      rt = ssr_rtype; "in"; c1 = lconstr ->
      mk_let ~loc:!@loc rt [mk_pat c (mk_ctype mp t)] mp c1
  ] ];
END

GEXTEND Gram
  GLOBAL: closed_binder;
  closed_binder: [
    [ ["of" | "&"]; c = operconstr LEVEL "99" ->
      [CLocalAssum ([CAst.make ~loc:!@loc Anonymous], Default Explicit, c)]
  ] ];
END
(* }}} *)

(** Vernacular commands: Prenex Implicits and Search *)(* {{{ **********************)

(* This should really be implemented as an extension to the implicit   *)
(* arguments feature, but unfortuately that API is sealed. The current *)
(* workaround uses a combination of notations that works reasonably,   *)
(* with the following caveats:                                         *)
(*  - The pretty-printing always elides prenex implicits, even when    *)
(*    they are obviously needed.                                       *)
(*  - Prenex Implicits are NEVER exported from a module, because this  *)
(*    would lead to faulty pretty-printing and scoping errors.         *)
(*  - The command "Import Prenex Implicits" can be used to reassert    *)
(*    Prenex Implicits for all the visible constants that had been     *)
(*    declared as Prenex Implicits.                                    *)

let declare_one_prenex_implicit locality f =
  let fref =
    try Smartlocate.global_with_alias f 
    with _ -> errorstrm (pr_qualid f ++ str " is not declared") in
  let rec loop = function
  | a :: args' when Impargs.is_status_implicit a ->
    (ExplByName (Impargs.name_of_implicit a), (true, true, true)) :: loop args'
  | args' when List.exists Impargs.is_status_implicit args' ->
      errorstrm (str "Expected prenex implicits for " ++ pr_qualid f)
  | _ -> [] in
  let impls =
    match Impargs.implicits_of_global fref  with
    | [cond,impls] -> impls
    | [] -> errorstrm (str "Expected some implicits for " ++ pr_qualid f)
    | _ -> errorstrm (str "Multiple implicits not supported") in
  match loop impls  with
  | [] ->
    errorstrm (str "Expected some implicits for " ++ pr_qualid f)
  | impls ->
    Impargs.declare_manual_implicits locality fref ~enriching:false [impls]

VERNAC COMMAND FUNCTIONAL EXTEND Ssrpreneximplicits CLASSIFIED AS SIDEFF
  | [ "Prenex" "Implicits" ne_global_list(fl) ]
  -> [ fun ~atts ~st ->
         let open Vernacinterp in
         let locality = Locality.make_section_locality atts.locality in
         List.iter (declare_one_prenex_implicit locality) fl;
         st
     ]
END

(* Vernac grammar visibility patch *)

GEXTEND Gram
  GLOBAL: gallina_ext;
  gallina_ext:
   [ [ IDENT "Import"; IDENT "Prenex"; IDENT "Implicits" ->
      Vernacexpr.VernacUnsetOption (false, ["Printing"; "Implicit"; "Defensive"])
   ] ]
  ;
END

(** Extend Search to subsume SearchAbout, also adding hidden Type coercions. *)

(* Main prefilter *)

type raw_glob_search_about_item =
  | RGlobSearchSubPattern of constr_expr
  | RGlobSearchString of Loc.t * string * string option

let pr_search_item = function
  | RGlobSearchString (_,s,_) -> str s
  | RGlobSearchSubPattern p -> pr_constr_expr p

let wit_ssr_searchitem = add_genarg "ssr_searchitem" pr_search_item

let pr_ssr_search_item _ _ _ = pr_search_item

(* Workaround the notation API that can only print notations *)

let is_ident s = try CLexer.check_ident s; true with _ -> false

let is_ident_part s = is_ident ("H" ^ s)

let interp_search_notation ?loc tag okey =
  let err msg = CErrors.user_err ?loc ~hdr:"interp_search_notation" msg in
  let mk_pntn s for_key =
    let n = String.length s in
    let s' = Bytes.make (n + 2) ' ' in
    let rec loop i i' =
      if i >= n then s', i' - 2 else if s.[i] = ' ' then loop (i + 1) i' else
      let j = try String.index_from s (i + 1) ' ' with _ -> n in
      let m = j - i in
      if s.[i] = '\'' && i < j - 2 && s.[j - 1] = '\'' then
        (String.blit s (i + 1) s' i' (m - 2); loop (j + 1) (i' + m - 1))
      else if for_key && is_ident (String.sub s i m) then
         (Bytes.set s' i' '_'; loop (j + 1) (i' + 2))
      else (String.blit s i s' i' m; loop (j + 1) (i' + m + 1)) in
    loop 0 1 in
  let trim_ntn (pntn, m) = (InConstrEntrySomeLevel,Bytes.sub_string pntn 1 (max 0 m)) in
  let pr_ntn ntn = str "(" ++ Notation.pr_notation ntn ++ str ")" in
  let pr_and_list pr = function
    | [x] -> pr x
    | x :: lx -> pr_list pr_comma pr lx ++ pr_comma () ++ str "and " ++ pr x
    | [] -> mt () in
  let pr_sc sc = str (if sc = "" then "independently" else sc) in
  let pr_scs = function
    | [""] -> pr_sc ""
    | scs -> str "in " ++ pr_and_list pr_sc scs in
  let generator, pr_tag_sc =
    let ign _ = mt () in match okey with
  | Some key ->
    let sc = Notation.find_delimiters_scope ?loc key in
    let pr_sc s_in = str s_in ++ spc() ++ str sc ++ pr_comma() in
    Notation.pr_scope ign sc, pr_sc
  | None -> Notation.pr_scopes ign, ign in
  let qtag s_in = pr_tag_sc s_in ++ qstring tag ++ spc()in
  let ptag, ttag =
    let ptag, m = mk_pntn tag false in
    if m <= 0 then err (str "empty notation fragment");
    ptag, trim_ntn (ptag, m) in
  let last = ref "" and last_sc = ref "" in
  let scs = ref [] and ntns = ref [] in
  let push_sc sc = match !scs with
  | "" :: scs' ->  scs := "" :: sc :: scs'
  | scs' -> scs := sc :: scs' in
  let get s _ _ = match !last with
  | "Scope " -> last_sc := s; last := ""
  | "Lonely notation" -> last_sc := ""; last := ""
  | "\"" ->
      let pntn, m = mk_pntn s true in
      if String.string_contains ~where:(Bytes.to_string pntn) ~what:(Bytes.to_string ptag) then begin
        let ntn = trim_ntn (pntn, m) in
        match !ntns with
        | [] -> ntns := [ntn]; scs := [!last_sc]
        | ntn' :: _ when ntn' = ntn -> push_sc !last_sc
        | _ when ntn = ttag -> ntns := ntn :: !ntns; scs := [!last_sc]
        | _ :: ntns' when List.mem ntn ntns' -> ()
        | ntn' :: ntns' -> ntns := ntn' :: ntn :: ntns'
      end;
      last := ""
  | _ -> last := s in
  pp_with (Format.make_formatter get (fun _ -> ())) generator;
  let ntn = match !ntns with
  | [] ->
    err (hov 0 (qtag "in" ++ str "does not occur in any notation"))
  | ntn :: ntns' when ntn = ttag ->
    if ntns' <> [] then begin
      let pr_ntns' = pr_and_list pr_ntn ntns' in
      Feedback.msg_warning (hov 4 (qtag "In" ++ str "also occurs in " ++ pr_ntns'))
    end; ntn
  | [ntn] ->
    Feedback.msg_info (hov 4 (qtag "In" ++ str "is part of notation " ++ pr_ntn ntn)); ntn
  | ntns' ->
    let e = str "occurs in" ++ spc() ++ pr_and_list pr_ntn ntns' in
    err (hov 4 (str "ambiguous: " ++ qtag "in" ++ e)) in
  let (nvars, body), ((_, pat), osc) = match !scs with
  | [sc] -> Notation.interp_notation ?loc ntn (None, [sc])
  | scs' ->
    try Notation.interp_notation ?loc ntn (None, []) with _ ->
    let e = pr_ntn ntn ++ spc() ++ str "is defined " ++ pr_scs scs' in
    err (hov 4 (str "ambiguous: " ++ pr_tag_sc "in" ++ e)) in
  let sc = Option.default "" osc in
  let _ =
    let m_sc =
      if osc <> None then str "In " ++ str sc ++ pr_comma() else mt() in
    let ntn_pat = trim_ntn (mk_pntn pat false) in
    let rbody = glob_constr_of_notation_constr ?loc body in
    let m_body = hov 0 (Constrextern.without_symbols prl_glob_constr rbody) in
    let m = m_sc ++ pr_ntn ntn_pat ++ spc () ++ str "denotes " ++ m_body in
    Feedback.msg_info (hov 0 m) in
  if List.length !scs > 1 then
    let scs' = List.remove (=) sc !scs in
    let w = pr_ntn ntn ++ str " is also defined " ++ pr_scs scs' in
    Feedback.msg_warning (hov 4 w)
  else if String.string_contains ~where:(snd ntn) ~what:" .. " then
    err (pr_ntn ntn ++ str " is an n-ary notation");
  let nvars = List.filter (fun (_,(_,typ)) -> typ = NtnTypeConstr) nvars in
  let rec sub () = function
  | NVar x when List.mem_assoc x nvars -> DAst.make ?loc @@ GPatVar (FirstOrderPatVar x)
  | c ->
    glob_constr_of_notation_constr_with_binders ?loc (fun _ x -> (), None, x) sub () c in
  let _, npat = Patternops.pattern_of_glob_constr (sub () body) in
  Search.GlobSearchSubPattern npat

ARGUMENT EXTEND ssr_search_item TYPED AS ssr_searchitem
  PRINTED BY pr_ssr_search_item
  | [ string(s) ] -> [ RGlobSearchString (loc,s,None) ]
  | [ string(s) "%" preident(key) ] -> [ RGlobSearchString (loc,s,Some key) ]
  | [ constr_pattern(p) ] -> [ RGlobSearchSubPattern p ]
END

let pr_ssr_search_arg _ _ _ =
  let pr_item (b, p) = str (if b then "-" else "") ++ pr_search_item p in
  pr_list spc pr_item

ARGUMENT EXTEND ssr_search_arg TYPED AS (bool * ssr_searchitem) list
  PRINTED BY pr_ssr_search_arg
  | [ "-" ssr_search_item(p) ssr_search_arg(a) ] -> [ (false, p) :: a ]
  | [ ssr_search_item(p) ssr_search_arg(a) ] -> [ (true, p) :: a ]
  | [ ] -> [ [] ]
END

(* Main type conclusion pattern filter *)

let rec splay_search_pattern na = function 
  | Pattern.PApp (fp, args) -> splay_search_pattern (na + Array.length args) fp
  | Pattern.PLetIn (_, _, _, bp) -> splay_search_pattern na bp
  | Pattern.PRef hr -> hr, na
  | _ -> CErrors.user_err (Pp.str "no head constant in head search pattern")

let push_rels_assum l e =
  let l = List.map (fun (n,t) -> n, EConstr.Unsafe.to_constr t) l in
  push_rels_assum l e

let coerce_search_pattern_to_sort hpat =
  let env = Global.env () in
  let sigma = Evd.(from_env env) in
  let mkPApp fp n_imps args =
    let args' = Array.append (Array.make n_imps (Pattern.PMeta None)) args in
    Pattern.PApp (fp, args') in
  let hr, na = splay_search_pattern 0 hpat in
  let dc, ht =
    let hr, _ = Global.type_of_global_in_context (Global.env ()) hr (** FIXME *) in
    Reductionops.splay_prod env sigma (EConstr.of_constr hr) in
  let np = List.length dc in
  if np < na then CErrors.user_err (Pp.str "too many arguments in head search pattern") else
  let hpat' = if np = na then hpat else mkPApp hpat (np - na) [||] in
  let warn () =
    Feedback.msg_warning (str "Listing only lemmas with conclusion matching " ++ 
      pr_constr_pattern_env env sigma hpat') in
  if EConstr.isSort sigma ht then begin warn (); true, hpat' end else
  let filter_head, coe_path =
    try 
      let _, cp =
        Classops.lookup_path_to_sort_from (push_rels_assum dc env) sigma ht in
      warn ();
      true, cp
    with _ -> false, [] in
  let coerce hp coe_index =
    let coe_ref = coe_index.Classops.coe_value in
    try
      let n_imps = Option.get (Classops.hide_coercion coe_ref) in
      mkPApp (Pattern.PRef coe_ref) n_imps [|hp|]
    with Not_found | Option.IsNone ->
    errorstrm (str "need explicit coercion " ++ pr_global coe_ref ++ spc ()
            ++ str "to interpret head search pattern as type") in
  filter_head, List.fold_left coerce hpat' coe_path

let interp_head_pat hpat =
  let filter_head, p = coerce_search_pattern_to_sort hpat in
  let rec loop c = match CoqConstr.kind c with
  | Cast (c', _, _) -> loop c'
  | Prod (_, _, c') -> loop c'
  | LetIn (_, _, _, c') -> loop c'
  | _ ->
    let env = Global.env () in
    let sigma = Evd.from_env env in
    Constr_matching.is_matching env sigma p (EConstr.of_constr c) in
  filter_head, loop

let all_true _ = true

let rec interp_search_about args accu = match args with
| [] -> accu
| (flag, arg) :: rem ->
  fun gr env typ ->
    let ans = Search.search_about_filter arg gr env typ in
    (if flag then ans else not ans) && interp_search_about rem accu gr env typ

let interp_search_arg arg =
  let arg = List.map (fun (x,arg) -> x, match arg with
  | RGlobSearchString (loc,s,key) ->
      if is_ident_part s then Search.GlobSearchString s else
      interp_search_notation ~loc s key
  | RGlobSearchSubPattern p ->
      try
        let env = Global.env () in
        let _, p = Constrintern.intern_constr_pattern env (Evd.from_env env) p in
        Search.GlobSearchSubPattern p
      with e -> let e = CErrors.push e in iraise (ExplainErr.process_vernac_interp_error e)) arg in
  let hpat, a1 = match arg with
  | (_, Search.GlobSearchSubPattern (Pattern.PMeta _)) :: a' -> all_true, a'
  | (true, Search.GlobSearchSubPattern p) :: a' ->
     let filter_head, p = interp_head_pat p in
     if filter_head then p, a' else all_true, arg
  | _ -> all_true, arg in
  let is_string =
    function (_, Search.GlobSearchString _) -> true | _ -> false in
  let a2, a3 = List.partition is_string a1 in
  interp_search_about (a2 @ a3) (fun gr env typ -> hpat typ)

(* Module path postfilter *)

let pr_modloc (b, m) = if b then str "-" ++ pr_qualid m else pr_qualid m

let wit_ssrmodloc = add_genarg "ssrmodloc" pr_modloc

let pr_ssr_modlocs _ _ _ ml =
  if ml = [] then str "" else spc () ++ str "in " ++ pr_list spc pr_modloc ml

ARGUMENT EXTEND ssr_modlocs TYPED AS ssrmodloc list PRINTED BY pr_ssr_modlocs
  | [ ] -> [ [] ]
END

GEXTEND Gram
  GLOBAL: ssr_modlocs;
  modloc: [[ "-"; m = global -> true, m | m = global -> false, m]];
  ssr_modlocs: [[ "in"; ml = LIST1 modloc -> ml ]];
END

let interp_modloc mr =
  let interp_mod (_, qid) =
    try Nametab.full_name_module qid with Not_found ->
    CErrors.user_err ?loc:qid.CAst.loc (str "No Module " ++ pr_qualid qid) in
  let mr_out, mr_in = List.partition fst mr in
  let interp_bmod b = function
  | [] -> fun _ _ _ -> true
  | rmods -> Search.module_filter (List.map interp_mod rmods, b) in
  let is_in = interp_bmod false mr_in and is_out = interp_bmod true mr_out in
  fun gr env typ -> is_in gr env typ && is_out gr env typ

(* The unified, extended vernacular "Search" command *)

let ssrdisplaysearch gr env t =
  let pr_res = pr_global gr ++ spc () ++ str " " ++ pr_lconstr_env env Evd.empty t in
  Feedback.msg_info (hov 2 pr_res ++ fnl ())

VERNAC COMMAND EXTEND SsrSearchPattern CLASSIFIED AS QUERY
| [ "Search" ssr_search_arg(a) ssr_modlocs(mr) ] ->
  [ let hpat = interp_search_arg a in
    let in_mod = interp_modloc mr in
    let post_filter gr env typ = in_mod gr env typ && hpat gr env typ in
    let display gr env typ =
      if post_filter gr env typ then ssrdisplaysearch gr env typ
    in
    Search.generic_search None display ]
END

(* }}} *)

(** View hint database and View application. *)(* {{{ ******************************)

(* There are three databases of lemmas used to mediate the application  *)
(* of reflection lemmas: one for forward chaining, one for backward     *)
(* chaining, and one for secondary backward chaining.                   *)

(* View hints *)

let pr_raw_ssrhintref prc _ _ = let open CAst in function
  | { v = CAppExpl ((None, r,x), args) } when isCHoles args ->
    prc (CAst.make @@ CRef (r,x)) ++ str "|" ++ int (List.length args)
  | { v = CApp ((_, { v = CRef _ }), _) } as c -> prc c
  | { v = CApp ((_, c), args) } when isCxHoles args ->
    prc c ++ str "|" ++ int (List.length args)
  | c -> prc c

let pr_rawhintref c =
  let _, env = Pfedit.get_current_context () in
  match DAst.get c with
  | GApp (f, args) when isRHoles args ->
    pr_glob_constr_env env f ++ str "|" ++ int (List.length args)
  | _ -> pr_glob_constr_env env c

let pr_glob_ssrhintref _ _ _ (c, _) = pr_rawhintref c

let pr_ssrhintref prc _ _ = prc

let mkhintref ?loc c n = match c.CAst.v with
  | CRef (r,x) -> CAst.make ?loc @@ CAppExpl ((None, r, x), mkCHoles ?loc n)
  | _ -> mkAppC (c, mkCHoles ?loc n)

ARGUMENT EXTEND ssrhintref
                             PRINTED BY pr_ssrhintref
    RAW_TYPED AS constr  RAW_PRINTED BY pr_raw_ssrhintref
   GLOB_TYPED AS constr GLOB_PRINTED BY pr_glob_ssrhintref
  | [ constr(c) ] -> [ c ]
  | [ constr(c) "|" natural(n) ] -> [ mkhintref ~loc c n ]
END

(* View purpose *)

let pr_viewpos = function
  | Some Ssrview.AdaptorDb.Forward -> str " for move/"
  | Some Ssrview.AdaptorDb.Backward -> str " for apply/"
  | Some Ssrview.AdaptorDb.Equivalence -> str " for apply//"
  | None -> mt ()

let pr_ssrviewpos _ _ _ = pr_viewpos

ARGUMENT EXTEND ssrviewpos PRINTED BY pr_ssrviewpos
  | [ "for" "move" "/" ] -> [ Some Ssrview.AdaptorDb.Forward ]
  | [ "for" "apply" "/" ] -> [ Some Ssrview.AdaptorDb.Backward ]
  | [ "for" "apply" "/" "/" ] -> [ Some Ssrview.AdaptorDb.Equivalence ]
  | [ "for" "apply" "//" ] -> [ Some Ssrview.AdaptorDb.Equivalence ]
  | [ ] -> [ None ]
END

let pr_ssrviewposspc _ _ _ i = pr_viewpos i ++ spc ()

ARGUMENT EXTEND ssrviewposspc TYPED AS ssrviewpos PRINTED BY pr_ssrviewposspc
  | [ ssrviewpos(i) ] -> [ i ]
END

let print_view_hints kind l =
  let pp_viewname = str "Hint View" ++ pr_viewpos (Some kind) ++ str " " in
  let pp_hints = pr_list spc pr_rawhintref l in
  Feedback.msg_info  (pp_viewname ++ hov 0 pp_hints ++ Pp.cut ())

VERNAC COMMAND EXTEND PrintView CLASSIFIED AS QUERY
| [ "Print" "Hint" "View" ssrviewpos(i) ] ->
  [ match i with
    | Some k -> print_view_hints k (Ssrview.AdaptorDb.get k)
    | None ->
        List.iter (fun k -> print_view_hints k (Ssrview.AdaptorDb.get k))
          [ Ssrview.AdaptorDb.Forward;
            Ssrview.AdaptorDb.Backward;
            Ssrview.AdaptorDb.Equivalence ]
  ]
END

let glob_view_hints lvh =
  List.map (Constrintern.intern_constr (Global.env ()) (Evd.from_env (Global.env ()))) lvh

VERNAC COMMAND EXTEND HintView CLASSIFIED AS SIDEFF
  |  [ "Hint" "View" ssrviewposspc(n) ne_ssrhintref_list(lvh) ] ->
     [ let hints = glob_view_hints lvh in
       match n with
       | None ->
          Ssrview.AdaptorDb.declare Ssrview.AdaptorDb.Forward hints;
          Ssrview.AdaptorDb.declare Ssrview.AdaptorDb.Backward hints
       | Some k ->
          Ssrview.AdaptorDb.declare k hints ]
END

(* }}} *)

(** Canonical Structure alias *)

GEXTEND Gram
  GLOBAL: gallina_ext;

  gallina_ext:
      (* Canonical structure *)
     [[ IDENT "Canonical"; qid = Constr.global ->
          Vernacexpr.VernacCanonical (CAst.make @@ AN qid)
      | IDENT "Canonical"; ntn = Prim.by_notation ->
          Vernacexpr.VernacCanonical (CAst.make @@ ByNotation ntn)
      | IDENT "Canonical"; qid = Constr.global;
          d = G_vernac.def_body ->
          let s = coerce_reference_to_id qid in
    Vernacexpr.VernacDefinition
      ((Decl_kinds.NoDischarge,Decl_kinds.CanonicalStructure),
          ((CAst.make (Name s)),None), d)
  ]];
END

(** Keyword compatibility fixes. *)

(* Coq v8.1 notation uses "by" and "of" quasi-keywords, i.e., reserved *)
(* identifiers used as keywords. This is incompatible with ssreflect.v *)
(* which makes "by" and "of" true keywords, because of technicalities  *)
(* in the internal lexer-parser API of Coq. We patch this here by      *)
(* adding new parsing rules that recognize the new keywords.           *)
(*   To make matters worse, the Coq grammar for tactics fails to       *)
(* export the non-terminals we need to patch. Fortunately, the CamlP5  *)
(* API provides a backdoor access (with loads of Obj.magic trickery).  *)

(* Coq v8.3 defines "by" as a keyword, some hacks are not needed any   *)
(* longer and thus comment out. Such comments are marked with v8.3     *)

open Pltac

GEXTEND Gram
  GLOBAL: hypident;
  hypident: [
  [ "("; IDENT "type"; "of"; id = Prim.identref; ")" -> id, Locus.InHypTypeOnly
  | "("; IDENT "value"; "of"; id = Prim.identref; ")" -> id, Locus.InHypValueOnly
  ] ];
END

GEXTEND Gram
  GLOBAL: hloc;
hloc: [
  [ "in"; "("; "Type"; "of"; id = ident; ")" ->
    Tacexpr.HypLocation (CAst.make id, Locus.InHypTypeOnly)
  | "in"; "("; IDENT "Value"; "of"; id = ident; ")" ->
    Tacexpr.HypLocation (CAst.make id, Locus.InHypValueOnly)
  ] ];
END

GEXTEND Gram
  GLOBAL: constr_eval;
  constr_eval: [
    [ IDENT "type"; "of"; c = Constr.constr -> Genredexpr.ConstrTypeOf c ]
  ];
END

(* We wipe out all the keywords generated by the grammar rules we defined. *)
(* The user is supposed to Require Import ssreflect or Require ssreflect   *)
(* and Import ssreflect.SsrSyntax to obtain these keywords and as a         *)
(* consequence the extended ssreflect grammar.                             *)
let () = CLexer.set_keyword_state frozen_lexer ;;

(* vim: set filetype=ocaml foldmethod=marker: *)
