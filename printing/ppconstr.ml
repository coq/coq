(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open CErrors
open Util
open Pp
open CAst
open Names
open Libnames
open Pputils
open Ppextend
open Glob_term
open Constrexpr
open Constrexpr_ops
(*i*)

module Tag =
struct
  let keyword   = "constr.keyword"
  let evar      = "constr.evar"
  let univ      = "constr.type"
  let notation  = "constr.notation"
  let variable  = "constr.variable"
  let reference = "constr.reference"
  let path      = "constr.path"

end

let do_not_tag _ x = x
let tag t s = Pp.tag t s
let tag_keyword     = tag Tag.keyword
let tag_evar        = tag Tag.evar
let tag_type        = tag Tag.univ
let tag_unparsing   = function
  | UnpTerminal s -> tag Tag.notation
  | _ -> do_not_tag ()
let tag_constr_expr = do_not_tag
let tag_path = tag Tag.path
let tag_ref = tag Tag.reference
let tag_var = tag Tag.variable

let keyword s = tag_keyword (str s)
let sep_v = fun _ -> str"," ++ spc()
let pr_tight_coma () = str "," ++ cut ()

let latom = 0
let lprod = 200
let llambda = 200
let lif = 200
let lletin = 200
let lletpattern = 200
let lfix = 200
let lcast = 100
let larg = 9
let lapp = Notation.app_level
let lposint = 0
let lnegint = 35 (* must be consistent with Notation "- x" *)
let ltop = LevelLe 200
let lproj = 1
let ldelim = 1
let lcase_type = LevelLe 100
let lsimpleconstr = LevelLe 8
let lsimplepatt = LevelLe 1
let no_after = None

type flags = {
  parentheses : bool;
}

let of_extern_flags f = {
  parentheses = f.PrintingFlags.Extern.parentheses;
}

let current_flags () = of_extern_flags (PrintingFlags.Extern.current())

let of_printing_flags f = of_extern_flags f.PrintingFlags.extern

let overlap_right_left which s lev_after =
  let { notation_printing_unparsing = unpl } = find_notation_printing_rule which s in
  let rec aux = function
    | [] -> false
    | [UnpMetaVar subentry | UnpListMetaVar (subentry, _)] ->
      if Notationextern.notation_entry_eq subentry.notation_subentry InConstrEntry then
        Notation.may_capture_cont_after lev_after subentry.notation_relative_level
      else
        (* Handled in constextern.ml *)
        false
    | [UnpBox (b,sub)] -> aux (List.map snd sub)
    | (UnpMetaVar _ | UnpListMetaVar _ | UnpBinderMetaVar _
      | UnpBinderListMetaVar _ | UnpTerminal _ | UnpBox _ | UnpCut _) :: l -> aux l in
  aux unpl

let prec_of_prim_token = function
  | Number (NumTok.SPlus,_) -> lposint
  | Number (NumTok.SMinus,_) -> lnegint
  | String _ -> latom

let adjust_level ~flags side lev_after l_not prec =
  match side with
  | Some _ when flags.parentheses -> no_after, LevelLe 0
  | Some Right ->
    (if Notation.may_capture_cont_after lev_after prec then no_after else lev_after), prec
  | Some Left -> Some l_not, prec
  | None -> no_after,prec (* should we care about the separator being possibly empty? *)

let print_hunks ~flags l_not lev_after pr pr_patt pr_binders subst unps =
  let env = ref subst in
  let pop r = let a = List.hd !r in r := List.tl !r; a in
  let return unp pp1 pp2 = (tag_unparsing unp pp1) ++ pp2 in
  let pr_constr lev_after prec = function
    | NtnTypeArgConstr c -> pr lev_after prec c
    | NtnTypeArgPattern (c,bk) -> pr_patt prec NotQuotedPattern bk c
    | _ -> assert false in
  (* Warning:
     The following function enforces a very precise order of
     evaluation of sub-components.
     Do not modify it unless you know what you are doing! *)
  let rec aux = function
    | [] ->
      mt ()
    | UnpMetaVar {notation_relative_level = prec; notation_position = side} as unp :: l ->
      let lev_after, prec = adjust_level ~flags side lev_after l_not prec in
      let pp1 = match pop env with
        | NtnTypeArg c -> pr_constr lev_after prec c
        | _ -> assert false in
      let pp2 = aux l in
      return unp pp1 pp2
    | UnpBinderMetaVar (subentry,style) as unp :: l ->
      let c,bk = match pop env with
        | NtnTypeArg (NtnTypeArgPattern (c,bk)) -> c,bk
        | _ -> assert false in
      let pp2 = aux l in
      let pp1 = pr_patt subentry.notation_relative_level style bk c in
      return unp pp1 pp2
    | UnpListMetaVar ({notation_relative_level = prec; notation_position = side}, sl) as unp :: l ->
      let lev_after', prec' = adjust_level ~flags side lev_after l_not prec in
      let cl = match pop env with
        | NtnTypeArgList l -> List.map (function NtnTypeArg c -> c | _ -> assert false) l
        | _ -> assert false in
      let pp1 =
        match cl with
        | [] -> assert false
        | [c] -> pr_constr lev_after' prec' c
        | c1::cl ->
          let cn, cl = List.sep_last cl in
          pr_constr lev_after' prec c1 ++
          prlist (fun c -> aux sl ++ pr_constr (if List.is_empty sl then Some l_not else no_after) prec c) cl ++
          aux sl ++ pr_constr lev_after prec' cn in
      let pp2 = aux l in
      return unp pp1 pp2
    | UnpBinderListMetaVar (isopen, withquote, sl) as unp :: l ->
      let cl = match pop env with
        | NtnTypeArg (NtnTypeArgBinders cl) -> cl
        | _ -> assert false in
      let pp2 = aux l in
      let pp1 = pr_binders (fun () -> aux sl) isopen withquote cl in
      return unp pp1 pp2
    | UnpTerminal s as unp :: l ->
      let pp2 = aux l in
      let pp1 = str s in
      return unp pp1 pp2
    | UnpBox (b,sub) as unp :: l ->
      let pp1 = ppcmd_of_box b (aux (List.map snd sub)) in
      let pp2 = aux l in
      return unp pp1 pp2
    | UnpCut cut as unp :: l ->
      let pp2 = aux l in
      let pp1 = ppcmd_of_cut cut in
      return unp pp1 pp2
  in
  aux unps

let pr_notation ~flags lev_after pr pr_patt pr_binders which s env =
  let { notation_printing_unparsing = unpl; notation_printing_level = level } = find_notation_printing_rule which s in
  print_hunks ~flags level lev_after pr pr_patt pr_binders env unpl

let pr_delimiters depth key strm =
  let d = match depth with DelimOnlyTmpScope -> "%_" | DelimUnboundedScope -> "%" in
  strm ++ str (d^key)

let pr_generalization bk c =
  let hd, tl =
    match bk with
    | NonMaxImplicit -> "[", "]"
    | MaxImplicit -> "{", "}"
    | Explicit -> "(", ")"
  in (* TODO: syntax Abstraction Kind *)
  str "`" ++ str hd ++ c ++ str tl

let pr_com_at n =
  if not (Int.equal n 0) then comment (Pputils.extract_comments n)
  else mt()

let pr_with_comments ?loc pp = pr_located (fun x -> x) (loc, pp)

let pr_sep_com sep f c = pr_with_comments ?loc:(constr_loc c) (sep() ++ f c)

let pr_sort_name_expr = function
  | CSProp -> str "SProp"
  | CProp -> str "Prop"
  | CSet -> str "Set"
  | CType qid -> pr_qualid qid
  | CRawType s -> Univ.Level.raw_pr s

let pr_univ_level_expr = function
  | UNamed s -> tag_type (pr_sort_name_expr s)
  | UAnonymous {rigid=UnivRigid} -> tag_type (str "Type")
  | UAnonymous {rigid=UnivFlexible b} -> assert (not b); tag_type (str "_")

let pr_univ_expr (u,n) =
  tag_type (pr_sort_name_expr u) ++ (match n with 0 -> mt () | _ -> str"+" ++ int n)

let pr_univ l =
  match l with
  | UNamed [x] -> pr_univ_expr x
  | UNamed l -> str"max(" ++ prlist_with_sep (fun () -> str",") pr_univ_expr l ++ str")"
  | UAnonymous {rigid=UnivRigid} -> tag_type (str "Type")
  | UAnonymous {rigid=UnivFlexible _} -> tag_type (str "_")

let pr_quality_expr = function
  | CQAnon _ -> tag_type (str "_")
  | CQVar qid -> tag_type (pr_qualid qid)
  | CRawQuality q -> tag_type (Sorts.Quality.raw_pr q)
  | CQConstant q -> tag_type (Sorts.Quality.Constants.pr q)

let pr_relevance = function
  | CRelevant -> str "Relevant"
  | CIrrelevant -> str "Irrelevant"
  | CRelevanceVar q -> pr_quality_expr q

let pr_relevance_info = function
  | None -> mt()
  | Some r -> str "(* " ++ pr_relevance r ++ str " *) "

let pr_quality_univ (q, l) = match q with
  | None -> pr_univ l
  | Some q ->  pr_quality_expr q ++ spc() ++ str ";" ++ spc () ++ pr_univ l

let pr_univ_annot pr x = hov 2 (str "@{" ++ pr x ++ str "}")

let pr_sort_expr : sort_expr -> Pp.t = function
  | None, UNamed [CSProp, 0] -> tag_type (str "SProp")
  | None, UNamed [CProp, 0] -> tag_type (str "Prop")
  | None, UNamed [CSet, 0] -> tag_type (str "Set")
  | None, UAnonymous {rigid=UnivRigid} -> tag_type (str "Type")
  | u -> hov 0 (tag_type (str "Type") ++ pr_univ_annot pr_quality_univ u)

let pr_qualid sp =
  let (sl, id) = repr_qualid sp in
  let id = tag_ref (Id.print id) in
  let sl = match List.rev (DirPath.repr sl) with
    | [] -> mt ()
    | sl ->
      let pr dir = tag_path (Id.print dir) ++ str "." in
      prlist pr sl
  in
  sl ++ id

let pr_id = Id.print
let pr_qualid = pr_qualid
let pr_patvar = pr_id

let pr_inside_universe_instance (ql,ul) =
  (if List.is_empty ql then mt()
   else prlist_with_sep spc pr_quality_expr ql ++ strbrk " ; ")
  ++ prlist_with_sep spc pr_univ_level_expr ul

let pr_universe_instance l =
  pr_opt_no_spc (pr_univ_annot pr_inside_universe_instance) l

let pr_reference qid =
  if qualid_is_ident qid then tag_var (pr_id @@ qualid_basename qid)
  else pr_qualid qid

let pr_cref ref us =
  (* for some reason the hov 0 around an reference without univ instance makes printing worse *)
  if Option.has_some us then hov 0 (pr_reference ref ++ pr_universe_instance us)
  else pr_reference ref

let pr_expl_args pr lev_after (a,expl) =
  match expl with
  | None -> pr lev_after (LevelLt lapp) a
  | Some {v=pos} ->
    let pr_pos = function
      | ExplByName id -> pr_id id
      | ExplByPos p -> int p in
    str "(" ++ pr_pos pos ++ str ":=" ++ pr no_after ltop a ++ str ")"

let is_anonymous_hole = function
  | Some (GNamedHole _) -> false
  | _ -> true

let pr_opt_type_spc pr = function
  | { CAst.v = CHole h } when is_anonymous_hole h -> mt ()
  | t ->  str " :" ++ pr_sep_com (fun()->brk(1,4)) (pr no_after ltop) t

let pr_prim_token = function
  | Number n -> NumTok.Signed.print n
  | String s -> qs s

let pr_evar pr id l =
  hov 0 (
    tag_evar (str "?" ++ pr_lident id) ++
    (match l with
     | [] -> mt()
     | l ->
       let f (id,c) = pr_lident id ++ str ":=" ++ pr no_after ltop c in
       str"@{" ++ hov 0 (prlist_with_sep pr_semicolon f (List.rev l)) ++ str"}"))

(* Assuming "{" and "}" brackets, prints
   - if there is enough room
     { a; b; c }
   - otherwise
     {
      a;
      b;
      c
     }
     Alternatively, replace outer hv with h to get instead:
     { a;
       b;
       c }
     Replace the inner hv with hov to respectively get instead (if enough room):
     {
      a; b;
      c
     }
     or
     { a; b;
       c }
*)
let pr_record_default = function
  | None -> mt()
  | Some def -> def ++ str " with" ++ spc()

let pr_record left right def pr = function
  | [] -> assert (Option.is_empty def); str left ++ str " " ++ str right
  | l ->
    hv 0 (
      str left ++
      brk (1,String.length left) ++
      pr_record_default def ++
      hv 0 (prlist_with_sep pr_semicolon pr l) ++
      brk (1,0) ++
      str right)

let pr_record_body left right pr def l =
  let pr_defined_field (id, c) = hov 2 (pr_reference id ++ str" :=" ++ pr c) in
  pr_record left right def pr_defined_field l

let las = lapp
let lpator = 0
let lpatrec = 0
let lpatcast = LevelLe 100
let lpattop = LevelLe 200

let rec pr_patt_args ~flags pr lev_after args =
  match args with
  | [] -> mt ()
  | args ->
    let last, args = List.sep_last args in
    prlist (pr_patt ~flags spc pr (Some lapp) (LevelLt lapp)) args ++ pr_patt ~flags spc pr lev_after (LevelLt lapp) last

and pr_patt ~flags sep pr lev_after inh p =
  let return cmds prec =
    let no_surround = Notation.prec_less prec inh in
    let lev_after = if no_surround then lev_after else no_after in
    let pp = cmds lev_after in
    let pp = if no_surround then pp else surround pp in
    pr_with_comments ?loc:p.CAst.loc (sep() ++ pp) in
  match CAst.(p.v) with
  | CPatRecord l ->
    return (fun lev_after -> pr_record_body "{|" "|}" (pr_patt ~flags spc pr no_after lpattop) None l) lpatrec

  | CPatAlias (p, na) ->
    return (fun lev_after -> pr_patt ~flags mt pr lev_after (LevelLe las) p ++ str " as " ++ pr_lname na) las

  | CPatCstr (c, None, []) ->
    return (fun lev_after -> pr_reference c) latom

  | CPatCstr (c, None, args) ->
    return (fun lev_after -> pr_reference c ++ pr_patt_args ~flags pr lev_after args) lapp

  | CPatCstr (c, Some args, []) ->
    return (fun lev_after -> str "@" ++ pr_reference c ++ pr_patt_args ~flags pr lev_after args) lapp

  | CPatCstr (c, Some expl_args, extra_args) ->
    return (fun lev_after ->
        surround (str "@" ++ pr_reference c ++ pr_patt_args ~flags pr lev_after expl_args)
        ++ pr_patt_args ~flags pr lev_after extra_args) lapp

  | CPatAtom (None) ->
    return (fun lev_after -> str "_") latom

  | CPatAtom (Some r) ->
    return (fun lev_after -> pr_reference r) latom

  | CPatOr pl ->
    return (fun lev_after ->
        let pp p = hov 0 (pr_patt ~flags mt pr lev_after lpattop p) in
        surround (hov 0 (prlist_with_sep pr_spcbar pp pl))) lpator

  | CPatNotation (_,{ntn_key = "( _ )"},[NtnTypeArg (NtnTypeArgPattern (p,_bk))],[]) ->
    return (fun lev_after -> pr_patt ~flags (fun()->str"(") pr no_after lpattop p ++ str")") latom

  | CPatNotation (which,s,l,args) ->
    let l_not = (find_notation_printing_rule which s).notation_printing_level in
    let no_inner_surrounding = List.is_empty args || Notation.prec_less l_not (LevelLt lapp) in
    return (fun lev_after ->
        let lev_after' = if no_inner_surrounding then lev_after else no_after in
        let strm_not = pr_notation ~flags lev_after pr (pr_patt_binder ~flags pr) (fun _ _ _ _ -> assert false) which s l in
        (if List.is_empty args then strm_not else
         if overlap_right_left which s lev_after then surround strm_not else
         if Notation.prec_less l_not (LevelLt lapp) then strm_not else
           surround strm_not)
        ++ pr_patt_args ~flags pr lev_after' args)
      (if not (List.is_empty args) then lapp else if no_inner_surrounding then l_not else latom)

  | CPatPrim p ->
    return (fun lev_after -> pr_prim_token p) latom

  | CPatDelimiters (depth,k,p) ->
    return (fun lev_after -> pr_delimiters depth k (pr_patt ~flags mt pr (Some 1) lsimplepatt p)) 1

  | CPatCast (p,t) ->
    return (fun lev_after -> pr_patt ~flags mt pr (Some 1) lpatcast p ++ spc () ++ str ":" ++ ws 1 ++ pr lev_after (LevelLe lprod) t) 1

and pr_patt_binder ~flags pr prec style bk c =
  match bk with
  | MaxImplicit -> str "{" ++ pr_patt ~flags mt pr no_after lpattop c ++ str "}"
  | NonMaxImplicit -> str "[" ++ pr_patt ~flags mt pr no_after lpattop c ++ str "]"
  | Explicit ->
    match style, c with
    | NotQuotedPattern, _ | _, {v=CPatAtom _} -> pr_patt ~flags mt pr no_after prec c
    | QuotedPattern, _ -> str "'" ++ pr_patt ~flags mt pr no_after prec c

let pr_patt ~flags = pr_patt ~flags mt

let pr_eqn ~flags pr {loc;v=(pl,rhs)} =
  spc() ++ hov 4
    (pr_with_comments ?loc
       (str "| " ++
        hov 0 (prlist_with_sep pr_spcbar
                 (fun p -> hov 0 (prlist_with_sep sep_v (pr_patt ~flags pr no_after ltop) p)) pl
               ++ str " =>") ++
        pr_sep_com spc (pr no_after ltop) rhs))

let begin_of_binder l_bi =
  let b_loc l = fst (Option.cata Loc.unloc (0,0) l) in
  match l_bi with
  | CLocalDef({loc},_,_,_) -> b_loc loc
  | CLocalAssum({loc}::_,_,_,_) -> b_loc loc
  | CLocalPattern{loc} -> b_loc loc
  | _ -> assert false

let begin_of_binders = function
  | b::_ -> begin_of_binder b
  | _ -> 0

let surround_impl k p =
  match k with
  | Explicit -> str"(" ++ p ++ str")"
  | NonMaxImplicit -> str"[" ++ p ++ str"]"
  | MaxImplicit -> str"{" ++ p ++ str"}"

let surround_implicit k p =
  match k with
  | Explicit -> p
  | NonMaxImplicit -> str"[" ++ p ++ str"]"
  | MaxImplicit -> (str"{" ++ p ++ str"}")

let pr_binder many pr (nal,r,k,t) =
  let r = pr_relevance_info r in
  match k with
  | Generalized (b', t') ->
    begin match nal with
    |[{loc; v=Anonymous}] ->
      hov 1 (str"`" ++ (surround_impl b'
                          (r ++ (if t' then str "!" else mt ()) ++ pr t)))
    |[{loc; v=Name id}] ->
      hov 1 (str "`" ++ (surround_impl b'
                           (pr_lident CAst.(make ?loc id) ++ str " : " ++ r ++
                            (if t' then str "!" else mt()) ++ pr t)))
    |_ -> anomaly (Pp.str "List of generalized binders have always one element.")
    end
  | Default b ->
    match t with
    | { CAst.v = CHole h } when is_anonymous_hole h ->
      let s = prlist_with_sep spc pr_lname nal in
      hov 1 (r ++ surround_implicit b s)
    | _ ->
      let s = prlist_with_sep spc pr_lname nal ++ str " : " ++ r ++ pr t in
      hov 1 (if many then surround_impl b s else surround_implicit b s)

let pr_binder_among_many ~flags withquote pr_c = function
  | CLocalAssum (nal,r,k,t) ->
    pr_binder true (pr_c no_after ltop) (nal,r,k,t)
  | CLocalDef (na,r,c,topt) ->
    surround (pr_lname na ++ pr_relevance_info r ++
              pr_opt_no_spc (fun t -> str " :" ++ ws 1 ++ pr_c no_after ltop t) topt ++
              str" :=" ++ spc() ++ pr_c no_after ltop c)
  | CLocalPattern p ->
    str (if withquote then "'" else "") ++ pr_patt ~flags pr_c no_after lsimplepatt p

let pr_undelimited_binders ~flags sep withquote pr_c =
  prlist_with_sep sep (pr_binder_among_many ~flags withquote pr_c)

let pr_delimited_binders ~flags kw sep withquote pr_c bl =
  let n = begin_of_binders bl in
  match bl with
  | [CLocalAssum (nal,r,k,t)] ->
    kw n ++ pr_binder false (pr_c no_after ltop) (nal,r,k,t)
  | (CLocalAssum _ | CLocalPattern _ | CLocalDef _) :: _ as bdl ->
    kw n ++ pr_undelimited_binders ~flags sep withquote pr_c bdl
  | [] -> anomaly (Pp.str "The ast is malformed, found lambda/prod without proper binders.")

let pr_binders_gen ~flags pr_c sep is_open withquote =
  if is_open then pr_delimited_binders ~flags pr_com_at sep withquote pr_c
  else pr_undelimited_binders ~flags sep withquote pr_c

let pr_recursive_decl ~flags pr pr_dangling lev_after kw dangling_with_for id bl annot t c =
  let pr_body =
    if dangling_with_for then pr_dangling else pr in
  hov 0 (str kw ++ brk(1,2) ++ pr_id id ++ (if bl = [] then mt () else brk(1,2)) ++
         hov 0 (pr_undelimited_binders ~flags spc true pr bl ++ annot) ++
         pr_opt_type_spc pr t ++ str " :=") ++
  pr_sep_com (fun () -> brk(1,2)) (pr_body lev_after ltop) c

let pr_guard_annot pr_aux bl ro =
  match ro with
  | None -> mt ()
  | Some {loc; v = ro} ->
    match ro with
    | CStructRec { v = id } ->
      let names_of_binder = function
        | CLocalAssum (nal,_,_,_) -> nal
        | CLocalDef (_,_,_,_) -> []
        | CLocalPattern _ -> assert false
      in let ids = List.flatten (List.map names_of_binder bl) in
      if List.length ids > 1 then
        spc() ++ str "{" ++ keyword "struct" ++ brk (1,1) ++ pr_id id ++ str"}"
      else mt()
    | CWfRec (id,c) ->
      spc() ++ str "{" ++ keyword "wf" ++ brk (1,1) ++ pr_aux c ++ brk (1,1) ++ pr_lident id ++ str"}"
    | CMeasureRec (id,m,r) ->
      spc() ++ str "{" ++ keyword "measure" ++ brk (1,1) ++ pr_aux m ++
      match id with None -> mt() | Some id -> brk (1,1) ++ pr_lident id ++
                                              (match r with None -> mt() | Some r -> str" on " ++ pr_aux r) ++ str"}"

let pr_fixdecl ~flags pr prd lev_after kw dangling_with_for ({v=id},_,ro,bl,t,c) =
  let annot = pr_guard_annot (pr no_after lsimpleconstr) bl ro in
  pr_recursive_decl ~flags pr prd lev_after kw dangling_with_for id bl annot t c

let pr_cofixdecl ~flags pr prd lev_after kw dangling_with_for ({v=id},_,bl,t,c) =
  pr_recursive_decl ~flags pr prd lev_after kw dangling_with_for id bl (mt()) t c

let pr_recursive lev_after kw pr_decl id = function
  | [] -> anomaly (Pp.str "(co)fixpoint with no definition.")
  | [d1] -> pr_decl lev_after kw false d1
  | d1::dl ->
    pr_decl no_after kw true d1 ++ fnl() ++
    prlist_with_sep (fun () -> fnl())
      (pr_decl no_after "with" true) dl ++
    fnl() ++ keyword "for" ++ spc () ++ pr_id id

let pr_as_in ~flags pr na indnalopt =
  (match na with (* Decision of printing "_" or not moved to constrextern.ml *)
   | Some na -> spc () ++ keyword "as" ++ spc () ++  pr_lname na
   | None -> mt ()) ++
  (match indnalopt with
   | None -> mt ()
   | Some t -> spc () ++ keyword "in" ++ spc () ++ pr_patt ~flags pr no_after ltop t)

let pr_case_item ~flags pr (tm,as_clause, in_clause) =
  hov 0 (pr no_after (LevelLe lcast) tm ++ pr_as_in ~flags pr as_clause in_clause)

let pr_case_type pr po =
  match po with
  | None -> mt ()
  | Some { CAst.v = CHole h } when is_anonymous_hole h -> mt()
  | Some p ->
    spc() ++ hov 2 (keyword "return" ++ pr_sep_com spc (pr no_after lcase_type) p)

let pr_simple_return_type pr na po =
  (match na with
   | Some {v=Name id} ->
     spc () ++ keyword "as" ++ spc () ++ pr_id id
   | _ -> mt ()) ++
  pr_case_type pr po

let pr_proj pr pr_app a f l =
  hov 0 (pr (Some lproj) (LevelLe lproj) a ++ cut() ++ str ".(" ++ pr_app pr no_after f l ++ str ")")

let pr_appexpl pr lev_after (f,us) l =
  let pargs = match l with
    | [] -> mt ()
    | args ->
      let last, l = List.sep_last l in
      prlist (pr_sep_com spc (pr (Some lapp) (LevelLt lapp))) l ++
      pr_sep_com spc (pr lev_after (LevelLt lapp)) last in
  hov 2 (
    str "@" ++ pr_reference f ++
    pr_universe_instance us ++ pargs)

let pr_app pr lev_after a l =
  let pargs = match l with
    | [] -> mt ()
    | args ->
      let last, l = List.sep_last l in
      prlist (fun a -> spc () ++ pr_expl_args pr (Some lapp) a) l ++
      spc () ++ pr_expl_args pr lev_after last in
  hov 2 (pr (Some lapp) (LevelLt lapp) a ++ pargs)

let pr_forall n = keyword "forall" ++ pr_com_at n ++ spc ()

let pr_fun n = keyword "fun" ++ pr_com_at n ++ spc ()

let pr_fun_sep = str " =>"

let pr_dangling_with_for sep pr lev_after inherited a =
  match a.v with
  | (CFix (_,[_])|CCoFix(_,[_])) ->
    pr sep lev_after (LevelLe latom) a
  | _ ->
    pr sep lev_after inherited a

let pr_cast = let open Constr in function
    | Some DEFAULTcast -> str ":"
    | Some VMcast-> str "<:"
    | Some NATIVEcast -> str "<<:"
    | None -> str ":>"

type raw_or_glob_genarg =
  | Rawarg of GenConstr.raw
  | Globarg of GenConstr.glb

let pr_genarg return arg =
  (* In principle this may use the env/sigma, in practice not sure if it
     does except through pr_constr_expr in beautify mode. *)
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let name, parg =
    match arg with
    | Globarg (Glb (tag, _) as arg) ->
      GenConstr.repr tag, Genprint.glb_print_constr arg
    | Rawarg (Raw (tag, _) as arg) ->
      GenConstr.repr tag, Genprint.raw_print_constr arg
  in
  let parg = match parg with
    | PrinterBasic pp -> pp env sigma
    | PrinterNeedsLevel { default_already_surrounded = level; printer } ->
      printer env sigma level
  in
  let name =
    (* cheat the name system
       there should be a better way to handle this *)
    if String.equal name "ltac_in_term" then "ltac"
    else if String.equal name "ltac2:in-constr" then "ltac2"
    else if String.equal name "ltac2:quotation" then ""
    else name
  in
  let pp = if String.is_empty name then parg else hov 2 (str name ++ str ":(" ++ parg ++ str ")") in
  return (fun _ -> pp) latom

let pr ~flags pr sep lev_after inherited a =
  let return cmds prec =
    let no_surround = Notation.prec_less prec inherited in
    let lev_after = if no_surround then lev_after else no_after in
    let pp = tag_constr_expr a (cmds lev_after) in
    let pp = if no_surround then pp else surround pp in
    pr_with_comments ?loc:a.CAst.loc (sep() ++ pp) in
  match CAst.(a.v) with
  | CRef (r, us) ->
    return (fun _ -> pr_cref r us) latom
  | CFix (id,fix) ->
    return (fun lev_after ->
        hv 0 (pr_recursive lev_after "fix"
                (pr_fixdecl ~flags (pr mt) (pr_dangling_with_for mt pr)) id.v fix))
      lfix
  | CCoFix (id,cofix) ->
    return (fun lev_after ->
        hv 0 (pr_recursive lev_after "cofix"
                (pr_cofixdecl ~flags (pr mt) (pr_dangling_with_for mt pr)) id.v cofix))
      lfix
  | CProdN (bl,a) ->
    return (fun lev_after ->
        hov 0 (
          hov 2 (pr_delimited_binders ~flags pr_forall spc true
                   (pr mt) bl) ++
          str "," ++ pr spc lev_after ltop a))
      lprod
  | CLambdaN (bl,a) ->
    return (fun lev_after ->
        hov 0 (
          hov 2 (pr_delimited_binders ~flags pr_fun spc true
                   (pr mt) bl) ++
          pr_fun_sep ++ pr spc lev_after ltop a))
      llambda
  | CLetIn ({v=Name x}, ({ v = CFix({v=x'},[_])}
                        |  { v = CCoFix({v=x'},[_]) } as fx), t, b)
    when Id.equal x x' ->
    return (fun lev_after ->
        hv 0 (
          hov 2 (keyword "let" ++ spc () ++ pr mt no_after ltop fx
                 ++ spc ()
                 ++ keyword "in") ++
          pr spc lev_after ltop b))
      lletin
  | CLetIn (x,a,t,b) ->
    return (fun lev_after ->
        hv 0 (
          hov 2 (keyword "let" ++ spc () ++ pr_lname x
                 ++ pr_opt_no_spc (fun t -> str " :" ++ ws 1 ++ pr mt no_after ltop t) t
                 ++ str " :=" ++ pr spc no_after ltop a ++ spc ()
                 ++ keyword "in") ++
          pr spc lev_after ltop b))
      lletin
  | CProj (true,(f,us),l,c) ->
    let l = List.map (function (c,None) -> c | _ -> assert false) l in
    return (fun lev_after -> pr_proj (pr mt) pr_appexpl c (f,us) l) lproj
  | CProj (false,(f,us),l,c) ->
    return (fun lev_after -> pr_proj (pr mt) pr_app c (CAst.make (CRef (f,us))) l) lproj
  | CAppExpl ((qid,us),[t])
  | CApp ({v = CRef(qid,us)},[t,None])
    when qualid_is_ident qid && Id.equal (qualid_basename qid) Notation_ops.ldots_var ->
    return (fun lev_after ->
        hov 0 (str ".." ++ pr spc no_after (LevelLe latom) t ++ spc () ++ str ".."))
      larg
  | CAppExpl ((f,us),l) ->
    return (fun lev_after -> pr_appexpl (pr mt) lev_after (f,us) l) lapp
  | CApp (a,l) ->
    return (fun lev_after -> pr_app (pr mt) lev_after a l) lapp
  | CRecord (def,l) ->
    let def = Option.map (pr mt no_after (LevelLe lproj)) def in
    return (fun lev_after -> pr_record_body "{|" "|}" (pr spc no_after ltop) def l) latom
  | CCases (Constr.LetPatternStyle,rtntypopt,[c,as_clause,in_clause],[{v=([[p]],b)}]) ->
    return (fun lev_after ->
        hv 0 (
          keyword "let" ++ spc () ++ str"'" ++
          hov 0 (pr_patt ~flags (pr mt) no_after ltop p ++
                 pr_as_in ~flags (pr mt) as_clause in_clause ++
                 str " :=" ++ pr spc no_after ltop c ++
                 pr_case_type (pr_dangling_with_for mt pr) rtntypopt ++
                 spc () ++ keyword "in" ++ pr spc lev_after ltop b)))
      lletpattern
  | CCases(Constr.IfStyle,rtntypopt,[c,as_clause,in_clause],[{v=([[p]],b1)};{v=(_,b2)}]) ->
    return (fun lev_after ->
        hv 0 (
          hov 1 (keyword "if" ++ spc () ++ pr mt no_after ltop c
                 ++ pr_as_in ~flags (pr mt) as_clause in_clause
                 ++ spc () ++ keyword "is" ++ spc ()
                 ++ pr_patt ~flags (pr mt) no_after ltop p) ++
          spc () ++
          hov 0 (keyword "then"
                 ++ pr (fun () -> brk (1,1)) no_after ltop b1) ++ spc () ++
          hov 0 (keyword "else" ++ pr (fun () -> brk (1,1)) lev_after ltop b2)))
      lif
  | CCases(_,rtntypopt,c,eqns) ->
    return (fun lev_after ->
        v 0
          (hv 0 (keyword "match" ++ brk (1,2) ++
                 hov 0 (
                   prlist_with_sep sep_v
                     (pr_case_item ~flags (pr_dangling_with_for mt pr)) c
                   ++ pr_case_type (pr_dangling_with_for mt pr) rtntypopt) ++
                 spc () ++ keyword "with") ++
           prlist (pr_eqn ~flags (pr mt)) eqns ++ spc()
           ++ keyword "end"))
      latom
  | CLetTuple (nal,(na,po),c,b) ->
    return (fun lev_after ->
        hv 0 (
          hov 2 (keyword "let" ++ spc () ++
                 hov 1 (str "(" ++
                        prlist_with_sep sep_v pr_lname nal ++
                        str ")" ++
                        pr_simple_return_type (pr mt) na po ++ str " :=") ++
                 pr spc no_after ltop c
                 ++ keyword " in") ++
          pr spc lev_after ltop b))
      lletin
  | CIf (c,(na,po),b1,b2) ->
    (* On force les parenthèses autour d'un "if" sous-terme (même si le
       parsing est lui plus tolérant) *)
    return (fun lev_after ->
        hv 0 (
          hov 1 (keyword "if" ++ spc () ++ pr mt no_after ltop c
                 ++ pr_simple_return_type (pr mt) na po) ++
          spc () ++
          hov 0 (keyword "then"
                 ++ pr (fun () -> brk (1,1)) no_after ltop b1) ++ spc () ++
          hov 0 (keyword "else" ++ pr (fun () -> brk (1,1)) lev_after ltop b2)))
      lif
  | CHole (Some (GNamedHole (false, id))) ->
    return (fun lev_after -> str "?[" ++ pr_id id ++ str "]") latom
  | CHole (Some (GNamedHole (true, id))) ->
    return (fun lev_after -> str "?[?" ++ pr_id id ++ str "]") latom
  | CHole _ -> return (fun lev_after -> str "_") latom
  | CGenarg arg -> pr_genarg return (Rawarg arg)
  | CGenargGlob arg -> pr_genarg return (Globarg arg)
  | CEvar (n,l) ->
    return (fun lev_after -> pr_evar (pr mt) n l) latom
  | CPatVar p ->
    return (fun lev_after -> str "@?" ++ pr_patvar p) latom
  | CSort s ->
    return (fun lev_after -> pr_sort_expr s) latom
  | CCast (a,k,b) ->
    return (fun lev_after ->
        hv 0 (pr mt no_after (LevelLt lcast) a ++ spc () ++
              (pr_cast k) ++ ws 1 ++ pr mt lev_after (LevelLe lprod) b))
      lcast
  | CNotation (_,{ntn_key = "( _ )"},[NtnTypeArg (NtnTypeArgConstr t)]) ->
    return (fun lev_after -> pr (fun()->str"(") no_after ltop t ++ str")") latom
  | CNotation (which,s,env) ->
    let l_not = (find_notation_printing_rule which s).notation_printing_level in
    let l_not = if overlap_right_left which s lev_after then max_int else l_not in
    return (fun lev_after -> pr_notation ~flags lev_after (pr mt) (pr_patt_binder ~flags (pr mt)) (pr_binders_gen ~flags (pr mt)) which s env) l_not
  | CGeneralization (bk,c) ->
    return (fun lev_after -> pr_generalization bk (pr mt no_after ltop c)) latom
  | CPrim p ->
    return (fun lev_after ->pr_prim_token p) (prec_of_prim_token p)
  | CDelimiters (depth,sc,a) ->
    return (fun lev_after -> pr_delimiters depth sc (pr mt (Some ldelim) (LevelLe ldelim) a)) ldelim
  | CArray(u, t,def,ty) ->
    return (fun lev_after ->
        hov 0 (str "[| " ++ prvect_with_sep (fun () -> str "; ") (pr mt no_after ltop) t ++
               (if not (Array.is_empty t) then str " " else mt()) ++
               str "|" ++ spc() ++ pr mt no_after ltop def ++ pr_opt_type_spc (pr mt) ty ++
               str " |]" ++ pr_universe_instance u)) 0

type term_pr = {
  pr_constr_expr   : flags:flags -> Environ.env -> Evd.evar_map -> constr_expr -> Pp.t;
  pr_lconstr_expr  : flags:flags -> Environ.env -> Evd.evar_map -> constr_expr -> Pp.t;
  pr_constr_pattern_expr  : flags:flags -> Environ.env -> Evd.evar_map -> constr_pattern_expr -> Pp.t;
  pr_lconstr_pattern_expr : flags:flags -> Environ.env -> Evd.evar_map -> constr_pattern_expr -> Pp.t
}

let modular_constr_pr = pr

let rec pr ~flags sep lev_after inherited a : Pp.t =
  modular_constr_pr ~flags (pr ~flags) sep lev_after inherited a

let pr ~flags lev_after inherited a : Pp.t = pr ~flags mt lev_after inherited a

let pr ~flags lev_after prec = function
  (* A toplevel printer hack mimicking parsing, incidentally meaning
     that we cannot use [pr] correctly anymore in a recursive loop
     if the current expr is followed by other exprs which would be
     interpreted as arguments *)
  | { CAst.v = CAppExpl ((f,us),[]) } -> str "@" ++ pr_cref f us
  | c -> pr ~flags lev_after prec c

let pr_expr ~flags env sigma lev_after prec c =
  pr ~flags lev_after prec c

let pr_simpleconstr_env ~flags env sigma c = pr_expr ~flags env sigma no_after lsimpleconstr c
let pr_top_env ~flags env sigma = pr_expr ~flags env sigma no_after ltop

let default_term_pr = {
  pr_constr_expr   = pr_simpleconstr_env;
  pr_lconstr_expr  = pr_top_env;
  pr_constr_pattern_expr  = pr_simpleconstr_env;
  pr_lconstr_pattern_expr = pr_top_env;
}

let term_pr = ref default_term_pr

let set_term_pr = (:=) term_pr

let pr_simpleconstr = pr no_after lsimpleconstr
let pr_top = pr no_after ltop

let pr_constr_expr_n ~flags env sigma n c : Pp.t = pr_expr ~flags env sigma no_after n c
let pr_constr_expr ~flags env sigma c : Pp.t = !term_pr.pr_constr_expr ~flags env sigma c
let pr_lconstr_expr ~flags env sigma c : Pp.t = !term_pr.pr_lconstr_expr ~flags env sigma c
let pr_constr_pattern_expr ~flags env sigma c : Pp.t = !term_pr.pr_constr_pattern_expr ~flags env sigma c
let pr_lconstr_pattern_expr ~flags env sigma c : Pp.t = !term_pr.pr_lconstr_pattern_expr ~flags env sigma c

let pr_cases_pattern_expr ~flags c : Pp.t = pr_patt ~flags (pr ~flags) no_after ltop c

let pr_binders ~flags env sigma l : Pp.t = pr_undelimited_binders ~flags spc true (pr_expr ~flags env sigma) l

module CompactedDecl = struct
  type t =
    | LocalAssum of (Environ.var_status option * Id.t EConstr.binder_annot) list * EConstr.types
    | LocalDef of (Environ.var_status option * Id.t EConstr.binder_annot) list * EConstr.constr * EConstr.types

  let of_named_decl status = function
    | Context.Named.Declaration.LocalAssum (id,t) ->
      LocalAssum ([status,id], t)
    | Context.Named.Declaration.LocalDef (id,v,t) ->
      LocalDef ([status,id], v, t)

  let to_tuple = function
    | LocalAssum (ids, t) -> List.map snd ids, None, t
    | LocalDef (ids, b, t) -> List.map snd ids, Some b, t
end

let compact_named_context sigma sign =
  let module NamedDecl = Context.Named.Declaration in
  let compact l status decl =
    match decl, l with
    | NamedDecl.LocalAssum (i,t), [] ->
      [CompactedDecl.LocalAssum ([Some status,i],t)]
    | NamedDecl.LocalDef (i,c,t), [] ->
      [CompactedDecl.LocalDef ([Some status,i],c,t)]
    | NamedDecl.LocalAssum (i1,t1), CompactedDecl.LocalAssum (li,t2) :: q ->
      if EConstr.eq_constr sigma t1 t2
      then CompactedDecl.LocalAssum ((Some status, i1)::li, t2) :: q
      else CompactedDecl.LocalAssum ([Some status, i1],t1) :: CompactedDecl.LocalAssum (li,t2) :: q
    | NamedDecl.LocalDef (i1,c1,t1), CompactedDecl.LocalDef (li,c2,t2) :: q ->
      if EConstr.eq_constr sigma c1 c2 && EConstr.eq_constr sigma t1 t2
      then CompactedDecl.LocalDef ((Some status, i1)::li, c2, t2) :: q
      else CompactedDecl.LocalDef ([Some status, i1],c1,t1) :: CompactedDecl.LocalDef (li,c2,t2) :: q
    | NamedDecl.LocalAssum (i,t), q ->
      CompactedDecl.LocalAssum ([Some status,i],t) :: q
    | NamedDecl.LocalDef (i,c,t), q ->
      CompactedDecl.LocalDef ([Some status,i],c,t) :: q
  in
  let ctx = EConstr.fold_named_context_val (fun _ status d acc -> compact acc status d) sign ~init:[] in
  List.map (function
      | CompactedDecl.LocalAssum (ids, t) -> CompactedDecl.LocalAssum (List.rev ids, t)
      | CompactedDecl.LocalDef (ids, a, b) -> CompactedDecl.LocalDef (List.rev ids, a, b))
    ctx
