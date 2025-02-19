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
let lsimpleconstr = LevelLe 8
let lsimplepatt = LevelLe 1
let no_after = None

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

let adjust_level side lev_after l_not prec =
  match side with
  | Some _ when !Constrextern.print_parentheses -> no_after, LevelLe 0
  | Some Right ->
    (if Notation.may_capture_cont_after lev_after prec then no_after else lev_after), prec
  | Some Left -> Some l_not, prec
  | None -> no_after,prec (* should we care about the separator being possibly empty? *)

let print_hunks l_not lev_after pr pr_patt pr_binders (terms, termlists, binders, binderlists) unps =
  let env = ref terms and envlist = ref termlists and bl = ref binders and bll = ref binderlists in
  let pop r = let a = List.hd !r in r := List.tl !r; a in
  let return unp pp1 pp2 = (tag_unparsing unp pp1) ++ pp2 in
  (* Warning:
     The following function enforces a very precise order of
     evaluation of sub-components.
     Do not modify it unless you know what you are doing! *)
  let rec aux = function
    | [] ->
      mt ()
    | UnpMetaVar {notation_relative_level = prec; notation_position = side} as unp :: l ->
      let c = pop env in
      let pp2 = aux l in
      let lev_after, prec = adjust_level side lev_after l_not prec in
      let pp1 = pr lev_after prec c in
      return unp pp1 pp2
    | UnpBinderMetaVar (subentry,style) as unp :: l ->
      let c,bk = pop bl in
      let pp2 = aux l in
      let pp1 = pr_patt subentry.notation_relative_level style bk c in
      return unp pp1 pp2
    | UnpListMetaVar ({notation_relative_level = prec; notation_position = side}, sl) as unp :: l ->
      let lev_after', prec' = adjust_level side lev_after l_not prec in
      let pp1 =
        match pop envlist with
        | [] -> assert false
        | [c] -> pr lev_after' prec' c
        | c1::cl ->
          let cn, cl = List.sep_last cl in
          pr lev_after' prec c1 ++
          prlist (fun c -> aux sl ++ pr (if List.is_empty sl then Some l_not else no_after) prec c) cl ++
          aux sl ++ pr lev_after prec' cn in
      let pp2 = aux l in
      return unp pp1 pp2
    | UnpBinderListMetaVar (isopen, withquote, sl) as unp :: l ->
      let cl = pop bll in
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

let pr_notation lev_after pr pr_patt pr_binders which s env =
  let { notation_printing_unparsing = unpl; notation_printing_level = level } = find_notation_printing_rule which s in
  print_hunks level lev_after pr pr_patt pr_binders env unpl

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
  if !Flags.beautify && not (Int.equal n 0) then comment (Pputils.extract_comments n)
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

let pr_qvar_expr = function
  | CQAnon _ -> tag_type (str "_")
  | CQVar qid -> tag_type (pr_qualid qid)
  | CRawQVar q -> tag_type (Sorts.QVar.raw_pr q)

let pr_relevance = function
  | CRelevant -> str "Relevant"
  | CIrrelevant -> str "Irrelevant"
  | CRelevanceVar q -> pr_qvar_expr q

let pr_relevance_info = function
  | None -> mt()
  | Some r -> str "(* " ++ pr_relevance r ++ str " *) "

let pr_quality_expr q = match q with
  | CQConstant q -> tag_type (Sorts.Quality.Constants.pr q)
  | CQualVar q -> pr_qvar_expr q

let pr_quality_univ (q, l) = match q with
  | None -> pr_univ l
  | Some q ->  pr_qvar_expr q ++ spc() ++ str "|" ++ spc () ++ pr_univ l

let pr_univ_annot pr x = str "@{" ++ pr x ++ str "}"

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
   else prlist_with_sep spc pr_quality_expr ql ++ strbrk " | ")
  ++ prlist_with_sep spc pr_univ_level_expr ul

let pr_universe_instance l =
  pr_opt_no_spc (pr_univ_annot pr_inside_universe_instance) l

let pr_reference qid =
  if qualid_is_ident qid then tag_var (pr_id @@ qualid_basename qid)
  else pr_qualid qid

let pr_cref ref us =
  pr_reference ref ++ pr_universe_instance us

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
let pr_record left right pr = function
  | [] -> str left ++ str " " ++ str right
  | l ->
    hv 0 (
      str left ++
      brk (1,String.length left) ++
      hv 0 (prlist_with_sep pr_semicolon pr l) ++
      brk (1,0) ++
      str right)

let pr_record_body left right pr l =
  let pr_defined_field (id, c) = hov 2 (pr_reference id ++ str" :=" ++ pr c) in
  pr_record left right pr_defined_field l

let las = lapp
let lpator = 0
let lpatrec = 0
let lpatcast = LevelLe 100
let lpattop = LevelLe 200

let rec pr_patt_args pr lev_after args =
  match args with
  | [] -> mt ()
  | args ->
    let last, args = List.sep_last args in
    prlist (pr_patt spc pr (Some lapp) (LevelLt lapp)) args ++ pr_patt spc pr lev_after (LevelLt lapp) last

and pr_patt sep pr lev_after inh p =
  let return cmds prec =
    let no_surround = Notation.prec_less prec inh in
    let lev_after = if no_surround then lev_after else no_after in
    let pp = cmds lev_after in
    let pp = if no_surround then pp else surround pp in
    pr_with_comments ?loc:p.CAst.loc (sep() ++ pp) in
  match CAst.(p.v) with
  | CPatRecord l ->
    return (fun lev_after -> pr_record_body "{|" "|}" (pr_patt spc pr no_after lpattop) l) lpatrec

  | CPatAlias (p, na) ->
    return (fun lev_after -> pr_patt mt pr lev_after (LevelLe las) p ++ str " as " ++ pr_lname na) las

  | CPatCstr (c, None, []) ->
    return (fun lev_after -> pr_reference c) latom

  | CPatCstr (c, None, args) ->
    return (fun lev_after -> pr_reference c ++ pr_patt_args pr lev_after args) lapp

  | CPatCstr (c, Some args, []) ->
    return (fun lev_after -> str "@" ++ pr_reference c ++ pr_patt_args pr lev_after args) lapp

  | CPatCstr (c, Some expl_args, extra_args) ->
    return (fun lev_after ->
        surround (str "@" ++ pr_reference c ++ pr_patt_args pr lev_after expl_args)
        ++ pr_patt_args pr lev_after extra_args) lapp

  | CPatAtom (None) ->
    return (fun lev_after -> str "_") latom

  | CPatAtom (Some r) ->
    return (fun lev_after -> pr_reference r) latom

  | CPatOr pl ->
    return (fun lev_after ->
        let pp p = hov 0 (pr_patt mt pr lev_after lpattop p) in
        surround (hov 0 (prlist_with_sep pr_spcbar pp pl))) lpator

  | CPatNotation (_,(_,"( _ )"),([p],[],[]),[]) ->
    return (fun lev_after -> pr_patt (fun()->str"(") pr no_after lpattop p ++ str")") latom

  | CPatNotation (which,s,(l,ll,bl),args) ->
    let l_not = (find_notation_printing_rule which s).notation_printing_level in
    let no_inner_surrounding = List.is_empty args || Notation.prec_less l_not (LevelLt lapp) in
    return (fun lev_after ->
        let lev_after' = if no_inner_surrounding then lev_after else no_after in
        let strm_not = pr_notation lev_after (pr_patt mt pr) (pr_patt_binder pr) (fun _ _ _ _ -> mt()) which s (l,ll,bl,[]) in
        (if List.is_empty args then strm_not else
         if overlap_right_left which s lev_after then surround strm_not else
         if Notation.prec_less l_not (LevelLt lapp) then strm_not else
           surround strm_not)
        ++ pr_patt_args pr lev_after' args)
      (if not (List.is_empty args) then lapp else if no_inner_surrounding then l_not else latom)

  | CPatPrim p ->
    return (fun lev_after -> pr_prim_token p) latom

  | CPatDelimiters (depth,k,p) ->
    return (fun lev_after -> pr_delimiters depth k (pr_patt mt pr (Some 1) lsimplepatt p)) 1

  | CPatCast (p,t) ->
    return (fun lev_after -> pr_patt mt pr (Some 1) lpatcast p ++ spc () ++ str ":" ++ ws 1 ++ pr t) 1

and pr_patt_binder pr prec style bk c =
  match bk with
  | MaxImplicit -> str "{" ++ pr_patt mt pr no_after lpattop c ++ str "}"
  | NonMaxImplicit -> str "[" ++ pr_patt mt pr no_after lpattop c ++ str "]"
  | Explicit ->
    match style, c with
    | NotQuotedPattern, _ | _, {v=CPatAtom _} -> pr_patt mt pr no_after prec c
    | QuotedPattern, _ -> str "'" ++ pr_patt mt pr no_after prec c

let pr_patt = pr_patt mt

let pr_eqn pr {loc;v=(pl,rhs)} =
  spc() ++ hov 4
    (pr_with_comments ?loc
       (str "| " ++
        hov 0 (prlist_with_sep pr_spcbar
                 (fun p -> hov 0 (prlist_with_sep sep_v (pr_patt (pr no_after ltop) no_after ltop) p)) pl
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

let pr_binder_among_many withquote pr_c = function
  | CLocalAssum (nal,r,k,t) ->
    pr_binder true pr_c (nal,r,k,t)
  | CLocalDef (na,r,c,topt) ->
    surround (pr_lname na ++ pr_relevance_info r ++
              pr_opt_no_spc (fun t -> str " :" ++ ws 1 ++ pr_c t) topt ++
              str" :=" ++ spc() ++ pr_c c)
  | CLocalPattern p ->
    str (if withquote then "'" else "") ++ pr_patt pr_c no_after lsimplepatt p

let pr_undelimited_binders sep withquote pr_c =
  prlist_with_sep sep (pr_binder_among_many withquote pr_c)

let pr_delimited_binders kw sep withquote pr_c bl =
  let n = begin_of_binders bl in
  match bl with
  | [CLocalAssum (nal,r,k,t)] ->
    kw n ++ pr_binder false pr_c (nal,r,k,t)
  | (CLocalAssum _ | CLocalPattern _ | CLocalDef _) :: _ as bdl ->
    kw n ++ pr_undelimited_binders sep withquote pr_c bdl
  | [] -> anomaly (Pp.str "The ast is malformed, found lambda/prod without proper binders.")

let pr_binders_gen pr_c sep is_open withquote =
  if is_open then pr_delimited_binders pr_com_at sep withquote pr_c
  else pr_undelimited_binders sep withquote pr_c

let pr_recursive_decl pr pr_dangling lev_after kw dangling_with_for id bl annot t c =
  let pr_body =
    if dangling_with_for then pr_dangling else pr in
  hov 0 (str kw ++ brk(1,2) ++ pr_id id ++ (if bl = [] then mt () else brk(1,2)) ++
         hov 0 (pr_undelimited_binders spc true (pr no_after ltop) bl ++ annot) ++
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

let pr_fixdecl pr prd lev_after kw dangling_with_for ({v=id},_,ro,bl,t,c) =
  let annot = pr_guard_annot (pr no_after lsimpleconstr) bl ro in
  pr_recursive_decl pr prd lev_after kw dangling_with_for id bl annot t c

let pr_cofixdecl pr prd lev_after kw dangling_with_for ({v=id},_,bl,t,c) =
  pr_recursive_decl pr prd lev_after kw dangling_with_for id bl (mt()) t c

let pr_recursive lev_after kw pr_decl id = function
  | [] -> anomaly (Pp.str "(co)fixpoint with no definition.")
  | [d1] -> pr_decl lev_after kw false d1
  | d1::dl ->
    pr_decl no_after kw true d1 ++ fnl() ++
    prlist_with_sep (fun () -> fnl())
      (pr_decl no_after "with" true) dl ++
    fnl() ++ keyword "for" ++ spc () ++ pr_id id

let pr_as_in pr na indnalopt =
  (match na with (* Decision of printing "_" or not moved to constrextern.ml *)
   | Some na -> spc () ++ keyword "as" ++ spc () ++  pr_lname na
   | None -> mt ()) ++
  (match indnalopt with
   | None -> mt ()
   | Some t -> spc () ++ keyword "in" ++ spc () ++ pr_patt pr no_after lsimplepatt t)

let pr_case_item pr (tm,as_clause, in_clause) =
  hov 0 (pr no_after (LevelLe lcast) tm ++ pr_as_in (pr no_after ltop) as_clause in_clause)

let pr_case_type pr po =
  match po with
  | None -> mt ()
  | Some { CAst.v = CHole h } when is_anonymous_hole h -> mt()
  | Some p ->
    spc() ++ hov 2 (keyword "return" ++ pr_sep_com spc (pr no_after lsimpleconstr) p)

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
  | Rawarg of Genarg.raw_generic_argument
  | Globarg of Genarg.glob_generic_argument

let pr_genarg return arg =
  (* In principle this may use the env/sigma, in practice not sure if it
     does except through pr_constr_expr in beautify mode. *)
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let name, parg = let open Genarg in
    match arg with
    | Globarg arg ->
      let GenArg (Glbwit tag, _) = arg in
      begin match tag with
      | ExtraArg tag -> ArgT.repr tag, Pputils.pr_glb_generic env sigma arg
      | _ -> assert false
      end
    | Rawarg arg ->
      let GenArg (Rawwit tag, _) = arg in
      begin match tag with
      | ExtraArg tag -> ArgT.repr tag, Pputils.pr_raw_generic env sigma arg
      | _ -> assert false
      end
  in
  let name =
    (* cheat the name system
       there should be a better way to handle this *)
    if String.equal name "tactic" then "ltac"
    else if String.equal name "ltac2:in-constr" then "ltac2"
    else if String.equal name "ltac2:quotation" then ""
    else name
  in
  let pp = if String.is_empty name then parg else str name ++ str ":" ++ surround parg in
  return (fun _ -> pp) latom

let pr pr sep lev_after inherited a =
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
                (pr_fixdecl (pr mt) (pr_dangling_with_for mt pr)) id.v fix))
      lfix
  | CCoFix (id,cofix) ->
    return (fun lev_after ->
        hv 0 (pr_recursive lev_after "cofix"
                (pr_cofixdecl (pr mt) (pr_dangling_with_for mt pr)) id.v cofix))
      lfix
  | CProdN (bl,a) ->
    return (fun lev_after ->
        hov 0 (
          hov 2 (pr_delimited_binders pr_forall spc true
                   (pr mt no_after ltop) bl) ++
          str "," ++ pr spc lev_after ltop a))
      lprod
  | CLambdaN (bl,a) ->
    return (fun lev_after ->
        hov 0 (
          hov 2 (pr_delimited_binders pr_fun spc true
                   (pr mt no_after ltop) bl) ++
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
  | CRecord l ->
    return (fun lev_after -> pr_record_body "{|" "|}" (pr spc no_after ltop) l) latom
  | CCases (Constr.LetPatternStyle,rtntypopt,[c,as_clause,in_clause],[{v=([[p]],b)}]) ->
    return (fun lev_after ->
        hv 0 (
          keyword "let" ++ spc () ++ str"'" ++
          hov 0 (pr_patt (pr mt no_after ltop) no_after ltop p ++
                 pr_as_in (pr mt no_after ltop) as_clause in_clause ++
                 str " :=" ++ pr spc no_after ltop c ++
                 pr_case_type (pr_dangling_with_for mt pr) rtntypopt ++
                 spc () ++ keyword "in" ++ pr spc lev_after ltop b)))
      lletpattern
  | CCases(_,rtntypopt,c,eqns) ->
    return (fun lev_after ->
        v 0
          (hv 0 (keyword "match" ++ brk (1,2) ++
                 hov 0 (
                   prlist_with_sep sep_v
                     (pr_case_item (pr_dangling_with_for mt pr)) c
                   ++ pr_case_type (pr_dangling_with_for mt pr) rtntypopt) ++
                 spc () ++ keyword "with") ++
           prlist (pr_eqn (pr mt)) eqns ++ spc()
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
  | CNotation (_,(_,"( _ )"),([t],[],[],[])) ->
    return (fun lev_after -> pr (fun()->str"(") no_after ltop t ++ str")") latom
  | CNotation (which,s,env) ->
    let l_not = (find_notation_printing_rule which s).notation_printing_level in
    let l_not = if overlap_right_left which s lev_after then max_int else l_not in
    return (fun lev_after -> pr_notation lev_after (pr mt) (pr_patt_binder (pr mt no_after ltop)) (pr_binders_gen (pr mt no_after ltop)) which s env) l_not
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
  pr_constr_expr   : Environ.env -> Evd.evar_map -> constr_expr -> Pp.t;
  pr_lconstr_expr  : Environ.env -> Evd.evar_map -> constr_expr -> Pp.t;
  pr_constr_pattern_expr  : Environ.env -> Evd.evar_map -> constr_pattern_expr -> Pp.t;
  pr_lconstr_pattern_expr : Environ.env -> Evd.evar_map -> constr_pattern_expr -> Pp.t
}

let modular_constr_pr = pr
let rec fix rf x = rf (fix rf) x
let pr = fix modular_constr_pr mt

let pr lev_after prec = function
  (* A toplevel printer hack mimicking parsing, incidentally meaning
     that we cannot use [pr] correctly anymore in a recursive loop
     if the current expr is followed by other exprs which would be
     interpreted as arguments *)
  | { CAst.v = CAppExpl ((f,us),[]) } -> str "@" ++ pr_cref f us
  | c -> pr lev_after prec c

let transf env sigma c =
  if !Flags.beautify_file then
    let r = Constrintern.intern_gen ~strict_check:false WithoutTypeConstraint env sigma c in
    Constrextern.(extern_glob_constr (extern_env env sigma)) r
  else c

let pr_expr env sigma lev_after prec c =
  pr lev_after prec (transf env sigma c)

let pr_simpleconstr_env env sigma = pr_expr env sigma no_after lsimpleconstr
let pr_top_env env sigma = pr_expr env sigma no_after ltop

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

let pr_constr_expr_n n c = pr_expr n c no_after
let pr_constr_expr c   = !term_pr.pr_constr_expr   c
let pr_lconstr_expr c  = !term_pr.pr_lconstr_expr  c
let pr_constr_pattern_expr c  = !term_pr.pr_constr_pattern_expr  c
let pr_lconstr_pattern_expr c = !term_pr.pr_lconstr_pattern_expr c

let pr_cases_pattern_expr = pr_patt (pr no_after ltop) no_after ltop

let pr_binders env sigma = pr_undelimited_binders spc true (pr_expr env sigma no_after ltop)
