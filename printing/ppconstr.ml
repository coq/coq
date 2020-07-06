(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
open Namegen
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
  let lapp = 10
  let lposint = 0
  let lnegint = 35 (* must be consistent with Notation "- x" *)
  let ltop = LevelLe 200
  let lproj = 1
  let ldelim = 1
  let lsimpleconstr = LevelLe 8
  let lsimplepatt = LevelLe 1

  let prec_less child = function
    | LevelLt parent -> (<) child parent
    | LevelLe parent -> if parent < 0 && Int.equal child lprod then true else child <= abs parent
    | LevelSome -> true

  let prec_of_prim_token = function
    | Numeral (NumTok.SPlus,_) -> lposint
    | Numeral (NumTok.SMinus,_) -> lnegint
    | String _ -> latom

  let print_hunks n pr pr_patt pr_binders (terms, termlists, binders, binderlists) unps =
    let env = ref terms and envlist = ref termlists and bl = ref binders and bll = ref binderlists in
    let pop r = let a = List.hd !r in r := List.tl !r; a in
    let return unp pp1 pp2 = (tag_unparsing unp pp1) ++ pp2 in
    let parens = !Constrextern.print_parentheses in
    (* Warning:
       The following function enforces a very precise order of
       evaluation of sub-components.
       Do not modify it unless you know what you are doing! *)
    let rec aux = function
      | [] ->
        mt ()
      | UnpMetaVar (prec, side) as unp :: l ->
        let c = pop env in
        let pp2 = aux l in
        let pp1 = pr (if parens && side <> None then LevelLe 0 else prec) c in
        return unp pp1 pp2
      | UnpBinderMetaVar prec as unp :: l ->
        let c = pop bl in
        let pp2 = aux l in
        let pp1 = pr_patt prec c in
        return unp pp1 pp2
      | UnpListMetaVar (prec, sl, side) as unp :: l ->
        let cl = pop envlist in
        let pp1 = prlist_with_sep (fun () -> aux sl) (pr (if parens && side <> None then LevelLe 0 else prec)) cl in
        let pp2 = aux l in
        return unp pp1 pp2
      | UnpBinderListMetaVar (isopen, sl) as unp :: l ->
        let cl = pop bll in
        let pp2 = aux l in
        let pp1 = pr_binders (fun () -> aux sl) isopen cl in
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

  let pr_notation pr pr_patt pr_binders which s env =
    let unpl, level = find_notation_printing_rule which s in
    print_hunks level pr pr_patt pr_binders env unpl, level

  let pr_delimiters key strm =
    strm ++ str ("%"^key)

  let pr_generalization bk ak c =
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

  let pr_glob_sort_name = function
    | GSProp -> str "SProp"
    | GProp -> str "Prop"
    | GSet -> str "Set"
    | GType qid -> pr_qualid qid

  let pr_univ_expr (u,n) =
    pr_glob_sort_name u ++ (match n with 0 -> mt () | _ -> str"+" ++ int n)

  let pr_univ l =
    match l with
      | [x] -> pr_univ_expr x
      | l -> str"max(" ++ prlist_with_sep (fun () -> str",") pr_univ_expr l ++ str")"

  let pr_univ_annot pr x = str "@{" ++ pr x ++ str "}"

  let pr_glob_sort = let open Glob_term in function
    | UNamed [GSProp,0] -> tag_type (str "SProp")
    | UNamed [GProp,0] -> tag_type (str "Prop")
    | UNamed [GSet,0] -> tag_type (str "Set")
    | UAnonymous {rigid=true} -> tag_type (str "Type")
    | UAnonymous {rigid=false} -> tag_type (str "Type") ++ pr_univ_annot (fun _ -> str "_") ()
    | UNamed u -> hov 0 (tag_type (str "Type") ++ pr_univ_annot pr_univ u)

  let pr_glob_level = let open Glob_term in function
    | UNamed GSProp -> tag_type (str "SProp")
    | UNamed GProp -> tag_type (str "Prop")
    | UNamed GSet -> tag_type (str "Set")
    | UAnonymous {rigid=true} -> tag_type (str "Type")
    | UAnonymous {rigid=false} -> tag_type (str "_")
    | UNamed (GType u) -> tag_type (pr_qualid u)

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

  let pr_universe_instance l =
    pr_opt_no_spc (pr_univ_annot (prlist_with_sep spc pr_glob_level)) l

  let pr_reference qid =
    if qualid_is_ident qid then tag_var (pr_id @@ qualid_basename qid)
    else pr_qualid qid

  let pr_cref ref us =
    pr_reference ref ++ pr_universe_instance us

  let pr_expl_args pr (a,expl) =
    match expl with
      | None -> pr (LevelLt lapp) a
      | Some {v=ExplByPos (n,_id)} ->
        anomaly (Pp.str "Explicitation by position not implemented.")
      | Some {v=ExplByName id} ->
        str "(" ++ pr_id id ++ str ":=" ++ pr ltop a ++ str ")"

  let pr_opt_type_spc pr = function
    | { CAst.v = CHole (_,IntroAnonymous,_) } -> mt ()
    | t ->  str " :" ++ pr_sep_com (fun()->brk(1,4)) (pr ltop) t

  let pr_prim_token = function
    | Numeral n -> NumTok.Signed.print n
    | String s -> qs s

  let pr_evar pr id l =
    hov 0 (
      tag_evar (str "?" ++ pr_id id) ++
        (match l with
          | [] -> mt()
          | l ->
            let f (id,c) = pr_id id ++ str ":=" ++ pr ltop c in
            str"@{" ++ hov 0 (prlist_with_sep pr_semicolon f (List.rev l)) ++ str"}"))

  let las = lapp
  let lpator = 0
  let lpatrec = 0
  let lpattop = LevelLe 200

  let rec pr_patt sep inh p =
    let (strm,prec) = match CAst.(p.v) with
      | CPatRecord l ->
        let pp (c, p) =
          pr_reference c ++ spc() ++ str ":=" ++ pr_patt spc lpattop p
        in
        (if l = [] then str "{| |}"
         else str "{| " ++ prlist_with_sep pr_semicolon pp l ++ str " |}"), lpatrec

      | CPatAlias (p, na) ->
        pr_patt mt (LevelLe las) p ++ str " as " ++ pr_lname na, las

      | CPatCstr (c, None, []) ->
        pr_reference c, latom

      | CPatCstr (c, None, args) ->
        pr_reference c ++ prlist (pr_patt spc (LevelLt lapp)) args, lapp

      | CPatCstr (c, Some args, []) ->
        str "@" ++ pr_reference c ++ prlist (pr_patt spc (LevelLt lapp)) args, lapp

      | CPatCstr (c, Some expl_args, extra_args) ->
        surround (str "@" ++ pr_reference c ++ prlist (pr_patt spc (LevelLt lapp)) expl_args)
        ++ prlist (pr_patt spc (LevelLt lapp)) extra_args, lapp

      | CPatAtom (None) ->
        str "_", latom

      | CPatAtom (Some r) ->
        pr_reference r, latom

      | CPatOr pl ->
        let pp p = hov 0 (pr_patt mt lpattop p) in
        surround (hov 0 (prlist_with_sep pr_spcbar pp pl)), lpator

      | CPatNotation (_,(_,"( _ )"),([p],[]),[]) ->
        pr_patt (fun()->str"(") lpattop p ++ str")", latom

      | CPatNotation (which,s,(l,ll),args) ->
        let strm_not, l_not = pr_notation (pr_patt mt) (fun _ _ -> mt ()) (fun _ _ _ -> mt()) which s (l,ll,[],[]) in
        (if List.is_empty args||prec_less l_not (LevelLt lapp) then strm_not else surround strm_not)
        ++ prlist (pr_patt spc (LevelLt lapp)) args, if not (List.is_empty args) then lapp else l_not

      | CPatPrim p ->
        pr_prim_token p, latom

      | CPatDelimiters (k,p) ->
        pr_delimiters k (pr_patt mt lsimplepatt p), 1
      | CPatCast _ ->
        assert false
    in
    let loc = p.CAst.loc in
    pr_with_comments ?loc
      (sep() ++ if prec_less prec inh then strm else surround strm)

  let pr_patt = pr_patt mt

  let pr_eqn pr {loc;v=(pl,rhs)} =
    spc() ++ hov 4
      (pr_with_comments ?loc
         (str "| " ++
            hov 0 (prlist_with_sep pr_spcbar
                     (fun p -> hov 0 (prlist_with_sep sep_v (pr_patt ltop) p)) pl
                   ++ str " =>") ++
            pr_sep_com spc (pr ltop) rhs))

  let begin_of_binder l_bi =
    let b_loc l = fst (Option.cata Loc.unloc (0,0) l) in
    match l_bi with
    | CLocalDef({loc},_,_) -> b_loc loc
    | CLocalAssum({loc}::_,_,_) -> b_loc loc
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

  let pr_binder many pr (nal,k,t) =
    match k with
      | Generalized (b', t') ->
        begin match nal with
          |[{loc; v=Anonymous}] ->
            hov 1 (str"`" ++ (surround_impl b'
                                ((if t' then str "!" else mt ()) ++ pr t)))
          |[{loc; v=Name id}] ->
            hov 1 (str "`" ++ (surround_impl b'
                                 (pr_lident CAst.(make ?loc id) ++ str " : " ++
                                    (if t' then str "!" else mt()) ++ pr t)))
          |_ -> anomaly (Pp.str "List of generalized binders have always one element.")
        end
      | Default b ->
        match t with
          | { CAst.v = CHole (_,IntroAnonymous,_) } ->
            let s = prlist_with_sep spc pr_lname nal in
            hov 1 (surround_implicit b s)
          | _ ->
            let s = prlist_with_sep spc pr_lname nal ++ str " : " ++ pr t in
            hov 1 (if many then surround_impl b s else surround_implicit b s)

  let pr_binder_among_many pr_c = function
    | CLocalAssum (nal,k,t) ->
      pr_binder true pr_c (nal,k,t)
    | CLocalDef (na,c,topt) ->
      surround (pr_lname na ++
                pr_opt_no_spc (fun t -> str " :" ++ ws 1 ++ pr_c t) topt ++
                str" :=" ++ spc() ++ pr_c c)
    | CLocalPattern {CAst.loc; v = p,tyo} ->
      let p = pr_patt lsimplepatt p in
      match tyo with
        | None ->
          str "'" ++ p
        | Some ty ->
          str "'" ++ surround (p ++ spc () ++ str ":" ++ ws 1 ++ pr_c ty)

  let pr_undelimited_binders sep pr_c =
    prlist_with_sep sep (pr_binder_among_many pr_c)

  let pr_delimited_binders kw sep pr_c bl =
    let n = begin_of_binders bl in
    match bl with
      | [CLocalAssum (nal,k,t)] ->
        kw n ++ pr_binder false pr_c (nal,k,t)
      | (CLocalAssum _ | CLocalPattern _ | CLocalDef _) :: _ as bdl ->
        kw n ++ pr_undelimited_binders sep pr_c bdl
      | [] -> anomaly (Pp.str "The ast is malformed, found lambda/prod without proper binders.")

  let pr_binders_gen pr_c sep is_open =
    if is_open then pr_delimited_binders pr_com_at sep pr_c
    else pr_undelimited_binders sep pr_c

  let pr_recursive_decl pr pr_dangling kw dangling_with_for id bl annot t c =
    let pr_body =
      if dangling_with_for then pr_dangling else pr in
    hov 0 (str kw ++ brk(1,2) ++ pr_id id ++ (if bl = [] then mt () else brk(1,2)) ++
      hov 0 (pr_undelimited_binders spc (pr ltop) bl ++ annot) ++
      pr_opt_type_spc pr t ++ str " :=") ++
      pr_sep_com (fun () -> brk(1,2)) (pr_body ltop) c

  let pr_guard_annot pr_aux bl ro =
    match ro with
      | None -> mt ()
      | Some {loc; v = ro} ->
        match ro with
          | CStructRec { v = id } ->
            let names_of_binder = function
              | CLocalAssum (nal,_,_) -> nal
              | CLocalDef (_,_,_) -> []
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

  let pr_fixdecl pr prd kw dangling_with_for ({v=id},ro,bl,t,c) =
    let annot = pr_guard_annot (pr lsimpleconstr) bl ro in
    pr_recursive_decl pr prd kw dangling_with_for id bl annot t c

  let pr_cofixdecl pr prd kw dangling_with_for ({v=id},bl,t,c) =
    pr_recursive_decl pr prd kw dangling_with_for id bl (mt()) t c

  let pr_recursive kw pr_decl id = function
    | [] -> anomaly (Pp.str "(co)fixpoint with no definition.")
    | [d1] -> pr_decl kw false d1
    | dl ->
      prlist_with_sep (fun () -> fnl())
        (pr_decl "with" true) dl ++
        fnl() ++ keyword "for" ++ spc () ++ pr_id id

  let pr_asin pr na indnalopt =
    (match na with (* Decision of printing "_" or not moved to constrextern.ml *)
      | Some na -> spc () ++ keyword "as" ++ spc () ++  pr_lname na
      | None -> mt ()) ++
      (match indnalopt with
        | None -> mt ()
        | Some t -> spc () ++ keyword "in" ++ spc () ++ pr_patt lsimplepatt t)

  let pr_case_item pr (tm,as_clause, in_clause) =
    hov 0 (pr (LevelLe lcast) tm ++ pr_asin pr as_clause in_clause)

  let pr_case_type pr po =
    match po with
      | None | Some { CAst.v = CHole (_,IntroAnonymous,_) } -> mt()
      | Some p ->
        spc() ++ hov 2 (keyword "return" ++ pr_sep_com spc (pr lsimpleconstr) p)

  let pr_simple_return_type pr na po =
    (match na with
      | Some {v=Name id} ->
        spc () ++ keyword "as" ++ spc () ++ pr_id id
      | _ -> mt ()) ++
      pr_case_type pr po

  let pr_proj pr pr_app a f l =
    hov 0 (pr (LevelLe lproj) a ++ cut() ++ str ".(" ++ pr_app pr f l ++ str ")")

  let pr_appexpl pr (f,us) l =
    hov 2 (
      str "@" ++ pr_reference f ++
        pr_universe_instance us ++
        prlist (pr_sep_com spc (pr (LevelLt lapp))) l)

  let pr_app pr a l =
    hov 2 (
      pr (LevelLt lapp) a  ++
        prlist (fun a -> spc () ++ pr_expl_args pr a) l)

  let pr_record_body_gen pr l =
    spc () ++
    prlist_with_sep pr_semicolon
      (fun (id, c) -> h 1 (pr_reference id ++ spc () ++ str":=" ++ pr ltop c)) l

  let pr_forall n = keyword "forall" ++ pr_com_at n ++ spc ()

  let pr_fun n = keyword "fun" ++ pr_com_at n ++ spc ()

  let pr_fun_sep = spc () ++ str "=>"

  let pr_dangling_with_for sep pr inherited a =
    match a.v with
      | (CFix (_,[_])|CCoFix(_,[_])) ->
        pr sep (LevelLe latom) a
      | _ ->
        pr sep inherited a

  let pr pr sep inherited a =
    let return (cmds, prec) = (tag_constr_expr a cmds, prec) in
    let (strm, prec) = match CAst.(a.v) with
      | CRef (r, us) ->
        return (pr_cref r us, latom)
      | CFix (id,fix) ->
        return (
          hv 0 (pr_recursive "fix"
                   (pr_fixdecl (pr mt) (pr_dangling_with_for mt pr)) id.v fix),
          lfix
        )
      | CCoFix (id,cofix) ->
        return (
          hv 0 (pr_recursive "cofix"
                   (pr_cofixdecl (pr mt) (pr_dangling_with_for mt pr)) id.v cofix),
          lfix
        )
      | CProdN (bl,a) ->
        return (
          hov 0 (
            hov 2 (pr_delimited_binders pr_forall spc
                     (pr mt ltop) bl) ++
              str "," ++ pr spc ltop a),
          lprod
        )
      | CLambdaN (bl,a) ->
        return (
          hov 0 (
            hov 2 (pr_delimited_binders pr_fun spc
                     (pr mt ltop) bl) ++
              pr_fun_sep ++ pr spc ltop a),
          llambda
        )
      | CLetIn ({v=Name x}, ({ v = CFix({v=x'},[_])}
                          |  { v = CCoFix({v=x'},[_]) } as fx), t, b)
          when Id.equal x x' ->
        return (
          hv 0 (
            hov 2 (keyword "let" ++ spc () ++ pr mt ltop fx
                   ++ spc ()
                   ++ keyword "in") ++
              pr spc ltop b),
          lletin
        )
      | CLetIn (x,a,t,b) ->
        return (
          hv 0 (
            hov 2 (keyword "let" ++ spc () ++ pr_lname x
                   ++ pr_opt_no_spc (fun t -> str " :" ++ ws 1 ++ pr mt ltop t) t
                   ++ str " :=" ++ pr spc ltop a ++ spc ()
                   ++ keyword "in") ++
              pr spc ltop b),
          lletin
        )
      | CAppExpl ((Some i,f,us),l) ->
        let l1,l2 = List.chop i l in
        let c,l1 = List.sep_last l1 in
        let p = pr_proj (pr mt) pr_appexpl c (f,us) l1 in
        if not (List.is_empty l2) then
          return (p ++ prlist (pr spc (LevelLt lapp)) l2, lapp)
        else
          return (p, lproj)
      | CAppExpl ((None,qid,us),[t])
      | CApp ((_, {v = CRef(qid,us)}),[t,None])
          when qualid_is_ident qid && Id.equal (qualid_basename qid) Notation_ops.ldots_var ->
        return (
          hov 0 (str ".." ++ pr spc (LevelLe latom) t ++ spc () ++ str ".."),
          larg
        )
      | CAppExpl ((None,f,us),l) ->
        return (pr_appexpl (pr mt) (f,us) l, lapp)
      | CApp ((Some i,f),l) ->
        let l1,l2 = List.chop i l in
        let c,l1 = List.sep_last l1 in
        assert (Option.is_empty (snd c));
        let p = pr_proj (pr mt) pr_app (fst c) f l1 in
        if not (List.is_empty l2) then
          return (
            p ++ prlist (fun a -> spc () ++ pr_expl_args (pr mt) a) l2,
            lapp
          )
        else
          return (p, lproj)
      | CApp ((None,a),l) ->
        return (pr_app (pr mt) a l, lapp)
      | CRecord l ->
        return (
          hv 0 (str"{|" ++ pr_record_body_gen (pr spc) l ++ str" |}"),
          latom
        )
      | CCases (Constr.LetPatternStyle,rtntypopt,[c,as_clause,in_clause],[{v=([[p]],b)}]) ->
        return (
          hv 0 (
            keyword "let" ++ spc () ++ str"'" ++
              hov 0 (pr_patt ltop p ++
                       pr_asin (pr_dangling_with_for mt pr) as_clause in_clause ++
                       str " :=" ++ pr spc ltop c ++
                       pr_case_type (pr_dangling_with_for mt pr) rtntypopt ++
                       spc () ++ keyword "in" ++ pr spc ltop b)),
          lletpattern
        )
      | CCases(_,rtntypopt,c,eqns) ->
        return (
          v 0
            (hv 0 (keyword "match" ++ brk (1,2) ++
                     hov 0 (
                       prlist_with_sep sep_v
                         (pr_case_item (pr_dangling_with_for mt pr)) c
                       ++ pr_case_type (pr_dangling_with_for mt pr) rtntypopt) ++
                     spc () ++ keyword "with") ++
               prlist (pr_eqn (pr mt)) eqns ++ spc()
             ++ keyword "end"),
          latom
        )
      | CLetTuple (nal,(na,po),c,b) ->
        return (
          hv 0 (
            hov 2 (keyword "let" ++ spc () ++
              hov 1 (str "(" ++
                       prlist_with_sep sep_v pr_lname nal ++
                       str ")" ++
                       pr_simple_return_type (pr mt) na po ++ str " :=") ++
                       pr spc ltop c
                     ++ keyword " in") ++
              pr spc ltop b),
          lletin
        )
      | CIf (c,(na,po),b1,b2) ->
      (* On force les parenthèses autour d'un "if" sous-terme (même si le
         parsing est lui plus tolérant) *)
        return (
          hv 0 (
            hov 1 (keyword "if" ++ spc () ++ pr mt ltop c
                   ++ pr_simple_return_type (pr mt) na po) ++
              spc () ++
              hov 0 (keyword "then"
                     ++ pr (fun () -> brk (1,1)) ltop b1) ++ spc () ++
              hov 0 (keyword "else" ++ pr (fun () -> brk (1,1)) ltop b2)),
        lif
        )

      | CHole (_,IntroIdentifier id,_) ->
        return (str "?[" ++ pr_id id ++ str "]", latom)
      | CHole (_,IntroFresh id,_) ->
        return (str "?[?" ++ pr_id id ++ str "]", latom)
      | CHole (_,_,_) ->
        return (str "_", latom)
      | CEvar (n,l) ->
        return (pr_evar (pr mt) n l, latom)
      | CPatVar p ->
        return (str "@?" ++ pr_patvar p, latom)
      | CSort s ->
        return (pr_glob_sort s, latom)
      | CCast (a,b) ->
        return (
          hv 0 (pr mt (LevelLt lcast) a ++ spc () ++
                  match b with
                    | CastConv b -> str ":" ++ ws 1 ++ pr mt (LevelLe (-lcast)) b
                    | CastVM b -> str "<:" ++ ws 1 ++ pr mt (LevelLe (-lcast)) b
                    | CastNative b -> str "<<:" ++ ws 1 ++ pr mt (LevelLe (-lcast)) b
                    | CastCoerce -> str ":>"),
          lcast
        )
      | CNotation (_,(_,"( _ )"),([t],[],[],[])) ->
        return (pr (fun()->str"(") ltop t ++ str")", latom)
      | CNotation (which,s,env) ->
        pr_notation (pr mt) pr_patt (pr_binders_gen (pr mt ltop)) which s env
      | CGeneralization (bk,ak,c) ->
        return (pr_generalization bk ak (pr mt ltop c), latom)
      | CPrim p ->
        return (pr_prim_token p, prec_of_prim_token p)
      | CDelimiters (sc,a) ->
        return (pr_delimiters sc (pr mt (LevelLe ldelim) a), ldelim)
      | CArray(u, t,def,ty) ->
        let pp = ref (str " |"++ spc () ++ pr mt ltop def
          ++ pr_opt_type_spc (pr mt) ty  ++ str " |]" ++ pr_universe_instance u) in
        for i = Array.length t - 1 downto 1 do
          pp :=  str ";" ++ pr mt ltop t.(i) ++ !pp
        done;
        pp :=  pr mt ltop t.(0) ++ !pp;
        hov 0 (str "[|" ++ !pp), 0
    in
    let loc = constr_loc a in
    pr_with_comments ?loc
      (sep() ++ if prec_less prec inherited then strm else surround strm)

  type term_pr = {
    pr_constr_expr   : Environ.env -> Evd.evar_map -> constr_expr -> Pp.t;
    pr_lconstr_expr  : Environ.env -> Evd.evar_map -> constr_expr -> Pp.t;
    pr_constr_pattern_expr  : Environ.env -> Evd.evar_map -> constr_pattern_expr -> Pp.t;
    pr_lconstr_pattern_expr : Environ.env -> Evd.evar_map -> constr_pattern_expr -> Pp.t
  }

  let modular_constr_pr = pr
  let rec fix rf x = rf (fix rf) x
  let pr = fix modular_constr_pr mt

  let pr prec = function
    (* A toplevel printer hack mimicking parsing, incidentally meaning
       that we cannot use [pr] correctly anymore in a recursive loop
       if the current expr is followed by other exprs which would be
       interpreted as arguments *)
    | { CAst.v = CAppExpl ((None,f,us),[]) } -> str "@" ++ pr_cref f us
    | c -> pr prec c

  let transf env sigma c =
    if !Flags.beautify_file then
      let r = Constrintern.for_grammar (Constrintern.intern_constr env sigma) c in
      Constrextern.extern_glob_constr (Termops.vars_of_env env) r
    else c

  let pr_expr env sigma prec c =
    pr prec (transf env sigma c)

  let pr_simpleconstr env sigma = pr_expr env sigma lsimpleconstr

  let default_term_pr = {
    pr_constr_expr   = pr_simpleconstr;
    pr_lconstr_expr  = (fun env sigma -> pr_expr env sigma ltop);
    pr_constr_pattern_expr  = pr_simpleconstr;
    pr_lconstr_pattern_expr = (fun env sigma -> pr_expr env sigma ltop)
  }

  let term_pr = ref default_term_pr

  let set_term_pr = (:=) term_pr

  let pr_constr_expr_n n c = pr_expr n c
  let pr_constr_expr c   = !term_pr.pr_constr_expr   c
  let pr_lconstr_expr c  = !term_pr.pr_lconstr_expr  c
  let pr_constr_pattern_expr c  = !term_pr.pr_constr_pattern_expr  c
  let pr_lconstr_pattern_expr c = !term_pr.pr_lconstr_pattern_expr c

  let pr_cases_pattern_expr = pr_patt ltop

  let pr_record_body = pr_record_body_gen pr

  let pr_binders env sigma = pr_undelimited_binders spc (pr_expr env sigma ltop)

