(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Errors
open Util
open Pp
open Names
open Nameops
open Libnames
open Pputils
open Ppextend
open Constrexpr
open Constrexpr_ops
open Decl_kinds
open Misctypes
(*i*)

module Make (Taggers : sig
  val tag_keyword     : std_ppcmds -> std_ppcmds
  val tag_evar     : std_ppcmds -> std_ppcmds
  val tag_type     : std_ppcmds -> std_ppcmds
  val tag_path     : std_ppcmds -> std_ppcmds
  val tag_ref     : std_ppcmds -> std_ppcmds
  val tag_var     : std_ppcmds -> std_ppcmds
  val tag_constr_expr : constr_expr -> std_ppcmds -> std_ppcmds
  val tag_unparsing   : unparsing -> std_ppcmds -> std_ppcmds
end) = struct

  open Taggers

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
  let ltop = (200,E)
  let lproj = 1
  let ldelim = 1
  let lsimpleconstr = (8,E)
  let lsimplepatt = (1,E)

  let prec_less child (parent,assoc) =
    if parent < 0 && Int.equal child lprod then true
    else
      let parent = abs parent in
      match assoc with
        | E -> (<=) child parent
        | L -> (<) child parent
        | Prec n -> child<=n
        | Any -> true

  let prec_of_prim_token = function
    | Numeral p -> if Bigint.is_pos_or_zero p then lposint else lnegint
    | String _ -> latom

  open Notation

  let print_hunks n pr pr_binders (terms, termlists, binders) unps =
    let env = ref terms and envlist = ref termlists and bll = ref binders in
    let pop r = let a = List.hd !r in r := List.tl !r; a in
    let return unp pp1 pp2 = (tag_unparsing unp pp1) ++ pp2 in
    (* Warning:
       The following function enforces a very precise order of
       evaluation of sub-components.
       Do not modify it unless you know what you are doing! *)
    let rec aux = function
      | [] ->
        mt ()
      | UnpMetaVar (_, prec) as unp :: l ->
        let c = pop env in
        let pp2 = aux l in
        let pp1 = pr (n, prec) c in
        return unp pp1 pp2
      | UnpListMetaVar (_, prec, sl) as unp :: l ->
        let cl = pop envlist in
        let pp1 = prlist_with_sep (fun () -> aux sl) (pr (n,prec)) cl in
        let pp2 = aux l in
        return unp pp1 pp2
      | UnpBinderListMetaVar (_, isopen, sl) as unp :: l ->
        let cl = pop bll in
        let pp2 = aux l in
        let pp1 = pr_binders (fun () -> aux sl) isopen cl in
        return unp pp1 pp2
      | UnpTerminal s as unp :: l ->
        let pp2 = aux l in
        let pp1 = str s in
        return unp pp1 pp2
      | UnpBox (b,sub) as unp :: l ->
        let pp1 = ppcmd_of_box b (aux sub) in
        let pp2 = aux l in
        return unp pp1 pp2
      | UnpCut cut as unp :: l ->
        let pp2 = aux l in
        let pp1 = ppcmd_of_cut cut in
        return unp pp1 pp2
    in
    aux unps

  let pr_notation pr pr_binders s env =
    let unpl, level = find_notation_printing_rule s in
    print_hunks level pr pr_binders env unpl, level

  let pr_delimiters key strm =
    strm ++ str ("%"^key)

  let pr_generalization bk ak c =
    let hd, tl =
      match bk with
        | Implicit -> "{", "}"
        | Explicit -> "(", ")"
    in (* TODO: syntax Abstraction Kind *)
    str "`" ++ str hd ++ c ++ str tl

  let pr_com_at n =
    if Flags.do_beautify() && not (Int.equal n 0) then comment n
    else mt()

  let pr_with_comments loc pp = pr_located (fun x -> x) (loc,pp)

  let pr_sep_com sep f c = pr_with_comments (constr_loc c) (sep() ++ f c)

  let pr_in_comment pr x = str "(* " ++ pr x ++ str " *)"

  let pr_univ l =
    match l with
      | [x] -> str x
      | l -> str"max(" ++ prlist_with_sep (fun () -> str",") str l ++ str")"

  let pr_univ_annot pr x = str "@{" ++ pr x ++ str "}"

  let pr_glob_sort = function
    | GProp -> tag_type (str "Prop")
    | GSet -> tag_type (str "Set")
    | GType [] -> tag_type (str "Type")
    | GType u -> hov 0 (tag_type (str "Type") ++ pr_univ_annot pr_univ u)

  let pr_qualid sp =
    let (sl, id) = repr_qualid sp in
    let id = tag_ref (str (Id.to_string id)) in
    let sl = match List.rev (DirPath.repr sl) with
    | [] -> mt ()
    | sl ->
      let pr dir = tag_path (str (Id.to_string dir)) ++ str "." in
      prlist pr sl
    in
    sl ++ id

  let pr_id = pr_id
  let pr_name = pr_name
  let pr_qualid = pr_qualid
  let pr_patvar = pr_id

  let pr_glob_sort_instance = function
    | GProp ->
      tag_type (str "Prop")
    | GSet ->
      tag_type (str "Set")
    | GType u ->
      (match u with
        | Some u -> str u
        | None -> tag_type (str "Type"))

  let pr_universe_instance l =
    pr_opt_no_spc (pr_univ_annot (prlist_with_sep spc pr_glob_sort_instance)) l

  let pr_reference = function
  | Qualid (_, qid) -> pr_qualid qid
  | Ident (_, id) -> tag_var (str (Id.to_string id))

  let pr_cref ref us =
    pr_reference ref ++ pr_universe_instance us

  let pr_expl_args pr (a,expl) =
    match expl with
      | None -> pr (lapp,L) a
      | Some (_,ExplByPos (n,_id)) ->
        anomaly (Pp.str "Explicitation by position not implemented")
      | Some (_,ExplByName id) ->
        str "(" ++ pr_id id ++ str ":=" ++ pr ltop a ++ str ")"

  let pr_opt_type pr = function
    | CHole (_,_,Misctypes.IntroAnonymous,_) -> mt ()
    | t -> cut () ++ str ":" ++ pr t

  let pr_opt_type_spc pr = function
    | CHole (_,_,Misctypes.IntroAnonymous,_) -> mt ()
    | t ->  str " :" ++ pr_sep_com (fun()->brk(1,2)) (pr ltop) t

  let pr_lident (loc,id) =
    if not (Loc.is_ghost loc) then
      let (b,_) = Loc.unloc loc in
      pr_located pr_id (Loc.make_loc (b,b + String.length (Id.to_string id)), id)
    else
      pr_id id

  let pr_lname = function
    | (loc,Name id) -> pr_lident (loc,id)
    | lna -> pr_located pr_name lna

  let pr_or_var pr = function
    | ArgArg x -> pr x
    | ArgVar (loc,s) -> pr_lident (loc,s)

  let pr_prim_token = function
    | Numeral n -> str (Bigint.to_string n)
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
  let lpator = 100
  let lpatrec = 0

  let rec pr_patt sep inh p =
    let (strm,prec) = match p with
      | CPatRecord (_, l) ->
        let pp (c, p) =
          pr_reference c ++ spc() ++ str ":=" ++ pr_patt spc (lpatrec, Any) p
        in
        str "{| " ++ prlist_with_sep pr_semicolon pp l ++ str " |}", lpatrec

      | CPatAlias (_, p, id) ->
        pr_patt mt (las,E) p ++ str " as " ++ pr_id id, las

      | CPatCstr (_,c, [], []) ->
        pr_reference c, latom

      | CPatCstr (_, c, [], args) ->
        pr_reference c ++ prlist (pr_patt spc (lapp,L)) args, lapp

      | CPatCstr (_, c, args, []) ->
        str "@" ++ pr_reference c ++ prlist (pr_patt spc (lapp,L)) args, lapp

      | CPatCstr (_, c, expl_args, extra_args) ->
        surround (str "@" ++ pr_reference c ++ prlist (pr_patt spc (lapp,L)) expl_args)
        ++ prlist (pr_patt spc (lapp,L)) extra_args, lapp

      | CPatAtom (_, None) ->
        str "_", latom

      | CPatAtom (_,Some r) ->
        pr_reference r, latom

      | CPatOr (_,pl) ->
        hov 0 (prlist_with_sep pr_bar (pr_patt spc (lpator,L)) pl), lpator

      | CPatNotation (_,"( _ )",([p],[]),[]) ->
        pr_patt (fun()->str"(") (max_int,E) p ++ str")", latom

      | CPatNotation (_,s,(l,ll),args) ->
        let strm_not, l_not = pr_notation (pr_patt mt) (fun _ _ _ -> mt()) s (l,ll,[]) in
        (if List.is_empty args||prec_less l_not (lapp,L) then strm_not else surround strm_not)
        ++ prlist (pr_patt spc (lapp,L)) args, if not (List.is_empty args) then lapp else l_not

      | CPatPrim (_,p) ->
        pr_prim_token p, latom

      | CPatDelimiters (_,k,p) ->
        pr_delimiters k (pr_patt mt lsimplepatt p), 1
    in
    let loc = cases_pattern_expr_loc p in
    pr_with_comments loc
      (sep() ++ if prec_less prec inh then strm else surround strm)

  let pr_patt = pr_patt mt

  let pr_eqn pr (loc,pl,rhs) =
    let pl = List.map snd pl in
    spc() ++ hov 4
      (pr_with_comments loc
         (str "| " ++
            hov 0 (prlist_with_sep pr_bar (prlist_with_sep sep_v (pr_patt ltop)) pl
                   ++ str " =>") ++
            pr_sep_com spc (pr ltop) rhs))

  let begin_of_binder = function
  LocalRawDef((loc,_),_) -> fst (Loc.unloc loc)
    | LocalRawAssum((loc,_)::_,_,_) -> fst (Loc.unloc loc)
    | _ -> assert false

  let begin_of_binders = function
    | b::_ -> begin_of_binder b
    | _ -> 0

  let surround_impl k p =
    match k with
      | Explicit -> str"(" ++ p ++ str")"
      | Implicit -> str"{" ++ p ++ str"}"

  let surround_implicit k p =
    match k with
      | Explicit -> p
      | Implicit -> (str"{" ++ p ++ str"}")

  let pr_binder many pr (nal,k,t) =
    match k with
      | Generalized (b, b', t') ->
        assert (match b with Implicit -> true | _ -> false);
        begin match nal with
          |[loc,Anonymous] ->
            hov 1 (str"`" ++ (surround_impl b'
                                ((if t' then str "!" else mt ()) ++ pr t)))
          |[loc,Name id] ->
            hov 1 (str "`" ++ (surround_impl b'
                                 (pr_lident (loc,id) ++ str " : " ++
                                    (if t' then str "!" else mt()) ++ pr t)))
          |_ -> anomaly (Pp.str "List of generalized binders have alwais one element.")
        end
      | Default b ->
        match t with
          | CHole (_,_,Misctypes.IntroAnonymous,_) ->
            let s = prlist_with_sep spc pr_lname nal in
            hov 1 (surround_implicit b s)
          | _ ->
            let s = prlist_with_sep spc pr_lname nal ++ str " : " ++ pr t in
            hov 1 (if many then surround_impl b s else surround_implicit b s)

  let pr_binder_among_many pr_c = function
    | LocalRawAssum (nal,k,t) ->
      pr_binder true pr_c (nal,k,t)
    | LocalRawDef (na,c) ->
      let c,topt = match c with
        | CCast(_,c, (CastConv t|CastVM t|CastNative t)) -> c, t
        | _ -> c, CHole (Loc.ghost, None, Misctypes.IntroAnonymous, None) in
      surround (pr_lname na ++ pr_opt_type pr_c topt ++
                  str":=" ++ cut() ++ pr_c c)

  let pr_undelimited_binders sep pr_c =
    prlist_with_sep sep (pr_binder_among_many pr_c)

  let pr_delimited_binders kw sep pr_c bl =
    let n = begin_of_binders bl in
    match bl with
      | [LocalRawAssum (nal,k,t)] ->
        pr_com_at n ++ kw() ++ pr_binder false pr_c (nal,k,t)
      | LocalRawAssum _ :: _ as bdl ->
        pr_com_at n ++ kw() ++ pr_undelimited_binders sep pr_c bdl
      | _ -> assert false

  let pr_binders_gen pr_c sep is_open =
    if is_open then pr_delimited_binders mt sep pr_c
    else pr_undelimited_binders sep pr_c

  let rec extract_prod_binders = function
  (*  | CLetIn (loc,na,b,c) as x ->
      let bl,c = extract_prod_binders c in
      if bl = [] then [], x else LocalRawDef (na,b) :: bl, c*)
    | CProdN (loc,[],c) ->
      extract_prod_binders c
    | CProdN (loc,(nal,bk,t)::bl,c) ->
      let bl,c = extract_prod_binders (CProdN(loc,bl,c)) in
      LocalRawAssum (nal,bk,t) :: bl, c
    | c -> [], c

  let rec extract_lam_binders = function
  (*  | CLetIn (loc,na,b,c) as x ->
      let bl,c = extract_lam_binders c in
      if bl = [] then [], x else LocalRawDef (na,b) :: bl, c*)
    | CLambdaN (loc,[],c) ->
      extract_lam_binders c
    | CLambdaN (loc,(nal,bk,t)::bl,c) ->
      let bl,c = extract_lam_binders (CLambdaN(loc,bl,c)) in
      LocalRawAssum (nal,bk,t) :: bl, c
    | c -> [], c

  let split_lambda = function
    | CLambdaN (loc,[[na],bk,t],c) -> (na,t,c)
    | CLambdaN (loc,([na],bk,t)::bl,c) -> (na,t,CLambdaN(loc,bl,c))
    | CLambdaN (loc,(na::nal,bk,t)::bl,c) -> (na,t,CLambdaN(loc,(nal,bk,t)::bl,c))
    | _ -> anomaly (Pp.str "ill-formed fixpoint body")

  let rename na na' t c =
    match (na,na') with
      | (_,Name id), (_,Name id') ->
        (na',t,Topconstr.replace_vars_constr_expr (Id.Map.singleton id id') c)
      | (_,Name id), (_,Anonymous) -> (na,t,c)
      | _ -> (na',t,c)

  let split_product na' = function
    | CProdN (loc,[[na],bk,t],c) -> rename na na' t c
    | CProdN (loc,([na],bk,t)::bl,c) -> rename na na' t (CProdN(loc,bl,c))
    | CProdN (loc,(na::nal,bk,t)::bl,c) ->
      rename na na' t (CProdN(loc,(nal,bk,t)::bl,c))
    | _ -> anomaly (Pp.str "ill-formed fixpoint body")

  let rec split_fix n typ def =
    if Int.equal n 0 then ([],typ,def)
    else
      let (na,_,def) = split_lambda def in
      let (na,t,typ) = split_product na typ in
      let (bl,typ,def) = split_fix (n-1) typ def in
      (LocalRawAssum ([na],default_binder_kind,t)::bl,typ,def)

  let pr_recursive_decl pr pr_dangling dangling_with_for id bl annot t c =
    let pr_body =
      if dangling_with_for then pr_dangling else pr in
    pr_id id ++ str" " ++
      hov 0 (pr_undelimited_binders spc (pr ltop) bl ++ annot) ++
      pr_opt_type_spc pr t ++ str " :=" ++
      pr_sep_com (fun () -> brk(1,2)) (pr_body ltop) c

  let pr_guard_annot pr_aux bl (n,ro) =
    match n with
      | None -> mt ()
      | Some (loc, id) ->
        match (ro : Constrexpr.recursion_order_expr) with
          | CStructRec ->
            let names_of_binder = function
              | LocalRawAssum (nal,_,_) -> nal
              | LocalRawDef (_,_) -> []
            in let ids = List.flatten (List.map names_of_binder bl) in
               if List.length ids > 1 then
                 spc() ++ str "{" ++ keyword "struct" ++ spc () ++ pr_id id ++ str"}"
               else mt()
          | CWfRec c ->
            spc() ++ str "{" ++ keyword "wf" ++ spc () ++ pr_aux c ++ spc() ++ pr_id id ++ str"}"
          | CMeasureRec (m,r) ->
            spc() ++ str "{" ++ keyword "measure" ++ spc () ++ pr_aux m ++ spc() ++ pr_id id++
              (match r with None -> mt() | Some r -> str" on " ++ pr_aux r) ++ str"}"

  let pr_fixdecl pr prd dangling_with_for ((_,id),ro,bl,t,c) =
    let annot = pr_guard_annot (pr lsimpleconstr) bl ro in
    pr_recursive_decl pr prd dangling_with_for id bl annot t c

  let pr_cofixdecl pr prd dangling_with_for ((_,id),bl,t,c) =
    pr_recursive_decl pr prd dangling_with_for id bl (mt()) t c

  let pr_recursive pr_decl id = function
    | [] -> anomaly (Pp.str "(co)fixpoint with no definition")
    | [d1] -> pr_decl false d1
    | dl ->
      prlist_with_sep (fun () -> fnl() ++ keyword "with" ++ spc ())
        (pr_decl true) dl ++
        fnl() ++ keyword "for" ++ spc () ++ pr_id id

  let pr_asin pr (na,indnalopt) =
    (match na with (* Decision of printing "_" or not moved to constrextern.ml *)
      | Some na -> spc () ++ keyword "as" ++ spc () ++  pr_lname na
      | None -> mt ()) ++
      (match indnalopt with
        | None -> mt ()
        | Some t -> spc () ++ keyword "in" ++ spc () ++ pr_patt lsimplepatt t)

  let pr_case_item pr (tm,asin) =
    hov 0 (pr (lcast,E) tm ++ pr_asin pr asin)

  let pr_case_type pr po =
    match po with
      | None | Some (CHole (_,_,Misctypes.IntroAnonymous,_)) -> mt()
      | Some p ->
        spc() ++ hov 2 (keyword "return" ++ pr_sep_com spc (pr lsimpleconstr) p)

  let pr_simple_return_type pr na po =
    (match na with
      | Some (_,Name id) ->
        spc () ++ keyword "as" ++ spc () ++ pr_id id
      | _ -> mt ()) ++
      pr_case_type pr po

  let pr_proj pr pr_app a f l =
    hov 0 (pr (lproj,E) a ++ cut() ++ str ".(" ++ pr_app pr f l ++ str ")")

  let pr_appexpl pr (f,us) l =
    hov 2 (
      str "@" ++ pr_reference f ++
        pr_universe_instance us ++
        prlist (pr_sep_com spc (pr (lapp,L))) l)

  let pr_app pr a l =
    hov 2 (
      pr (lapp,L) a  ++
        prlist (fun a -> spc () ++ pr_expl_args pr a) l)

  let pr_forall () = keyword "forall" ++ spc ()

  let pr_fun () = keyword "fun" ++ spc ()

  let pr_fun_sep = spc () ++ str "=>"

  let pr_dangling_with_for sep pr inherited a =
    match a with
      | (CFix (_,_,[_])|CCoFix(_,_,[_])) ->
        pr sep (latom,E) a
      | _ ->
        pr sep inherited a

  let pr pr sep inherited a =
    let return (cmds, prec) = (tag_constr_expr a cmds, prec) in
    let (strm, prec) = match a with
      | CRef (r, us) ->
        return (pr_cref r us, latom)
      | CFix (_,id,fix) ->
        return (
          hov 0 (keyword "fix" ++ spc () ++
                   pr_recursive
                   (pr_fixdecl (pr mt) (pr_dangling_with_for mt pr)) (snd id) fix),
          lfix
        )
      | CCoFix (_,id,cofix) ->
        return (
          hov 0 (keyword "cofix" ++ spc () ++
                   pr_recursive
                   (pr_cofixdecl (pr mt) (pr_dangling_with_for mt pr)) (snd id) cofix),
          lfix
        )
      | CProdN _ ->
        let (bl,a) = extract_prod_binders a in
        return (
          hov 0 (
            hov 2 (pr_delimited_binders pr_forall spc
                     (pr mt ltop) bl) ++
              str "," ++ pr spc ltop a),
          lprod
        )
      | CLambdaN _ ->
        let (bl,a) = extract_lam_binders a in
        return (
          hov 0 (
            hov 2 (pr_delimited_binders pr_fun spc
                     (pr mt ltop) bl) ++
              pr_fun_sep ++ pr spc ltop a),
          llambda
        )
      | CLetIn (_,(_,Name x),(CFix(_,(_,x'),[_])|CCoFix(_,(_,x'),[_]) as fx), b)
          when Id.equal x x' ->
        return (
          hv 0 (
            hov 2 (keyword "let" ++ spc () ++ pr mt ltop fx
                   ++ spc ()
                   ++ keyword "in") ++
              pr spc ltop b),
          lletin
        )
      | CLetIn (_,x,a,b) ->
        return (
          hv 0 (
            hov 2 (keyword "let" ++ spc () ++ pr_lname x ++ str " :="
                   ++ pr spc ltop a ++ spc ()
                   ++ keyword "in") ++
              pr spc ltop b),
          lletin
        )
      | CAppExpl (_,(Some i,f,us),l) ->
        let l1,l2 = List.chop i l in
        let c,l1 = List.sep_last l1 in
        let p = pr_proj (pr mt) pr_appexpl c (f,us) l1 in
        if not (List.is_empty l2) then
          return (p ++ prlist (pr spc (lapp,L)) l2, lapp)
        else
          return (p, lproj)
      | CAppExpl (_,(None,Ident (_,var),us),[t])
      | CApp (_,(_,CRef(Ident(_,var),us)),[t,None])
          when Id.equal var Notation_ops.ldots_var ->
        return (
          hov 0 (str ".." ++ pr spc (latom,E) t ++ spc () ++ str ".."),
          larg
        )
      | CAppExpl (_,(None,f,us),l) ->
        return (pr_appexpl (pr mt) (f,us) l, lapp)
      | CApp (_,(Some i,f),l) ->
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
      | CApp (_,(None,a),l) ->
        return (pr_app (pr mt) a l, lapp)
      | CRecord (_,w,l) ->
        let beg =
          match w with
            | None ->
              spc ()
            | Some t ->
              spc () ++ pr spc ltop t ++ spc ()
              ++ keyword "with" ++ spc ()
        in
        return (
          hv 0 (str"{|" ++ beg ++
                  prlist_with_sep pr_semicolon
                  (fun (id, c) -> h 1 (pr_reference id ++ spc () ++ str":=" ++ pr spc ltop c)) l
                ++ str" |}"),
          latom
        )
      | CCases (_,LetPatternStyle,rtntypopt,[c,asin],[(_,[(loc,[p])],b)]) ->
        return (
          hv 0 (
            keyword "let" ++ spc () ++ str"'" ++
              hov 0 (pr_patt ltop p ++
                       pr_asin (pr_dangling_with_for mt pr) asin ++
                       str " :=" ++ pr spc ltop c ++
                       pr_case_type (pr_dangling_with_for mt pr) rtntypopt ++
                       spc () ++ keyword "in" ++ pr spc ltop b)),
          lletpattern
        )
      | CCases(_,_,rtntypopt,c,eqns) ->
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
      | CLetTuple (_,nal,(na,po),c,b) ->
        return (
          hv 0 (
            keyword "let" ++ spc () ++
              hov 0 (str "(" ++
                       prlist_with_sep sep_v pr_lname nal ++
                       str ")" ++
                       pr_simple_return_type (pr mt) na po ++ str " :=" ++
                       pr spc ltop c ++ spc ()
                     ++ keyword "in") ++
              pr spc ltop b),
          lletin
        )
      | CIf (_,c,(na,po),b1,b2) ->
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

      | CHole (_,_,Misctypes.IntroIdentifier id,_) ->
        return (str "?[" ++ pr_id id ++ str "]", latom)
      | CHole (_,_,Misctypes.IntroFresh id,_) ->
        return (str "?[?" ++ pr_id id ++ str "]", latom)
      | CHole (_,_,_,_) ->
        return (str "_", latom)
      | CEvar (_,n,l) ->
        return (pr_evar (pr mt) n l, latom)
      | CPatVar (_,p) ->
        return (str "?" ++ pr_patvar p, latom)
      | CSort (_,s) ->
        return (pr_glob_sort s, latom)
      | CCast (_,a,b) ->
        return (
          hv 0 (pr mt (lcast,L) a ++ cut () ++
                  match b with
                    | CastConv b -> str ":" ++ pr mt (-lcast,E) b
                    | CastVM b -> str "<:" ++ pr mt (-lcast,E) b
                    | CastNative b -> str "<<:" ++ pr mt (-lcast,E) b
                    | CastCoerce -> str ":>"),
          lcast
        )
      | CNotation (_,"( _ )",([t],[],[])) ->
        return (pr (fun()->str"(") (max_int,L) t ++ str")", latom)
      | CNotation (_,s,env) ->
        pr_notation (pr mt) (pr_binders_gen (pr mt ltop)) s env
      | CGeneralization (_,bk,ak,c) ->
        return (pr_generalization bk ak (pr mt ltop c), latom)
      | CPrim (_,p) ->
        return (pr_prim_token p, prec_of_prim_token p)
      | CDelimiters (_,sc,a) ->
        return (pr_delimiters sc (pr mt (ldelim,E) a), ldelim)
    in
    let loc = constr_loc a in
    pr_with_comments loc
      (sep() ++ if prec_less prec inherited then strm else surround strm)

  type term_pr = {
    pr_constr_expr   : constr_expr -> std_ppcmds;
    pr_lconstr_expr  : constr_expr -> std_ppcmds;
    pr_constr_pattern_expr  : constr_pattern_expr -> std_ppcmds;
    pr_lconstr_pattern_expr : constr_pattern_expr -> std_ppcmds
  }

  type precedence =  Ppextend.precedence * Ppextend.parenRelation
  let modular_constr_pr = pr
  let rec fix rf x = rf (fix rf) x
  let pr = fix modular_constr_pr mt

  let transf env c =
    if !Flags.beautify_file then
      let r = Constrintern.for_grammar (Constrintern.intern_constr env) c in
      Constrextern.extern_glob_constr (Termops.vars_of_env env) r
    else c

  let pr prec c = pr prec (transf (Global.env()) c)

  let pr_simpleconstr = function
    | CAppExpl (_,(None,f,us),[]) -> str "@" ++ pr_cref f us
    | c -> pr lsimpleconstr c

  let default_term_pr = {
    pr_constr_expr   = pr_simpleconstr;
    pr_lconstr_expr  = pr ltop;
    pr_constr_pattern_expr  = pr_simpleconstr;
    pr_lconstr_pattern_expr = pr ltop
  }

  let term_pr = ref default_term_pr

  let set_term_pr = (:=) term_pr

  let pr_constr_expr c   = !term_pr.pr_constr_expr   c
  let pr_lconstr_expr c  = !term_pr.pr_lconstr_expr  c
  let pr_constr_pattern_expr c  = !term_pr.pr_constr_pattern_expr  c
  let pr_lconstr_pattern_expr c = !term_pr.pr_lconstr_pattern_expr c

  let pr_cases_pattern_expr = pr_patt ltop

  let pr_binders = pr_undelimited_binders spc (pr ltop)

end

module Tag =
struct
  let keyword =
    let style = Terminal.make ~bold:true () in
    Ppstyle.make ~style ["constr"; "keyword"]

  let evar =
    let style = Terminal.make ~fg_color:`LIGHT_BLUE () in
    Ppstyle.make ~style ["constr"; "evar"]

  let univ =
    let style = Terminal.make ~bold:true ~fg_color:`YELLOW () in
    Ppstyle.make ~style ["constr"; "type"]

  let notation =
    let style = Terminal.make ~fg_color:`WHITE () in
    Ppstyle.make ~style ["constr"; "notation"]

  let variable =
    Ppstyle.make ["constr"; "variable"]

  let reference =
    let style = Terminal.make ~fg_color:`LIGHT_GREEN () in
    Ppstyle.make ~style ["constr"; "reference"]

  let path =
    let style = Terminal.make ~fg_color:`LIGHT_MAGENTA () in
    Ppstyle.make ~style ["constr"; "path"]

end

let do_not_tag _ x = x

(** Instantiating Make with tagging functions that only add style
    information. *)
include Make (struct
    let tag t s = Pp.tag (Pp.Tag.inj t Ppstyle.tag) s
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
end)

module Richpp = struct

  include Make (struct
    open Ppannotation
    let tag_keyword       = Pp.tag (Pp.Tag.inj AKeyword tag)
    let tag_type          = Pp.tag (Pp.Tag.inj AKeyword tag)
    let tag_evar          = do_not_tag ()
    let tag_unparsing unp = Pp.tag (Pp.Tag.inj (AUnparsing unp) tag)
    let tag_constr_expr e = Pp.tag (Pp.Tag.inj (AConstrExpr e) tag)
    let tag_path = do_not_tag ()
    let tag_ref = do_not_tag ()
    let tag_var = do_not_tag ()
  end)

end

