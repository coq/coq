(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Tacexpr
open Genredexpr
open Constrexpr
open Libnames
open Tok
open Compat
open Misctypes
open Locus
open Decl_kinds

open Pcoq


let all_with delta = Redops.make_red_flag [FBeta;FIota;FZeta;delta]

let tactic_kw = [ "->"; "<-" ; "by" ]
let _ = List.iter Lexer.add_keyword tactic_kw

let err () = raise Stream.Failure

(* Hack to parse "(x:=t)" as an explicit argument without conflicts with the *)
(* admissible notation "(x t)" *)
let test_lpar_id_coloneq =
  Gram.Entry.of_parser "lpar_id_coloneq"
    (fun strm ->
      match get_tok (stream_nth 0 strm) with
        | KEYWORD "(" ->
            (match get_tok (stream_nth 1 strm) with
              | IDENT _ ->
                  (match get_tok (stream_nth 2 strm) with
	            | KEYWORD ":=" -> ()
	            | _ -> err ())
	      | _ -> err ())
	| _ -> err ())

(* idem for (x:=t) and (1:=t) *)
let test_lpar_idnum_coloneq =
  Gram.Entry.of_parser "test_lpar_idnum_coloneq"
    (fun strm ->
      match get_tok (stream_nth 0 strm) with
        | KEYWORD "(" ->
            (match get_tok (stream_nth 1 strm) with
              | IDENT _ | INT _ ->
                  (match get_tok (stream_nth 2 strm) with
                    | KEYWORD ":=" -> ()
                    | _ -> err ())
              | _ -> err ())
        | _ -> err ())

(* idem for (x:t) *)
let test_lpar_id_colon =
  Gram.Entry.of_parser "lpar_id_colon"
    (fun strm ->
      match get_tok (stream_nth 0 strm) with
        | KEYWORD "(" ->
            (match get_tok (stream_nth 1 strm) with
              | IDENT _ ->
                  (match get_tok (stream_nth 2 strm) with
                    | KEYWORD ":" -> ()
                    | _ -> err ())
              | _ -> err ())
        | _ -> err ())

(* idem for (x1..xn:t) [n^2 complexity but exceptional use] *)
let check_for_coloneq =
  Gram.Entry.of_parser "lpar_id_colon"
    (fun strm ->
      let rec skip_to_rpar p n =
	match get_tok (List.last (Stream.npeek n strm)) with
        | KEYWORD "(" -> skip_to_rpar (p+1) (n+1)
        | KEYWORD ")" -> if Int.equal p 0 then n+1 else skip_to_rpar (p-1) (n+1)
	| KEYWORD "." -> err ()
	| _ -> skip_to_rpar p (n+1) in
      let rec skip_names n =
	match get_tok (List.last (Stream.npeek n strm)) with
        | IDENT _ | KEYWORD "_" -> skip_names (n+1)
	| KEYWORD ":" -> skip_to_rpar 0 (n+1) (* skip a constr *)
	| _ -> err () in
      let rec skip_binders n =
	match get_tok (List.last (Stream.npeek n strm)) with
        | KEYWORD "(" -> skip_binders (skip_names (n+1))
        | IDENT _ | KEYWORD "_" -> skip_binders (n+1)
	| KEYWORD ":=" -> ()
	| _ -> err () in
      match get_tok (stream_nth 0 strm) with
      | KEYWORD "(" -> skip_binders 2
      | _ -> err ())

let lookup_at_as_coma =
  Gram.Entry.of_parser "lookup_at_as_coma"
    (fun strm ->
      match get_tok (stream_nth 0 strm) with
	| KEYWORD (","|"at"|"as") -> ()
	| _ -> err ())

open Constr
open Prim
open Tactic

let mk_fix_tac (loc,id,bl,ann,ty) =
  let n =
    match bl,ann with
        [([_],_,_)], None -> 1
      | _, Some x ->
          let ids = List.map snd (List.flatten (List.map pi1 bl)) in
          (try List.index Names.Name.equal (snd x) ids
          with Not_found -> error "No such fix variable.")
      | _ -> error "Cannot guess decreasing argument of fix." in
  (id,n,CProdN(loc,bl,ty))

let mk_cofix_tac (loc,id,bl,ann,ty) =
  let _ = Option.map (fun (aloc,_) ->
    user_err_loc
      (aloc,"Constr:mk_cofix_tac",
       Pp.str"Annotation forbidden in cofix expression.")) ann in
  (id,CProdN(loc,bl,ty))

(* Functions overloaded by quotifier *)
let induction_arg_of_constr (c,lbind as clbind) = match lbind with
  | NoBindings ->
    begin
      try ElimOnIdent (Constrexpr_ops.constr_loc c,snd(Constrexpr_ops.coerce_to_id c))
      with e when Errors.noncritical e -> ElimOnConstr clbind
    end
  | _ -> ElimOnConstr clbind

let mkTacCase with_evar = function
  | [(clear,ElimOnConstr cl),(None,None),None],None ->
      TacCase (with_evar,(clear,cl))
  (* Reinterpret numbers as a notation for terms *)
  | [(clear,ElimOnAnonHyp n),(None,None),None],None ->
      TacCase (with_evar,
        (clear,(CPrim (Loc.ghost, Numeral (Bigint.of_int n)),
	 NoBindings)))
  (* Reinterpret ident as notations for variables in the context *)
  (* because we don't know if they are quantified or not *)
  | [(clear,ElimOnIdent id),(None,None),None],None ->
      TacCase (with_evar,(clear,(CRef (Ident id,None),NoBindings)))
  | ic ->
      if List.exists (function ((_, ElimOnAnonHyp _),_,_) -> true | _ -> false) (fst ic)
      then
	error "Use of numbers as direct arguments of 'case' is not supported.";
      TacInductionDestruct (false,with_evar,ic)

let rec mkCLambdaN_simple_loc loc bll c =
  match bll with
  | ((loc1,_)::_ as idl,bk,t) :: bll ->
      CLambdaN (loc,[idl,bk,t],mkCLambdaN_simple_loc (Loc.merge loc1 loc) bll c)
  | ([],_,_) :: bll -> mkCLambdaN_simple_loc loc bll c
  | [] -> c

let mkCLambdaN_simple bl c = match bl with
  | [] -> c
  | h :: _ ->
    let loc = Loc.merge (fst (List.hd (pi1 h))) (Constrexpr_ops.constr_loc c) in
    mkCLambdaN_simple_loc loc bl c

let loc_of_ne_list l = Loc.merge (fst (List.hd l)) (fst (List.last l))

let map_int_or_var f = function
  | ArgArg x -> ArgArg (f x)
  | ArgVar _ as y -> y

let all_concl_occs_clause = { onhyps=Some[]; concl_occs=AllOccurrences }

let merge_occurrences loc cl = function
  | None ->
      if Locusops.clause_with_generic_occurrences cl then (None, cl)
      else
	user_err_loc (loc,"",str "Found an \"at\" clause without \"with\" clause.")
  | Some (occs, p) ->
    let ans = match occs with
    | AllOccurrences -> cl
    | _ ->
      begin match cl with
      | { onhyps = Some []; concl_occs = AllOccurrences } ->
        { onhyps = Some []; concl_occs = occs }
      | { onhyps = Some [(AllOccurrences, id), l]; concl_occs = NoOccurrences } ->
        { cl with onhyps = Some [(occs, id), l] }
      | _ ->
        if Locusops.clause_with_generic_occurrences cl then
          user_err_loc (loc,"",str "Unable to interpret the \"at\" clause; move it in the \"in\" clause.")
        else
          user_err_loc (loc,"",str "Cannot use clause \"at\" twice.")
      end
    in
    (Some p, ans)

(* Auxiliary grammar rules *)

GEXTEND Gram
  GLOBAL: simple_tactic constr_with_bindings quantified_hypothesis
  bindings red_expr int_or_var open_constr uconstr
  simple_intropattern clause_dft_concl;

  int_or_var:
    [ [ n = integer  -> ArgArg n
      | id = identref -> ArgVar id ] ]
  ;
  nat_or_var:
    [ [ n = natural  -> ArgArg n
      | id = identref -> ArgVar id ] ]
  ;
  (* An identifier or a quotation meta-variable *)
  id_or_meta:
    [ [ id = identref -> id ] ]
  ;
  open_constr:
    [ [ c = constr -> ((),c) ] ]
  ;
  uconstr:
    [ [ c = constr -> c ] ]
  ;
  induction_arg:
    [ [ n = natural -> (None,ElimOnAnonHyp n)
      | c = constr_with_bindings -> (None,induction_arg_of_constr c)
      | "!"; c = constr_with_bindings -> (Some false,induction_arg_of_constr c)
    ] ]
  ;
  constr_with_bindings_arg:
    [ [ ">"; c = constr_with_bindings -> (Some true,c)
      | c = constr_with_bindings -> (None,c) ] ]
  ;
  quantified_hypothesis:
    [ [ id = ident -> NamedHyp id
      | n = natural -> AnonHyp n ] ]
  ;
  conversion:
    [ [ c = constr -> (None, c)
      | c1 = constr; "with"; c2 = constr -> (Some (AllOccurrences,c1),c2)
      | c1 = constr; "at"; occs = occs_nums; "with"; c2 = constr ->
          (Some (occs,c1), c2) ] ]
  ;
  occs_nums:
    [ [ nl = LIST1 nat_or_var -> OnlyOccurrences nl
      | "-"; n = nat_or_var; nl = LIST0 int_or_var ->
	  (* have used int_or_var instead of nat_or_var for compatibility *)
	   AllOccurrencesBut (List.map (map_int_or_var abs) (n::nl)) ] ]
  ;
  occs:
    [ [ "at"; occs = occs_nums -> occs | -> AllOccurrences ] ]
  ;
  pattern_occ:
    [ [ c = constr; nl = occs -> (nl,c) ] ]
  ;
  ref_or_pattern_occ:
    (* If a string, it is interpreted as a ref
       (anyway a Coq string does not reduce) *)
    [ [ c = smart_global; nl = occs -> nl,Inl c
      | c = constr; nl = occs -> nl,Inr c ] ]
  ;
  unfold_occ:
    [ [ c = smart_global; nl = occs -> (nl,c) ] ]
  ;
  intropatterns:
    [ [ l = LIST0 nonsimple_intropattern -> l ]]
  ;
  or_and_intropattern:
    [ [ "["; tc = LIST1 intropatterns SEP "|"; "]" -> tc
      | "()" -> [[]]
      | "("; si = simple_intropattern; ")" -> [[si]]
      | "("; si = simple_intropattern; ",";
             tc = LIST1 simple_intropattern SEP "," ; ")" -> [si::tc]
      | "("; si = simple_intropattern; "&";
	     tc = LIST1 simple_intropattern SEP "&" ; ")" ->
	  (* (A & B & C) is translated into (A,(B,C)) *)
	  let rec pairify = function
	    | ([]|[_]|[_;_]) as l -> [l]
	    | t::q -> [[t;(loc_of_ne_list q,IntroAction (IntroOrAndPattern (pairify q)))]]
	  in pairify (si::tc) ] ]
  ;
  equality_intropattern:
    [ [ "->" -> IntroRewrite true
      | "<-" -> IntroRewrite false
      | "[="; tc = intropatterns; "]" -> IntroInjection tc ] ]
  ;
  naming_intropattern:
    [ [ prefix = pattern_ident -> IntroFresh prefix
      | "?" -> IntroAnonymous
      | id = ident -> IntroIdentifier id ] ]
  ;
  nonsimple_intropattern:
    [ [ l = simple_intropattern -> l
      | "*" -> !@loc, IntroForthcoming true
      | "**" -> !@loc, IntroForthcoming false ]]
  ;
  simple_intropattern:
    [ [ pat = or_and_intropattern -> !@loc, IntroAction (IntroOrAndPattern pat)
      | pat = equality_intropattern -> !@loc, IntroAction pat
      | "_" -> !@loc, IntroAction IntroWildcard 
      | pat = simple_intropattern; "/"; c = constr ->
          !@loc, IntroAction (IntroApplyOn (c,pat))
      | pat = naming_intropattern -> !@loc, IntroNaming pat ] ]
  ;
  simple_binding:
    [ [ "("; id = ident; ":="; c = lconstr; ")" -> (!@loc, NamedHyp id, c)
      | "("; n = natural; ":="; c = lconstr; ")" -> (!@loc, AnonHyp n, c) ] ]
  ;
  bindings:
    [ [ test_lpar_idnum_coloneq; bl = LIST1 simple_binding ->
          ExplicitBindings bl
      | bl = LIST1 constr -> ImplicitBindings bl ] ]
  ;
  opt_bindings:
    [ [ bl = LIST1 bindings SEP "," -> bl | -> [NoBindings] ] ]
  ;
  constr_with_bindings:
    [ [ c = constr; l = with_bindings -> (c, l) ] ]
  ;
  with_bindings:
    [ [ "with"; bl = bindings -> bl | -> NoBindings ] ]
  ;
  red_flag:
    [ [ IDENT "beta" -> FBeta
      | IDENT "iota" -> FIota
      | IDENT "zeta" -> FZeta
      | IDENT "delta"; d = delta_flag -> d
    ] ]
  ;
  delta_flag:
    [ [ "-"; "["; idl = LIST1 smart_global; "]" -> FDeltaBut idl
      | "["; idl = LIST1 smart_global; "]" -> FConst idl
      | -> FDeltaBut []
    ] ]
  ;
  strategy_flag:
    [ [ s = LIST1 red_flag -> Redops.make_red_flag s
      | d = delta_flag -> all_with d
    ] ]
  ;
  red_tactic:
    [ [ IDENT "red" -> Red false
      | IDENT "hnf" -> Hnf
      | IDENT "simpl"; d = delta_flag; po = OPT ref_or_pattern_occ -> Simpl (all_with d,po)
      | IDENT "cbv"; s = strategy_flag -> Cbv s
      | IDENT "cbn"; s = strategy_flag -> Cbn s
      | IDENT "lazy"; s = strategy_flag -> Lazy s
      | IDENT "compute"; delta = delta_flag -> Cbv (all_with delta)
      | IDENT "vm_compute"; po = OPT ref_or_pattern_occ -> CbvVm po
      | IDENT "native_compute"; po = OPT ref_or_pattern_occ -> CbvNative po
      | IDENT "unfold"; ul = LIST1 unfold_occ SEP "," -> Unfold ul
      | IDENT "fold"; cl = LIST1 constr -> Fold cl
      | IDENT "pattern"; pl = LIST1 pattern_occ SEP"," -> Pattern pl ] ]
  ;
  (* This is [red_tactic] including possible extensions *)
  red_expr:
    [ [ IDENT "red" -> Red false
      | IDENT "hnf" -> Hnf
      | IDENT "simpl"; d = delta_flag; po = OPT ref_or_pattern_occ -> Simpl (all_with d,po)
      | IDENT "cbv"; s = strategy_flag -> Cbv s
      | IDENT "cbn"; s = strategy_flag -> Cbn s
      | IDENT "lazy"; s = strategy_flag -> Lazy s
      | IDENT "compute"; delta = delta_flag -> Cbv (all_with delta)
      | IDENT "vm_compute"; po = OPT ref_or_pattern_occ -> CbvVm po
      | IDENT "native_compute"; po = OPT ref_or_pattern_occ -> CbvNative po
      | IDENT "unfold"; ul = LIST1 unfold_occ SEP "," -> Unfold ul
      | IDENT "fold"; cl = LIST1 constr -> Fold cl
      | IDENT "pattern"; pl = LIST1 pattern_occ SEP"," -> Pattern pl
      | s = IDENT -> ExtraRedExpr s ] ]
  ;
  hypident:
    [ [ id = id_or_meta ->
          id,InHyp
      | "("; IDENT "type"; IDENT "of"; id = id_or_meta; ")" ->
	  id,InHypTypeOnly
      | "("; IDENT "value"; IDENT "of"; id = id_or_meta; ")" ->
	  id,InHypValueOnly
    ] ]
  ;
  hypident_occ:
    [ [ (id,l)=hypident; occs=occs -> ((occs,id),l) ] ]
  ;
  in_clause:
    [ [ "*"; occs=occs ->
          {onhyps=None; concl_occs=occs}
      | "*"; "|-"; occs=concl_occ ->
          {onhyps=None; concl_occs=occs}
      | hl=LIST0 hypident_occ SEP","; "|-"; occs=concl_occ ->
          {onhyps=Some hl; concl_occs=occs}
      | hl=LIST0 hypident_occ SEP"," ->
          {onhyps=Some hl; concl_occs=NoOccurrences} ] ]
  ;
  clause_dft_concl:
    [ [ "in"; cl = in_clause -> cl
      | occs=occs -> {onhyps=Some[]; concl_occs=occs}
      | -> all_concl_occs_clause ] ]
  ;
  clause_dft_all:
    [ [ "in"; cl = in_clause -> cl
      | -> {onhyps=None; concl_occs=AllOccurrences} ] ]
  ;
  opt_clause:
    [ [ "in"; cl = in_clause -> Some cl
      | "at"; occs = occs_nums -> Some {onhyps=Some[]; concl_occs=occs}
      | -> None ] ]
  ;
  concl_occ:
    [ [ "*"; occs = occs -> occs
      | -> NoOccurrences ] ]
  ;
  in_hyp_list:
    [ [ "in"; idl = LIST1 id_or_meta -> idl
      | -> [] ] ]
  ;
  in_hyp_as:
    [ [ "in"; id = id_or_meta; ipat = as_ipat -> Some (None,id,ipat)
      | -> None ] ]
  ;
  orient:
    [ [ "->" -> true
      | "<-" -> false
      | -> true ]]
  ;
  simple_binder:
    [ [ na=name -> ([na],Default Explicit,CHole (!@loc, Some (Evar_kinds.BinderType (snd na)), IntroAnonymous, None))
      | "("; nal=LIST1 name; ":"; c=lconstr; ")" -> (nal,Default Explicit,c)
    ] ]
  ;
  fixdecl:
    [ [ "("; id = ident; bl=LIST0 simple_binder; ann=fixannot;
        ":"; ty=lconstr; ")" -> (!@loc, id, bl, ann, ty) ] ]
  ;
  fixannot:
    [ [ "{"; IDENT "struct"; id=name; "}" -> Some id
      | -> None ] ]
  ;
  cofixdecl:
    [ [ "("; id = ident; bl=LIST0 simple_binder; ":"; ty=lconstr; ")" ->
        (!@loc, id, bl, None, ty) ] ]
  ;
  bindings_with_parameters:
    [ [ check_for_coloneq; "(";  id = ident; bl = LIST0 simple_binder;
        ":="; c = lconstr; ")" -> (id, mkCLambdaN_simple bl c) ] ]
  ;
  hintbases:
    [ [ "with"; "*" -> None
      | "with"; l = LIST1 [ x = IDENT -> x] -> Some l
      | -> Some [] ] ]
  ;
  auto_using:
    [ [ "using"; l = LIST1 constr SEP "," -> l
      | -> [] ] ]
  ;
  trivial:
    [ [ IDENT "trivial" -> Off
      | IDENT "info_trivial" -> Info
      | IDENT "debug"; IDENT "trivial" -> Debug ] ]
  ;
  auto:
    [ [ IDENT "auto" -> Off
      | IDENT "info_auto" -> Info
      | IDENT "debug"; IDENT "auto" -> Debug ] ]
  ;
  eliminator:
    [ [ "using"; el = constr_with_bindings -> el ] ]
  ;
  as_ipat:
    [ [ "as"; ipat = simple_intropattern -> Some ipat
      | -> None ] ]
  ;
  or_and_intropattern_loc:
    [ [ ipat = or_and_intropattern -> ArgArg (!@loc,ipat)
      | locid = identref -> ArgVar locid ] ]
  ;
  as_or_and_ipat:
    [ [ "as"; ipat = or_and_intropattern_loc -> Some ipat
      | -> None ] ]
  ;
  eqn_ipat:
    [ [ IDENT "eqn"; ":"; pat = naming_intropattern -> Some (!@loc, pat)
      | IDENT "_eqn"; ":"; pat = naming_intropattern ->
        let msg = "Obsolete syntax \"_eqn:H\" could be replaced by \"eqn:H\"" in
        msg_warning (strbrk msg); Some (!@loc, pat)
      | IDENT "_eqn" ->
        let msg = "Obsolete syntax \"_eqn\" could be replaced by \"eqn:?\"" in
        msg_warning (strbrk msg); Some (!@loc, IntroAnonymous)
      | -> None ] ]
  ;
  as_name:
    [ [ "as"; id = ident -> Names.Name id | -> Names.Anonymous ] ]
  ;
  by_tactic:
    [ [ "by"; tac = tactic_expr LEVEL "3" -> TacComplete tac
      | -> TacId [] ] ]
  ;
  opt_by_tactic:
    [ [ "by"; tac = tactic_expr LEVEL "3" -> Some tac
    | -> None ] ]
  ;
  rename :
    [ [ id1 = id_or_meta; IDENT "into"; id2 = id_or_meta -> (id1,id2) ] ]
  ;
  rewriter :
    [ [ "!"; c = constr_with_bindings -> (RepeatPlus,(None,c))
      | ["?"| LEFTQMARK]; c = constr_with_bindings_arg -> (RepeatStar,c)
      | n = natural; "!"; c = constr_with_bindings -> (Precisely n,(None,c))
      |	n = natural; ["?" | LEFTQMARK]; c = constr_with_bindings_arg -> (UpTo n,c)
      | n = natural; c = constr_with_bindings_arg -> (Precisely n,c)
      | c = constr_with_bindings -> (Precisely 1, (None,c))
      ] ]
  ;
  oriented_rewriter :
    [ [ b = orient; p = rewriter -> let (m,c) = p in (b,m,c) ] ]
  ;
  induction_clause:
    [ [ c = induction_arg; pat = as_or_and_ipat; eq = eqn_ipat; cl = opt_clause
        -> (c,(eq,pat),cl) ] ]
  ;
  induction_clause_list:
    [ [ ic = LIST1 induction_clause SEP ","; el = OPT eliminator;
        cl_tolerance = opt_clause ->
        (* Condition for accepting "in" at the end by compatibility *)
        match ic,el,cl_tolerance with
        | [c,pat,None],Some _,Some _ -> ([c,pat,cl_tolerance],el)
        | _,_,Some _ -> err ()
        | _,_,None -> (ic,el) ]]
  ;
  move_location:
    [ [ IDENT "after"; id = id_or_meta -> MoveAfter id
      | IDENT "before"; id = id_or_meta -> MoveBefore id
      | "at"; IDENT "top" -> MoveFirst
      | "at"; IDENT "bottom" -> MoveLast ] ]
  ;
  simple_tactic:
    [ [
      (* Basic tactics *)
        IDENT "intros"; pl = intropatterns -> TacAtom (!@loc, TacIntroPattern pl)
      | IDENT "intro"; id = ident; hto = move_location ->
	  TacAtom (!@loc, TacIntroMove (Some id, hto))
      | IDENT "intro"; hto = move_location -> TacAtom (!@loc, TacIntroMove (None, hto))
      | IDENT "intro"; id = ident -> TacAtom (!@loc, TacIntroMove (Some id, MoveLast))
      | IDENT "intro" -> TacAtom (!@loc, TacIntroMove (None, MoveLast))

      | IDENT "exact"; c = constr -> TacAtom (!@loc, TacExact c)

      | IDENT "apply"; cl = LIST1 constr_with_bindings_arg SEP ",";
          inhyp = in_hyp_as -> TacAtom (!@loc, TacApply (true,false,cl,inhyp))
      | IDENT "eapply"; cl = LIST1 constr_with_bindings_arg SEP ",";
          inhyp = in_hyp_as -> TacAtom (!@loc, TacApply (true,true,cl,inhyp))
      | IDENT "simple"; IDENT "apply";
          cl = LIST1 constr_with_bindings_arg SEP ",";
          inhyp = in_hyp_as -> TacAtom (!@loc, TacApply (false,false,cl,inhyp))
      | IDENT "simple"; IDENT "eapply";
          cl = LIST1 constr_with_bindings_arg SEP",";
          inhyp = in_hyp_as -> TacAtom (!@loc, TacApply (false,true,cl,inhyp))
      | IDENT "elim"; cl = constr_with_bindings_arg; el = OPT eliminator ->
          TacAtom (!@loc, TacElim (false,cl,el))
      | IDENT "eelim"; cl = constr_with_bindings_arg; el = OPT eliminator ->
          TacAtom (!@loc, TacElim (true,cl,el))
      | IDENT "case"; icl = induction_clause_list -> TacAtom (!@loc, mkTacCase false icl)
      | IDENT "ecase"; icl = induction_clause_list -> TacAtom (!@loc, mkTacCase true icl)
      | "fix"; n = natural -> TacAtom (!@loc, TacFix (None,n))
      | "fix"; id = ident; n = natural -> TacAtom (!@loc, TacFix (Some id,n))
      | "fix"; id = ident; n = natural; "with"; fd = LIST1 fixdecl ->
	  TacAtom (!@loc, TacMutualFix (id,n,List.map mk_fix_tac fd))
      | "cofix" -> TacAtom (!@loc, TacCofix None)
      | "cofix"; id = ident -> TacAtom (!@loc, TacCofix (Some id))
      | "cofix"; id = ident; "with"; fd = LIST1 cofixdecl ->
	  TacAtom (!@loc, TacMutualCofix (id,List.map mk_cofix_tac fd))

      | IDENT "pose"; (id,b) = bindings_with_parameters ->
	  TacAtom (!@loc, TacLetTac (Names.Name id,b,Locusops.nowhere,true,None))
      | IDENT "pose"; b = constr; na = as_name ->
	  TacAtom (!@loc, TacLetTac (na,b,Locusops.nowhere,true,None))
      | IDENT "set"; (id,c) = bindings_with_parameters; p = clause_dft_concl ->
	  TacAtom (!@loc, TacLetTac (Names.Name id,c,p,true,None))
      | IDENT "set"; c = constr; na = as_name; p = clause_dft_concl ->
          TacAtom (!@loc, TacLetTac (na,c,p,true,None))
      | IDENT "remember"; c = constr; na = as_name; e = eqn_ipat;
          p = clause_dft_all ->
          TacAtom (!@loc, TacLetTac (na,c,p,false,e))

      (* Alternative syntax for "pose proof c as id" *)
      | IDENT "assert"; test_lpar_id_coloneq; "("; (loc,id) = identref; ":=";
	  c = lconstr; ")" ->
	  TacAtom (!@loc, TacAssert (true,None,Some (!@loc,IntroNaming (IntroIdentifier id)),c))

      (* Alternative syntax for "assert c as id by tac" *)
      | IDENT "assert"; test_lpar_id_colon; "("; (loc,id) = identref; ":";
	  c = lconstr; ")"; tac=by_tactic ->
	  TacAtom (!@loc, TacAssert (true,Some tac,Some (!@loc,IntroNaming (IntroIdentifier id)),c))

      (* Alternative syntax for "enough c as id by tac" *)
      | IDENT "enough"; test_lpar_id_colon; "("; (loc,id) = identref; ":";
	  c = lconstr; ")"; tac=by_tactic ->
	  TacAtom (!@loc, TacAssert (false,Some tac,Some (!@loc,IntroNaming (IntroIdentifier id)),c))

      | IDENT "assert"; c = constr; ipat = as_ipat; tac = by_tactic ->
	  TacAtom (!@loc, TacAssert (true,Some tac,ipat,c))
      | IDENT "pose"; IDENT "proof"; c = lconstr; ipat = as_ipat ->
	  TacAtom (!@loc, TacAssert (true,None,ipat,c))
      | IDENT "enough"; c = constr; ipat = as_ipat; tac = by_tactic ->
	  TacAtom (!@loc, TacAssert (false,Some tac,ipat,c))

      | IDENT "generalize"; c = constr ->
	  TacAtom (!@loc, TacGeneralize [((AllOccurrences,c),Names.Anonymous)])
      | IDENT "generalize"; c = constr; l = LIST1 constr ->
	  let gen_everywhere c = ((AllOccurrences,c),Names.Anonymous) in
          TacAtom (!@loc, TacGeneralize (List.map gen_everywhere (c::l)))
      | IDENT "generalize"; c = constr; lookup_at_as_coma; nl = occs;
          na = as_name;
          l = LIST0 [","; c = pattern_occ; na = as_name -> (c,na)] ->
          TacAtom (!@loc, TacGeneralize (((nl,c),na)::l))
      | IDENT "generalize"; IDENT "dependent"; c = constr -> TacAtom (!@loc, TacGeneralizeDep c)

      (* Derived basic tactics *)
      | IDENT "induction"; ic = induction_clause_list ->
	  TacAtom (!@loc, TacInductionDestruct (true,false,ic))
      | IDENT "einduction"; ic = induction_clause_list ->
	  TacAtom (!@loc, TacInductionDestruct(true,true,ic))
      | IDENT "double"; IDENT "induction"; h1 = quantified_hypothesis;
	  h2 = quantified_hypothesis -> TacAtom (!@loc, TacDoubleInduction (h1,h2))
      | IDENT "destruct"; icl = induction_clause_list ->
	  TacAtom (!@loc, TacInductionDestruct(false,false,icl))
      | IDENT "edestruct";  icl = induction_clause_list ->
	  TacAtom (!@loc, TacInductionDestruct(false,true,icl))

      (* Automation tactic *)
      | d = trivial; lems = auto_using; db = hintbases -> TacAtom (!@loc, TacTrivial (d,lems,db))
      | d = auto; n = OPT int_or_var; lems = auto_using; db = hintbases ->
          TacAtom (!@loc, TacAuto (d,n,lems,db))

      (* Context management *)
      | IDENT "clear"; "-"; l = LIST1 id_or_meta -> TacAtom (!@loc, TacClear (true, l))
      | IDENT "clear"; l = LIST0 id_or_meta ->
        let is_empty = match l with [] -> true | _ -> false in
        TacAtom (!@loc, TacClear (is_empty, l))
      | IDENT "clearbody"; l = LIST1 id_or_meta -> TacAtom (!@loc, TacClearBody l)
      | IDENT "move"; hfrom = id_or_meta; hto = move_location ->
	  TacAtom (!@loc, TacMove (hfrom,hto))
      | IDENT "rename"; l = LIST1 rename SEP "," -> TacAtom (!@loc, TacRename l)

      (* Constructors *)
      | "exists"; bll = opt_bindings -> TacAtom (!@loc, TacSplit (false,bll))
      | IDENT "eexists"; bll = opt_bindings ->
	  TacAtom (!@loc, TacSplit (true,bll))
      (* Equivalence relations *)
      | IDENT "symmetry"; "in"; cl = in_clause -> TacAtom (!@loc, TacSymmetry cl)

      (* Equality and inversion *)
      | IDENT "rewrite"; l = LIST1 oriented_rewriter SEP ",";
	  cl = clause_dft_concl; t=opt_by_tactic -> TacAtom (!@loc, TacRewrite (false,l,cl,t))
      | IDENT "erewrite"; l = LIST1 oriented_rewriter SEP ",";
	  cl = clause_dft_concl; t=opt_by_tactic -> TacAtom (!@loc, TacRewrite (true,l,cl,t))
      | IDENT "dependent"; k =
	  [ IDENT "simple"; IDENT "inversion" -> SimpleInversion
	  | IDENT "inversion" -> FullInversion
	  | IDENT "inversion_clear" -> FullInversionClear ];
	  hyp = quantified_hypothesis;
	  ids = as_or_and_ipat; co = OPT ["with"; c = constr -> c] ->
	    TacAtom (!@loc, TacInversion (DepInversion (k,co,ids),hyp))
      | IDENT "simple"; IDENT "inversion";
	  hyp = quantified_hypothesis; ids = as_or_and_ipat;
	  cl = in_hyp_list ->
	    TacAtom (!@loc, TacInversion (NonDepInversion (SimpleInversion, cl, ids), hyp))
      | IDENT "inversion";
	  hyp = quantified_hypothesis; ids = as_or_and_ipat;
	  cl = in_hyp_list ->
	    TacAtom (!@loc, TacInversion (NonDepInversion (FullInversion, cl, ids), hyp))
      | IDENT "inversion_clear";
	  hyp = quantified_hypothesis; ids = as_or_and_ipat;
	  cl = in_hyp_list ->
	    TacAtom (!@loc, TacInversion (NonDepInversion (FullInversionClear, cl, ids), hyp))
      | IDENT "inversion"; hyp = quantified_hypothesis;
	  "using"; c = constr; cl = in_hyp_list ->
	    TacAtom (!@loc, TacInversion (InversionUsing (c,cl), hyp))

      (* Conversion *)
      | r = red_tactic; cl = clause_dft_concl -> TacAtom (!@loc, TacReduce (r, cl))
      (* Change ne doit pas s'appliquer dans un Definition t := Eval ... *)
      | IDENT "change"; (oc,c) = conversion; cl = clause_dft_concl ->
	  let p,cl = merge_occurrences (!@loc) cl oc in
	  TacAtom (!@loc, TacChange (p,c,cl))
    ] ]
  ;
END;;
