(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4use: "pa_extend.cmo" i*)

(* $Id$ *)

open Pp
open Pcoq
open Util
open Tacexpr
open Rawterm
open Genarg
open Topconstr
open Libnames
open Termops

let all_with delta = make_red_flag [FBeta;FIota;FZeta;delta]

let tactic_kw = [ "->"; "<-" ]
let _ = List.iter (fun s -> Lexer.add_token("",s)) tactic_kw

(* Hack to parse "(x:=t)" as an explicit argument without conflicts with the *)
(* admissible notation "(x t)" *)
let test_lpar_id_coloneq =
  Gram.Entry.of_parser "lpar_id_coloneq"
    (fun strm ->
      match Stream.npeek 1 strm with
        | [("","(")] ->
            (match Stream.npeek 2 strm with
              | [_; ("IDENT",s)] ->
                  (match Stream.npeek 3 strm with
	            | [_; _; ("", ":=")] -> ()
	            | _ -> raise Stream.Failure)
	      | _ -> raise Stream.Failure)
	| _ -> raise Stream.Failure)

(* idem for (x:=t) and (1:=t) *)
let test_lpar_idnum_coloneq =
  Gram.Entry.of_parser "test_lpar_idnum_coloneq"
    (fun strm ->
      match Stream.npeek 1 strm with
        | [("","(")] ->
            (match Stream.npeek 2 strm with
              | [_; (("IDENT"|"INT"),_)] ->
                  (match Stream.npeek 3 strm with
                    | [_; _; ("", ":=")] -> ()
                    | _ -> raise Stream.Failure)
              | _ -> raise Stream.Failure)
        | _ -> raise Stream.Failure)

(* idem for (x:t) *)
let test_lpar_id_colon =
  Gram.Entry.of_parser "lpar_id_colon"
    (fun strm ->
      match Stream.npeek 1 strm with
        | [("","(")] ->
            (match Stream.npeek 2 strm with
              | [_; ("IDENT",id)] ->
                  (match Stream.npeek 3 strm with
                    | [_; _; ("", ":")] -> ()
                    | _ -> raise Stream.Failure)
              | _ -> raise Stream.Failure)
        | _ -> raise Stream.Failure)

(* idem for (x1..xn:t) [n^2 complexity but exceptional use] *)
let check_for_coloneq =
  Gram.Entry.of_parser "lpar_id_colon"
    (fun strm ->
      let rec skip_to_rpar p n =
	match list_last (Stream.npeek n strm) with
        | ("","(") -> skip_to_rpar (p+1) (n+1)
        | ("",")") -> if p=0 then n+1 else skip_to_rpar (p-1) (n+1)
	| ("",".") -> raise Stream.Failure
	| _ -> skip_to_rpar p (n+1) in
      let rec skip_names n =
	match list_last (Stream.npeek n strm) with
        | ("IDENT",_) | ("","_") -> skip_names (n+1)
	| ("",":") -> skip_to_rpar 0 (n+1) (* skip a constr *)
	| _ -> raise Stream.Failure in
      let rec skip_binders n =
	match list_last (Stream.npeek n strm) with
        | ("","(") -> skip_binders (skip_names (n+1))
        | ("IDENT",_) | ("","_") -> skip_binders (n+1)
	| ("",":=") -> ()
	| _ -> raise Stream.Failure in
      match Stream.npeek 1 strm with
      | [("","(")] -> skip_binders 2
      | _ -> raise Stream.Failure)

let guess_lpar_ipat s strm =
  match Stream.npeek 1 strm with
    | [("","(")] ->
        (match Stream.npeek 2 strm with
          | [_; ("",("("|"["))] -> ()
          | [_; ("IDENT",_)] ->
              (match Stream.npeek 3 strm with
                | [_; _; ("", s')] when s = s' -> ()
                | _ -> raise Stream.Failure)
          | _ -> raise Stream.Failure)
    | _ -> raise Stream.Failure

let guess_lpar_coloneq =
  Gram.Entry.of_parser "guess_lpar_coloneq" (guess_lpar_ipat ":=")

let guess_lpar_colon =
  Gram.Entry.of_parser "guess_lpar_colon" (guess_lpar_ipat ":")

let lookup_at_as_coma =
  Gram.Entry.of_parser "lookup_at_as_coma"
    (fun strm ->
      match Stream.npeek 1 strm with
	| [("",(","|"at"|"as"))] -> ()
	| _ -> raise Stream.Failure)

open Constr
open Prim
open Tactic

let mk_fix_tac (loc,id,bl,ann,ty) =
  let n =
    match bl,ann with
        [([_],_,_)], None -> 1
      | _, Some x ->
          let ids = List.map snd (List.flatten (List.map pi1 bl)) in
          (try list_index (snd x) ids
          with Not_found -> error "No such fix variable.")
      | _ -> error "Cannot guess decreasing argument of fix." in
  (id,n,CProdN(loc,bl,ty))

let mk_cofix_tac (loc,id,bl,ann,ty) =
  let _ = Option.map (fun (aloc,_) ->
    Util.user_err_loc
      (aloc,"Constr:mk_cofix_tac",
       Pp.str"Annotation forbidden in cofix expression.")) ann in
  (id,CProdN(loc,bl,ty))

(* Functions overloaded by quotifier *)
let induction_arg_of_constr (c,lbind as clbind) =
  if lbind = NoBindings then
    try ElimOnIdent (constr_loc c,snd(coerce_to_id c))
    with _ -> ElimOnConstr clbind
  else ElimOnConstr clbind

let rec mkCLambdaN_simple_loc loc bll c =
  match bll with
  | ((loc1,_)::_ as idl,bk,t) :: bll ->
      CLambdaN (loc,[idl,bk,t],mkCLambdaN_simple_loc (join_loc loc1 loc) bll c)
  | ([],_,_) :: bll -> mkCLambdaN_simple_loc loc bll c
  | [] -> c

let mkCLambdaN_simple bl c =
  if bl=[] then c
  else
    let loc = join_loc (fst (List.hd (pi1 (List.hd bl)))) (constr_loc c) in
    mkCLambdaN_simple_loc loc bl c

let loc_of_ne_list l = join_loc (fst (List.hd l)) (fst (list_last l))

let map_int_or_var f = function
  | Rawterm.ArgArg x -> Rawterm.ArgArg (f x)
  | Rawterm.ArgVar _ as y -> y

(* Auxiliary grammar rules *)

GEXTEND Gram
  GLOBAL: simple_tactic constr_with_bindings quantified_hypothesis
  bindings red_expr int_or_var open_constr casted_open_constr
  simple_intropattern;

  int_or_var:
    [ [ n = integer  -> Rawterm.ArgArg n
      | id = identref -> Rawterm.ArgVar id ] ]
  ;
  nat_or_var:
    [ [ n = natural  -> Rawterm.ArgArg n
      | id = identref -> Rawterm.ArgVar id ] ]
  ;
  (* An identifier or a quotation meta-variable *)
  id_or_meta:
    [ [ id = identref -> AI id

      (* This is used in quotations *)
      | id = METAIDENT -> MetaId (loc,id) ] ]
  ;
  (* A number or a quotation meta-variable *)
  num_or_meta:
    [ [ n = integer -> AI n
      |	id = METAIDENT -> MetaId (loc,id)
      ] ]
  ;
  open_constr:
    [ [ c = constr -> ((),c) ] ]
  ;
  casted_open_constr:
    [ [ c = constr -> ((),c) ] ]
  ;
  induction_arg:
    [ [ n = natural -> ElimOnAnonHyp n
      | c = constr_with_bindings -> induction_arg_of_constr c
    ] ]
  ;
  quantified_hypothesis:
    [ [ id = ident -> NamedHyp id
      | n = natural -> AnonHyp n ] ]
  ;
  conversion:
    [ [ c = constr -> (None, c)
      | c1 = constr; "with"; c2 = constr -> (Some (all_occurrences_expr,c1),c2)
      | c1 = constr; "at"; occs = occs_nums; "with"; c2 = constr ->
          (Some (occs,c1), c2) ] ]
  ;
  occs_nums:
    [ [ nl = LIST1 nat_or_var -> no_occurrences_expr_but nl
      | "-"; n = nat_or_var; nl = LIST0 int_or_var ->
	  (* have used int_or_var instead of nat_or_var for compatibility *)
	   all_occurrences_expr_but (List.map (map_int_or_var abs) (n::nl)) ] ]
  ;
  occs:
    [ [ "at"; occs = occs_nums -> occs | -> all_occurrences_expr_but [] ] ]
  ;
  pattern_occ:
    [ [ c = constr; nl = occs -> (nl,c) ] ]
  ;
  unfold_occ:
    [ [ c = smart_global; nl = occs -> (nl,c) ] ]
  ;
  intropatterns:
    [ [ l = LIST0 simple_intropattern -> l ]]
  ;
  disjunctive_intropattern:
    [ [ "["; tc = LIST1 intropatterns SEP "|"; "]" -> loc,IntroOrAndPattern tc
      | "()" -> loc,IntroOrAndPattern [[]]
      | "("; si = simple_intropattern; ")" -> loc,IntroOrAndPattern [[si]]
      | "("; si = simple_intropattern; ",";
             tc = LIST1 simple_intropattern SEP "," ; ")" ->
	       loc,IntroOrAndPattern [si::tc]
      | "("; si = simple_intropattern; "&";
	     tc = LIST1 simple_intropattern SEP "&" ; ")" ->
	  (* (A & B & C) is translated into (A,(B,C)) *)
	  let rec pairify = function
	    | ([]|[_]|[_;_]) as l -> IntroOrAndPattern [l]
	    | t::q -> IntroOrAndPattern [[t;(loc_of_ne_list q,pairify q)]]
	  in loc,pairify (si::tc) ] ]
  ;
  naming_intropattern:
    [ [ prefix = pattern_ident -> loc, IntroFresh prefix
      | "?" -> loc, IntroAnonymous
      | id = ident -> loc, IntroIdentifier id
      | "*" -> loc, IntroForthcoming true
      | "**" -> loc, IntroForthcoming false ] ]
  ;
  intropattern_modifier:
    [ [ IDENT "_eqn";
        id = [ ":"; id = naming_intropattern -> id | -> loc, IntroAnonymous ]
        -> id ] ]
  ;
  simple_intropattern:
    [ [ pat = disjunctive_intropattern -> pat
      | pat = naming_intropattern -> pat
      | "_" -> loc, IntroWildcard
      | "->" -> loc, IntroRewrite true
      | "<-" -> loc, IntroRewrite false ] ]
  ;
  simple_binding:
    [ [ "("; id = ident; ":="; c = lconstr; ")" -> (loc, NamedHyp id, c)
      | "("; n = natural; ":="; c = lconstr; ")" -> (loc, AnonHyp n, c) ] ]
  ;
  bindings:
    [ [ test_lpar_idnum_coloneq; bl = LIST1 simple_binding ->
          ExplicitBindings bl
      | bl = LIST1 constr -> ImplicitBindings bl ] ]
  ;
  opt_bindings:
    [ [ bl = bindings -> bl | -> NoBindings ] ]
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
    [ [ s = LIST1 red_flag -> make_red_flag s
      | d = delta_flag -> all_with d
    ] ]
  ;
  red_tactic:
    [ [ IDENT "red" -> Red false
      | IDENT "hnf" -> Hnf
      | IDENT "simpl"; po = OPT pattern_occ -> Simpl po
      | IDENT "cbv"; s = strategy_flag -> Cbv s
      | IDENT "lazy"; s = strategy_flag -> Lazy s
      | IDENT "compute"; delta = delta_flag -> Cbv (all_with delta)
      | IDENT "vm_compute" -> CbvVm
      | IDENT "unfold"; ul = LIST1 unfold_occ SEP "," -> Unfold ul
      | IDENT "fold"; cl = LIST1 constr -> Fold cl
      | IDENT "pattern"; pl = LIST1 pattern_occ SEP"," -> Pattern pl ] ]
  ;
  (* This is [red_tactic] including possible extensions *)
  red_expr:
    [ [ IDENT "red" -> Red false
      | IDENT "hnf" -> Hnf
      | IDENT "simpl"; po = OPT pattern_occ -> Simpl po
      | IDENT "cbv"; s = strategy_flag -> Cbv s
      | IDENT "lazy"; s = strategy_flag -> Lazy s
      | IDENT "compute"; delta = delta_flag -> Cbv (all_with delta)
      | IDENT "vm_compute" -> CbvVm
      | IDENT "unfold"; ul = LIST1 unfold_occ -> Unfold ul
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
          {onhyps=Some hl; concl_occs=no_occurrences_expr} ] ]
  ;
  clause_dft_concl:
    [ [ "in"; cl = in_clause -> cl
      | occs=occs -> {onhyps=Some[]; concl_occs=occs}
      | -> {onhyps=Some[]; concl_occs=all_occurrences_expr} ] ]
  ;
  clause_dft_all:
    [ [ "in"; cl = in_clause -> cl
      | -> {onhyps=None; concl_occs=all_occurrences_expr} ] ]
  ;
  opt_clause:
    [ [ "in"; cl = in_clause -> Some cl | -> None ] ]
  ;
  concl_occ:
    [ [ "*"; occs = occs -> occs
      | -> no_occurrences_expr ] ]
  ;
  in_hyp_list:
    [ [ "in"; idl = LIST1 id_or_meta -> idl
      | -> [] ] ]
  ;
  in_hyp_as:
    [ [ "in"; id = id_or_meta; ipat = as_ipat -> Some (id,ipat)
      | -> None ] ]
  ;
  orient:
    [ [ "->" -> true
      | "<-" -> false
      | -> true ]]
  ;
  simple_binder:
    [ [ na=name -> ([na],Default Explicit,CHole (loc, None))
      | "("; nal=LIST1 name; ":"; c=lconstr; ")" -> (nal,Default Explicit,c)
    ] ]
  ;
  fixdecl:
    [ [ "("; id = ident; bl=LIST0 simple_binder; ann=fixannot;
        ":"; ty=lconstr; ")" -> (loc,id,bl,ann,ty) ] ]
  ;
  fixannot:
    [ [ "{"; IDENT "struct"; id=name; "}" -> Some id
      | -> None ] ]
  ;
  cofixdecl:
    [ [ "("; id = ident; bl=LIST0 simple_binder; ":"; ty=lconstr; ")" ->
        (loc,id,bl,None,ty) ] ]
  ;
  bindings_with_parameters:
    [ [ check_for_coloneq; "(";  id = ident; bl = LIST0 simple_binder;
        ":="; c = lconstr; ")" -> (id, mkCLambdaN_simple bl c) ] ]
  ;
  hintbases:
    [ [ "with"; "*" -> None
      | "with"; l = LIST1 IDENT -> Some l
      | -> Some [] ] ]
  ;
  auto_using:
    [ [ "using"; l = LIST1 constr SEP "," -> l
      | -> [] ] ]
  ;
  eliminator:
    [ [ "using"; el = constr_with_bindings -> el ] ]
  ;
  as_ipat:
    [ [ "as"; ipat = simple_intropattern -> Some ipat
      | -> None ] ]
  ;
  with_inversion_names:
    [ [ "as"; ipat = simple_intropattern -> Some ipat
      | -> None ] ]
  ;
  with_induction_names:
    [ [ "as"; ipat = simple_intropattern; eq = OPT intropattern_modifier
        -> (eq,Some ipat)
      | -> (None,None) ] ]
  ;
  as_name:
    [ [ "as"; id = ident -> Names.Name id | -> Names.Anonymous ] ]
  ;
  by_tactic:
    [ [ IDENT "by"; tac = tactic_expr LEVEL "3" -> TacComplete tac
      | -> TacId [] ] ]
  ;
  opt_by_tactic:
    [ [ IDENT "by"; tac = tactic_expr LEVEL "3" -> Some tac
    | -> None ] ]
  ;
  rename :
    [ [ id1 = id_or_meta; IDENT "into"; id2 = id_or_meta -> (id1,id2) ] ]
  ;
  rewriter :
    [ [ "!"; c = constr_with_bindings -> (RepeatPlus,c)
      | ["?"| LEFTQMARK]; c = constr_with_bindings -> (RepeatStar,c)
      | n = natural; "!"; c = constr_with_bindings -> (Precisely n,c)
      |	n = natural; ["?" | LEFTQMARK]; c = constr_with_bindings -> (UpTo n,c)
      | n = natural; c = constr_with_bindings -> (Precisely n,c)
      | c = constr_with_bindings -> (Precisely 1, c)
      ] ]
  ;
  oriented_rewriter :
    [ [ b = orient; p = rewriter -> let (m,c) = p in (b,m,c) ] ]
  ;
  induction_clause:
    [ [ lc = LIST1 induction_arg; ipats = with_induction_names;
        el = OPT eliminator; cl = opt_clause -> (lc,el,ipats,cl) ] ]
  ;
  move_location:
    [ [ IDENT "after"; id = id_or_meta -> MoveAfter id
      | IDENT "before"; id = id_or_meta -> MoveBefore id
      | "at"; IDENT "bottom" -> MoveToEnd true
      | "at"; IDENT "top" -> MoveToEnd false ] ]
  ;
  simple_tactic:
    [ [
      (* Basic tactics *)
        IDENT "intros"; IDENT "until"; id = quantified_hypothesis ->
	  TacIntrosUntil id
      | IDENT "intros"; pl = intropatterns -> TacIntroPattern pl
      | IDENT "intro"; id = ident; hto = move_location ->
	  TacIntroMove (Some id, hto)
      | IDENT "intro"; hto = move_location -> TacIntroMove (None, hto)
      | IDENT "intro"; id = ident -> TacIntroMove (Some id, no_move)
      | IDENT "intro" -> TacIntroMove (None, no_move)

      | IDENT "assumption" -> TacAssumption
      | IDENT "exact"; c = constr -> TacExact c
      | IDENT "exact_no_check"; c = constr -> TacExactNoCheck c
      | IDENT "vm_cast_no_check"; c = constr -> TacVmCastNoCheck c

      | IDENT "apply"; cl = LIST1 constr_with_bindings SEP ",";
          inhyp = in_hyp_as -> TacApply (true,false,cl,inhyp)
      | IDENT "eapply"; cl = LIST1 constr_with_bindings SEP ",";
          inhyp = in_hyp_as -> TacApply (true,true,cl,inhyp)
      | IDENT "simple"; IDENT "apply"; cl = LIST1 constr_with_bindings SEP ",";
          inhyp = in_hyp_as -> TacApply (false,false,cl,inhyp)
      | IDENT "simple"; IDENT "eapply"; cl = LIST1 constr_with_bindings SEP",";
          inhyp = in_hyp_as -> TacApply (false,true,cl,inhyp)
      | IDENT "elim"; cl = constr_with_bindings; el = OPT eliminator ->
          TacElim (false,cl,el)
      | IDENT "eelim"; cl = constr_with_bindings; el = OPT eliminator ->
          TacElim (true,cl,el)
      | IDENT "elimtype"; c = constr -> TacElimType c
      | IDENT "case"; cl = constr_with_bindings -> TacCase (false,cl)
      | IDENT "ecase"; cl = constr_with_bindings -> TacCase (true,cl)
      | IDENT "casetype"; c = constr -> TacCaseType c
      | "fix"; n = natural -> TacFix (None,n)
      | "fix"; id = ident; n = natural -> TacFix (Some id,n)
      | "fix"; id = ident; n = natural; "with"; fd = LIST1 fixdecl ->
	  TacMutualFix (false,id,n,List.map mk_fix_tac fd)
      | "cofix" -> TacCofix None
      | "cofix"; id = ident -> TacCofix (Some id)
      | "cofix"; id = ident; "with"; fd = LIST1 cofixdecl ->
	  TacMutualCofix (false,id,List.map mk_cofix_tac fd)

      | IDENT "pose"; (id,b) = bindings_with_parameters ->
	  TacLetTac (Names.Name id,b,nowhere,true)
      | IDENT "pose"; b = constr; na = as_name ->
	  TacLetTac (na,b,nowhere,true)
      | IDENT "set"; (id,c) = bindings_with_parameters; p = clause_dft_concl ->
	  TacLetTac (Names.Name id,c,p,true)
      | IDENT "set"; c = constr; na = as_name; p = clause_dft_concl ->
          TacLetTac (na,c,p,true)
      | IDENT "remember"; c = constr; na = as_name; p = clause_dft_all ->
          TacLetTac (na,c,p,false)

      (* Begin compatibility *)
      | IDENT "assert"; test_lpar_id_coloneq; "("; (loc,id) = identref; ":=";
	  c = lconstr; ")" ->
	  TacAssert (None,Some (loc,IntroIdentifier id),c)
      | IDENT "assert"; test_lpar_id_colon; "("; (loc,id) = identref; ":";
	  c = lconstr; ")"; tac=by_tactic ->
	  TacAssert (Some tac,Some (loc,IntroIdentifier id),c)
      (* End compatibility *)

      | IDENT "assert"; c = constr; ipat = as_ipat; tac = by_tactic ->
	  TacAssert (Some tac,ipat,c)
      | IDENT "pose"; IDENT "proof"; c = lconstr; ipat = as_ipat ->
	  TacAssert (None,ipat,c)

      | IDENT "cut"; c = constr -> TacCut c
      | IDENT "generalize"; c = constr ->
	  TacGeneralize [((all_occurrences_expr,c),Names.Anonymous)]
      | IDENT "generalize"; c = constr; l = LIST1 constr ->
	  let gen_everywhere c = ((all_occurrences_expr,c),Names.Anonymous) in
          TacGeneralize (List.map gen_everywhere (c::l))
      | IDENT "generalize"; c = constr; lookup_at_as_coma; nl = occs;
          na = as_name;
          l = LIST0 [","; c = pattern_occ; na = as_name -> (c,na)] ->
          TacGeneralize (((nl,c),na)::l)
      | IDENT "generalize"; IDENT "dependent"; c = constr -> TacGeneralizeDep c

      | IDENT "specialize"; n = OPT natural; lcb = constr_with_bindings ->
	  TacSpecialize (n,lcb)
      | IDENT "lapply"; c = constr -> TacLApply c

      (* Derived basic tactics *)
      | IDENT "simple"; IDENT"induction"; h = quantified_hypothesis ->
          TacSimpleInductionDestruct (true,h)
      | IDENT "induction"; ic = induction_clause ->
	  TacInductionDestruct (true,false,[ic])
      | IDENT "einduction"; ic = induction_clause ->
	  TacInductionDestruct(true,true,[ic])
      | IDENT "double"; IDENT "induction"; h1 = quantified_hypothesis;
	  h2 = quantified_hypothesis -> TacDoubleInduction (h1,h2)
      | IDENT "simple"; IDENT "destruct"; h = quantified_hypothesis ->
          TacSimpleInductionDestruct (false,h)
      | IDENT "destruct"; ic = induction_clause ->
	  TacInductionDestruct(false,false,[ic])
      | IDENT "edestruct";  ic = induction_clause ->
	  TacInductionDestruct(false,true,[ic])
      | IDENT "decompose"; IDENT "record" ; c = constr -> TacDecomposeAnd c
      | IDENT "decompose"; IDENT "sum"; c = constr -> TacDecomposeOr c
      | IDENT "decompose"; "["; l = LIST1 smart_global; "]"; c = constr
        -> TacDecompose (l,c)

      (* Automation tactic *)
      | IDENT "trivial"; lems = auto_using; db = hintbases ->
	  TacTrivial (lems,db)
      | IDENT "auto"; n = OPT int_or_var; lems = auto_using; db = hintbases ->
	  TacAuto (n,lems,db)

(* Obsolete since V8.0
      | IDENT "autotdb"; n = OPT natural -> TacAutoTDB n
      | IDENT "cdhyp"; id = identref -> TacDestructHyp (true,id)
      | IDENT "dhyp";  id = identref -> TacDestructHyp (false,id)
      | IDENT "dconcl"  -> TacDestructConcl
      | IDENT "superauto"; l = autoargs -> TacSuperAuto l
*)
      | IDENT "auto"; IDENT "decomp"; p = OPT natural;
          lems = auto_using -> TacDAuto (None,p,lems)
      | IDENT "auto"; n = OPT int_or_var; IDENT "decomp"; p = OPT natural;
          lems = auto_using -> TacDAuto (n,p,lems)

      (* Context management *)
      | IDENT "clear"; "-"; l = LIST1 id_or_meta -> TacClear (true, l)
      | IDENT "clear"; l = LIST0 id_or_meta -> TacClear (l=[], l)
      | IDENT "clearbody"; l = LIST1 id_or_meta -> TacClearBody l
      | IDENT "move"; hfrom = id_or_meta; hto = move_location ->
	  TacMove (true,hfrom,hto)
      | IDENT "rename"; l = LIST1 rename SEP "," -> TacRename l
      | IDENT "revert"; l = LIST1 id_or_meta -> TacRevert l

      (* Constructors *)
      | IDENT "left";   bl = with_bindings -> TacLeft  (false,bl)
      | IDENT "eleft";  bl = with_bindings -> TacLeft  (true,bl)
      | IDENT "right";  bl = with_bindings -> TacRight (false,bl)
      | IDENT "eright"; bl = with_bindings -> TacRight (true,bl)
      | IDENT "split";  bl = with_bindings -> TacSplit (false,false,[bl])
      | IDENT "esplit"; bl = with_bindings -> TacSplit (true,false,[bl])
      | "exists"; bll = LIST1 opt_bindings SEP "," -> TacSplit (false,true,bll)
      | IDENT "eexists"; bll = LIST1 opt_bindings SEP "," ->
	  TacSplit (true,true,bll)
      | IDENT "constructor"; n = num_or_meta; l = with_bindings ->
	  TacConstructor (false,n,l)
      | IDENT "econstructor"; n = num_or_meta; l = with_bindings ->
	  TacConstructor (true,n,l)
      | IDENT "constructor"; t = OPT tactic -> TacAnyConstructor (false,t)
      | IDENT "econstructor"; t = OPT tactic -> TacAnyConstructor (true,t)

      (* Equivalence relations *)
      | IDENT "reflexivity" -> TacReflexivity
      | IDENT "symmetry"; cl = clause_dft_concl -> TacSymmetry cl
      | IDENT "transitivity"; c = constr -> TacTransitivity (Some c)
      | IDENT "etransitivity" -> TacTransitivity None

      (* Equality and inversion *)
      | IDENT "rewrite"; l = LIST1 oriented_rewriter SEP ",";
	  cl = clause_dft_concl; t=opt_by_tactic -> TacRewrite (false,l,cl,t)
      | IDENT "erewrite"; l = LIST1 oriented_rewriter SEP ",";
	  cl = clause_dft_concl; t=opt_by_tactic -> TacRewrite (true,l,cl,t)
      | IDENT "dependent"; k =
	  [ IDENT "simple"; IDENT "inversion" -> SimpleInversion
	  | IDENT "inversion" -> FullInversion
	  | IDENT "inversion_clear" -> FullInversionClear ];
	  hyp = quantified_hypothesis;
	  ids = with_inversion_names; co = OPT ["with"; c = constr -> c] ->
	    TacInversion (DepInversion (k,co,ids),hyp)
      | IDENT "simple"; IDENT "inversion";
	  hyp = quantified_hypothesis; ids = with_inversion_names;
	  cl = in_hyp_list ->
	    TacInversion (NonDepInversion (SimpleInversion, cl, ids), hyp)
      | IDENT "inversion";
	  hyp = quantified_hypothesis; ids = with_inversion_names;
	  cl = in_hyp_list ->
	    TacInversion (NonDepInversion (FullInversion, cl, ids), hyp)
      | IDENT "inversion_clear";
	  hyp = quantified_hypothesis; ids = with_inversion_names;
	  cl = in_hyp_list ->
	    TacInversion (NonDepInversion (FullInversionClear, cl, ids), hyp)
      | IDENT "inversion"; hyp = quantified_hypothesis;
	  "using"; c = constr; cl = in_hyp_list ->
	    TacInversion (InversionUsing (c,cl), hyp)

      (* Conversion *)
      | r = red_tactic; cl = clause_dft_concl -> TacReduce (r, cl)
      (* Change ne doit pas s'appliquer dans un Definition t := Eval ... *)
      | IDENT "change"; (oc,c) = conversion; cl = clause_dft_concl ->
	  TacChange (oc,c,cl)
    ] ]
  ;
END;;
