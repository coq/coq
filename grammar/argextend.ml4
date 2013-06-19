(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "tools/compat5b.cmo" i*)

open Genarg
open Q_util
open Egramml
open Compat

let loc = CompatLoc.ghost
let default_loc = <:expr< Loc.ghost >>

let qualified_name s =
  let path = CString.split '.' s in
  let (name, path) = CList.sep_last path in
  let fold dir accu = <:expr< $uid:dir$.$accu$ >> in
  List.fold_right fold path <:expr< $lid:name$ >>

let mk_extraarg s =
  if Extrawit.tactic_genarg_level s = None then
    try
      let name = Genarg.get_name0 s in
      qualified_name name
    with Not_found ->
      <:expr< $lid:"wit_"^s$ >>
  else
    qualified_name ("Extrawit.wit_" ^ s)

let rec make_wit loc = function
  | IntOrVarArgType -> <:expr< Genarg.wit_int_or_var >>
  | IntroPatternArgType -> <:expr< Genarg.wit_intro_pattern >>
  | IdentArgType b -> <:expr< Genarg.wit_ident_gen $mlexpr_of_bool b$ >>
  | VarArgType -> <:expr< Genarg.wit_var >>
  | RefArgType -> <:expr< Genarg.wit_ref >>
  | QuantHypArgType -> <:expr< Genarg.wit_quant_hyp >>
  | GenArgType -> <:expr< Genarg.wit_genarg >>
  | SortArgType -> <:expr< Genarg.wit_sort >>
  | ConstrArgType -> <:expr< Genarg.wit_constr >>
  | ConstrMayEvalArgType -> <:expr< Genarg.wit_constr_may_eval >>
  | RedExprArgType -> <:expr< Genarg.wit_red_expr >>
  | OpenConstrArgType b -> <:expr< Genarg.wit_open_constr_gen $mlexpr_of_bool b$ >>
  | ConstrWithBindingsArgType -> <:expr< Genarg.wit_constr_with_bindings >>
  | BindingsArgType -> <:expr< Genarg.wit_bindings >>
  | List0ArgType t -> <:expr< Genarg.wit_list0 $make_wit loc t$ >>
  | List1ArgType t -> <:expr< Genarg.wit_list1 $make_wit loc t$ >>
  | OptArgType t -> <:expr< Genarg.wit_opt $make_wit loc t$ >>
  | PairArgType (t1,t2) ->
      <:expr< Genarg.wit_pair $make_wit loc t1$ $make_wit loc t2$ >>
  | ExtraArgType s -> mk_extraarg s

let make_rawwit loc arg = <:expr< Genarg.rawwit $make_wit loc arg$ >>
let make_globwit loc arg = <:expr< Genarg.glbwit $make_wit loc arg$ >>
let make_topwit loc arg = <:expr< Genarg.topwit $make_wit loc arg$ >>

let has_extraarg =
  List.exists (function GramNonTerminal(_,ExtraArgType _,_,_) -> true | _ -> false)

let statically_known_possibly_empty s (prods,_) =
  List.for_all (function
    | GramNonTerminal(_,ExtraArgType s',_,_) ->
        (* For ExtraArg we don't know (we'll have to test dynamically) *)
        (* unless it is a recursive call *)
        s <> s'
    | GramNonTerminal(_,(OptArgType _|List0ArgType _),_,_) ->
        (* Opt and List0 parses the empty string *)
        true
    | _ ->
        (* This consumes a token for sure *) false)
      prods

let possibly_empty_subentries loc (prods,act) =
  let bind_name p v e = match p with
    | None -> e
    | Some id ->
        let s = Names.Id.to_string id in <:expr< let $lid:s$ = $v$ in $e$ >> in
  let rec aux = function
    | [] -> <:expr< let loc = $default_loc$ in let _ = loc in $act$ >>
    | GramNonTerminal(_,OptArgType _,_,p) :: tl ->
        bind_name p <:expr< None >> (aux tl)
    | GramNonTerminal(_,List0ArgType _,_,p) :: tl ->
        bind_name p <:expr< [] >> (aux tl)
    | GramNonTerminal(_,(ExtraArgType _ as t),_,p) :: tl ->
        (* We check at runtime if extraarg s parses "epsilon" *)
        let s = match p with None -> "_" | Some id -> Names.Id.to_string id in
        <:expr< let $lid:s$ = match Genarg.default_empty_value $make_wit loc t$ with
          [ None -> raise Exit
          | Some v -> v ] in $aux tl$ >>
    | _ -> assert false (* already filtered out *) in
  if has_extraarg prods then
    (* Needs a dynamic check; catch all exceptions if ever some rhs raises *)
    (* an exception rather than returning a value; *)
    (* declares loc because some code can refer to it; *)
    (* ensures loc is used to avoid "unused variable" warning *)
    (true, <:expr< try Some $aux prods$
                   with [ e when Errors.noncritical e -> None ] >>)
  else
    (* Static optimisation *)
    (false, aux prods)

let make_possibly_empty_subentries loc s cl =
  let cl = List.filter (statically_known_possibly_empty s) cl in
  if cl = [] then
    <:expr< None >>
  else
    let rec aux = function
    | (true, e) :: l ->
        <:expr< match $e$ with [ Some v -> Some v | None -> $aux l$ ] >>
    | (false, e) :: _ ->
        <:expr< Some $e$ >>
    | [] ->
        <:expr< None >> in
    aux (List.map (possibly_empty_subentries loc) cl)

let make_act loc act pil =
  let rec make = function
    | [] -> <:expr< Pcoq.Gram.action (fun loc -> ($act$ : 'a)) >>
    | GramNonTerminal (_,t,_,Some p) :: tl ->
	let p = Names.Id.to_string p in
	<:expr<
          Pcoq.Gram.action
            (fun $lid:p$ ->
               let _ = Genarg.in_gen $make_rawwit loc t$ $lid:p$ in $make tl$)
        >>
    | (GramTerminal _ | GramNonTerminal (_,_,_,None)) :: tl ->
	<:expr< Pcoq.Gram.action (fun _ -> $make tl$) >> in
  make (List.rev pil)

let make_prod_item = function
  | GramTerminal s -> <:expr< Pcoq.gram_token_of_string $str:s$ >>
  | GramNonTerminal (_,_,g,_) ->
      <:expr< Pcoq.symbol_of_prod_entry_key $mlexpr_of_prod_entry_key g$ >>

let make_rule loc (prods,act) =
  <:expr< ($mlexpr_of_list make_prod_item prods$,$make_act loc act prods$) >>

let declare_tactic_argument loc s (typ, pr, f, g, h) cl =
  let rawtyp, rawpr, globtyp, globpr = match typ with
    | `Uniform typ ->
      typ, pr, typ, pr
    | `Specialized (a, b, c, d) -> a, b, c, d
  in
  let glob = match g with
    | None ->
      begin match rawtyp with
      | Genarg.ExtraArgType s' when CString.equal s s' ->
        <:expr< fun ist v -> (ist, v) >>
      | _ ->
        <:expr< fun ist v ->
          let ans = out_gen $make_globwit loc rawtyp$
          (Tacintern.intern_genarg ist
          (Genarg.in_gen $make_rawwit loc rawtyp$ v)) in
          (ist, ans) >>
      end
    | Some f ->
      <:expr< fun ist v -> (ist, $lid:f$ ist v) >>
  in
  let interp = match f with
    | None ->
      begin match globtyp with
      | Genarg.ExtraArgType s' when CString.equal s s' ->
        <:expr< fun ist gl v -> (gl.Evd.sigma, v) >>
      | _ ->
	<:expr< fun ist gl x ->
	  let (sigma,a_interp) =
	    Tacinterp.interp_genarg ist gl
               (Genarg.in_gen $make_globwit loc globtyp$ x)
	  in
          (sigma , out_gen $make_topwit loc globtyp$ a_interp)>>
      end
    | Some f -> <:expr< $lid:f$>> in
  let subst = match h with
    | None ->
      begin match globtyp with
      | Genarg.ExtraArgType s' when CString.equal s s' ->
        <:expr< fun s v -> v >>
      | _ ->
        <:expr< fun s x ->
          out_gen $make_globwit loc globtyp$
          (Tacsubst.subst_genarg s
            (Genarg.in_gen $make_globwit loc globtyp$ x)) >>
      end
    | Some f -> <:expr< $lid:f$>> in
  let defs = [
    <:patt< Genarg.arg0_subst >>, subst;
    <:patt< Genarg.arg0_glob >>, glob;
    <:patt< Genarg.arg0_interp >>, interp;
  ] in
  let se = mlexpr_of_string s in
  let wit = <:expr< $lid:"wit_"^s$ >> in
  let rawwit = <:expr< Genarg.rawwit $wit$ >> in
  let rules = mlexpr_of_list (make_rule loc) (List.rev cl) in
  let default_value = <:expr< $make_possibly_empty_subentries loc s cl$ >> in
  declare_str_items loc
   [ <:str_item<
      value ($lid:"wit_"^s$) =
        let arg = { (Genarg.default_arg0 $se$) with $list:defs$ } in
      Genarg.make0 $default_value$ $se$ arg >>;
     <:str_item<
      value $lid:s$ = Pcoq.create_generic_entry $se$ $rawwit$ >>;
     <:str_item< do {
      Compat.maybe_uncurry (Pcoq.Gram.extend ($lid:s$ : Pcoq.Gram.entry 'a))
	(None, [(None, None, $rules$)]);
      Pptactic.declare_extra_genarg_pprule
        $wit$ $lid:rawpr$ $lid:globpr$ $lid:pr$ }
     >> ]

let declare_vernac_argument loc s pr cl =
  let se = mlexpr_of_string s in
  let wit = <:expr< $lid:"wit_"^s$ >> in
  let rawwit = <:expr< Genarg.rawwit $wit$ >> in
  let rules = mlexpr_of_list (make_rule loc) (List.rev cl) in
  let pr_rules = match pr with
    | None -> <:expr< fun _ _ _ _ -> str $str:"[No printer for "^s^"]"$ >>
    | Some pr -> <:expr< fun _ _ _ -> $lid:pr$ >> in
  declare_str_items loc
   [ <:str_item<
      value ($lid:"wit_"^s$ : Genarg.genarg_type 'a unit unit) =
        Genarg.create_arg None $se$ >>;
     <:str_item<
      value $lid:s$ = Pcoq.create_generic_entry $se$ $rawwit$ >>;
    <:str_item< do {
      Compat.maybe_uncurry (Pcoq.Gram.extend ($lid:s$ : Pcoq.Gram.entry 'a))
	(None, [(None, None, $rules$)]);
      Pptactic.declare_extra_genarg_pprule $wit$
        $pr_rules$
        (fun _ _ _ _ -> Errors.anomaly (Pp.str "vernac argument needs not globwit printer"))
        (fun _ _ _ _ -> Errors.anomaly (Pp.str "vernac argument needs not wit printer")) }
      >> ]

open Pcoq
open Pcaml
open PcamlSig

EXTEND
  GLOBAL: str_item;
  str_item:
    [ [ "ARGUMENT"; "EXTEND"; s = entry_name;
        header = argextend_header;
        OPT "|"; l = LIST1 argrule SEP "|";
        "END" ->
         declare_tactic_argument loc s header l
      | "VERNAC"; "ARGUMENT"; "EXTEND"; s = entry_name;
        pr = OPT ["PRINTED"; "BY"; pr = LIDENT -> pr];
        OPT "|"; l = LIST1 argrule SEP "|";
        "END" ->
         declare_vernac_argument loc s pr l ] ]
  ;
  argextend_header:
    [ [ "TYPED"; "AS"; typ = argtype;
        "PRINTED"; "BY"; pr = LIDENT;
        f = OPT [ "INTERPRETED"; "BY"; f = LIDENT -> f ];
        g = OPT [ "GLOBALIZED"; "BY"; f = LIDENT -> f ];
        h = OPT [ "SUBSTITUTED"; "BY"; f = LIDENT -> f ] ->
        (`Uniform typ, pr, f, g, h)
      | "PRINTED"; "BY"; pr = LIDENT;
        f = OPT [ "INTERPRETED"; "BY"; f = LIDENT -> f ];
        g = OPT [ "GLOBALIZED"; "BY"; f = LIDENT -> f ];
        h = OPT [ "SUBSTITUTED"; "BY"; f = LIDENT -> f ];
        "RAW_TYPED"; "AS"; rawtyp = argtype;
        "RAW_PRINTED"; "BY"; rawpr = LIDENT;
        "GLOB_TYPED"; "AS"; globtyp = argtype;
        "GLOB_PRINTED"; "BY"; globpr = LIDENT ->
        (`Specialized (rawtyp, rawpr, globtyp, globpr), pr, f, g, h) ] ]
  ;
  argtype:
    [ "2"
      [ e1 = argtype; "*"; e2 = argtype -> PairArgType (e1, e2) ]
    | "1"
      [ e = argtype; LIDENT "list" -> List0ArgType e
      | e = argtype; LIDENT "option" -> OptArgType e ]
    | "0"
      [ e = LIDENT -> fst (interp_entry_name false None e "")
      | "("; e = argtype; ")" -> e ] ]
  ;
  argrule:
    [ [ "["; l = LIST0 genarg; "]"; "->"; "["; e = Pcaml.expr; "]" -> (l,e) ] ]
  ;
  genarg:
    [ [ e = LIDENT; "("; s = LIDENT; ")" ->
        let t, g = interp_entry_name false None e "" in
	GramNonTerminal (!@loc, t, g, Some (Names.Id.of_string s))
      | e = LIDENT; "("; s = LIDENT; ","; sep = STRING; ")" ->
        let t, g = interp_entry_name false None e sep in
	GramNonTerminal (!@loc, t, g, Some (Names.Id.of_string s))
      | s = STRING ->
	  if String.length s > 0 && Util.is_letter s.[0] then
	    Lexer.add_keyword s;
          GramTerminal s
    ] ]
  ;
  entry_name:
    [ [ s = LIDENT -> s
      | UIDENT -> failwith "Argument entry names must be lowercase"
      ] ]
  ;
  END
