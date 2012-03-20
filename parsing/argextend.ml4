(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "tools/compat5b.cmo" i*)

open Genarg
open Q_util
open Egrammar
open Pcoq
open Compat

let loc = Pp.dummy_loc
let default_loc = <:expr< Pp.dummy_loc >>

let rec make_rawwit loc = function
  | BoolArgType -> <:expr< Genarg.rawwit_bool >>
  | IntArgType -> <:expr< Genarg.rawwit_int >>
  | IntOrVarArgType -> <:expr< Genarg.rawwit_int_or_var >>
  | StringArgType -> <:expr< Genarg.rawwit_string >>
  | PreIdentArgType -> <:expr< Genarg.rawwit_pre_ident >>
  | IntroPatternArgType -> <:expr< Genarg.rawwit_intro_pattern >>
  | IdentArgType b -> <:expr< Genarg.rawwit_ident_gen $mlexpr_of_bool b$ >>
  | VarArgType -> <:expr< Genarg.rawwit_var >>
  | RefArgType -> <:expr< Genarg.rawwit_ref >>
  | SortArgType -> <:expr< Genarg.rawwit_sort >>
  | ConstrArgType -> <:expr< Genarg.rawwit_constr >>
  | ConstrMayEvalArgType -> <:expr< Genarg.rawwit_constr_may_eval >>
  | QuantHypArgType -> <:expr< Genarg.rawwit_quant_hyp >>
  | RedExprArgType -> <:expr< Genarg.rawwit_red_expr >>
  | OpenConstrArgType b -> <:expr< Genarg.rawwit_open_constr_gen $mlexpr_of_bool b$ >>
  | ConstrWithBindingsArgType -> <:expr< Genarg.rawwit_constr_with_bindings >>
  | BindingsArgType -> <:expr< Genarg.rawwit_bindings >>
  | List0ArgType t -> <:expr< Genarg.wit_list0 $make_rawwit loc t$ >>
  | List1ArgType t -> <:expr< Genarg.wit_list1 $make_rawwit loc t$ >>
  | OptArgType t -> <:expr< Genarg.wit_opt $make_rawwit loc t$ >>
  | PairArgType (t1,t2) ->
      <:expr< Genarg.wit_pair $make_rawwit loc t1$ $make_rawwit loc t2$ >>
  | ExtraArgType s ->
    <:expr<
      let module WIT = struct
        open Extrawit;
        value wit = $lid:"rawwit_"^s$;
      end in WIT.wit >>

let rec make_globwit loc = function
  | BoolArgType -> <:expr< Genarg.globwit_bool >>
  | IntArgType -> <:expr< Genarg.globwit_int >>
  | IntOrVarArgType -> <:expr< Genarg.globwit_int_or_var >>
  | StringArgType -> <:expr< Genarg.globwit_string >>
  | PreIdentArgType -> <:expr< Genarg.globwit_pre_ident >>
  | IntroPatternArgType -> <:expr< Genarg.globwit_intro_pattern >>
  | IdentArgType b -> <:expr< Genarg.globwit_ident_gen $mlexpr_of_bool b$ >>
  | VarArgType -> <:expr< Genarg.globwit_var >>
  | RefArgType -> <:expr< Genarg.globwit_ref >>
  | QuantHypArgType -> <:expr< Genarg.globwit_quant_hyp >>
  | SortArgType -> <:expr< Genarg.globwit_sort >>
  | ConstrArgType -> <:expr< Genarg.globwit_constr >>
  | ConstrMayEvalArgType -> <:expr< Genarg.globwit_constr_may_eval >>
  | RedExprArgType -> <:expr< Genarg.globwit_red_expr >>
  | OpenConstrArgType b -> <:expr< Genarg.globwit_open_constr_gen $mlexpr_of_bool b$ >>
  | ConstrWithBindingsArgType -> <:expr< Genarg.globwit_constr_with_bindings >>
  | BindingsArgType -> <:expr< Genarg.globwit_bindings >>
  | List0ArgType t -> <:expr< Genarg.wit_list0 $make_globwit loc t$ >>
  | List1ArgType t -> <:expr< Genarg.wit_list1 $make_globwit loc t$ >>
  | OptArgType t -> <:expr< Genarg.wit_opt $make_globwit loc t$ >>
  | PairArgType (t1,t2) ->
      <:expr< Genarg.wit_pair $make_globwit loc t1$ $make_globwit loc t2$ >>
  | ExtraArgType s ->
    <:expr<
      let module WIT = struct
        open Extrawit;
        value wit = $lid:"globwit_"^s$;
      end in WIT.wit >>

let rec make_wit loc = function
  | BoolArgType -> <:expr< Genarg.wit_bool >>
  | IntArgType -> <:expr< Genarg.wit_int >>
  | IntOrVarArgType -> <:expr< Genarg.wit_int_or_var >>
  | StringArgType -> <:expr< Genarg.wit_string >>
  | PreIdentArgType -> <:expr< Genarg.wit_pre_ident >>
  | IntroPatternArgType -> <:expr< Genarg.wit_intro_pattern >>
  | IdentArgType b -> <:expr< Genarg.wit_ident_gen $mlexpr_of_bool b$ >>
  | VarArgType -> <:expr< Genarg.wit_var >>
  | RefArgType -> <:expr< Genarg.wit_ref >>
  | QuantHypArgType -> <:expr< Genarg.wit_quant_hyp >>
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
  | ExtraArgType s ->
    <:expr<
      let module WIT = struct
        open Extrawit;
        value wit = $lid:"wit_"^s$;
      end in WIT.wit >>

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
        let s = Names.string_of_id id in <:expr< let $lid:s$ = $v$ in $e$ >> in
  let rec aux = function
    | [] -> <:expr< let loc = $default_loc$ in let _ = loc = loc in $act$ >>
    | GramNonTerminal(_,OptArgType _,_,p) :: tl ->
        bind_name p <:expr< None >> (aux tl)
    | GramNonTerminal(_,List0ArgType _,_,p) :: tl ->
        bind_name p <:expr< [] >> (aux tl)
    | GramNonTerminal(_,(ExtraArgType _ as t),_,p) :: tl ->
        (* We check at runtime if extraarg s parses "epsilon" *)
        let s = match p with None -> "_" | Some id -> Names.string_of_id id in
        <:expr< let $lid:s$ = match Genarg.default_empty_value $make_rawwit loc t$ with
          [ None -> raise Exit
          | Some v -> v ] in $aux tl$ >>
    | _ -> assert false (* already filtered out *) in
  if has_extraarg prods then
    (* Needs a dynamic check; catch all exceptions if ever some rhs raises *)
    (* an exception rather than returning a value; *)
    (* declares loc because some code can refer to it; *)
    (* ensures loc is used to avoid "unused variable" warning *)
    (true, <:expr< try Some $aux prods$ with [ _ -> None ] >>)
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
	let p = Names.string_of_id p in
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
    | `Uniform typ -> typ, pr, typ, pr
    | `Specialized (a, b, c, d) -> a, b, c, d
  in
  let glob = match g with
    | None ->
	<:expr< fun e x ->
          out_gen $make_globwit loc rawtyp$
            (Tacinterp.intern_genarg e
               (Genarg.in_gen $make_rawwit loc rawtyp$ x)) >>
    | Some f -> <:expr< $lid:f$>> in
  let interp = match f with
    | None ->
	<:expr< fun ist gl x ->
          out_gen $make_wit loc globtyp$
            (Tacinterp.interp_genarg ist gl
               (Genarg.in_gen $make_globwit loc globtyp$ x)) >>
    | Some f -> <:expr< $lid:f$>> in
  let substitute = match h with
    | None ->
	<:expr< fun s x ->
          out_gen $make_globwit loc globtyp$
	    (Tacinterp.subst_genarg s
               (Genarg.in_gen $make_globwit loc globtyp$ x)) >>
    | Some f -> <:expr< $lid:f$>> in
  let se = mlexpr_of_string s in
  let wit = <:expr< $lid:"wit_"^s$ >> in
  let rawwit = <:expr< $lid:"rawwit_"^s$ >> in
  let globwit = <:expr< $lid:"globwit_"^s$ >> in
  let rules = mlexpr_of_list (make_rule loc) (List.rev cl) in
  let default_value = <:expr< $make_possibly_empty_subentries loc s cl$ >> in
  declare_str_items loc
   [ <:str_item<
      value ($lid:"wit_"^s$, $lid:"globwit_"^s$, $lid:"rawwit_"^s$) =
      Genarg.create_arg $default_value$ $se$>>;
     <:str_item<
      value $lid:s$ = Pcoq.create_generic_entry $se$ $rawwit$ >>;
     <:str_item< do {
      Tacinterp.add_interp_genarg $se$
        ((fun e x ->
          (Genarg.in_gen $globwit$ ($glob$ e (out_gen $rawwit$ x)))),
        (fun ist gl x ->
          (Genarg.in_gen $wit$ ($interp$ ist gl (out_gen $globwit$ x)))),
        (fun subst x ->
          (Genarg.in_gen $globwit$ ($substitute$ subst (out_gen $globwit$ x)))));
      Compat.maybe_uncurry (Pcoq.Gram.extend ($lid:s$ : Pcoq.Gram.entry 'a))
	(None, [(None, None, $rules$)]);
      Pptactic.declare_extra_genarg_pprule
        ($rawwit$, $lid:rawpr$)
        ($globwit$, $lid:globpr$)
        ($wit$, $lid:pr$) }
     >> ]

let declare_vernac_argument loc s pr cl =
  let se = mlexpr_of_string s in
  let wit = <:expr< $lid:"wit_"^s$ >> in
  let rawwit = <:expr< $lid:"rawwit_"^s$ >> in
  let globwit = <:expr< $lid:"globwit_"^s$ >> in
  let rules = mlexpr_of_list (make_rule loc) (List.rev cl) in
  let pr_rules = match pr with
    | None -> <:expr< fun _ _ _ _ -> str $str:"[No printer for "^s^"]"$ >>
    | Some pr -> <:expr< fun _ _ _ -> $lid:pr$ >> in
  declare_str_items loc
   [ <:str_item<
      value (($lid:"wit_"^s$:Genarg.abstract_argument_type unit Genarg.tlevel),
             ($lid:"globwit_"^s$:Genarg.abstract_argument_type unit Genarg.glevel),
              $lid:"rawwit_"^s$) = Genarg.create_arg None $se$ >>;
     <:str_item<
      value $lid:s$ = Pcoq.create_generic_entry $se$ $rawwit$ >>;
    <:str_item< do {
      Compat.maybe_uncurry (Pcoq.Gram.extend ($lid:s$ : Pcoq.Gram.entry 'a))
	(None, [(None, None, $rules$)]);
      Pptactic.declare_extra_genarg_pprule
        ($rawwit$, $pr_rules$)
        ($globwit$, fun _ _ _ _ -> Errors.anomaly "vernac argument needs not globwit printer")
        ($wit$, fun _ _ _ _ -> Errors.anomaly "vernac argument needs not wit printer") }
      >> ]

open Vernacexpr
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
	GramNonTerminal (loc, t, g, Some (Names.id_of_string s))
      | e = LIDENT; "("; s = LIDENT; ","; sep = STRING; ")" ->
        let t, g = interp_entry_name false None e sep in
	GramNonTerminal (loc, t, g, Some (Names.id_of_string s))
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

