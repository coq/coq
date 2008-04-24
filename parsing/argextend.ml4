(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4use: "pa_extend.cmo q_MLast.cmo" i*)

(* $Id$ *)

open Genarg
open Q_util
open Q_coqast

let join_loc = Util.join_loc
let loc = Util.dummy_loc
let default_loc = <:expr< Util.dummy_loc >>

let rec make_rawwit loc = function
  | BoolArgType -> <:expr< Genarg.rawwit_bool >>
  | IntArgType -> <:expr< Genarg.rawwit_int >>
  | IntOrVarArgType -> <:expr< Genarg.rawwit_int_or_var >>
  | StringArgType -> <:expr< Genarg.rawwit_string >>
  | PreIdentArgType -> <:expr< Genarg.rawwit_pre_ident >>
  | IntroPatternArgType -> <:expr< Genarg.rawwit_intro_pattern >>
  | IdentArgType -> <:expr< Genarg.rawwit_ident >>
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
  | ExtraArgType s -> <:expr< $lid:"rawwit_"^s$ >>

let rec make_globwit loc = function
  | BoolArgType -> <:expr< Genarg.globwit_bool >>
  | IntArgType -> <:expr< Genarg.globwit_int >>
  | IntOrVarArgType -> <:expr< Genarg.globwit_int_or_var >>
  | StringArgType -> <:expr< Genarg.globwit_string >>
  | PreIdentArgType -> <:expr< Genarg.globwit_pre_ident >>
  | IntroPatternArgType -> <:expr< Genarg.globwit_intro_pattern >>
  | IdentArgType -> <:expr< Genarg.globwit_ident >>
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
  | ExtraArgType s -> <:expr< $lid:"globwit_"^s$ >>

let rec make_wit loc = function
  | BoolArgType -> <:expr< Genarg.wit_bool >>
  | IntArgType -> <:expr< Genarg.wit_int >>
  | IntOrVarArgType -> <:expr< Genarg.wit_int_or_var >>
  | StringArgType -> <:expr< Genarg.wit_string >>
  | PreIdentArgType -> <:expr< Genarg.wit_pre_ident >>
  | IntroPatternArgType -> <:expr< Genarg.wit_intro_pattern >>
  | IdentArgType -> <:expr< Genarg.wit_ident >>
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
  | ExtraArgType s -> <:expr< $lid:"wit_"^s$ >>

let make_act loc act pil =
  let rec make = function
    | [] -> <:expr< Gramext.action (fun loc -> ($act$ : 'a)) >>
    | None :: tl -> <:expr< Gramext.action (fun _ -> $make tl$) >>
    | Some (p, t) :: tl ->
	<:expr<
          Gramext.action 
            (fun $lid:p$ ->
               let _ = Genarg.in_gen $make_rawwit loc t$ $lid:p$ in $make tl$)
        >> in
  make (List.rev pil)

let make_rule loc (prods,act) =
  let (symbs,pil) = List.split prods in
  <:expr< ($mlsensitive_list (fun x -> x) symbs$,$make_act loc act pil$) >>

let declare_tactic_argument loc s typ pr f g h rawtyppr globtyppr cl =
  let rawtyp, rawpr = match rawtyppr with
    | None -> typ,pr
    | Some (t,p) -> t,p in
  let globtyp, globpr = match globtyppr with
    | None -> typ,pr
    | Some (t,p) -> t,p in
  let glob = match g with
    | None ->
	<:expr< fun e x ->
          out_gen $make_globwit loc typ$
            (Tacinterp.intern_genarg e
               (Genarg.in_gen $make_rawwit loc rawtyp$ x)) >>
    | Some f -> <:expr< $lid:f$>> in
  let interp = match f with
    | None -> 
	<:expr< fun ist gl x ->
          out_gen $make_wit loc typ$
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
  let rules = mlsensitive_list (make_rule loc) (List.rev cl) in
  <:str_item<
    declare
      value ($lid:"wit_"^s$, $lid:"globwit_"^s$, $lid:"rawwit_"^s$) =
        Genarg.create_arg $se$;
      value $lid:s$ = Pcoq.create_generic_entry $se$ $rawwit$;
      Tacinterp.add_interp_genarg $se$
        ((fun e x ->
          (Genarg.in_gen $globwit$ ($glob$ e (out_gen $rawwit$ x)))),
        (fun ist gl x ->
          (Genarg.in_gen $wit$ ($interp$ ist gl (out_gen $globwit$ x)))),
        (fun subst x ->
          (Genarg.in_gen $globwit$ ($substitute$ subst (out_gen $globwit$ x)))));
      Pcoq.Gram.extend ($lid:s$ : Pcoq.Gram.Entry.e 'a) None 
        [(None, None, $rules$)];
      Pptactic.declare_extra_genarg_pprule
        ($rawwit$, $lid:rawpr$)
        ($globwit$, $lid:globpr$)
        ($wit$, $lid:pr$);
    end
  >>

let declare_vernac_argument loc s cl =
  let se = mlexpr_of_string s in
  let rawwit = <:expr< $lid:"rawwit_"^s$ >> in
  let rules = mlsensitive_list (make_rule loc) (List.rev cl) in
  <:str_item<
    declare
      value $lid:"rawwit_"^s$ = let (_,_,x) = Genarg.create_arg $se$ in x;
      value $lid:s$ = Pcoq.create_generic_entry $se$ $rawwit$;
      Pcoq.Gram.extend ($lid:s$ : Pcoq.Gram.Entry.e 'a) None 
        [(None, None, $rules$)];
    end
  >>

open Vernacexpr
open Pcoq
open Pcaml

EXTEND
  GLOBAL: str_item;
  str_item:
    [ [ "ARGUMENT"; "EXTEND"; s = [ UIDENT | LIDENT ];
        "TYPED"; "AS"; typ = argtype;
        "PRINTED"; "BY"; pr = LIDENT;
        f = OPT [ "INTERPRETED"; "BY"; f = LIDENT -> f ];
        g = OPT [ "GLOBALIZED"; "BY"; f = LIDENT -> f ];
        h = OPT [ "SUBSTITUTED"; "BY"; f = LIDENT -> f ];
        rawtyppr =
        (* Necessary if the globalized type is different from the final type *)
          OPT [ "RAW_TYPED"; "AS"; t = argtype; 
                "RAW_PRINTED"; "BY"; pr = LIDENT -> (t,pr) ];
        globtyppr =
          OPT [ "GLOB_TYPED"; "AS"; t = argtype; 
                "GLOB_PRINTED"; "BY"; pr = LIDENT -> (t,pr) ];
        OPT "|"; l = LIST1 argrule SEP "|";
        "END" ->
	  if String.capitalize s = s then
	    failwith "Argument entry names must be lowercase";
         declare_tactic_argument loc s typ pr f g h rawtyppr globtyppr l
      | "VERNAC"; "ARGUMENT"; "EXTEND"; s = [ UIDENT | LIDENT ];
        OPT "|"; l = LIST1 argrule SEP "|";
        "END" ->
	  if String.capitalize s = s then
	    failwith "Argument entry names must be lowercase";
         declare_vernac_argument loc s l ] ]
  ;
  argtype:
    [ "2" 
      [ e1 = argtype; "*"; e2 = argtype -> PairArgType (e1, e2) ]
    | "1"
      [ e = argtype; LIDENT "list" -> List0ArgType e
      | e = argtype; LIDENT "option" -> OptArgType e ]
    | "0"
      [ e = LIDENT -> fst (interp_entry_name loc e "")
      | "("; e = argtype; ")" -> e ] ]
  ;
  argrule:
    [ [ "["; l = LIST0 genarg; "]"; "->"; "["; e = Pcaml.expr; "]" -> (l,e) ] ]
  ;
  genarg:
    [ [ e = LIDENT; "("; s = LIDENT; ")" ->
        let t, g = interp_entry_name loc e "" in (g, Some (s,t))
      | e = LIDENT; "("; s = LIDENT; ","; sep = STRING; ")" ->
        let t, g = interp_entry_name loc e sep in (g, Some (s,t))
      | s = STRING ->
	  if String.length s > 0 && Util.is_letter s.[0] then
	    Compat.using Pcoq.lexer ("", s);
        (<:expr< (Gramext.Stoken (Lexer.terminal $str:s$)) >>, None)
    ] ]
  ;
  END

