(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4use: "pa_extend.cmo q_MLast.cmo" i*)

open Util
open Genarg
open Q_util
open Q_coqast
open Argextend
open Pcoq
open Extrawit
open Egrammar

let rec make_patt = function
  | [] -> <:patt< [] >>
  | GramNonTerminal(loc',_,_,Some p)::l ->
      let p = Names.string_of_id p in
      <:patt< [ $lid:p$ :: $make_patt l$ ] >>
  | _::l -> make_patt l

let rec make_when loc = function
  | [] -> <:expr< True >>
  | GramNonTerminal(loc',t,_,Some p)::l ->
      let p = Names.string_of_id p in
      let l = make_when loc l in
      let loc = join_loc loc' loc in
      let t = mlexpr_of_argtype loc' t in
      <:expr< Genarg.genarg_tag $lid:p$ = $t$ && $l$ >>
  | _::l -> make_when loc l

let rec make_let e = function
  | [] -> e
  | GramNonTerminal(loc,t,_,Some p)::l ->
      let p = Names.string_of_id p in
      let loc = join_loc loc (MLast.loc_of_expr e) in
      let e = make_let e l in
      let v = <:expr< Genarg.out_gen $make_wit loc t$ $lid:p$ >> in
      let v =
        (* Special case for tactics which must be stored in algebraic
           form to avoid marshalling closures and to be reprinted *)
        if is_tactic_genarg t then
          <:expr< ($v$, Tacinterp.eval_tactic $v$) >>
        else v in
      <:expr< let $lid:p$ = $v$ in $e$ >>
  | _::l -> make_let e l

let add_clause s (pt,e) l =
  let p = make_patt pt in
  let w = Some (make_when (MLast.loc_of_expr e) pt) in
  (p, w, make_let e pt)::l

let rec extract_signature = function
  | [] -> []
  | GramNonTerminal (_,t,_,_) :: l -> t :: extract_signature l
  | _::l -> extract_signature l

let check_unicity s l =
  let l' = List.map (fun (l,_) -> extract_signature l) l in
  if not (Util.list_distinct l') then
    Pp.warning_with !Pp_control.err_ft
      ("Two distinct rules of tactic entry "^s^" have the same\n"^
      "non-terminals in the same order: put them in distinct tactic entries")

let make_clauses s l =
  check_unicity s l;
  let default =
    (<:patt< _ >>,None,<:expr< failwith "Tactic extension: cannot occur" >>) in
  List.fold_right (add_clause s) l [default]

let rec make_args = function
  | [] -> <:expr< [] >>
  | GramNonTerminal(loc,t,_,Some p)::l ->
      let p = Names.string_of_id p in
      <:expr< [ Genarg.in_gen $make_wit loc t$ $lid:p$ :: $make_args l$ ] >>
  | _::l -> make_args l

let rec make_eval_tactic e = function
  | [] -> e
  | GramNonTerminal(loc,tag,_,Some p)::l when is_tactic_genarg tag ->
      let p = Names.string_of_id p in
      let loc = join_loc loc (MLast.loc_of_expr e) in
      let e = make_eval_tactic e l in
        (* Special case for tactics which must be stored in algebraic
           form to avoid marshalling closures and to be reprinted *)
      <:expr< let $lid:p$ = ($lid:p$,Tacinterp.eval_tactic $lid:p$) in $e$ >>
  | _::l -> make_eval_tactic e l

let rec make_fun e = function
  | [] -> e
  | GramNonTerminal(loc,_,_,Some p)::l ->
      let p = Names.string_of_id p in
      <:expr< fun $lid:p$ -> $make_fun e l$ >>
  | _::l -> make_fun e l

let mlexpr_terminals_of_grammar_tactic_prod_item_expr = function
  | GramTerminal s -> <:expr< Some $mlexpr_of_string s$ >>
  | GramNonTerminal (loc,nt,_,sopt) -> <:expr< None >>

let make_prod_item = function
  | GramTerminal s -> <:expr< Egrammar.GramTerminal $str:s$ >>
  | GramNonTerminal (loc,nt,g,sopt) ->
      <:expr< Egrammar.GramNonTerminal $default_loc$ $mlexpr_of_argtype loc nt$
      $mlexpr_of_prod_entry_key g$ $mlexpr_of_option mlexpr_of_ident sopt$ >>

let mlexpr_of_clause =
  mlexpr_of_list (fun (a,b) -> mlexpr_of_list make_prod_item a)

let rec make_tags loc = function
  | [] -> <:expr< [] >>
  | GramNonTerminal(loc',t,_,Some p)::l ->
      let l = make_tags loc l in
      let loc = join_loc loc' loc in
      let t = mlexpr_of_argtype loc' t in
      <:expr< [ $t$ :: $l$ ] >>
  | _::l -> make_tags loc l

let make_one_printing_rule se (pt,e) =
  let level = mlexpr_of_int 0 in (* only level 0 supported here *)
  let loc = MLast.loc_of_expr e in
  let prods = mlexpr_of_list mlexpr_terminals_of_grammar_tactic_prod_item_expr pt in
  <:expr< ($se$, $make_tags loc pt$, ($level$, $prods$)) >>

let make_printing_rule se = mlexpr_of_list (make_one_printing_rule se)

let rec contains_epsilon = function
  | List0ArgType _ -> true
  | List1ArgType t -> contains_epsilon t
  | OptArgType _ -> true
  | PairArgType(t1,t2) -> contains_epsilon t1 && contains_epsilon t2
  | ExtraArgType("hintbases") -> true
  | _ -> false
let is_atomic = function
  | GramTerminal s :: l when
      List.for_all (function
          GramTerminal _ -> false
	| GramNonTerminal(_,t,_,_) -> contains_epsilon t) l
	-> [s]
  | _ -> []

let declare_tactic loc s cl =
  let se = mlexpr_of_string s in
  let pp = make_printing_rule se cl in
  let gl = mlexpr_of_clause cl in
  let hide_tac (p,e) =
    (* reste a definir les fonctions cachees avec des noms frais *)
    let stac = "h_"^s in
    let e =
      make_fun
        <:expr<
          Refiner.abstract_extended_tactic $mlexpr_of_string s$ $make_args p$ $make_eval_tactic e p$
        >>
      p in
    <:str_item< value $lid:stac$ = $e$ >>
  in
  let hidden = if List.length cl = 1 then List.map hide_tac cl else [] in
  let atomic_tactics =
    mlexpr_of_list mlexpr_of_string
      (List.flatten (List.map (fun (al,_) -> is_atomic al) cl)) in
  <:str_item<
    declare
      open Pcoq;
      open Extrawit;
      declare $list:hidden$ end;
      try
        let _=Tacinterp.add_tactic $se$ (fun [ $list:make_clauses s cl$ ]) in
        List.iter
          (fun s -> Tacinterp.add_primitive_tactic s
              (Tacexpr.TacAtom($default_loc$,
                 Tacexpr.TacExtend($default_loc$,s,[]))))
          $atomic_tactics$
      with e -> Pp.pp (Cerrors.explain_exn e);
      Egrammar.extend_tactic_grammar $se$ $gl$;
      List.iter Pptactic.declare_extra_tactic_pprule $pp$;
    end
  >>

open Pcaml

EXTEND
  GLOBAL: str_item;
  str_item:
    [ [ "TACTIC"; "EXTEND"; s = [ UIDENT | LIDENT ];
        OPT "|"; l = LIST1 tacrule SEP "|";
        "END" ->
         declare_tactic loc s l ] ]
  ;
  tacrule:
    [ [ "["; l = LIST1 tacargs; "]"; "->"; "["; e = Pcaml.expr; "]"
        ->
	  if match List.hd l with GramNonTerminal _ -> true | _ -> false then
	    (* En attendant la syntaxe de tacticielles *)
	    failwith "Tactic syntax must start with an identifier";
	  (l,e)
    ] ]
  ;
  tacargs:
    [ [ e = LIDENT; "("; s = LIDENT; ")" ->
        let t, g = interp_entry_name false None e "" in
        GramNonTerminal (loc, t, g, Some (Names.id_of_string s))
      | e = LIDENT; "("; s = LIDENT; ","; sep = STRING; ")" ->
        let t, g = interp_entry_name false None e sep in
        GramNonTerminal (loc, t, g, Some (Names.id_of_string s))
      | s = STRING ->
	if s = "" then Util.user_err_loc (loc,"",Pp.str "Empty terminal.");
        GramTerminal s
    ] ]
  ;
  END

