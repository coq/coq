(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Genarg
open Q_util
open Q_coqast
open Ast

let join_loc (deb1,_) (_,fin2) = (deb1,fin2)
let loc = (0,0)
let default_loc = <:expr< (0,0) >>

type grammar_tactic_production_expr =
  | VernacTerm of string
  | VernacNonTerm of Util.loc * Genarg.argument_type * MLast.expr * string option
let rec make_patt = function
  | [] -> <:patt< [] >>
  | VernacNonTerm(_,_,_,Some p)::l ->
      <:patt< [ $lid:p$ :: $make_patt l$ ] >>
  | _::l -> make_patt l

let rec make_when loc = function
  | [] -> <:expr< True >>
  | VernacNonTerm(loc',t,_,Some p)::l ->
      let l = make_when loc l in
      let loc = join_loc loc' loc in
      let t = mlexpr_of_argtype loc' t in
      <:expr< Genarg.genarg_tag $lid:p$ = $t$ && $l$ >>
  | _::l -> make_when loc l

let rec make_wit loc = function
  | BoolArgType -> <:expr< Genarg.rawwit_bool >>
  | IntArgType -> <:expr< Genarg.rawwit_int >>
  | IntOrVarArgType -> <:expr< Genarg.rawwit_int_or_var >>
  | StringArgType -> <:expr< Genarg.rawwit_string >>
  | PreIdentArgType -> <:expr< Genarg.rawwit_pre_ident >>
  | IdentArgType -> <:expr< Genarg.rawwit_ident >>
  | QualidArgType -> <:expr< Genarg.rawwit_qualid >>
  | ConstrArgType -> <:expr< Genarg.rawwit_constr >>
  | ConstrMayEvalArgType -> <:expr< Genarg.rawwit_constr_may_eval >>
  | QuantHypArgType -> <:expr< Genarg.rawwit_quant_hyp >>
  | TacticArgType -> <:expr< Genarg.rawwit_tactic >>
  | RedExprArgType -> <:expr< Genarg.rawwit_red_expr >>
  | CastedOpenConstrArgType -> <:expr< Genarg.rawwit_casted_open_constr >>
  | ConstrWithBindingsArgType -> <:expr< Genarg.rawwit_constr_with_bindings >>
  | List0ArgType t -> <:expr< Genarg.wit_list0 $make_wit loc t$ >>
  | List1ArgType t -> <:expr< Genarg.wit_list1 $make_wit loc t$ >>
  | OptArgType t -> <:expr< Genarg.wit_opt $make_wit loc t$ >>
  | PairArgType (t1,t2) -> 
      <:expr< Genarg.wit_pair $make_wit loc t1$ $make_wit loc t2$ >>
  | ExtraArgType s -> <:expr< $lid:"rawwit_"^s$ >>

let rec make_let e = function
  | [] -> e
  | VernacNonTerm(loc,t,_,Some p)::l ->
      let loc = join_loc loc (MLast.loc_of_expr e) in
      let e = make_let e l in
      <:expr< let $lid:p$ = Genarg.out_gen $make_wit loc t$ $lid:p$ in $e$ >>
  | _::l -> make_let e l

let add_clause s (_,pt,e) l =
  let p = make_patt pt in
  let w = Some (make_when (MLast.loc_of_expr e) pt) in
  if List.exists (fun (p',w',_) -> p=p' & w=w') l then
    Pp.warning_with Pp_control.err_ft
      ("Two distinct rules of entry "^s^" have the same\n"^
      "non-terminals in the same order: put them in distinct tactic entries");
  (p, w, make_let e pt)::l

let make_clauses s l =
  let default =
    (<:patt< _ >>,None,<:expr< failwith "Vernac extension: cannot occur" >>) in
  List.fold_right (add_clause s) l [default]

let rec make_fun e = function
  | [] -> e
  | VernacNonTerm(loc,_,_,Some p)::l -> 
      <:expr< fun $lid:p$ -> $make_fun e l$ >>
  | _::l -> make_fun e l

let mlexpr_of_grammar_production = function
  | VernacTerm s ->
      <:expr< Egrammar.TacTerm $mlexpr_of_string s$ >>
  | VernacNonTerm (loc,nt,g,sopt) ->
      <:expr< Egrammar.TacNonTerm $default_loc$ ($g$,$mlexpr_of_argtype loc nt$) $mlexpr_of_option mlexpr_of_string sopt$ >>

let mlexpr_of_clause =
  mlexpr_of_list
    (fun (a,b,c) ->
      (mlexpr_of_pair
	mlexpr_of_string
	(mlexpr_of_list mlexpr_of_grammar_production)
	(a,b)))

let declare_command loc s cl =
  let gl = mlexpr_of_clause cl in
  let icl = make_clauses s cl in
  <:str_item<
    declare
      open Pcoq;
      try Vernacinterp.vinterp_add $mlexpr_of_string s$ (fun [ $list:icl$ ])
      with e -> Pp.pp (Cerrors.explain_exn e);
      Egrammar.extend_vernac_command_grammar $mlexpr_of_string s$ $gl$;
    end
  >>

open Vernacexpr
open Pcoq

let rec interp_entry_name loc s =
  let l = String.length s in
  if l > 8 & String.sub s 0 3 = "ne_" & String.sub s (l-5) 5 = "_list" then
    let t, g = interp_entry_name loc (String.sub s 3 (l-8)) in
    List1ArgType t, <:expr< Gramext.Slist1 $g$ >>
  else if l > 5 & String.sub s (l-5) 5 = "_list" then
    let t, g = interp_entry_name loc (String.sub s 0 (l-5)) in
    List0ArgType t, <:expr< Gramext.Slist0 $g$ >>
  else if l > 4 & String.sub s (l-4) 4 = "_opt" then
    let t, g = interp_entry_name loc (String.sub s 0 (l-4)) in
    OptArgType t, <:expr< Gramext.Sopt $g$ >>
  else
    let t, se = 
      match Pcoq.entry_type (Pcoq.get_univ "prim") s with
	| Some _ as x -> x, <:expr< Prim. $lid:s$ >>
	| None ->
      match Pcoq.entry_type (Pcoq.get_univ "constr") s with
	| Some _ as x -> x, <:expr< Constr. $lid:s$ >>
	| None -> 
      match Pcoq.entry_type (Pcoq.get_univ "tactic") s with
	| Some _ as x -> x, <:expr< Tactic. $lid:s$ >>
	| None -> None, <:expr< $lid:s$ >> in
    let t =
      match t with
	| Some (GenAstType t) -> t
	| Some _ -> 
	    failwith "Only entries of generic type can be used in extension"
	| None ->
(*	    Pp.warning_with Pp_control.err_ft
            ("Unknown primitive grammar entry: "^s);*)
	    ExtraArgType s
    in t, <:expr< Gramext.Snterm (Pcoq.Gram.Entry.obj $se$) >>

open Pcaml

EXTEND
  GLOBAL: str_item;
  str_item:
    [ [ "VERNAC"; "COMMAND"; "EXTEND"; s = UIDENT;
        OPT "|"; l = LIST1 rule SEP "|";
        "END" ->
         declare_command loc s l ] ]
  ;
  rule:
    [ [ "["; s = STRING; l = LIST0 args; "]"; "->"; "["; e = Pcaml.expr; "]"
        -> (s,l,<:expr< fun () -> $e$ >>)
    ] ]
  ;
  args:
    [ [ e = LIDENT; "("; s = LIDENT; ")" ->
        let t, g = interp_entry_name loc e in
        VernacNonTerm (loc, t, g, Some s)
      | s = STRING ->
        VernacTerm s
    ] ]
  ;
  END
;;
