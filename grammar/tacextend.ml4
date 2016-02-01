(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "tools/compat5b.cmo" i*)

(** Implementation of the TACTIC EXTEND macro. *)

open Util
open Pp
open Names
open Genarg
open Q_util
open Q_coqast
open Argextend
open Pcoq
open Egramml
open Compat

let dloc = <:expr< Loc.ghost >>

let plugin_name = <:expr< __coq_plugin_name >>

let rec make_patt = function
  | [] -> <:patt< [] >>
  | ExtNonTerminal (_, _, p) :: l ->
      let p = Names.Id.to_string p in
      <:patt< [ $lid:p$ :: $make_patt l$ ] >>
  | _::l -> make_patt l

let rec make_when loc = function
  | [] -> <:expr< True >>
  | ExtNonTerminal (t, _, p) :: l ->
      let p = Names.Id.to_string p in
      let l = make_when loc l in
      let t = mlexpr_of_argtype loc t in
      <:expr< Genarg.argument_type_eq (Genarg.genarg_tag $lid:p$) $t$ && $l$ >>
  | _::l -> make_when loc l

let rec make_let raw e = function
  | [] -> <:expr< fun $lid:"ist"$ -> $e$ >>
  | ExtNonTerminal (t, _, p) :: l ->
      let p = Names.Id.to_string p in
      let loc = MLast.loc_of_expr e in
      let e = make_let raw e l in
      let v =
        if raw then <:expr< Genarg.out_gen $make_rawwit loc t$ $lid:p$ >>
               else <:expr< Tacinterp.Value.cast $make_topwit    loc t$ $lid:p$ >> in
      <:expr< let $lid:p$ = $v$ in $e$ >>
  | _::l -> make_let raw e l

let rec extract_signature = function
  | [] -> []
  | ExtNonTerminal (t, _, _) :: l -> t :: extract_signature l
  | _::l -> extract_signature l



let check_unicity s l =
  let l' = List.map (fun (l,_,_) -> extract_signature l) l in
  if not (Util.List.distinct l') then
    Pp.msg_warning
      (strbrk ("Two distinct rules of tactic entry "^s^" have the same "^
      "non-terminals in the same order: put them in distinct tactic entries"))

let make_clause (pt,_,e) =
  (make_patt pt,
   vala None,
   make_let false e pt)

let make_fun_clauses loc s l =
  check_unicity s l;
  let map c = Compat.make_fun loc [make_clause c] in
  mlexpr_of_list map l

let make_prod_item = function
  | ExtTerminal s -> <:expr< Egramml.GramTerminal $str:s$ >>
  | ExtNonTerminal (nt, g, id) ->
      <:expr< Egramml.GramNonTerminal $default_loc$ $make_rawwit loc nt$
      $mlexpr_of_prod_entry_key g$ >>

let mlexpr_of_clause cl =
  mlexpr_of_list (fun (a,_,_) -> mlexpr_of_list make_prod_item a) cl

let make_one_printing_rule (pt,_,e) =
  let level = mlexpr_of_int 0 in (* only level 0 supported here *)
  let loc = MLast.loc_of_expr e in
  let prods = mlexpr_of_list make_prod_item pt in
  <:expr< { Pptactic.pptac_level = $level$;
            pptac_prods = $prods$ } >>

let make_printing_rule r = mlexpr_of_list make_one_printing_rule r

(** Special treatment of constr entries *)
let is_constr_gram = function
| ExtTerminal _ -> false
| ExtNonTerminal (_, Extend.Uentry "constr", _) -> true
| _ -> false

let make_var = function
  | ExtNonTerminal (_, _, p) -> Some p
  | _ -> assert false

let declare_tactic loc s c cl = match cl with
| [(ExtTerminal name) :: rem, _, tac] when List.for_all is_constr_gram rem ->
  (** The extension is only made of a name followed by constr entries: we do not
      add any grammar nor printing rule and add it as a true Ltac definition. *)
  let patt = make_patt rem in
  let vars = List.map make_var rem in
  let vars = mlexpr_of_list (mlexpr_of_option mlexpr_of_ident) vars in
  let entry = mlexpr_of_string s in
  let se = <:expr< { Tacexpr.mltac_tactic = $entry$; Tacexpr.mltac_plugin = $plugin_name$ } >> in
  let ml = <:expr< { Tacexpr.mltac_name = $se$; Tacexpr.mltac_index = 0 } >> in
  let name = mlexpr_of_string name in
  let tac =
    (** Special handling of tactics without arguments: such tactics do not do
        a Proofview.Goal.nf_enter to compute their arguments. It matters for some
        whole-prof tactics like [shelve_unifiable]. *)
    if List.is_empty rem then
      <:expr< fun _ $lid:"ist"$ -> $tac$ >>
    else
      let f = Compat.make_fun loc [patt, vala None, <:expr< fun $lid:"ist"$ -> $tac$ >>] in
      <:expr< Tacinterp.lift_constr_tac_to_ml_tac $vars$ $f$ >>
  in
  (** Arguments are not passed directly to the ML tactic in the TacML node,
      the ML tactic retrieves its arguments in the [ist] environment instead.
      This is the rôle of the [lift_constr_tac_to_ml_tac] function. *)
  let body = <:expr< Tacexpr.TacFun ($vars$, Tacexpr.TacML ($dloc$, $ml$, [])) >> in
  let name = <:expr< Names.Id.of_string $name$ >> in
  declare_str_items loc
    [ <:str_item< do {
      let obj () = Tacenv.register_ltac True False $name$ $body$ in
      try do {
        Tacenv.register_ml_tactic $se$ [|$tac$|];
        Mltop.declare_cache_obj obj $plugin_name$; }
      with [ e when Errors.noncritical e ->
        Pp.msg_warning
          (Pp.app
            (Pp.str ("Exception in tactic extend " ^ $entry$ ^": "))
            (Errors.print e)) ]; } >>
    ]
| _ ->
  (** Otherwise we add parsing and printing rules to generate a call to a
      TacML tactic. *)
  let entry = mlexpr_of_string s in
  let se = <:expr< { Tacexpr.mltac_tactic = $entry$; Tacexpr.mltac_plugin = $plugin_name$ } >> in
  let pp = make_printing_rule cl in
  let gl = mlexpr_of_clause cl in
  let obj = <:expr< fun () -> Metasyntax.add_ml_tactic_notation $se$ $gl$ >> in
  declare_str_items loc
    [ <:str_item< do {
      try do {
        Tacenv.register_ml_tactic $se$ (Array.of_list $make_fun_clauses loc s cl$);
        Mltop.declare_cache_obj $obj$ $plugin_name$;
        Pptactic.declare_ml_tactic_pprule $se$ (Array.of_list $pp$); }
      with [ e when Errors.noncritical e ->
        Pp.msg_warning
          (Pp.app
            (Pp.str ("Exception in tactic extend " ^ $entry$ ^": "))
            (Errors.print e)) ]; } >>
    ]

open Pcaml
open PcamlSig (* necessary for camlp4 *)

EXTEND
  GLOBAL: str_item;
  str_item:
    [ [ "TACTIC"; "EXTEND"; s = tac_name;
        c = OPT [ "CLASSIFIED"; "BY"; c = LIDENT -> <:expr< $lid:c$ >> ];
        OPT "|"; l = LIST1 tacrule SEP "|";
        "END" ->
         declare_tactic loc s c l ] ]
  ;
  tacrule:
    [ [ "["; l = LIST1 tacargs; "]";
        c = OPT [ "=>"; "["; c = Pcaml.expr; "]" -> c ];
        "->"; "["; e = Pcaml.expr; "]" ->
	(match l with
	  | ExtNonTerminal _ :: _ ->
	    (* En attendant la syntaxe de tacticielles *)
	    failwith "Tactic syntax must start with an identifier"
	  | _ -> (l,c,e))
    ] ]
  ;
  tacargs:
    [ [ e = LIDENT; "("; s = LIDENT; ")" ->
        let e = parse_user_entry e "" in
        ExtNonTerminal (type_of_user_symbol e, e, Names.Id.of_string s)
      | e = LIDENT; "("; s = LIDENT; ","; sep = STRING; ")" ->
        let e = parse_user_entry e sep in
        ExtNonTerminal (type_of_user_symbol e, e, Names.Id.of_string s)
      | s = STRING ->
	if String.is_empty s then Errors.user_err_loc (!@loc,"",Pp.str "Empty terminal.");
        ExtTerminal s
    ] ]
  ;
  tac_name:
    [ [ s = LIDENT -> s
      | s = UIDENT -> s
    ] ]
  ;
  END
