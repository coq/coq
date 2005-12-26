(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Names
open Nameops
open Util
open Tacexpr
open Rawterm
open Topconstr
open Genarg
open Libnames
open Pattern
open Ppextend

let pr_red_expr = Ppconstrnew.pr_red_expr
let pr_may_eval = Ppconstrnew.pr_may_eval
let pr_sort = Ppconstrnew.pr_sort
let pr_global x = Nametab.pr_global_env Idset.empty x
let pr_opt = Ppconstrnew.pr_opt

type grammar_terminals = string option list

  (* Extensions *)
let prtac_tab = Hashtbl.create 17

let declare_extra_tactic_pprule (s,tags,prods) =
  Hashtbl.add prtac_tab (s,tags) prods

let exists_extra_tactic_pprule s tags = Hashtbl.mem prtac_tab (s,tags)

type 'a raw_extra_genarg_printer =
    (constr_expr -> std_ppcmds) -> 
    (constr_expr -> std_ppcmds) -> 
    (tolerability -> raw_tactic_expr -> std_ppcmds) ->
    'a -> std_ppcmds

type 'a glob_extra_genarg_printer =
    (rawconstr_and_expr -> std_ppcmds) ->
    (rawconstr_and_expr -> std_ppcmds) ->
    (tolerability -> glob_tactic_expr -> std_ppcmds) ->
    'a -> std_ppcmds

type 'a extra_genarg_printer =
    (Term.constr -> std_ppcmds) -> 
    (Term.constr -> std_ppcmds) -> 
    (tolerability -> glob_tactic_expr -> std_ppcmds) ->
    'a -> std_ppcmds

let genarg_pprule = ref Stringmap.empty

let declare_extra_genarg_pprule (rawwit, f) (globwit, g) (wit, h) =
  let s = match unquote wit with
    | ExtraArgType s -> s 
    | _ -> error
	"Can declare a pretty-printing rule only for extra argument types"
  in
  let f prc prlc prtac x = f prc prlc prtac (out_gen rawwit x) in
  let g prc prlc prtac x = g prc prlc prtac (out_gen globwit x) in
  let h prc prlc prtac x = h prc prlc prtac (out_gen wit x) in
  genarg_pprule := Stringmap.add s (f,g,h) !genarg_pprule

let pr_arg pr x = spc () ++ pr x

let pr_or_var pr = function
  | ArgArg x -> pr x
  | ArgVar (_,s) -> pr_id s

let pr_or_metaid pr = function
  | AI x -> pr x
  | _ -> failwith "pr_hyp_location: unexpected quotation meta-variable"

let pr_and_short_name pr (c,_) = pr c

let pr_located pr (loc,x) = pr x

let pr_evaluable_reference = function 
  | EvalVarRef id -> pr_id id
  | EvalConstRef sp -> pr_global (Libnames.ConstRef sp)

let pr_quantified_hypothesis = function
  | AnonHyp n -> int n
  | NamedHyp id -> pr_id id 

let pr_quantified_hypothesis_arg h = spc () ++ pr_quantified_hypothesis h

let pr_binding prc = function
  | loc, NamedHyp id, c -> hov 1 (pr_id id ++ str " := " ++ cut () ++ prc c)
  | loc, AnonHyp n, c -> hov 1 (int n ++ str " := " ++ cut () ++ prc c)

let pr_bindings prc prlc = function
  | ImplicitBindings l ->
      brk (1,1) ++ str "with" ++ brk (1,1) ++
      prlist_with_sep spc prc l
  | ExplicitBindings l ->
      brk (1,1) ++ str "with" ++ brk (1,1) ++ 
        prlist_with_sep spc (fun b -> str"(" ++ pr_binding prlc b ++ str")") l
  | NoBindings -> mt ()

let pr_bindings_no_with prc prlc = function
  | ImplicitBindings l ->
      brk (1,1) ++
      prlist_with_sep spc prc l
  | ExplicitBindings l ->
      brk (1,1) ++ 
        prlist_with_sep spc (fun b -> str"(" ++ pr_binding prlc b ++ str")") l
  | NoBindings -> mt ()

let pr_with_bindings prc prlc (c,bl) =
  prc c ++ hv 0 (pr_bindings prc prlc bl)

let pr_with_constr prc = function
  | None -> mt ()
  | Some c -> spc () ++ hov 1 (str "with" ++ spc () ++ prc c)

let pr_with_names = function
  | None -> mt ()
  | Some ipat -> spc () ++ hov 1 (str "as" ++ spc () ++ pr_intro_pattern ipat)

let rec pr_raw_generic prc prlc prtac prref x =
  match Genarg.genarg_tag x with
  | BoolArgType -> pr_arg str (if out_gen rawwit_bool x then "true" else "false")
  | IntArgType -> pr_arg int (out_gen rawwit_int x)
  | IntOrVarArgType -> pr_arg (pr_or_var pr_int) (out_gen rawwit_int_or_var x)
  | StringArgType -> spc () ++ str "\"" ++ str (out_gen rawwit_string x) ++ str "\""
  | PreIdentArgType -> pr_arg str (out_gen rawwit_pre_ident x)
  | IntroPatternArgType -> pr_arg pr_intro_pattern 
      (out_gen rawwit_intro_pattern x)
  | IdentArgType -> pr_arg pr_id (out_gen rawwit_ident x)
  | VarArgType -> pr_arg (pr_located pr_id) (out_gen rawwit_var x)
  | RefArgType -> pr_arg prref (out_gen rawwit_ref x)
  | SortArgType -> pr_arg pr_sort (out_gen rawwit_sort x)
  | ConstrArgType -> pr_arg prc (out_gen rawwit_constr x)
  | ConstrMayEvalArgType ->
      pr_arg (pr_may_eval prc prlc prref)
        (out_gen rawwit_constr_may_eval x)
  | QuantHypArgType ->
      pr_arg pr_quantified_hypothesis (out_gen rawwit_quant_hyp x)
  | RedExprArgType ->
      pr_arg (pr_red_expr (prc,prlc,prref)) (out_gen rawwit_red_expr x)
  | TacticArgType n -> pr_arg (prtac (n,E)) (out_gen (rawwit_tactic n) x)
  | OpenConstrArgType b -> pr_arg prc (snd (out_gen (rawwit_open_constr_gen b) x))
  | ConstrWithBindingsArgType -> 
      pr_arg (pr_with_bindings prc prlc) (out_gen rawwit_constr_with_bindings x)
  | BindingsArgType -> 
      pr_arg (pr_bindings_no_with prc prlc) (out_gen rawwit_bindings x)
  | List0ArgType _ -> 
      hov 0 (fold_list0 (fun x a -> pr_raw_generic prc prlc prtac prref x ++ a) x (mt()))
  | List1ArgType _ ->
      hov 0 (fold_list1 (fun x a -> pr_raw_generic prc prlc prtac prref x ++ a) x (mt()))
  | OptArgType _ -> hov 0 (fold_opt (pr_raw_generic prc prlc prtac prref) (mt()) x)
  | PairArgType _ ->
      hov 0
        (fold_pair
	  (fun a b -> pr_raw_generic prc prlc prtac prref a ++ spc () ++ 
            pr_raw_generic prc prlc prtac prref b)
	  x)
  | ExtraArgType s -> 
      try pi1 (Stringmap.find s !genarg_pprule) prc prlc prtac x
      with Not_found -> str " [no printer for " ++ str s ++ str "] "


let rec pr_glob_generic prc prlc prtac x =
  match Genarg.genarg_tag x with
  | BoolArgType -> pr_arg str (if out_gen globwit_bool x then "true" else "false")
  | IntArgType -> pr_arg int (out_gen globwit_int x)
  | IntOrVarArgType -> pr_arg (pr_or_var pr_int) (out_gen globwit_int_or_var x)
  | StringArgType -> spc () ++ str "\"" ++ str (out_gen globwit_string x) ++ str "\""
  | PreIdentArgType -> pr_arg str (out_gen globwit_pre_ident x)
  | IntroPatternArgType ->
      pr_arg pr_intro_pattern (out_gen globwit_intro_pattern x)
  | IdentArgType -> pr_arg pr_id (out_gen globwit_ident x)
  | VarArgType -> pr_arg (pr_located pr_id) (out_gen globwit_var x)
  | RefArgType -> pr_arg (pr_or_var (pr_located pr_global)) (out_gen globwit_ref x)
  | SortArgType -> pr_arg pr_sort (out_gen globwit_sort x)
  | ConstrArgType -> pr_arg prc (out_gen globwit_constr x)
  | ConstrMayEvalArgType ->
      pr_arg (pr_may_eval prc prlc
        (pr_or_var (pr_and_short_name pr_evaluable_reference))) (out_gen globwit_constr_may_eval x)
  | QuantHypArgType ->
      pr_arg pr_quantified_hypothesis (out_gen globwit_quant_hyp x)
  | RedExprArgType ->
      pr_arg (pr_red_expr 
        (prc,prlc,pr_or_var (pr_and_short_name pr_evaluable_reference)))
        (out_gen globwit_red_expr x)
  | TacticArgType n -> pr_arg (prtac (n,E)) (out_gen (globwit_tactic n) x)
  | OpenConstrArgType b -> pr_arg prc (snd (out_gen (globwit_open_constr_gen b) x))
  | ConstrWithBindingsArgType -> 
      pr_arg (pr_with_bindings prc prlc) (out_gen globwit_constr_with_bindings x)
  | BindingsArgType -> 
      pr_arg (pr_bindings_no_with prc prlc) (out_gen globwit_bindings x)
  | List0ArgType _ -> 
      hov 0 (fold_list0 (fun x a -> pr_glob_generic prc prlc prtac x ++ a) x (mt()))
  | List1ArgType _ ->
      hov 0 (fold_list1 (fun x a -> pr_glob_generic prc prlc prtac x ++ a) x (mt()))
  | OptArgType _ -> hov 0 (fold_opt (pr_glob_generic prc prlc prtac) (mt()) x)
  | PairArgType _ ->
      hov 0
        (fold_pair
	  (fun a b -> pr_glob_generic prc prlc prtac a ++ spc () ++ 
            pr_glob_generic prc prlc prtac b)
	  x)
  | ExtraArgType s -> 
      try pi2 (Stringmap.find s !genarg_pprule) prc prlc prtac x
      with Not_found -> str " [no printer for " ++ str s ++ str "] "

open Closure

let rec pr_generic prc prlc prtac x =
  match Genarg.genarg_tag x with
  | BoolArgType -> pr_arg str (if out_gen wit_bool x then "true" else "false")
  | IntArgType -> pr_arg int (out_gen wit_int x)
  | IntOrVarArgType -> pr_arg (pr_or_var pr_int) (out_gen wit_int_or_var x)
  | StringArgType -> spc () ++ str "\"" ++ str (out_gen wit_string x) ++ str "\""
  | PreIdentArgType -> pr_arg str (out_gen wit_pre_ident x)
  | IntroPatternArgType -> 
      pr_arg pr_intro_pattern (out_gen wit_intro_pattern x)
  | IdentArgType -> pr_arg pr_id (out_gen wit_ident x)
  | VarArgType -> pr_arg pr_id (out_gen wit_var x)
  | RefArgType -> pr_arg pr_global (out_gen wit_ref x)
  | SortArgType -> pr_arg prc (Term.mkSort (out_gen wit_sort x))
  | ConstrArgType -> pr_arg prc (out_gen wit_constr x)
  | ConstrMayEvalArgType ->
      pr_arg prc (out_gen wit_constr_may_eval x)
  | QuantHypArgType ->
      pr_arg pr_quantified_hypothesis (out_gen wit_quant_hyp x)
  | RedExprArgType ->
      pr_arg (pr_red_expr (prc,prlc,pr_evaluable_reference)) 
        (out_gen wit_red_expr x)
  | TacticArgType n -> pr_arg (prtac (n,E)) (out_gen (wit_tactic n) x)
  | OpenConstrArgType b -> pr_arg prc (snd (out_gen (wit_open_constr_gen b) x))
  | ConstrWithBindingsArgType -> 
      pr_arg (pr_with_bindings prc prlc) (out_gen wit_constr_with_bindings x)
  | BindingsArgType -> 
      pr_arg (pr_bindings_no_with prc prlc) (out_gen wit_bindings x)
  | List0ArgType _ -> 
      hov 0 (fold_list0 (fun x a -> pr_generic prc prlc prtac x ++ a) x (mt()))
  | List1ArgType _ ->
      hov 0 (fold_list1 (fun x a -> pr_generic prc prlc prtac x ++ a) x (mt()))
  | OptArgType _ -> hov 0 (fold_opt (pr_generic prc prlc prtac) (mt()) x)
  | PairArgType _ ->
      hov 0
        (fold_pair
	  (fun a b -> pr_generic prc prlc prtac a ++ spc () ++ 
            pr_generic prc prlc prtac b)
	  x)
  | ExtraArgType s -> 
      try pi3 (Stringmap.find s !genarg_pprule) prc prlc prtac x
      with Not_found -> str " [no printer for " ++ str s ++ str "]"

let rec pr_tacarg_using_rule pr_gen = function
  | Some s :: l, al -> spc () ++ str s ++ pr_tacarg_using_rule pr_gen (l,al)
  | None :: l, a :: al -> pr_gen a ++ pr_tacarg_using_rule  pr_gen (l,al)
  | [], [] -> mt ()
  | _ -> failwith "Inconsistent arguments of extended tactic"

let surround p = hov 1 (str"(" ++ p ++ str")")

let pr_extend_gen prgen lev s l =
  try 
    let tags = List.map genarg_tag l in
    let (lev',pl) = Hashtbl.find prtac_tab (s,tags) in
    let p = pr_tacarg_using_rule prgen (pl,l) in
    if lev' > lev then surround p else p
  with Not_found ->
    str s ++ prlist prgen l ++ str " (* Generic printer *)"

let pr_raw_extend prc prlc prtac = 
  pr_extend_gen (pr_raw_generic prc prlc prtac Ppconstrnew.pr_reference)
let pr_glob_extend prc prlc prtac =
  pr_extend_gen (pr_glob_generic prc prlc prtac)
let pr_extend prc prlc prtac =
  pr_extend_gen (pr_generic prc prlc prtac)
