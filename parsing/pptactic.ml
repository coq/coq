(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Names
open Nameops
open Util
open Extend
open Tacexpr
open Rawterm
open Topconstr
open Genarg
open Libnames
open Pattern

let pr_red_expr = Ppconstr.pr_red_expr
let pr_may_eval = Ppconstr.pr_may_eval
let pr_sort = Ppconstr.pr_sort
let pr_global x =
  if Options.do_translate () then (* for pr_gen *)
    Ppconstrnew.pr_global Idset.empty x
  else
    Ppconstr.pr_global Idset.empty x
let pr_name = Ppconstr.pr_name
let pr_opt = Ppconstr.pr_opt
let pr_occurrences = Ppconstr.pr_occurrences

type grammar_terminals = string option list

  (* Extensions *)
let prtac_tab_v7 = Hashtbl.create 17
let prtac_tab = Hashtbl.create 17

let declare_extra_tactic_pprule for_v8 s (tags,prods) =
  Hashtbl.add prtac_tab_v7 (s,tags) prods;
  if for_v8 then Hashtbl.add prtac_tab (s,tags) prods

type 'a raw_extra_genarg_printer =
    (constr_expr -> std_ppcmds) -> (raw_tactic_expr -> std_ppcmds) ->
      'a -> std_ppcmds
type 'a glob_extra_genarg_printer =
    (rawconstr_and_expr -> std_ppcmds) -> (glob_tactic_expr -> std_ppcmds) ->
      'a -> std_ppcmds
type 'a extra_genarg_printer =
    (Term.constr -> std_ppcmds) -> (glob_tactic_expr -> std_ppcmds) ->
      'a -> std_ppcmds

let genarg_pprule_v7 = ref Stringmap.empty
let genarg_pprule = ref Stringmap.empty

let declare_extra_genarg_pprule for_v8 (rawwit, f) (globwit, g) (wit, h) =
  let s = match unquote wit with
    | ExtraArgType s -> s 
    | _ -> error
	"Can declare a pretty-printing rule only for extra argument types"
  in
  let f prc prtac x = f prc prtac (out_gen rawwit x) in
  let g prc prtac x = g prc prtac (out_gen globwit x) in
  let h prc prtac x = h prc prtac (out_gen wit x) in
  genarg_pprule_v7 := Stringmap.add s (f,g,h) !genarg_pprule_v7;
  if for_v8 then
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

let pr_ltac_constant sp = pr_qualid (Nametab.shortest_qualid_of_tactic sp)

let pr_evaluable_reference = function 
  | EvalVarRef id -> pr_id id
  | EvalConstRef sp -> pr_global (Libnames.ConstRef sp)

let pr_inductive ind = pr_global (Libnames.IndRef ind)

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
        prlist_with_sep spc
          (fun b -> if Options.do_translate () or not !Options.v7 then
	    str"(" ++ pr_binding prlc b ++ str")" 
	   else
	    pr_binding prc b)
        l
  | NoBindings -> mt ()

let pr_bindings_no_with prc prlc = function
  | ImplicitBindings l ->
      brk (1,1) ++
      prlist_with_sep spc prc l
  | ExplicitBindings l ->
      brk (1,1) ++ 
        prlist_with_sep spc
          (fun b -> if Options.do_translate () or not !Options.v7 then
	    str"(" ++ pr_binding prlc b ++ str")" 
	   else
	    pr_binding prc b)
        l
  | NoBindings -> mt ()

let pr_with_bindings prc prlc (c,bl) =
  if Options.do_translate () then
    (* translator calls pr_with_bindings on rawconstr: we cast it! *)
    let bl' = Ppconstrnew.translate_with_bindings (fst (Obj.magic c) : rawconstr) bl in
    prc c ++ hv 0 (pr_bindings prc prlc bl')
  else
    prc c ++ hv 0 (pr_bindings prc prlc bl)

let pr_with_constr prc = function
  | None -> mt ()
  | Some c -> spc () ++ hov 1 (str "with" ++ spc () ++ prc c)

let pr_with_names = function
  | None -> mt ()
  | Some ipat -> spc () ++ hov 1 (str "as" ++ spc () ++ pr_intro_pattern ipat)

let pr_hyp_location pr_id = function
  | id, _, (InHyp,_) -> spc () ++ pr_id id
  | id, _, (InHypTypeOnly,_) ->
      spc () ++ str "(Type of " ++ pr_id id ++ str ")"
  | id, _, _ -> error "Unsupported hyp location in v7"

let pr_clause pr_id = function
  | [] -> mt ()
  | l -> spc () ++ hov 0 (str "in" ++ prlist (pr_hyp_location pr_id) l)


let pr_clauses pr_id cls =
  match cls with
      { onhyps = Some l; onconcl = false } ->
        spc () ++ hov 0 (str "in" ++ prlist (pr_hyp_location pr_id) l)
    | { onhyps = Some []; onconcl = true } -> mt()
    | _ -> error "this clause has both hypothesis and conclusion"

let pr_simple_clause pr_id = function
  | [] -> mt ()
  | l -> spc () ++
      hov 0 (str "in" ++ spc () ++ prlist_with_sep spc pr_id l)

let pr_clause_pattern pr_id cls =
  pr_opt
    (prlist (fun (id,occs,_) ->
      prlist (pr_arg int) occs ++ spc () ++ pr_id id)) cls.onhyps ++
  if cls.onconcl then
    prlist (pr_arg int) cls.concl_occs ++ spc() ++ str"Goal"
  else mt()

let pr_subterms pr occl =
  hov 0 (pr_occurrences pr occl ++ spc () ++ str "with")

let pr_induction_arg prc = function
  | ElimOnConstr c -> prc c
  | ElimOnIdent (_,id) -> pr_id id
  | ElimOnAnonHyp n -> int n

let pr_induction_kind = function
  | SimpleInversion -> str "Simple Inversion"
  | FullInversion -> str "Inversion"
  | FullInversionClear -> str "Inversion_clear"

let pr_match_pattern pr_pat = function
  | Term a -> pr_pat a
  | Subterm (None,a) -> str "[" ++ pr_pat a ++ str "]"
  | Subterm (Some id,a) -> pr_id id ++ str "[" ++ pr_pat a ++ str "]"

let pr_match_hyps pr_pat = function
  | Hyp ((_,na),mp) -> pr_name na ++ str ":" ++ pr_match_pattern pr_pat mp

let pr_match_rule m pr_pat pr = function
  | Pat ([],mp,t) when m ->
      str "[" ++ pr_match_pattern pr_pat mp ++ str "]"
      ++ spc () ++ str "->" ++ brk (1,2) ++ pr t
  | Pat (rl,mp,t) ->
      str "[" ++ prlist_with_sep pr_semicolon
                   (pr_match_hyps pr_pat) rl ++ spc () ++ 
      str "|-" ++ spc () ++ pr_match_pattern pr_pat mp ++ spc () ++ str "]" ++
      spc () ++ str "->" ++ brk (1,2) ++ pr t
  | All t -> str "_" ++ spc () ++ str "->" ++ brk (1,2) ++ pr t

let pr_funvar = function
  | None -> spc () ++ str "()"
  | Some id -> spc () ++ pr_id id

let pr_let_clause k pr = function
  | ((_,id),None,t) -> hv 0(str k ++ pr_id id ++ str " =" ++ brk (1,1) ++ pr t)
  | ((_,id),Some c,t) -> str "TODO(LETCLAUSE)"

let pr_let_clauses pr = function
  | hd::tl ->
      hv 0
        (pr_let_clause "Let " pr hd ++
         prlist (fun t -> spc () ++ pr_let_clause "And " pr t) tl)
  | [] -> anomaly "LetIn must declare at least one binding"

let pr_rec_clause pr ((_,id),(l,t)) =
  pr_id id ++ prlist pr_funvar l ++ str "->" ++ spc () ++ pr t

let pr_rec_clauses pr l = 
  prlist_with_sep (fun () -> fnl () ++ str "And ") (pr_rec_clause pr) l

let pr_hintbases = function
  | None -> spc () ++ str "with *"
  | Some [] -> mt ()
  | Some l ->
      spc () ++ str "with" ++ hv 0 (prlist (fun s -> spc () ++ str s) l)

let pr_autoarg_adding = function
  | [] -> mt ()
  | l ->
      spc () ++ str "Adding [" ++
        hv 0 (prlist_with_sep spc pr_reference l) ++ str "]"

let pr_autoarg_destructing = function
  | true -> spc () ++ str "Destructing"
  | false -> mt ()

let pr_autoarg_usingTDB = function
  | true -> spc () ++ str "Using TDB"
  | false -> mt ()

let rec pr_raw_generic prc prlc prtac prref x =
  match Genarg.genarg_tag x with
  | BoolArgType -> pr_arg str (if out_gen rawwit_bool x then "true" else "false")
  | IntArgType -> pr_arg int (out_gen rawwit_int x)
  | IntOrVarArgType -> pr_arg (pr_or_var pr_int) (out_gen rawwit_int_or_var x)
  | StringArgType -> spc () ++ str "\"" ++ str (out_gen rawwit_string x) ++ str "\""
  | PreIdentArgType -> pr_arg str (out_gen rawwit_pre_ident x)
  | IntroPatternArgType -> pr_arg pr_intro_pattern 
      (out_gen rawwit_intro_pattern x)
  | IdentArgType -> pr_arg pr_id ((*Constrextern.v7_to_v8_id*) (out_gen rawwit_ident x))
  | HypArgType -> pr_arg
      (pr_located (fun id -> pr_id (Constrextern.v7_to_v8_id id))) (out_gen rawwit_var x)
  | RefArgType -> pr_arg prref (out_gen rawwit_ref x)
  | SortArgType -> pr_arg pr_sort (out_gen rawwit_sort x)
  | ConstrArgType -> pr_arg prc (out_gen rawwit_constr x)
  | ConstrMayEvalArgType ->
      pr_arg (pr_may_eval prc prref)
        (out_gen rawwit_constr_may_eval x)
  | QuantHypArgType ->
      pr_arg pr_quantified_hypothesis (out_gen rawwit_quant_hyp x)
  | RedExprArgType ->
      pr_arg (pr_red_expr 
        (prc,prref)) (out_gen rawwit_red_expr x)
  | TacticArgType -> pr_arg prtac (out_gen rawwit_tactic x)
  | CastedOpenConstrArgType ->
      pr_arg prc (out_gen rawwit_casted_open_constr x)
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
      let tab =
	if Options.do_translate() or not !Options.v7 then !genarg_pprule
        else !genarg_pprule_v7 in
      try pi1 (Stringmap.find s tab) prc prtac x
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
  | IdentArgType -> pr_arg pr_id ((*Constrextern.v7_to_v8_id*) (out_gen globwit_ident x))
  | HypArgType -> pr_arg (pr_located (fun id -> pr_id (Constrextern.v7_to_v8_id id))) (out_gen globwit_var x)
  | RefArgType -> pr_arg (pr_or_var (pr_located pr_global)) (out_gen globwit_ref x)
  | SortArgType -> pr_arg pr_sort (out_gen globwit_sort x)
  | ConstrArgType -> pr_arg prc (out_gen globwit_constr x)
  | ConstrMayEvalArgType ->
      pr_arg (pr_may_eval prc
        (pr_or_var (pr_and_short_name pr_evaluable_reference))) (out_gen globwit_constr_may_eval x)
  | QuantHypArgType ->
      pr_arg pr_quantified_hypothesis (out_gen globwit_quant_hyp x)
  | RedExprArgType ->
      pr_arg (pr_red_expr 
        (prc,pr_or_var (pr_and_short_name pr_evaluable_reference))) (out_gen globwit_red_expr x)
  | TacticArgType -> pr_arg prtac (out_gen globwit_tactic x)
  | CastedOpenConstrArgType ->
      pr_arg prc (out_gen globwit_casted_open_constr x)
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
      let tab =
	if Options.do_translate() or not !Options.v7 then !genarg_pprule
        else !genarg_pprule_v7 in
      try pi2 (Stringmap.find s tab) prc prtac x
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
  | IdentArgType -> pr_arg pr_id (Constrextern.v7_to_v8_id (out_gen wit_ident x))
  | HypArgType -> pr_arg prc (out_gen wit_var x)
  | RefArgType -> pr_arg pr_global (out_gen wit_ref x)
  | SortArgType -> pr_arg prc (Term.mkSort (out_gen wit_sort x))
  | ConstrArgType -> pr_arg prc (out_gen wit_constr x)
  | ConstrMayEvalArgType ->
      pr_arg prc (out_gen wit_constr_may_eval x)
  | QuantHypArgType ->
      pr_arg pr_quantified_hypothesis (out_gen wit_quant_hyp x)
  | RedExprArgType ->
      pr_arg (pr_red_expr (prc,pr_evaluable_reference)) (out_gen wit_red_expr x)
  | TacticArgType -> pr_arg prtac (out_gen wit_tactic x)
  | CastedOpenConstrArgType ->
      pr_arg prc (snd (out_gen wit_casted_open_constr x))
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
      let tab = 
	if Options.do_translate() or not !Options.v7 then !genarg_pprule
        else !genarg_pprule_v7 in
      try pi3 (Stringmap.find s tab) prc prtac x
      with Not_found -> str " [no printer for " ++ str s ++ str "]"

let rec pr_tacarg_using_rule pr_gen = function
  | Some s :: l, al -> spc () ++ str s ++ pr_tacarg_using_rule pr_gen (l,al)
  | None :: l, a :: al -> pr_gen a ++ pr_tacarg_using_rule  pr_gen (l,al)
  | [], [] -> mt ()
  | _ -> failwith "Inconsistent arguments of extended tactic"

let pr_extend_gen prgen s l =
  let tab = 
    if Options.do_translate() or not !Options.v7 then prtac_tab
    else prtac_tab_v7
  in
  try 
    let tags = List.map genarg_tag l in
    (* Hack pour les syntaxes changeant non uniformément en passant a la V8 *)
    let s =
      let n = String.length s in
      if Options.do_translate() & n > 2 & String.sub s (n-2) 2 = "v7"
      then String.sub s 0 (n-2) ^ "v8"
      else s in
    let (s,pl) = Hashtbl.find tab (s,tags) in
    str s ++ pr_tacarg_using_rule prgen (pl,l)
  with Not_found ->
    str s ++ prlist prgen l ++ str " (* Generic printer *)"

let make_pr_tac (pr_tac,pr_tac0,pr_constr,pr_pat,pr_cst,pr_ind,pr_ref,pr_ident,pr_extend) =

let pr_bindings = pr_bindings pr_constr pr_constr in
let pr_bindings_no_with = pr_bindings_no_with pr_constr pr_constr in
let pr_with_bindings = pr_with_bindings pr_constr pr_constr in
let pr_eliminator cb = str "using" ++ pr_arg (pr_with_bindings) cb in
let pr_constrarg c = spc () ++ pr_constr c in
let pr_intarg n = spc () ++ int n in

  (* Printing tactics as arguments *)
let rec pr_atom0 = function
  | TacIntroPattern [] -> str "Intros"
  | TacIntroMove (None,None) -> str "Intro"
  | TacAssumption -> str "Assumption"
  | TacAnyConstructor None -> str "Constructor"
  | TacTrivial (Some []) -> str "Trivial"
  | TacAuto (None,Some []) -> str "Auto"
  | TacAutoTDB None -> str "AutoTDB"
  | TacDestructConcl -> str "DConcl"
  | TacReflexivity -> str "Reflexivity"
  | t -> str "(" ++ pr_atom1 t ++ str ")"

  (* Main tactic printer *)
and pr_atom1 = function
  | TacExtend (_,s,l) -> pr_extend pr_constr pr_constr pr_tac s l
  | TacAlias (_,s,l,_) ->
      pr_extend pr_constr pr_constr pr_tac s (List.map snd l)

  (* Basic tactics *)
  | TacIntroPattern [] as t -> pr_atom0 t
  | TacIntroPattern (_::_ as p) -> 
      hov 1 (str "Intros" ++ spc () ++ prlist_with_sep spc pr_intro_pattern p)
  | TacIntrosUntil h ->
      hv 1 (str "Intros until" ++ pr_arg pr_quantified_hypothesis h)
  | TacIntroMove (None,None) as t -> pr_atom0 t
  | TacIntroMove (Some id1,None) -> str "Intro " ++ pr_id id1
  | TacIntroMove (ido1,Some (_,id2)) ->
      hov 1
      (str "Intro" ++ pr_opt pr_id ido1 ++ spc () ++ str "after " ++ pr_id id2)
  | TacAssumption as t -> pr_atom0 t
  | TacExact c -> hov 1 (str "Exact" ++ pr_arg pr_constr c)
  | TacApply cb -> hov 1 (str "Apply" ++ spc () ++ pr_with_bindings cb)
  | TacElim (cb,cbo) ->
      hov 1 (str "Elim" ++ pr_arg pr_with_bindings cb ++ 
        pr_opt pr_eliminator cbo)
  | TacElimType c -> hov 1 (str "ElimType" ++ pr_arg pr_constr c)
  | TacCase cb -> hov 1 (str "Case" ++ spc () ++ pr_with_bindings cb)
  | TacCaseType c -> hov 1 (str "CaseType" ++ pr_arg pr_constr c)
  | TacFix (ido,n) -> hov 1 (str "Fix" ++ pr_opt pr_id ido ++ pr_intarg n)
  | TacMutualFix (id,n,l) ->
      hov 1 (str "Fix" ++ spc () ++ pr_id id ++ pr_intarg n ++ spc () ++
        hov 0 (str "with" ++ brk (1,1) ++
          prlist_with_sep spc
	    (fun (id,n,c) ->
	      spc () ++ pr_id id ++ pr_intarg n ++ pr_arg pr_constr c)
	  l))
  | TacCofix ido -> hov 1 (str "Cofix" ++ pr_opt pr_id ido)
  | TacMutualCofix (id,l) ->
      hov 1 (str "Cofix" ++ spc () ++ pr_id id ++ spc () ++
        hov 0 (str "with" ++ brk (1,1) ++
          prlist (fun (id,c) -> spc () ++ pr_id id ++ pr_arg pr_constr c)
	  l))
  | TacCut c -> hov 1 (str "Cut" ++ pr_arg pr_constr c)
  | TacTrueCut (Anonymous,c) -> 
      hov 1 (str "Assert" ++ pr_arg pr_constr c)
  | TacTrueCut (Name id,c) -> 
      hov 1 (str "Assert" ++ spc () ++ pr_id id ++ str ":" ++ pr_constr c)
  | TacForward (false,na,c) ->
      hov 1 (str "Assert" ++ pr_arg pr_name na ++ str ":=" ++ pr_constr c)
  | TacForward (true,na,c) ->
      hov 1 (str "Pose" ++ pr_arg pr_name na ++ str ":=" ++ pr_constr c)
  | TacGeneralize l ->
      hov 1 (str "Generalize" ++ spc () ++ prlist_with_sep spc pr_constr l)
  | TacGeneralizeDep c ->
      hov 1 (str "Generalize" ++ spc () ++ str "Dependent" ++ spc () ++
      pr_constr c)
  | TacLetTac (na,c,cl) ->
      let pcl = match cl with
          {onhyps=None;onconcl=true;concl_occs=[]} -> mt()
        | _ -> pr_clauses pr_ident cl in
      hov 1 (str "LetTac" ++ spc () ++ pr_name na ++ str ":=" ++
             pr_constr c ++ pcl)
  | TacInstantiate (n,c,cls) ->
      hov 1 (str "Instantiate" ++ pr_arg int n ++ pr_arg pr_constr c ++ 
	     pr_clauses pr_ident cls)
  (* Derived basic tactics *)
  | TacSimpleInduction (h,_) ->
      hov 1 (str "Induction" ++ pr_arg pr_quantified_hypothesis h)
  | TacNewInduction (h,e,(ids,_)) ->
      hov 1 (str "NewInduction" ++ spc () ++ pr_induction_arg pr_constr h ++
        pr_opt pr_eliminator e ++ pr_with_names ids)
  | TacSimpleDestruct h ->
      hov 1 (str "Destruct" ++ pr_arg pr_quantified_hypothesis h)
  | TacNewDestruct (h,e,(ids,_)) ->
      hov 1 (str "NewDestruct" ++ spc () ++ pr_induction_arg pr_constr h ++
        pr_opt pr_eliminator e ++ pr_with_names ids)
  | TacDoubleInduction (h1,h2) ->
      hov 1
        (str "Double Induction" ++ 
         pr_arg pr_quantified_hypothesis h1 ++
 	 pr_arg pr_quantified_hypothesis h2)
  | TacDecomposeAnd c ->
      hov 1 (str "Decompose Record" ++ pr_arg pr_constr c)
  | TacDecomposeOr c ->
      hov 1 (str "Decompose Sum" ++ pr_arg pr_constr c)
  | TacDecompose (l,c) ->
      hov 1 (str "Decompose" ++ spc () ++
        hov 0 (str "[" ++ prlist_with_sep spc pr_ind l
	  ++ str "]" ++ pr_arg pr_constr c))
  | TacSpecialize (n,c) ->
      hov 1 (str "Specialize" ++ pr_opt int n ++ pr_with_bindings c)
  | TacLApply c -> 
      hov 1 (str "LApply" ++ pr_constr c)

  (* Automation tactics *)
  | TacTrivial (Some []) as x -> pr_atom0 x
  | TacTrivial db -> hov 0 (str "Trivial" ++ pr_hintbases db)
  | TacAuto (None,Some []) as x -> pr_atom0 x
  | TacAuto (n,db) -> hov 0 (str "Auto" ++ pr_opt int n ++ pr_hintbases db)
  | TacAutoTDB None as x -> pr_atom0 x
  | TacAutoTDB (Some n) -> hov 0 (str "AutoTDB" ++ spc () ++ int n)
  | TacDestructHyp (true,(_,id)) -> hov 0 (str "CDHyp" ++ spc () ++ pr_id id)
  | TacDestructHyp (false,(_,id)) -> hov 0 (str "DHyp" ++ spc () ++ pr_id id)
  | TacDestructConcl as x -> pr_atom0 x
  | TacSuperAuto (n,l,b1,b2) ->
      hov 1 (str "SuperAuto" ++ pr_opt int n ++ pr_autoarg_adding l ++ 
             pr_autoarg_destructing b1 ++ pr_autoarg_usingTDB b2)
  | TacDAuto (n,p) ->
      hov 1 (str "Auto" ++ pr_opt int n ++ str "Decomp" ++ pr_opt int p)

  (* Context management *)
  | TacClear l ->
      hov 1 (str "Clear" ++ spc () ++ prlist_with_sep spc pr_ident l)
  | TacClearBody l ->
      hov 1 (str "ClearBody" ++ spc () ++ prlist_with_sep spc pr_ident l)
  | TacMove (b,id1,id2) ->
      (* Rem: only b = true is available for users *)
      assert b;
      hov 1
        (str "Move" ++ brk (1,1) ++ pr_ident id1 ++ spc () ++ 
	 str "after" ++ brk (1,1) ++ pr_ident id2)
  | TacRename (id1,id2) ->
      hov 1
        (str "Rename" ++ brk (1,1) ++ pr_ident id1 ++ spc () ++ 
	 str "into" ++ brk (1,1) ++ pr_ident id2)

  (* Constructors *)
  | TacLeft l -> hov 1 (str "Left" ++ pr_bindings l)
  | TacRight l -> hov 1 (str "Right" ++ pr_bindings l)
  | TacSplit (_,l) -> hov 1 (str "Split" ++ pr_bindings l)
  | TacAnyConstructor (Some t) ->
      hov 1 (str "Constructor" ++ pr_arg pr_tac0 t)
  | TacAnyConstructor None as t -> pr_atom0 t
  | TacConstructor (n,l) ->
      hov 1 (str "Constructor" ++ pr_or_metaid pr_intarg n ++ pr_bindings l)

  (* Conversion *)  
  | TacReduce (r,h) ->
      hov 1 (pr_red_expr (pr_constr,pr_cst) r ++ pr_clauses pr_ident h)
  | TacChange (occl,c,h) ->
      hov 1 (str "Change" ++ pr_opt (pr_subterms pr_constr) occl ++ 
        brk (1,1) ++ pr_constr c ++ pr_clauses pr_ident h)

  (* Equivalence relations *)
  | TacReflexivity as x -> pr_atom0 x
  | TacSymmetry cls -> str "Symmetry " ++ pr_clauses pr_ident cls
  | TacTransitivity c -> str "Transitivity" ++ pr_arg pr_constr c

  (* Equality and inversion *)
  | TacInversion (DepInversion (k,c,ids),hyp) ->
      hov 1 (str "Dependent " ++ pr_induction_kind k ++ 
      pr_quantified_hypothesis hyp ++
      pr_with_names ids ++ pr_with_constr pr_constr c)
  | TacInversion (NonDepInversion (k,cl,ids),hyp) ->
      hov 1 (pr_induction_kind k ++ spc () ++
      pr_quantified_hypothesis hyp ++
      pr_with_names ids ++ pr_simple_clause pr_ident cl)
  | TacInversion (InversionUsing (c,cl),hyp) ->
      hov 1 (str "Inversion" ++ spc() ++ pr_quantified_hypothesis hyp ++ 
      str "using" ++ spc () ++ pr_constr c ++ 
      pr_simple_clause pr_ident cl)

and pr_tactic_seq_body tl = 
  hv 0 (str "[ " ++
        prlist_with_sep (fun () -> spc () ++ str "| ") prtac tl ++ str " ]")

  (* Strictly closed atomic tactic expressions *)
and pr0 = function
  | TacFirst tl -> str "First" ++ spc () ++ pr_tactic_seq_body tl
  | TacSolve tl -> str "Solve" ++ spc () ++ pr_tactic_seq_body tl
  | TacId "" -> str "Idtac" 
  | TacFail (ArgArg 0,"") -> str "Fail"
  | TacAtom (_,t) -> pr_atom0 t
  | TacArg c -> pr_tacarg c
  | t -> str "(" ++ prtac t ++ str ")"

  (* Semi-closed atomic tactic expressions *)
and pr1 = function
  | TacAtom (_,t) -> pr_atom1 t
  | TacId s -> str "Idtac \"" ++ str s ++ str "\""	
  | TacFail (ArgArg 0,s) -> str "Fail \"" ++ str s ++ str "\""
  | TacFail (n,"") -> str "Fail " ++ pr_or_var int n
  | TacFail (n,s) -> str "Fail " ++ pr_or_var int n ++ str " \"" ++ str s ++ str "\""
  | t -> pr0 t

  (* Orelse tactic expressions (printed as if parsed associating on the right
     though the semantics is purely associative) *)
and pr2 = function
  | TacOrelse (t1,t2) ->
      hov 1 (pr1 t1 ++ str " Orelse" ++ brk (1,1) ++ pr3 t2)
  | t -> pr1 t

  (* Non closed prefix tactic expressions *)
and pr3 = function
  | TacTry t -> hov 1 (str "Try" ++ spc () ++ pr3 t)
  | TacDo (n,t) -> hov 1 (str "Do " ++ pr_or_var int n ++ spc () ++ pr3 t)
  | TacRepeat t -> hov 1 (str "Repeat" ++ spc () ++ pr3 t)
  | TacProgress t -> hov 1 (str "Progress" ++ spc () ++ pr3 t)
  | TacInfo t -> hov 1 (str "Info" ++ spc () ++ pr3 t)
  | t -> pr2 t

and pr4 = function
  | t -> pr3 t

  (* THEN and THENS tactic expressions (printed as if parsed
     associating on the left though the semantics is purely associative) *)
and pr5 = function
  | TacThens (t,tl) -> 
      hov 1 (pr5 t ++ str ";" ++ spc () ++ pr_tactic_seq_body tl)
  | TacThen (t1,t2) ->
      hov 1 (pr5 t1 ++ str ";" ++ spc () ++ pr4 t2)
  | t -> pr4 t

  (* Ltac tactic expressions *)
and pr6 = function
  |(TacAtom _
  | TacThen _
  | TacThens _
  | TacFirst _
  | TacSolve _
  | TacTry _
  | TacOrelse _
  | TacDo _
  | TacRepeat _
  | TacProgress _
  | TacId _
  | TacFail _
  | TacInfo _) as t -> pr5 t

  | TacAbstract (t,None) -> str "Abstract " ++ pr6 t
  | TacAbstract (t,Some s) -> 
      hov 0
       (str "Abstract " ++ pr6 t ++ spc () ++ str "using" ++ spc () ++ pr_id s)
  | TacLetRecIn (l,t) -> 
      hv 0
        (str "Rec " ++ pr_rec_clauses prtac l ++
        spc () ++ str "In" ++ fnl () ++ prtac t)
  | TacLetIn (llc,u) ->
      v 0
       (hv 0 (pr_let_clauses pr_tacarg0 llc ++ spc () ++ str "In") ++ fnl () ++ prtac u)
  | TacMatch (t,lrul) ->
      hov 0 (str "Match" ++ spc () ++ pr6 t ++ spc()
        ++ str "With"
        ++ prlist
	  (fun r -> fnl () ++ str "|" ++ spc () ++
            pr_match_rule true pr_pat prtac r)
	lrul)
  | TacMatchContext (lr,lrul) ->
      hov 0 (
	str (if lr then "Match Reverse Context With" else "Match Context With")
	++ prlist
	  (fun r -> fnl () ++ str "|" ++ spc () ++
            pr_match_rule false pr_pat prtac r)
	lrul)
  | TacFun (lvar,body) ->
      hov 0 (str "Fun" ++
        prlist pr_funvar lvar ++ spc () ++ str "->" ++ spc () ++ prtac body)

  | TacArg c -> pr_tacarg c

and pr_tacarg0 = function
  | TacDynamic (_,t) -> str ("<dynamic ["^(Dyn.tag t)^"]>")
  | MetaIdArg (_,s) -> str ("$" ^ s)
  | IntroPattern ipat -> pr_intro_pattern ipat
  | TacVoid -> str "()"
  | Reference r -> pr_ref r
  | ConstrMayEval (ConstrTerm c) -> str "'" ++ pr_constr c
  | ConstrMayEval c -> pr_may_eval pr_constr pr_cst c
  | Integer n -> int n
  | TacFreshId sopt -> str "FreshId" ++ pr_opt qstring sopt
  | (TacCall _ | Tacexp _) as t -> str "(" ++ pr_tacarg1 t ++ str ")"

and pr_tacarg1 = function
  | TacCall (_,f,l) ->
      hov 0 (pr_ref f ++ spc () ++ prlist_with_sep spc pr_tacarg0 l)
  | Tacexp t -> pr_tac t
  | t -> pr_tacarg0 t

and pr_tacarg x = pr_tacarg1 x

and prtac x = pr6 x

in (prtac,pr0,pr_match_rule false pr_pat pr_tac)

let pr_raw_extend prc prlc prtac = 
  pr_extend_gen (pr_raw_generic prc prlc prtac Ppconstrnew.pr_reference)
let pr_glob_extend prc prlc prtac =
  pr_extend_gen (pr_glob_generic prc prlc prtac)
let pr_extend prc prlc prtac =
  pr_extend_gen (pr_generic prc prlc prtac)

let pr_and_constr_expr pr (c,_) = pr c

let rec glob_printers =
    (pr_glob_tactic, 
     pr_glob_tactic0,
     pr_and_constr_expr Printer.pr_rawterm,
     Printer.pr_pattern,
     pr_or_var (pr_and_short_name pr_evaluable_reference),
     pr_or_var pr_inductive,
     pr_or_var (pr_located pr_ltac_constant),
     pr_located pr_id,
     pr_glob_extend)

and pr_glob_tactic (t:glob_tactic_expr) = pi1 (make_pr_tac glob_printers) t

and pr_glob_tactic0 t = pi2 (make_pr_tac glob_printers) t

and pr_glob_match_context t = pi3 (make_pr_tac glob_printers) t

let (pr_tactic,_,_) =
  make_pr_tac
    (pr_glob_tactic,
     pr_glob_tactic0,
     Printer.prterm,
     Printer.pr_pattern,
     pr_evaluable_reference,
     pr_inductive,
     pr_ltac_constant,
     pr_id,
     pr_extend)
