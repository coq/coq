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
open Ppconstr

let pr_global x = Nametab.pr_global_env Idset.empty x

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
  pr_extend_gen (pr_raw_generic prc prlc prtac pr_reference)
let pr_glob_extend prc prlc prtac =
  pr_extend_gen (pr_glob_generic prc prlc prtac)
let pr_extend prc prlc prtac =
  pr_extend_gen (pr_generic prc prlc prtac)

(**********************************************************************)
(* The tactic printer                                                 *)

let sep_v = fun _ -> str"," ++ spc()

let strip_prod_binders_expr n ty =
  let rec strip_ty acc n ty =
    match ty with
        Topconstr.CProdN(_,bll,a) ->
          let nb =
            List.fold_left (fun i (nal,_) -> i + List.length nal) 0 bll in
          if nb >= n then (List.rev (bll@acc), a)
          else strip_ty (bll@acc) (n-nb) a
      | Topconstr.CArrow(_,a,b) ->
          if n=1 then
            (List.rev (([(dummy_loc,Anonymous)],a)::acc), b)
          else strip_ty (([(dummy_loc,Anonymous)],a)::acc) (n-1) b
      | _ -> error "Cannot translate fix tactic: not enough products" in
  strip_ty [] n ty

let pr_ltac_or_var pr = function
  | ArgArg x -> pr x
  | ArgVar (loc,id) -> pr_with_comments loc (pr_id id)

let pr_arg pr x = spc () ++ pr x

let pr_ltac_constant sp =
  pr_qualid (Nametab.shortest_qualid_of_tactic sp)

let pr_evaluable_reference_env env = function 
  | EvalVarRef id -> pr_id id
  | EvalConstRef sp -> 
      Nametab.pr_global_env (Termops.vars_of_env env) (Libnames.ConstRef sp)

let pr_inductive env ind =
  Nametab.pr_global_env (Termops.vars_of_env env) (Libnames.IndRef ind)

let pr_quantified_hypothesis = function
  | AnonHyp n -> int n
  | NamedHyp id -> pr_id id 

let pr_quantified_hypothesis_arg h = spc () ++ pr_quantified_hypothesis h

let pr_esubst prc l =
  let pr_qhyp = function
      (_,AnonHyp n,c) -> str "(" ++ int n ++ str" := " ++ prc c ++ str ")"
    | (_,NamedHyp id,c) ->
        str "(" ++ pr_id id ++ str" := " ++ prc c ++ str ")"
  in
  prlist_with_sep spc pr_qhyp l

let pr_bindings_gen for_ex prlc prc = function
  | ImplicitBindings l ->
      spc () ++
      hv 2 ((if for_ex then mt() else str "with" ++ spc ()) ++
            prlist_with_sep spc prc l)
  | ExplicitBindings l ->
      spc () ++
      hv 2 ((if for_ex then mt() else str "with" ++ spc ()) ++
            pr_esubst prlc l)
  | NoBindings -> mt ()

let pr_bindings prlc prc = pr_bindings_gen false prlc prc

let pr_with_bindings prlc prc (c,bl) =
  hov 1 (prc c ++ pr_bindings prlc prc bl)

let pr_with_constr prc = function
  | None -> mt ()
  | Some c -> spc () ++ hov 1 (str "with" ++ spc () ++ prc c)

(* Translator copy of pr_intro_pattern based on a translating "pr_id" *)
let rec pr_intro_pattern = function
  | IntroOrAndPattern pll -> pr_case_intro_pattern pll
  | IntroWildcard -> str "_"
  | IntroIdentifier id -> pr_id id
and pr_case_intro_pattern = function
  | [_::_ as pl] ->
      str "(" ++ hov 0 (prlist_with_sep pr_coma pr_intro_pattern pl) ++ str ")"
  | pll ->
      str "[" ++
      hv 0 (prlist_with_sep pr_bar 
        (fun l -> hov 0 (prlist_with_sep spc pr_intro_pattern l)) pll)
      ++ str "]"

let pr_with_names = function
  | None -> mt ()
  | Some ipat -> spc () ++ hov 1 (str "as" ++ spc () ++ pr_intro_pattern ipat)

let pr_occs pp = function
    [] -> pp
  | nl -> hov 1 (pp ++ spc() ++ str"at " ++
                 hov 0 (prlist_with_sep spc int nl))

let pr_hyp_location pr_id = function
  | id, occs, InHyp -> spc () ++ pr_occs (pr_id id) occs
  | id, occs, InHypTypeOnly ->
      spc () ++ pr_occs (str "(type of " ++ pr_id id ++ str ")") occs
  | id, occs, InHypValueOnly ->
      spc () ++ pr_occs (str "(value of " ++ pr_id id ++ str ")") occs

let pr_in pp = spc () ++ hov 0 (str "in" ++ pp)

let pr_simple_clause pr_id = function
  | [] -> mt ()
  | l -> pr_in (spc () ++ prlist_with_sep spc pr_id l)

let pr_clauses pr_id = function
    { onhyps=None; onconcl=true; concl_occs=nl } ->
      pr_in (pr_occs (str " *") nl)
  | { onhyps=None; onconcl=false } -> pr_in (str " * |-")
  | { onhyps=Some l; onconcl=true; concl_occs=nl } -> 
      pr_in (prlist_with_sep (fun () -> str",") (pr_hyp_location pr_id) l
             ++ pr_occs (str" |- *") nl)
  | { onhyps=Some l; onconcl=false } ->
      pr_in (prlist_with_sep (fun()->str",") (pr_hyp_location pr_id) l)

let pr_clause_pattern pr_id = function
  | (None, []) -> mt ()
  | (glopt,l) ->
      str " in" ++
      prlist
        (fun (id,nl) -> prlist (pr_arg int) nl 
	  ++ spc () ++ pr_id id) l ++
        pr_opt (fun nl -> prlist_with_sep spc int nl ++ str " Goal") glopt

let pr_induction_arg prc = function
  | ElimOnConstr c -> prc c
  | ElimOnIdent (loc,id) -> pr_with_comments loc (pr_id id)
  | ElimOnAnonHyp n -> int n

let pr_induction_kind = function
  | SimpleInversion -> str "simple inversion"
  | FullInversion -> str "inversion"
  | FullInversionClear -> str "inversion_clear"

let pr_lazy lz = if lz then str "lazy " else mt ()

let pr_match_pattern pr_pat = function
  | Term a -> pr_pat a
  | Subterm (None,a) -> str "context [" ++ pr_pat a ++ str "]"
  | Subterm (Some id,a) ->
      str "context " ++ pr_id id ++ str "[" ++ pr_pat a ++ str "]"

let pr_match_hyps pr_pat = function
  | Hyp (nal,mp) -> pr_lname nal ++ str ":" ++ pr_match_pattern pr_pat mp

let pr_match_rule m pr pr_pat = function
  | Pat ([],mp,t) when m ->
      pr_match_pattern pr_pat mp ++
      spc () ++ str "=>" ++ brk (1,4) ++ pr t
  | Pat (rl,mp,t) ->
      prlist_with_sep (fun () -> str",") (pr_match_hyps pr_pat) rl ++
      spc () ++ str "|-" ++ spc () ++ pr_match_pattern pr_pat mp ++ spc () ++
      str "=>" ++ brk (1,4) ++ pr t
  | All t -> str "_" ++ spc () ++ str "=>" ++ brk (1,4) ++ pr t

let pr_funvar = function
  | None -> spc () ++ str "_"
  | Some id -> spc () ++ pr_id id

let pr_let_clause k pr = function
  | (id,None,t) ->
      hov 0 (str k ++ pr_lident id ++ str " :=" ++ brk (1,1) ++
             pr (TacArg t))
  | (id,Some c,t) ->
      hv 0 (str k ++ pr_lident id ++ str" :" ++ brk(1,2) ++
      pr c ++
      str " :=" ++ brk (1,1) ++ pr (TacArg t))

let pr_let_clauses pr = function
  | hd::tl ->
      hv 0
        (pr_let_clause "let " pr hd ++
         prlist (fun t -> spc () ++ pr_let_clause "with " pr t) tl)
  | [] -> anomaly "LetIn must declare at least one binding"

let pr_rec_clause pr (id,(l,t)) =
  hov 0
    (pr_lident id ++ prlist pr_funvar l ++ str " :=") ++ spc () ++ pr t

let pr_rec_clauses pr l = 
  prlist_with_sep (fun () -> fnl () ++ str "with ") (pr_rec_clause pr) l

let pr_seq_body pr tl =
  hv 0 (str "[ " ++
        prlist_with_sep (fun () -> spc () ++ str "| ") pr tl ++
        str " ]")

let pr_hintbases = function
  | None -> spc () ++ str "with *"
  | Some [] -> mt ()
  | Some l ->
      spc () ++ hov 2 (str "with" ++ prlist (fun s -> spc () ++ str s) l)

let pr_autoarg_adding = function
  | [] -> mt ()
  | l ->
      spc () ++ str "adding [" ++
        hv 0 (prlist_with_sep spc pr_reference l) ++ str "]"

let pr_autoarg_destructing = function
  | true -> spc () ++ str "destructing"
  | false -> mt ()

let pr_autoarg_usingTDB = function
  | true -> spc () ++ str "using tdb"
  | false -> mt ()

let rec pr_tacarg_using_rule pr_gen = function
  | Egrammar.TacTerm s :: l, al -> spc () ++ str s ++ pr_tacarg_using_rule pr_gen (l,al)
  | Egrammar.TacNonTerm _ :: l, a :: al -> pr_gen a ++ pr_tacarg_using_rule pr_gen (l,al)
  | [], [] -> mt ()
  | _ -> failwith "Inconsistent arguments of extended tactic"

let pr_then () = str ";"

let ltop = (5,E)
let lseq = 5
let ltactical = 3
let lorelse = 2
let llet = 1
let lfun = 1
let labstract = 3
let lmatch = 1
let latom = 0
let lcall = 1
let leval = 1
let ltatom = 1

let level_of (n,p) = match p with E -> n | L -> n-1 | Prec n -> n | Any -> lseq

open Closure

let make_pr_tac 
  (pr_tac_level,pr_constr,pr_lconstr,pr_pat,
   pr_cst,pr_ind,pr_ref,pr_ident,
   pr_extend,strip_prod_binders) =

let pr_bindings env =
  pr_bindings (pr_lconstr env) (pr_constr env) in
let pr_ex_bindings env =
  pr_bindings_gen true (pr_lconstr env) (pr_constr env) in
let pr_with_bindings env =
  pr_with_bindings (pr_lconstr env) (pr_constr env) in
let pr_eliminator env cb =
  str "using" ++ pr_arg (pr_with_bindings env) cb in
let pr_extend env =
  pr_extend (pr_constr env) (pr_lconstr env) (pr_tac_level env) in
let pr_red_expr env = 
  pr_red_expr (pr_constr env,pr_lconstr env,pr_cst env) in

let pr_constrarg env c = spc () ++ pr_constr env c in
let pr_lconstrarg env c = spc () ++ pr_lconstr env c in
let pr_intarg n = spc () ++ int n in

let pr_binder_fix env (nal,t) =
(*  match t with
  | CHole _ -> spc() ++ prlist_with_sep spc (pr_lname) nal
  | _ ->*)
    let s =
      prlist_with_sep spc (pr_lname) nal ++ str ":" ++
      pr_lconstr env t in
    spc() ++ hov 1 (str"(" ++ s ++ str")") in

let pr_fix_tac env (id,n,c) =
  let rec set_nth_name avoid n = function
      (nal,ty)::bll ->
        if n <= List.length nal then
          match list_chop (n-1) nal with
              _, (_,Name id) :: _ -> id, (nal,ty)::bll
            | bef, (loc,Anonymous) :: aft ->
                let id = next_ident_away_from (id_of_string"y") avoid in
                id, ((bef@(loc,Name id)::aft, ty)::bll)
            | _ -> assert false
        else
          let (id,bll') = set_nth_name avoid (n-List.length nal) bll in
          (id,(nal,ty)::bll')
    | [] -> assert false in
  let (bll,ty) = strip_prod_binders n c in
  let names =
    List.fold_left
      (fun ln (nal,_) -> List.fold_left
          (fun ln na -> match na with (_,Name id) -> id::ln | _ -> ln)
          ln nal)
      [] bll in
  let idarg,bll = set_nth_name names n bll in
  let annot =
    if List.length names = 1 then mt()
    else spc() ++ str"{struct " ++ pr_id idarg ++ str"}" in
  hov 1 (str"(" ++ pr_id id ++ 
        prlist (pr_binder_fix env) bll ++ annot ++ str" :" ++
        pr_lconstrarg env ty ++ str")") in
(*  spc() ++
  hov 0 (pr_id id ++ pr_intarg n ++ str":" ++ pr_constrarg
    env c)
*)
let pr_cofix_tac env (id,c) =
  hov 1 (str"(" ++ pr_id id ++ str" :" ++ pr_lconstrarg env c ++ str")") in


  (* Printing tactics as arguments *)
let rec pr_atom0 env = function
  | TacIntroPattern [] -> str "intros"
  | TacIntroMove (None,None) -> str "intro"
  | TacAssumption -> str "assumption"
  | TacAnyConstructor None -> str "constructor"
  | TacTrivial (Some []) -> str "trivial"
  | TacAuto (None,Some []) -> str "auto"
  | TacReflexivity -> str "reflexivity"
  | t -> str "(" ++ pr_atom1 env t ++ str ")"

  (* Main tactic printer *)
and pr_atom1 env = function
  | TacAutoTDB _ | TacDestructHyp _ | TacDestructConcl
  | TacSuperAuto _ | TacExtend (_,
    ("GTauto"|"GIntuition"|"TSimplif"|
     "LinearIntuition"),_) ->
      errorlabstrm "Obsolete V8" (str "Tactic is not ported to V8.0")
  | TacExtend (loc,s,l) ->
      pr_with_comments loc (pr_extend env 1 s l)
  | TacAlias (loc,s,l,_) ->
      pr_with_comments loc (pr_extend env 1 s (List.map snd l))

  (* Basic tactics *)
  | TacIntroPattern [] as t -> pr_atom0 env t
  | TacIntroPattern (_::_ as p) -> 
      hov 1 (str "intros" ++ spc () ++ prlist_with_sep spc pr_intro_pattern p)
  | TacIntrosUntil h ->
      hv 1 (str "intros until" ++ pr_arg pr_quantified_hypothesis h)
  | TacIntroMove (None,None) as t -> pr_atom0 env t
  | TacIntroMove (Some id1,None) -> str "intro " ++ pr_id id1
  | TacIntroMove (ido1,Some id2) ->
      hov 1
      (str "intro" ++ pr_opt pr_id ido1 ++ spc () ++ str "after " ++
       pr_lident id2)
  | TacAssumption as t -> pr_atom0 env t
  | TacExact c -> hov 1 (str "exact" ++ pr_constrarg env c)
  | TacExactNoCheck c -> hov 1 (str "exact_no_check" ++ pr_constrarg env c)
  | TacApply cb -> hov 1 (str "apply" ++ spc () ++ pr_with_bindings env cb)
  | TacElim (cb,cbo) ->
      hov 1 (str "elim" ++ pr_arg (pr_with_bindings env) cb ++ 
        pr_opt (pr_eliminator env) cbo)
  | TacElimType c -> hov 1 (str "elimtype" ++ pr_constrarg env c)
  | TacCase cb -> hov 1 (str "case" ++ spc () ++ pr_with_bindings env cb)
  | TacCaseType c -> hov 1 (str "casetype" ++ pr_constrarg env c)
  | TacFix (ido,n) -> hov 1 (str "fix" ++ pr_opt pr_id ido ++ pr_intarg n)
  | TacMutualFix (id,n,l) ->
      hov 1 (str "fix" ++ spc () ++ pr_id id ++ pr_intarg n ++ spc() ++
             str"with " ++ prlist_with_sep spc (pr_fix_tac env) l)
  | TacCofix ido -> hov 1 (str "cofix" ++ pr_opt pr_id ido)
  | TacMutualCofix (id,l) ->
      hov 1 (str "cofix" ++ spc () ++ pr_id id ++ spc() ++
             str"with " ++ prlist_with_sep spc (pr_cofix_tac env) l)
  | TacCut c -> hov 1 (str "cut" ++ pr_constrarg env c)
  | TacTrueCut (Anonymous,c) -> 
      hov 1 (str "assert" ++ pr_constrarg env c)
  | TacTrueCut (Name id,c) -> 
      hov 1 (str "assert" ++ spc () ++
             hov 1 (str"(" ++ pr_id id ++ str " :" ++
                    pr_lconstrarg env c ++ str")"))
  | TacForward (false,na,c) ->
      hov 1 (str "assert" ++ spc () ++
             hov 1 (str"(" ++ pr_name na ++ str " :=" ++
                    pr_lconstrarg env c ++ str")"))
  | TacForward (true,Anonymous,c) ->
      hov 1 (str "pose" ++ pr_constrarg env c)
  | TacForward (true,Name id,c) ->
      hov 1 (str "pose" ++ spc() ++
             hov 1 (str"(" ++ pr_id id ++ str " :=" ++
                    pr_lconstrarg env c ++ str")"))
  | TacGeneralize l ->
      hov 1 (str "generalize" ++ spc () ++
             prlist_with_sep spc (pr_constr env) l)
  | TacGeneralizeDep c ->
      hov 1 (str "generalize" ++ spc () ++ str "dependent" ++
             pr_constrarg env c)
  | TacLetTac (Anonymous,c,cl) ->
      hov 1 (str "set" ++ pr_constrarg env c) ++ pr_clauses pr_ident cl
  | TacLetTac (Name id,c,cl) ->
      hov 1 (str "set" ++ spc () ++
             hov 1 (str"(" ++ pr_id id ++ str " :=" ++
                    pr_lconstrarg env c ++ str")") ++
             pr_clauses pr_ident cl)
(*  | TacInstantiate (n,c,ConclLocation ()) ->
      hov 1 (str "instantiate" ++ spc() ++
             hov 1 (str"(" ++ pr_arg int n ++ str" :=" ++
                    pr_lconstrarg env c ++ str ")" ))
  | TacInstantiate (n,c,HypLocation (id,hloc)) ->
      hov 1 (str "instantiate" ++ spc() ++
             hov 1 (str"(" ++ pr_arg int n ++ str" :=" ++
                    pr_lconstrarg env c ++ str ")" ) 
	     ++ str "in" ++ pr_hyp_location pr_ident (id,[],(hloc,ref None)))
*)
  (* Derived basic tactics *)
  | TacSimpleInduction h ->
      hov 1 (str "simple induction" ++ pr_arg pr_quantified_hypothesis h)
  | TacNewInduction (h,e,ids) ->
      hov 1 (str "induction" ++ spc () ++
             pr_induction_arg (pr_constr env) h ++ pr_with_names ids ++
             pr_opt (pr_eliminator env) e)
  | TacSimpleDestruct h ->
      hov 1 (str "simple destruct" ++ pr_arg pr_quantified_hypothesis h)
  | TacNewDestruct (h,e,ids) ->
      hov 1 (str "destruct" ++ spc () ++
             pr_induction_arg (pr_constr env) h ++ pr_with_names ids ++
             pr_opt (pr_eliminator env) e)
  | TacDoubleInduction (h1,h2) ->
      hov 1
        (str "double induction" ++  
         pr_arg pr_quantified_hypothesis h1 ++
 	 pr_arg pr_quantified_hypothesis h2)
  | TacDecomposeAnd c ->
      hov 1 (str "decompose record" ++ pr_constrarg env c)
  | TacDecomposeOr c ->
      hov 1 (str "decompose sum" ++ pr_constrarg env c)
  | TacDecompose (l,c) ->
      hov 1 (str "decompose" ++ spc () ++
        hov 0 (str "[" ++ prlist_with_sep spc (pr_ind env) l
	  ++ str "]" ++ pr_constrarg env c))
  | TacSpecialize (n,c) ->
      hov 1 (str "specialize" ++ spc () ++ pr_opt int n ++ 
             pr_with_bindings env c)
  | TacLApply c -> 
      hov 1 (str "lapply" ++ pr_constrarg env c)

  (* Automation tactics *)
  | TacTrivial (Some []) as x -> pr_atom0 env x
  | TacTrivial db -> hov 0 (str "trivial" ++ pr_hintbases db)
  | TacAuto (None,Some []) as x -> pr_atom0 env x
  | TacAuto (n,db) ->
      hov 0 (str "auto" ++ pr_opt (pr_or_var int) n ++ pr_hintbases db)
  | TacDAuto (n,p) ->
      hov 1 (str "auto" ++ pr_opt (pr_or_var int) n ++ str "decomp" ++ pr_opt int p)

  (* Context management *)
  | TacClear (keep,l) ->
      hov 1 (str "clear" ++ spc () ++ (if keep then str "- " else mt ()) ++
             prlist_with_sep spc pr_ident l)
  | TacClearBody l ->
      hov 1 (str "clearbody" ++ spc () ++ prlist_with_sep spc pr_ident l)
  | TacMove (b,id1,id2) ->
      (* Rem: only b = true is available for users *)
      assert b;
      hov 1
        (str "move" ++ brk (1,1) ++ pr_ident id1 ++ spc () ++ 
	 str "after" ++ brk (1,1) ++ pr_ident id2)
  | TacRename (id1,id2) ->
      hov 1
        (str "rename" ++ brk (1,1) ++ pr_ident id1 ++ spc () ++ 
	 str "into" ++ brk (1,1) ++ pr_ident id2)

  (* Constructors *)
  | TacLeft l -> hov 1 (str "left" ++ pr_bindings env l)
  | TacRight l -> hov 1 (str "right" ++ pr_bindings env l)
  | TacSplit (false,l) -> hov 1 (str "split" ++ pr_bindings env l)
  | TacSplit (true,l) -> hov 1 (str "exists" ++ pr_ex_bindings env l)
  | TacAnyConstructor (Some t) ->
      hov 1 (str "constructor" ++ pr_arg (pr_tac_level env (latom,E)) t)
  | TacAnyConstructor None as t -> pr_atom0 env t
  | TacConstructor (n,l) ->
      hov 1 (str "constructor" ++ pr_or_metaid pr_intarg n ++ pr_bindings env l)

  (* Conversion *)  
  | TacReduce (r,h) ->
      hov 1 (pr_red_expr env r ++
             pr_clauses pr_ident h)
  | TacChange (occ,c,h) ->
      hov 1 (str "change" ++ brk (1,1) ++
      (match occ with
          None -> mt()
        | Some([],c1) -> hov 1 (pr_constr env c1 ++ spc() ++ str "with ")
        | Some(ocl,c1) ->
            hov 1 (pr_constr env c1 ++ spc() ++
	           str "at " ++ prlist_with_sep spc int ocl) ++ spc() ++
	           str "with ") ++
      pr_constr env c ++ pr_clauses pr_ident h)

  (* Equivalence relations *)
  | TacReflexivity as x -> pr_atom0 env x
  | TacSymmetry cls -> str "symmetry " ++ pr_clauses pr_ident cls
  | TacTransitivity c -> str "transitivity" ++ pr_constrarg env c

  (* Equality and inversion *)
  | TacInversion (DepInversion (k,c,ids),hyp) ->
      hov 1 (str "dependent " ++ pr_induction_kind k ++ spc () ++
      pr_quantified_hypothesis hyp ++
      pr_with_names ids ++ pr_with_constr (pr_constr env) c)
  | TacInversion (NonDepInversion (k,cl,ids),hyp) ->
      hov 1 (pr_induction_kind k ++ spc () ++
      pr_quantified_hypothesis hyp ++
      pr_with_names ids ++ pr_simple_clause pr_ident cl)
  | TacInversion (InversionUsing (c,cl),hyp) ->
      hov 1 (str "inversion" ++ spc() ++ pr_quantified_hypothesis hyp ++ 
      spc () ++ str "using" ++ spc () ++ pr_constr env c ++ 
      pr_simple_clause pr_ident cl)

in

let rec pr_tac env inherited tac =
  let (strm,prec) = match tac with
  | TacAbstract (t,None) ->
      str "abstract " ++ pr_tac env (labstract,L) t, labstract
  | TacAbstract (t,Some s) -> 
      hov 0
       (str "abstract (" ++ pr_tac env (labstract,L) t ++ str")" ++ spc () ++
        str "using " ++ pr_id s),
      labstract
  | TacLetRecIn (l,t) -> 
      hv 0
        (str "let rec " ++ pr_rec_clauses (pr_tac env ltop) l ++ str " in" ++
         fnl () ++ pr_tac env (llet,E) t),
      llet
  | TacLetIn (llc,u) ->
      v 0
       (hv 0 (pr_let_clauses (pr_tac env ltop) llc
       ++ str " in") ++
       fnl () ++ pr_tac env (llet,E) u),
      llet
  | TacMatch (lz,t,lrul) ->
      hov 0 (pr_lazy lz ++ str "match " ++ pr_tac env ltop t ++ str " with"
        ++ prlist
	  (fun r -> fnl () ++ str "| " ++
            pr_match_rule true (pr_tac env ltop) pr_pat r)
	lrul
        ++ fnl() ++ str "end"),
      lmatch
  | TacMatchContext (lz,lr,lrul) ->
      hov 0 (pr_lazy lz ++ 
	str (if lr then "match reverse goal with" else "match goal with")
	++ prlist
	  (fun r -> fnl () ++ str "| " ++
            pr_match_rule false (pr_tac env ltop) pr_pat r)
	lrul
        ++ fnl() ++ str "end"),
      lmatch
  | TacFun (lvar,body) ->
(*      let env = List.fold_right (option_fold_right Idset.add) lvar env in*)
      hov 2 (str "fun" ++
        prlist pr_funvar lvar ++ str " =>" ++ spc () ++
        pr_tac env (lfun,E) body),
      lfun
  | TacThens (t,tl) -> 
      hov 1 (pr_tac env (lseq,E) t ++ pr_then () ++ spc () ++
             pr_seq_body (pr_tac env ltop) tl),
      lseq
  | TacThen (t1,t2) ->
      hov 1 (pr_tac env (lseq,E) t1 ++ pr_then () ++ spc () ++
             pr_tac env (lseq,L) t2),
      lseq
  | TacTry t ->
      hov 1 (str "try" ++ spc () ++ pr_tac env (ltactical,E) t),
      ltactical
  | TacDo (n,t) ->
      hov 1 (str "do " ++ pr_or_var int n ++ spc () ++ 
             pr_tac env (ltactical,E) t),
      ltactical
  | TacRepeat t ->
      hov 1 (str "repeat" ++ spc () ++ pr_tac env (ltactical,E) t),
      ltactical
  | TacProgress t ->
      hov 1 (str "progress" ++ spc () ++ pr_tac env (ltactical,E) t),
      ltactical
  | TacInfo t ->
      hov 1 (str "info" ++ spc () ++ pr_tac env (ltactical,E) t),
      ltactical
  | TacOrelse (t1,t2) ->
      hov 1 (pr_tac env (lorelse,L) t1 ++ str " ||" ++ brk (1,1) ++
             pr_tac env (lorelse,E) t2),
      lorelse
  | TacFail (ArgArg 0,"") -> str "fail", latom
  | TacFail (n,s) -> 
      str "fail" ++ (if n=ArgArg 0 then mt () else pr_arg (pr_or_var int) n) ++
      (if s="" then mt() else (spc() ++ qs s)), latom
  | TacFirst tl ->
      str "first" ++ spc () ++ pr_seq_body (pr_tac env ltop) tl, llet
  | TacSolve tl ->
      str "solve" ++ spc () ++ pr_seq_body (pr_tac env ltop) tl, llet
  | TacId "" -> str "idtac", latom
  | TacId s -> str "idtac" ++ (qs s), latom
  | TacAtom (loc,TacAlias (_,s,l,_)) ->
      pr_with_comments loc
        (pr_extend env (level_of inherited) s (List.map snd l)),
      latom
  | TacAtom (loc,t) ->
      pr_with_comments loc (hov 1 (pr_atom1 env t)), ltatom
  | TacArg(Tacexp e) -> pr_tac_level env (latom,E) e, latom
  | TacArg(ConstrMayEval (ConstrTerm c)) ->
      str "constr:" ++ pr_constr env c, latom
  | TacArg(ConstrMayEval c) ->
      pr_may_eval (pr_constr env) (pr_lconstr env) (pr_cst env) c, leval
  | TacArg(TacFreshId sopt) -> str "fresh" ++ pr_opt qs sopt, latom
  | TacArg(Integer n) -> int n, latom
  | TacArg(TacCall(loc,f,l)) ->
      pr_with_comments loc
        (hov 1 (pr_ref f ++ spc () ++
         prlist_with_sep spc (pr_tacarg env) l)),
      lcall
  | TacArg a -> pr_tacarg env a, latom
  in
  if prec_less prec inherited then strm
  else str"(" ++ strm ++ str")"

and pr_tacarg env = function
  | TacDynamic (loc,t) ->
      pr_with_comments loc (str ("<dynamic ["^(Dyn.tag t)^"]>"))
  | MetaIdArg (loc,s) -> pr_with_comments loc (str ("$" ^ s))
  | IntroPattern ipat -> str "ipattern:" ++ pr_intro_pattern ipat
  | TacVoid -> str "()"
  | Reference r -> pr_ref r
  | ConstrMayEval c ->
      pr_may_eval (pr_constr env) (pr_lconstr env) (pr_cst env) c
  | TacFreshId sopt -> str "fresh" ++ pr_opt qs sopt
  | TacExternal (_,com,req,la) ->
      str "external" ++ spc() ++ qs com ++ spc() ++ qs req ++ 
      spc() ++ prlist_with_sep spc (pr_tacarg env) la
  | (TacCall _|Tacexp _|Integer _) as a ->
      str "ltac:" ++ pr_tac env (latom,E) (TacArg a)

in (pr_tac, pr_match_rule)

let strip_prod_binders_rawterm n (ty,_) =
  let rec strip_ty acc n ty =
    if n=0 then (List.rev acc, (ty,None)) else
      match ty with
          Rawterm.RProd(loc,na,a,b) ->
            strip_ty (([dummy_loc,na],(a,None))::acc) (n-1) b
        | _ -> error "Cannot translate fix tactic: not enough products" in
  strip_ty [] n ty

let strip_prod_binders_constr n ty =
  let rec strip_ty acc n ty =
    if n=0 then (List.rev acc, ty) else
      match Term.kind_of_term ty with
          Term.Prod(na,a,b) ->
            strip_ty (([dummy_loc,na],a)::acc) (n-1) b
        | _ -> error "Cannot translate fix tactic: not enough products" in
  strip_ty [] n ty

let drop_env f _env = f

let rec raw_printers =
    (pr_raw_tactic_level, 
     drop_env pr_constr,
     drop_env pr_lconstr,
     pr_pattern,
     drop_env pr_reference,
     drop_env pr_reference,
     pr_reference,
     pr_or_metaid pr_lident,
     pr_raw_extend,
     strip_prod_binders_expr)

and pr_raw_tactic_level env n (t:raw_tactic_expr) =
  fst (make_pr_tac raw_printers) env n t

and pr_raw_match_rule env t =
  snd (make_pr_tac raw_printers) env t

let pr_and_constr_expr pr (c,_) = pr c

let rec glob_printers =
    (pr_glob_tactic_level, 
     (fun env -> pr_and_constr_expr (pr_rawconstr_env env)),
     (fun env -> pr_and_constr_expr (pr_lrawconstr_env env)),
     (fun c -> pr_constr_pattern_env (Global.env()) c),
     (fun env -> pr_or_var (pr_and_short_name (pr_evaluable_reference_env env))),
     (fun env -> pr_or_var (pr_inductive env)),
     pr_ltac_or_var (pr_located pr_ltac_constant),
     pr_lident,
     pr_glob_extend,
     strip_prod_binders_rawterm)

and pr_glob_tactic_level env n (t:glob_tactic_expr) =
  fst (make_pr_tac glob_printers) env n t

and pr_glob_match_rule env t =
  snd (make_pr_tac glob_printers) env t

let ((pr_tactic_level:Environ.env -> tolerability -> Proof_type.tactic_expr -> std_ppcmds),_) =
  make_pr_tac
    (pr_glob_tactic_level,
     pr_term_env,
     pr_lterm_env,
     pr_constr_pattern,
     pr_evaluable_reference_env,
     pr_inductive,
     pr_ltac_constant,
     pr_id,
     pr_extend,
     strip_prod_binders_constr)

let pr_raw_tactic env = pr_raw_tactic_level env ltop
let pr_glob_tactic env = pr_glob_tactic_level env ltop
let pr_tactic env = pr_tactic_level env ltop

let _ = Tactic_debug.set_tactic_printer
  (fun x -> pr_glob_tactic (Global.env()) x)

let _ = Tactic_debug.set_match_pattern_printer
  (fun env hyp ->
    pr_match_pattern
      (Printer.pr_pattern_env env (Termops.names_of_rel_context env)) hyp)

let _ = Tactic_debug.set_match_rule_printer
  (fun rl ->
    pr_match_rule false (pr_glob_tactic (Global.env())) Printer.pr_pattern rl)
