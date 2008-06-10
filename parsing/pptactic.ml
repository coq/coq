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
open Printer

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

let pr_or_by_notation f = function
  | AN v -> f v
  | ByNotation (_,s) -> str s

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

let rec pr_message_token prid = function
  | MsgString s -> qs s
  | MsgInt n -> int n
  | MsgIdent id -> prid id

let pr_fresh_ids = prlist (fun s -> spc() ++ pr_or_var qs s)

let with_evars ev s = if ev then "e" ^ s else s

let out_bindings = function
  | ImplicitBindings l -> ImplicitBindings (List.map snd l)
  | ExplicitBindings l -> ExplicitBindings (List.map (fun (loc,id,c) -> (loc,id,snd c)) l)
  | NoBindings -> NoBindings

let rec pr_raw_generic prc prlc prtac prref (x:Genarg.rlevel Genarg.generic_argument) =
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
  | SortArgType -> pr_arg pr_rawsort (out_gen rawwit_sort x)
  | ConstrArgType -> pr_arg prc (out_gen rawwit_constr x)
  | ConstrMayEvalArgType ->
      pr_arg (pr_may_eval prc prlc (pr_or_by_notation prref))
        (out_gen rawwit_constr_may_eval x)
  | QuantHypArgType ->
      pr_arg pr_quantified_hypothesis (out_gen rawwit_quant_hyp x)
  | RedExprArgType ->
      pr_arg (pr_red_expr (prc,prlc,pr_or_by_notation prref))
        (out_gen rawwit_red_expr x)
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
  | SortArgType -> pr_arg pr_rawsort (out_gen globwit_sort x)
  | ConstrArgType -> pr_arg prc (out_gen globwit_constr x)
  | ConstrMayEvalArgType ->
      pr_arg (pr_may_eval prc prlc
        (pr_or_var (pr_and_short_name pr_evaluable_reference)))
        (out_gen globwit_constr_may_eval x)
  | QuantHypArgType ->
      pr_arg pr_quantified_hypothesis (out_gen globwit_quant_hyp x)
  | RedExprArgType ->
      pr_arg (pr_red_expr 
        (prc,prlc,pr_or_var (pr_and_short_name pr_evaluable_reference)))
        (out_gen globwit_red_expr x)
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
  | SortArgType -> pr_arg pr_sort (out_gen wit_sort x)
  | ConstrArgType -> pr_arg prc (out_gen wit_constr x)
  | ConstrMayEvalArgType ->
      pr_arg prc (out_gen wit_constr_may_eval x)
  | QuantHypArgType ->
      pr_arg pr_quantified_hypothesis (out_gen wit_quant_hyp x)
  | RedExprArgType ->
      pr_arg (pr_red_expr (prc,prlc,pr_evaluable_reference)) 
        (out_gen wit_red_expr x)
  | OpenConstrArgType b -> pr_arg prc (snd (out_gen (wit_open_constr_gen b) x))
  | ConstrWithBindingsArgType ->
      let (c,b) = out_gen wit_constr_with_bindings x in
      pr_arg (pr_with_bindings prc prlc) (c,out_bindings b)
  | BindingsArgType -> 
      pr_arg (pr_bindings_no_with prc prlc)
        (out_bindings (out_gen wit_bindings x))
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
  pr_extend_gen (pr_generic (fun c -> prc (Evd.empty,c)) (fun c -> prlc (Evd.empty,c)) prtac)

(**********************************************************************)
(* The tactic printer                                                 *)

let sep_v = fun _ -> str"," ++ spc()

let strip_prod_binders_expr n ty =
  let rec strip_ty acc n ty =
    match ty with
        Topconstr.CProdN(_,bll,a) ->
          let nb =
            List.fold_left (fun i (nal,_,_) -> i + List.length nal) 0 bll in
	  let bll = List.map (fun (x, _, y) -> x, y) bll in
            if nb >= n then (List.rev (bll@acc)), a
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

let pr_with_names = function
  | IntroAnonymous -> mt ()
  | ipat -> spc () ++ hov 1 (str "as" ++ spc () ++ pr_intro_pattern ipat)

let pr_as_name = function
  | Anonymous -> mt ()
  | Name id -> str "as " ++ pr_lident (dummy_loc,id)

let pr_pose_as_style prc na c =
  spc() ++ prc c ++ pr_as_name na

let pr_pose prlc prc na c = match na with
  | Anonymous -> spc() ++ prc c
  | Name id -> spc() ++ surround (pr_id id ++ str " :=" ++ spc() ++ prlc c)

let pr_assertion _prlc prc ipat c = match ipat with
(* Use this "optimisation" or use only the general case ?
  | IntroIdentifier id ->
      spc() ++ surround (pr_intro_pattern ipat ++ str " :" ++ spc() ++ prlc c)
*)
  | ipat ->
      spc() ++ prc c ++ pr_with_names ipat

let pr_assumption prlc prc ipat c = match ipat with
(* Use this "optimisation" or use only the general case ?
  | IntroIdentifier id ->
      spc() ++ surround (pr_intro_pattern ipat ++ str " :" ++ spc() ++ prlc c)
*)
  | ipat ->
      spc() ++ prc c ++ pr_with_names ipat

let pr_by_tactic prt = function
  | TacId [] -> mt ()
  | tac -> spc() ++ str "by " ++ prt tac

let pr_hyp_location pr_id = function
  | occs, InHyp -> spc () ++ pr_with_occurrences pr_id occs
  | occs, InHypTypeOnly ->
      spc () ++ 
      pr_with_occurrences (fun id -> str "(type of " ++ pr_id id ++ str ")") occs
  | occs, InHypValueOnly ->
      spc () ++ 
      pr_with_occurrences (fun id -> str "(value of " ++ pr_id id ++ str ")") occs

let pr_in pp = spc () ++ hov 0 (str "in" ++ pp)

let pr_simple_clause pr_id = function
  | [] -> mt ()
  | l -> pr_in (spc () ++ prlist_with_sep spc pr_id l)

let pr_clauses pr_id = function
  | { onhyps=None; concl_occs=occs } ->
      if occs = no_occurrences_expr then pr_in (str " * |-")
      else pr_in (pr_with_occurrences (fun () -> str " *") (occs,()))
  | { onhyps=Some l; concl_occs=occs } ->
      pr_in
        (prlist_with_sep (fun () -> str",") (pr_hyp_location pr_id) l ++
	 (if occs = no_occurrences_expr then mt ()
	  else pr_with_occurrences (fun () -> str" |- *") (occs,())))

let pr_clause_pattern pr_id = function
  | (None, []) -> mt ()
  | (glopt,l) ->
      str " in" ++
      prlist
        (fun (id,nl) -> prlist (pr_arg int) nl 
	  ++ spc () ++ pr_id id) l ++
        pr_opt (fun nl -> prlist_with_sep spc int nl ++ str " Goal") glopt

let pr_orient b = if b then mt () else str " <-"

let pr_multi = function 
  | Precisely 1 -> mt ()
  | Precisely n -> pr_int n ++ str "!"
  | UpTo n -> pr_int n ++ str "?"
  | RepeatStar -> str "?"
  | RepeatPlus -> str "!"

let pr_induction_arg prlc prc = function
  | ElimOnConstr c -> pr_with_bindings prlc prc c
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

let pr_match_hyps pr_pat (Hyp (nal,mp)) =
  pr_lname nal ++ str ":" ++ pr_match_pattern pr_pat mp

let pr_match_rule m pr pr_pat = function
  | Pat ([],mp,t) when m ->
      pr_match_pattern pr_pat mp ++
      spc () ++ str "=>" ++ brk (1,4) ++ pr t
(*
  | Pat (rl,mp,t) ->
      hv 0 (prlist_with_sep pr_coma (pr_match_hyps pr_pat) rl ++
        (if rl <> [] then spc () else mt ()) ++ 
         hov 0 (str "|-" ++ spc () ++ pr_match_pattern pr_pat mp ++ spc () ++
	 str "=>" ++ brk (1,4) ++ pr t))
*)
  | Pat (rl,mp,t) ->
      hov 0 (
	hv 0 (prlist_with_sep pr_coma (pr_match_hyps pr_pat) rl) ++
        (if rl <> [] then spc () else mt ()) ++ 
        hov 0 (
	  str "|-" ++ spc () ++ pr_match_pattern pr_pat mp ++ spc () ++
	  str "=>" ++ brk (1,4) ++ pr t))
  | All t -> str "_" ++ spc () ++ str "=>" ++ brk (1,4) ++ pr t

let pr_funvar = function
  | None -> spc () ++ str "_"
  | Some id -> spc () ++ pr_id id

let pr_let_clause k pr (id,t) =
  hov 0 (str k ++ pr_lident id ++ str " :=" ++ brk (1,1) ++ pr (TacArg t))

let pr_let_clauses recflag pr = function
  | hd::tl ->
      hv 0
        (pr_let_clause (if recflag then "let rec " else "let ") pr hd ++
         prlist (fun t -> spc () ++ pr_let_clause "with " pr t) tl)
  | [] -> anomaly "LetIn must declare at least one binding"

let pr_seq_body pr tl =
  hv 0 (str "[ " ++
        prlist_with_sep (fun () -> spc () ++ str "| ") pr tl ++
        str " ]")

let pr_opt_tactic pr = function
  | TacId [] -> mt ()
  | t -> pr t

let pr_then_gen pr tf tm tl =
  hv 0 (str "[ " ++
        prvect_with_sep mt (fun t -> pr t ++ spc () ++ str "| ") tf ++
	pr_opt_tactic pr tm ++ str ".." ++
	prvect_with_sep mt (fun t -> spc () ++ str "| " ++ pr t) tl ++
        str " ]")

let pr_hintbases = function
  | None -> spc () ++ str "with *"
  | Some [] -> mt ()
  | Some l ->
      spc () ++ hov 2 (str "with" ++ prlist (fun s -> spc () ++ str s) l)

let pr_auto_using prc = function
  | [] -> mt ()
  | l -> spc () ++ 
      hov 2 (str "using" ++ spc () ++ prlist_with_sep pr_coma prc l)

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
let lseq = 4
let ltactical = 3
let lorelse = 2
let llet = 5
let lfun = 5
let lcomplete = 1
let labstract = 3
let lmatch = 1
let latom = 0
let lcall = 1
let leval = 1
let ltatom = 1
let linfo = 5

let level_of (n,p) = match p with E -> n | L -> n-1 | Prec n -> n | Any -> lseq

open Closure

(** A printer for tactics that polymorphically works on the three
    "raw", "glob" and "typed" levels; in practice, the environment is
    used only at the glob and typed level: it is used to feed the
    constr printers *)

let make_pr_tac 
  (pr_tac_level,pr_constr,pr_lconstr,pr_pat,
   pr_cst,pr_ind,pr_ref,pr_ident,
   pr_extend,strip_prod_binders) env =

(* The environment is not used by the tactic printer: it is passed to the
   constr and cst printers; hence we can make some abbreviations *)
let pr_constr = pr_constr env in
let pr_lconstr = pr_lconstr env in
let pr_cst = pr_cst env in
let pr_ind = pr_ind env in
let pr_tac_level = pr_tac_level env in

(* Other short cuts *)
let pr_bindings = pr_bindings pr_lconstr pr_constr in
let pr_ex_bindings = pr_bindings_gen true pr_lconstr pr_constr in
let pr_with_bindings = pr_with_bindings pr_lconstr pr_constr in
let pr_extend = pr_extend pr_constr pr_lconstr pr_tac_level in
let pr_red_expr = pr_red_expr (pr_constr,pr_lconstr,pr_cst) in

let pr_constrarg c = spc () ++ pr_constr c in
let pr_lconstrarg c = spc () ++ pr_lconstr c in
let pr_intarg n = spc () ++ int n in

(* Some printing combinators *)
let pr_eliminator cb = str "using" ++ pr_arg pr_with_bindings cb in

let pr_binder_fix (nal,t) =
(*  match t with
  | CHole _ -> spc() ++ prlist_with_sep spc (pr_lname) nal
  | _ ->*)
    let s = prlist_with_sep spc pr_lname nal ++ str ":" ++ pr_lconstr t in
    spc() ++ hov 1 (str"(" ++ s ++ str")") in

let pr_fix_tac (id,n,c) =
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
        prlist pr_binder_fix bll ++ annot ++ str" :" ++
        pr_lconstrarg ty ++ str")") in
(*  spc() ++
  hov 0 (pr_id id ++ pr_intarg n ++ str":" ++ pr_constrarg
    c)
*)
let pr_cofix_tac (id,c) =
  hov 1 (str"(" ++ pr_id id ++ str" :" ++ pr_lconstrarg c ++ str")") in

  (* Printing tactics as arguments *)
let rec pr_atom0 = function
  | TacIntroPattern [] -> str "intros"
  | TacIntroMove (None,None) -> str "intro"
  | TacAssumption -> str "assumption"
  | TacAnyConstructor (false,None) -> str "constructor"
  | TacAnyConstructor (true,None) -> str "econstructor"
  | TacTrivial ([],Some []) -> str "trivial"
  | TacAuto (None,[],Some []) -> str "auto"
  | TacReflexivity -> str "reflexivity"
  | TacClear (true,[]) -> str "clear"
  | t -> str "(" ++ pr_atom1 t ++ str ")"

  (* Main tactic printer *)
and pr_atom1 = function
  | TacAutoTDB _ | TacDestructHyp _ | TacDestructConcl
  | TacSuperAuto _ | TacExtend (_,
    ("GTauto"|"GIntuition"|"TSimplif"|
     "LinearIntuition"),_) ->
      errorlabstrm "Obsolete V8" (str "Tactic is not ported to V8.0")
  | TacExtend (loc,s,l) ->
      pr_with_comments loc (pr_extend 1 s l)
  | TacAlias (loc,s,l,_) ->
      pr_with_comments loc (pr_extend 1 s (List.map snd l))

  (* Basic tactics *)
  | TacIntroPattern [] as t -> pr_atom0 t
  | TacIntroPattern (_::_ as p) -> 
      hov 1 (str "intros" ++ spc () ++ prlist_with_sep spc pr_intro_pattern p)
  | TacIntrosUntil h ->
      hv 1 (str "intros until" ++ pr_arg pr_quantified_hypothesis h)
  | TacIntroMove (None,None) as t -> pr_atom0 t
  | TacIntroMove (Some id1,None) -> str "intro " ++ pr_id id1
  | TacIntroMove (ido1,Some id2) ->
      hov 1
      (str "intro" ++ pr_opt pr_id ido1 ++ spc () ++ str "after " ++
       pr_lident id2)
  | TacAssumption as t -> pr_atom0 t
  | TacExact c -> hov 1 (str "exact" ++ pr_constrarg c)
  | TacExactNoCheck c -> hov 1 (str "exact_no_check" ++ pr_constrarg c)
  | TacVmCastNoCheck c -> hov 1 (str "vm_cast_no_check" ++ pr_constrarg c)
  | TacApply (a,ev,cb) ->
      hov 1 ((if a then mt() else str "simple ") ++
             str (with_evars ev "apply") ++ spc () ++ 
             pr_with_bindings cb)
  | TacElim (ev,cb,cbo) ->
      hov 1 (str (with_evars ev "elim") ++ pr_arg pr_with_bindings cb ++ 
        pr_opt pr_eliminator cbo)
  | TacElimType c -> hov 1 (str "elimtype" ++ pr_constrarg c)
  | TacCase (ev,cb) ->
      hov 1 (str (with_evars ev "case") ++ spc () ++ pr_with_bindings cb)
  | TacCaseType c -> hov 1 (str "casetype" ++ pr_constrarg c)
  | TacFix (ido,n) -> hov 1 (str "fix" ++ pr_opt pr_id ido ++ pr_intarg n)
  | TacMutualFix (hidden,id,n,l) ->
      if hidden then str "idtac" (* should caught before! *) else
      hov 1 (str "fix" ++ spc () ++ pr_id id ++ pr_intarg n ++ spc() ++
             str"with " ++ prlist_with_sep spc pr_fix_tac l)
  | TacCofix ido -> hov 1 (str "cofix" ++ pr_opt pr_id ido)
  | TacMutualCofix (hidden,id,l) ->
      if hidden then str "idtac" (* should be caught before! *) else
      hov 1 (str "cofix" ++ spc () ++ pr_id id ++ spc() ++
             str"with " ++ prlist_with_sep spc pr_cofix_tac l)
  | TacCut c -> hov 1 (str "cut" ++ pr_constrarg c)
  | TacAssert (Some tac,ipat,c) -> 
      hov 1 (str "assert" ++ 
             pr_assumption pr_lconstr pr_constr ipat c ++ 
             pr_by_tactic (pr_tac_level ltop) tac)
  | TacAssert (None,ipat,c) -> 
      hov 1 (str "pose proof" ++
             pr_assertion pr_lconstr pr_constr ipat c)
  | TacGeneralize l ->
      hov 1 (str "generalize" ++ spc () ++
             prlist_with_sep pr_coma (fun (cl,na) -> 
	       pr_with_occurrences pr_constr cl ++ pr_as_name na)
	     l)
  | TacGeneralizeDep c ->
      hov 1 (str "generalize" ++ spc () ++ str "dependent" ++
             pr_constrarg c)
  | TacLetTac (na,c,cl,true) when cl = nowhere ->
      hov 1 (str "pose" ++ pr_pose pr_lconstr pr_constr na c)
  | TacLetTac (na,c,cl,b) ->
      hov 1 ((if b then str "set" else str "remember") ++
             (if b then pr_pose pr_lconstr else pr_pose_as_style)
	        pr_constr na c ++
             pr_clauses pr_ident cl)
(*  | TacInstantiate (n,c,ConclLocation ()) ->
      hov 1 (str "instantiate" ++ spc() ++
             hov 1 (str"(" ++ pr_arg int n ++ str" :=" ++
                    pr_lconstrarg c ++ str ")" ))
  | TacInstantiate (n,c,HypLocation (id,hloc)) ->
      hov 1 (str "instantiate" ++ spc() ++
             hov 1 (str"(" ++ pr_arg int n ++ str" :=" ++
                    pr_lconstrarg c ++ str ")" ) 
	     ++ str "in" ++ pr_hyp_location pr_ident (id,[],(hloc,ref None)))
*)
  (* Derived basic tactics *)
  | TacSimpleInduction h ->
      hov 1 (str "simple induction" ++ pr_arg pr_quantified_hypothesis h)
  | TacNewInduction (ev,h,e,ids,cl) ->
      hov 1 (str (with_evars ev "induction") ++ spc () ++
	     prlist_with_sep spc (pr_induction_arg pr_lconstr pr_constr) h ++
	     pr_with_names ids ++
             pr_opt pr_eliminator e ++
             pr_opt_no_spc (pr_clauses pr_ident) cl)
  | TacSimpleDestruct h ->
      hov 1 (str "simple destruct" ++ pr_arg pr_quantified_hypothesis h)
  | TacNewDestruct (ev,h,e,ids,cl) ->
      hov 1 (str (with_evars ev "destruct") ++ spc () ++
             prlist_with_sep spc (pr_induction_arg pr_lconstr pr_constr) h ++ 
	     pr_with_names ids ++
             pr_opt pr_eliminator e ++
             pr_opt_no_spc (pr_clauses pr_ident) cl)
  | TacDoubleInduction (h1,h2) ->
      hov 1
        (str "double induction" ++  
         pr_arg pr_quantified_hypothesis h1 ++
 	 pr_arg pr_quantified_hypothesis h2)
  | TacDecomposeAnd c ->
      hov 1 (str "decompose record" ++ pr_constrarg c)
  | TacDecomposeOr c ->
      hov 1 (str "decompose sum" ++ pr_constrarg c)
  | TacDecompose (l,c) ->
      hov 1 (str "decompose" ++ spc () ++
        hov 0 (str "[" ++ prlist_with_sep spc pr_ind l
	  ++ str "]" ++ pr_constrarg c))
  | TacSpecialize (n,c) ->
      hov 1 (str "specialize" ++ spc () ++ pr_opt int n ++ 
             pr_with_bindings c)
  | TacLApply c -> 
      hov 1 (str "lapply" ++ pr_constrarg c)

  (* Automation tactics *)
  | TacTrivial ([],Some []) as x -> pr_atom0 x
  | TacTrivial (lems,db) ->
      hov 0 (str "trivial" ++ 
             pr_auto_using pr_constr lems ++ pr_hintbases db)
  | TacAuto (None,[],Some []) as x -> pr_atom0 x
  | TacAuto (n,lems,db) ->
      hov 0 (str "auto" ++ pr_opt (pr_or_var int) n ++ 
             pr_auto_using pr_constr lems ++ pr_hintbases db)
  | TacDAuto (n,p,lems) ->
      hov 1 (str "auto" ++ pr_opt (pr_or_var int) n ++ str "decomp" ++ 
             pr_opt int p ++ pr_auto_using pr_constr lems)

  (* Context management *)
  | TacClear (true,[]) as t -> pr_atom0 t
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
  | TacRename l ->
      hov 1
        (str "rename" ++ brk (1,1) ++
         prlist_with_sep 
	   (fun () -> str "," ++ brk (1,1))
	   (fun (i1,i2) -> 
	      pr_ident i1 ++ spc () ++ str "into" ++ spc () ++ pr_ident i2)
	   l)
  | TacRevert l -> 
      hov 1 (str "revert" ++ spc () ++ prlist_with_sep spc pr_ident l) 

  (* Constructors *)
  | TacLeft (ev,l) -> hov 1 (str (with_evars ev "left") ++ pr_bindings l)
  | TacRight (ev,l) -> hov 1 (str (with_evars ev "right") ++ pr_bindings l)
  | TacSplit (ev,false,l) -> hov 1 (str (with_evars ev "split") ++ pr_bindings l)
  | TacSplit (ev,true,l) -> hov 1 (str (with_evars ev "exists") ++ pr_ex_bindings l)
  | TacAnyConstructor (ev,Some t) ->
      hov 1 (str (with_evars ev "constructor") ++ pr_arg (pr_tac_level (latom,E)) t)
  | TacAnyConstructor (ev,None) as t -> pr_atom0 t
  | TacConstructor (ev,n,l) ->
      hov 1 (str (with_evars ev "constructor") ++ 
             pr_or_metaid pr_intarg n ++ pr_bindings l)

  (* Conversion *)  
  | TacReduce (r,h) ->
      hov 1 (pr_red_expr r ++
             pr_clauses pr_ident h)
  | TacChange (occ,c,h) ->
      hov 1 (str "change" ++ brk (1,1) ++
      (match occ with
          None -> mt()
        | Some occlc ->
	    pr_with_occurrences_with_trailer pr_constr occlc 
	      (spc () ++ str "with ")) ++
      pr_constr c ++ pr_clauses pr_ident h)

  (* Equivalence relations *)
  | TacReflexivity as x -> pr_atom0 x
  | TacSymmetry cls -> str "symmetry " ++ pr_clauses pr_ident cls
  | TacTransitivity c -> str "transitivity" ++ pr_constrarg c

  (* Equality and inversion *)
  | TacRewrite (ev,l,cl,by) -> 
      hov 1 (str (with_evars ev "rewrite") ++ 
	     prlist_with_sep
	     (fun () -> str ","++spc())
	     (fun (b,m,c) -> 
		pr_orient b ++ spc() ++ pr_multi m ++ pr_with_bindings c)
	     l
	     ++ pr_clauses pr_ident cl
	     ++	(match by with Some by -> pr_by_tactic (pr_tac_level ltop) by | None -> mt())) 
  | TacInversion (DepInversion (k,c,ids),hyp) ->
      hov 1 (str "dependent " ++ pr_induction_kind k ++ spc () ++
      pr_quantified_hypothesis hyp ++
      pr_with_names ids ++ pr_with_constr pr_constr c)
  | TacInversion (NonDepInversion (k,cl,ids),hyp) ->
      hov 1 (pr_induction_kind k ++ spc () ++
      pr_quantified_hypothesis hyp ++
      pr_with_names ids ++ pr_simple_clause pr_ident cl)
  | TacInversion (InversionUsing (c,cl),hyp) ->
      hov 1 (str "inversion" ++ spc() ++ pr_quantified_hypothesis hyp ++ 
      spc () ++ str "using" ++ spc () ++ pr_constr c ++ 
      pr_simple_clause pr_ident cl)

in

let rec pr_tac inherited tac =
  let (strm,prec) = match tac with
  | TacAbstract (t,None) ->
      str "abstract " ++ pr_tac (labstract,L) t, labstract
  | TacAbstract (t,Some s) -> 
      hov 0
       (str "abstract (" ++ pr_tac (labstract,L) t ++ str")" ++ spc () ++
        str "using " ++ pr_id s),
      labstract
  | TacLetIn (recflag,llc,u) ->
      v 0
       (hv 0 (pr_let_clauses recflag (pr_tac ltop) llc ++ str " in") ++
       fnl () ++ pr_tac (llet,E) u),
      llet
  | TacMatch (lz,t,lrul) ->
      hov 0 (pr_lazy lz ++ str "match " ++ pr_tac ltop t ++ str " with"
        ++ prlist
	  (fun r -> fnl () ++ str "| " ++
            pr_match_rule true (pr_tac ltop) pr_pat r)
	lrul
        ++ fnl() ++ str "end"),
      lmatch
  | TacMatchContext (lz,lr,lrul) ->
      hov 0 (pr_lazy lz ++ 
	str (if lr then "match reverse goal with" else "match goal with")
	++ prlist
	  (fun r -> fnl () ++ str "| " ++
            pr_match_rule false (pr_tac ltop) pr_pat r)
	lrul
        ++ fnl() ++ str "end"),
      lmatch
  | TacFun (lvar,body) ->
      hov 2 (str "fun" ++
        prlist pr_funvar lvar ++ str " =>" ++ spc () ++
        pr_tac (lfun,E) body),
      lfun
  | TacThens (t,tl) -> 
      hov 1 (pr_tac (lseq,E) t ++ pr_then () ++ spc () ++
             pr_seq_body (pr_tac ltop) tl),
      lseq
  | TacThen (t1,[||],t2,[||]) ->
      hov 1 (pr_tac (lseq,E) t1 ++ pr_then () ++ spc () ++
             pr_tac (lseq,L) t2),
      lseq
  | TacThen (t1,tf,t2,tl) ->
      hov 1 (pr_tac (lseq,E) t1 ++ pr_then () ++ spc () ++
             pr_then_gen (pr_tac ltop) tf t2 tl),
      lseq
  | TacTry t ->
      hov 1 (str "try" ++ spc () ++ pr_tac (ltactical,E) t),
      ltactical
  | TacDo (n,t) ->
      hov 1 (str "do " ++ pr_or_var int n ++ spc () ++ 
             pr_tac (ltactical,E) t),
      ltactical
  | TacRepeat t ->
      hov 1 (str "repeat" ++ spc () ++ pr_tac (ltactical,E) t),
      ltactical
  | TacProgress t ->
      hov 1 (str "progress" ++ spc () ++ pr_tac (ltactical,E) t),
      ltactical
  | TacInfo t ->
      hov 1 (str "info" ++ spc () ++ pr_tac (ltactical,E) t),
      linfo
  | TacOrelse (t1,t2) ->
      hov 1 (pr_tac (lorelse,L) t1 ++ str " ||" ++ brk (1,1) ++
             pr_tac (lorelse,E) t2),
      lorelse
  | TacFail (n,l) -> 
      str "fail" ++ (if n=ArgArg 0 then mt () else pr_arg (pr_or_var int) n) ++
      prlist (pr_arg (pr_message_token pr_ident)) l, latom
  | TacFirst tl ->
      str "first" ++ spc () ++ pr_seq_body (pr_tac ltop) tl, llet
  | TacSolve tl ->
      str "solve" ++ spc () ++ pr_seq_body (pr_tac ltop) tl, llet
  | TacComplete t ->
      str "complete" ++ spc () ++ pr_tac (lcomplete,E) t, lcomplete
  | TacId l ->
      str "idtac" ++ prlist (pr_arg (pr_message_token pr_ident)) l, latom
  | TacAtom (loc,TacAlias (_,s,l,_)) ->
      pr_with_comments loc
        (pr_extend (level_of inherited) s (List.map snd l)),
      latom
  | TacAtom (loc,t) ->
      pr_with_comments loc (hov 1 (pr_atom1 t)), ltatom
  | TacArg(Tacexp e) -> pr_tac_level (latom,E) e, latom
  | TacArg(ConstrMayEval (ConstrTerm c)) ->
      str "constr:" ++ pr_constr c, latom
  | TacArg(ConstrMayEval c) ->
      pr_may_eval pr_constr pr_lconstr pr_cst c, leval
  | TacArg(TacFreshId l) -> str "fresh" ++ pr_fresh_ids l, latom
  | TacArg(Integer n) -> int n, latom
  | TacArg(TacCall(loc,f,[])) -> pr_ref f, latom
  | TacArg(TacCall(loc,f,l)) ->
      pr_with_comments loc
        (hov 1 (pr_ref f ++ spc () ++
         prlist_with_sep spc pr_tacarg l)),
      lcall
  | TacArg a -> pr_tacarg a, latom
  in
  if prec_less prec inherited then strm
  else str"(" ++ strm ++ str")"

and pr_tacarg = function
  | TacDynamic (loc,t) ->
      pr_with_comments loc (str ("<dynamic ["^(Dyn.tag t)^"]>"))
  | MetaIdArg (loc,true,s) -> pr_with_comments loc (str ("$" ^ s))
  | MetaIdArg (loc,false,s) -> pr_with_comments loc (str ("constr: $" ^ s))
  | IntroPattern ipat -> str "ipattern:" ++ pr_intro_pattern ipat
  | TacVoid -> str "()"
  | Reference r -> pr_ref r
  | ConstrMayEval c ->
      pr_may_eval pr_constr pr_lconstr pr_cst c
  | TacFreshId l -> str "fresh" ++ pr_fresh_ids l
  | TacExternal (_,com,req,la) ->
      str "external" ++ spc() ++ qs com ++ spc() ++ qs req ++ 
      spc() ++ prlist_with_sep spc pr_tacarg la
  | (TacCall _|Tacexp _|Integer _) as a ->
      str "ltac:" ++ pr_tac (latom,E) (TacArg a)

in (pr_tac, pr_match_rule)

let strip_prod_binders_rawterm n (ty,_) =
  let rec strip_ty acc n ty =
    if n=0 then (List.rev acc, (ty,None)) else
      match ty with
          Rawterm.RProd(loc,na,Explicit,a,b) ->
            strip_ty (([dummy_loc,na],(a,None))::acc) (n-1) b
        | _ -> error "Cannot translate fix tactic: not enough products" in
  strip_ty [] n ty

let strip_prod_binders_constr n (sigma,ty) =
  let rec strip_ty acc n ty =
    if n=0 then (List.rev acc, (sigma,ty)) else
      match Term.kind_of_term ty with
          Term.Prod(na,a,b) ->
            strip_ty (([dummy_loc,na],(sigma,a))::acc) (n-1) b
        | _ -> error "Cannot translate fix tactic: not enough products" in
  strip_ty [] n ty

let drop_env f _env = f

let rec raw_printers =
    (pr_raw_tactic_level, 
     drop_env pr_constr_expr,
     drop_env pr_lconstr_expr,
     pr_lpattern_expr,
     drop_env (pr_or_by_notation pr_reference),
     drop_env (pr_or_by_notation pr_reference),
     pr_reference,
     pr_or_metaid pr_lident,
     pr_raw_extend,
     strip_prod_binders_expr)

and pr_raw_tactic_level env n (t:raw_tactic_expr) =
  fst (make_pr_tac raw_printers env) n t

and pr_raw_match_rule env t =
  snd (make_pr_tac raw_printers env) t

let pr_and_constr_expr pr (c,_) = pr c

let rec glob_printers =
    (pr_glob_tactic_level, 
     (fun env -> pr_and_constr_expr (pr_rawconstr_env env)),
     (fun env -> pr_and_constr_expr (pr_lrawconstr_env env)),
     (fun c -> pr_lconstr_pattern_env (Global.env()) c),
     (fun env -> pr_or_var (pr_and_short_name (pr_evaluable_reference_env env))),
     (fun env -> pr_or_var (pr_inductive env)),
     pr_ltac_or_var (pr_located pr_ltac_constant),
     pr_lident,
     pr_glob_extend,
     strip_prod_binders_rawterm)

and pr_glob_tactic_level env n (t:glob_tactic_expr) =
  fst (make_pr_tac glob_printers env) n t

and pr_glob_match_rule env t =
  snd (make_pr_tac glob_printers env) t

let typed_printers =
    (pr_glob_tactic_level,
     pr_open_constr_env,
     pr_open_lconstr_env,
     pr_lconstr_pattern,
     pr_evaluable_reference_env,
     pr_inductive,
     pr_ltac_constant,
     pr_id,
     pr_extend,
     strip_prod_binders_constr)

let pr_tactic_level env = fst (make_pr_tac typed_printers env)

let pr_raw_tactic env = pr_raw_tactic_level env ltop
let pr_glob_tactic env = pr_glob_tactic_level env ltop
let pr_tactic env = pr_tactic_level env ltop

let _ = Tactic_debug.set_tactic_printer
  (fun x -> pr_glob_tactic (Global.env()) x)

let _ = Tactic_debug.set_match_pattern_printer
  (fun env hyp -> pr_match_pattern (pr_constr_pattern_env env) hyp)

let _ = Tactic_debug.set_match_rule_printer
  (fun rl ->
    pr_match_rule false (pr_glob_tactic (Global.env())) pr_constr_pattern rl)

open Pcoq

let pr_tac_polymorphic n _ _ prtac = prtac (n,E)

let _ = for i=0 to 5 do
  declare_extra_genarg_pprule
  (rawwit_tactic i, pr_tac_polymorphic i)
  (globwit_tactic i, pr_tac_polymorphic i)
  (wit_tactic i, pr_tac_polymorphic i)
done
