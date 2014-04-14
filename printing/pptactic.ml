(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Names
open Namegen
open Errors
open Util
open Constrexpr
open Tacexpr
open Genarg
open Constrarg
open Libnames
open Ppextend
open Misctypes
open Locus
open Decl_kinds
open Genredexpr
open Ppconstr
open Printer

let pr_global x = Nametab.pr_global_env Id.Set.empty x

type grammar_terminals = string option list

type pp_tactic = {
  pptac_args : argument_type list;
  pptac_prods : int * grammar_terminals;
}

(* ML Extensions *)
let prtac_tab = Hashtbl.create 17

(* Tactic notations *)
let prnotation_tab = Summary.ref ~name:"pptactic-notation" KNmap.empty

let declare_ml_tactic_pprule key pt =
  Hashtbl.add prtac_tab (key, pt.pptac_args) pt.pptac_prods

let declare_notation_tactic_pprule kn pt =
  prnotation_tab := KNmap.add kn pt !prnotation_tab

type 'a raw_extra_genarg_printer =
    (constr_expr -> std_ppcmds) ->
    (constr_expr -> std_ppcmds) ->
    (tolerability -> raw_tactic_expr -> std_ppcmds) ->
    'a -> std_ppcmds

type 'a glob_extra_genarg_printer =
    (glob_constr_and_expr -> std_ppcmds) ->
    (glob_constr_and_expr -> std_ppcmds) ->
    (tolerability -> glob_tactic_expr -> std_ppcmds) ->
    'a -> std_ppcmds

type 'a extra_genarg_printer =
    (Term.constr -> std_ppcmds) ->
    (Term.constr -> std_ppcmds) ->
    (tolerability -> glob_tactic_expr -> std_ppcmds) ->
    'a -> std_ppcmds

let genarg_pprule = ref String.Map.empty

let declare_extra_genarg_pprule wit f g h =
  let s = match unquote (topwit wit) with
    | ExtraArgType s -> s
    | _ -> error
	"Can declare a pretty-printing rule only for extra argument types."
  in
  let f prc prlc prtac x = f prc prlc prtac (out_gen (rawwit wit) x) in
  let g prc prlc prtac x = g prc prlc prtac (out_gen (glbwit wit) x) in
  let h prc prlc prtac x = h prc prlc prtac (out_gen (topwit wit) x) in
  genarg_pprule := String.Map.add s (f,g,h) !genarg_pprule

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
  | ByNotation (_,s,sc) -> qs s ++ pr_opt (fun sc -> str "%" ++ str sc) sc

let pr_located pr (loc,x) = pr x

let pr_evaluable_reference = function
  | EvalVarRef id -> pr_id id
  | EvalConstRef sp -> pr_global (Globnames.ConstRef sp)

let pr_quantified_hypothesis = function
  | AnonHyp n -> int n
  | NamedHyp id -> pr_id id

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

let pr_message_token prid = function
  | MsgString s -> qs s
  | MsgInt n -> int n
  | MsgIdent id -> prid id

let pr_fresh_ids = prlist (fun s -> spc() ++ pr_or_var qs s)

let with_evars ev s = if ev then "e" ^ s else s


let rec pr_raw_generic prc prlc prtac prpat prref (x:Genarg.rlevel Genarg.generic_argument) =
  match Genarg.genarg_tag x with
  | IntOrVarArgType -> pr_or_var int (out_gen (rawwit wit_int_or_var) x)
  | IdentArgType -> pr_id (out_gen (rawwit wit_ident) x)
  | VarArgType -> pr_located pr_id (out_gen (rawwit wit_var) x)
  | GenArgType -> pr_raw_generic prc prlc prtac prpat prref (out_gen (rawwit wit_genarg) x)
  | ConstrArgType -> prc (out_gen (rawwit wit_constr) x)
  | ConstrMayEvalArgType ->
      pr_may_eval prc prlc (pr_or_by_notation prref) prpat
        (out_gen (rawwit wit_constr_may_eval) x)
  | QuantHypArgType -> pr_quantified_hypothesis (out_gen (rawwit wit_quant_hyp) x)
  | RedExprArgType ->
      pr_red_expr (prc,prlc,pr_or_by_notation prref,prpat)
        (out_gen (rawwit wit_red_expr) x)
  | OpenConstrArgType -> prc (snd (out_gen (rawwit wit_open_constr) x))
  | ConstrWithBindingsArgType ->
      pr_with_bindings prc prlc (out_gen (rawwit wit_constr_with_bindings) x)
  | BindingsArgType ->
      pr_bindings_no_with prc prlc (out_gen (rawwit wit_bindings) x)
  | ListArgType _ ->
      hov 0 (pr_sequence (pr_raw_generic prc prlc prtac prpat prref)
	(fold_list (fun a l -> a::l) x []))
  | OptArgType _ -> hov 0 (fold_opt (pr_raw_generic prc prlc prtac prpat prref) (mt()) x)
  | PairArgType _ ->
      hov 0
        (fold_pair
	  (fun a b -> pr_sequence (pr_raw_generic prc prlc prtac prpat prref)
            [a;b])
	  x)
  | ExtraArgType s ->
      try pi1 (String.Map.find s !genarg_pprule) prc prlc prtac x
      with Not_found -> Genprint.generic_raw_print x


let rec pr_glb_generic prc prlc prtac prpat x =
  match Genarg.genarg_tag x with
  | IntOrVarArgType -> pr_or_var int (out_gen (glbwit wit_int_or_var) x)
  | IdentArgType -> pr_id (out_gen (glbwit wit_ident) x)
  | VarArgType -> pr_located pr_id (out_gen (glbwit wit_var) x)
  | GenArgType -> pr_glb_generic prc prlc prtac prpat (out_gen (glbwit wit_genarg) x)
  | ConstrArgType -> prc (out_gen (glbwit wit_constr) x)
  | ConstrMayEvalArgType ->
      pr_may_eval prc prlc
        (pr_or_var (pr_and_short_name pr_evaluable_reference)) prpat
        (out_gen (glbwit wit_constr_may_eval) x)
  | QuantHypArgType ->
      pr_quantified_hypothesis (out_gen (glbwit wit_quant_hyp) x)
  | RedExprArgType ->
      pr_red_expr
        (prc,prlc,pr_or_var (pr_and_short_name pr_evaluable_reference),prpat)
        (out_gen (glbwit wit_red_expr) x)
  | OpenConstrArgType -> prc (snd (out_gen (glbwit wit_open_constr) x))
  | ConstrWithBindingsArgType ->
      pr_with_bindings prc prlc (out_gen (glbwit wit_constr_with_bindings) x)
  | BindingsArgType ->
      pr_bindings_no_with prc prlc (out_gen (glbwit wit_bindings) x)
  | ListArgType _ ->
      hov 0 (pr_sequence (pr_glb_generic prc prlc prtac prpat)
	(fold_list (fun a l -> a::l) x []))
  | OptArgType _ -> hov 0 (fold_opt (pr_glb_generic prc prlc prtac prpat) (mt()) x)
  | PairArgType _ ->
      hov 0
        (fold_pair
	  (fun a b -> pr_sequence (pr_glb_generic prc prlc prtac prpat) [a;b])
	  x)
  | ExtraArgType s ->
      try pi2 (String.Map.find s !genarg_pprule) prc prlc prtac x
      with Not_found -> Genprint.generic_glb_print x

let rec pr_top_generic prc prlc prtac prpat x =
  match Genarg.genarg_tag x with
  | IntOrVarArgType -> pr_or_var int (out_gen (topwit wit_int_or_var) x)
  | IdentArgType -> pr_id (out_gen (topwit wit_ident) x)
  | VarArgType -> pr_id (out_gen (topwit wit_var) x)
  | GenArgType -> pr_top_generic prc prlc prtac prpat (out_gen (topwit wit_genarg) x)
  | ConstrArgType -> prc (out_gen (topwit wit_constr) x)
  | ConstrMayEvalArgType -> prc (out_gen (topwit wit_constr_may_eval) x)
  | QuantHypArgType -> pr_quantified_hypothesis (out_gen (topwit wit_quant_hyp) x)
  | RedExprArgType ->
      pr_red_expr (prc,prlc,pr_evaluable_reference,prpat)
        (out_gen (topwit wit_red_expr) x)
  | OpenConstrArgType -> prc (snd (out_gen (topwit wit_open_constr) x))
  | ConstrWithBindingsArgType ->
      let (c,b) = (out_gen (topwit wit_constr_with_bindings) x).Evd.it in
      pr_with_bindings prc prlc (c,b)
  | BindingsArgType ->
      pr_bindings_no_with prc prlc (out_gen (topwit wit_bindings) x).Evd.it
  | ListArgType _ ->
      hov 0 (pr_sequence (pr_top_generic prc prlc prtac prpat)
	(fold_list (fun a l -> a::l) x []))
  | OptArgType _ -> hov 0 (fold_opt (pr_top_generic prc prlc prtac prpat) (mt()) x)
  | PairArgType _ ->
      hov 0
        (fold_pair (fun a b -> pr_sequence (pr_top_generic prc prlc prtac prpat)
          [a;b])
	  x)
  | ExtraArgType s ->
      try pi3 (String.Map.find s !genarg_pprule) prc prlc prtac x
      with Not_found -> Genprint.generic_top_print x

let rec tacarg_using_rule_token pr_gen = function
  | Some s :: l, al -> str s :: tacarg_using_rule_token pr_gen (l,al)
  | None :: l, a :: al ->
      let print_it =
        match genarg_tag a with
        | OptArgType _ -> fold_opt (fun _ -> true) false a
        | _ -> true
      in
      let r = tacarg_using_rule_token pr_gen (l,al) in
      if print_it then pr_gen a :: r else r
  | [], [] -> []
  | _ -> failwith "Inconsistent arguments of extended tactic"

let pr_tacarg_using_rule pr_gen l=
  pr_sequence (fun x -> x) (tacarg_using_rule_token pr_gen l)

let pr_extend_gen pr_gen lev s l =
  try
    let tags = List.map genarg_tag l in
    let (lev',pl) = Hashtbl.find prtac_tab (s,tags) in
    let p = pr_tacarg_using_rule pr_gen (pl,l) in
    if lev' > lev then surround p else p
  with Not_found ->
    str s ++ spc() ++ pr_sequence pr_gen l ++ str" (* Generic printer *)"

let pr_alias_gen pr_gen lev key l =
  try
    let pp = KNmap.find key !prnotation_tab in
    let (lev', pl) = pp.pptac_prods in
    let p = pr_tacarg_using_rule pr_gen (pl, l) in
    if lev' > lev then surround p else p
  with Not_found ->
    KerName.print key ++ spc() ++ pr_sequence pr_gen l ++ str" (* Generic printer *)"

let pr_raw_extend prc prlc prtac prpat =
  pr_extend_gen (pr_raw_generic prc prlc prtac prpat pr_reference)
let pr_glob_extend prc prlc prtac prpat =
  pr_extend_gen (pr_glb_generic prc prlc prtac prpat)
let pr_extend prc prlc prtac prpat =
  pr_extend_gen (pr_top_generic prc prlc prtac prpat)

let pr_raw_alias prc prlc prtac prpat =
  pr_alias_gen (pr_raw_generic prc prlc prtac prpat pr_reference)
let pr_glob_alias prc prlc prtac prpat =
  pr_alias_gen (pr_glb_generic prc prlc prtac prpat)

(**********************************************************************)
(* The tactic printer                                                 *)

let strip_prod_binders_expr n ty =
  let rec strip_ty acc n ty =
    match ty with
        Constrexpr.CProdN(_,bll,a) ->
          let nb =
            List.fold_left (fun i (nal,_,_) -> i + List.length nal) 0 bll in
	  let bll = List.map (fun (x, _, y) -> x, y) bll in
            if nb >= n then (List.rev (bll@acc)), a
            else strip_ty (bll@acc) (n-nb) a
      | _ -> error "Cannot translate fix tactic: not enough products" in
  strip_ty [] n ty

let pr_ltac_or_var pr = function
  | ArgArg x -> pr x
  | ArgVar (loc,id) -> pr_with_comments loc (pr_id id)

let pr_ltac_constant kn =
  if !Constrextern.in_debugger then pr_kn kn
  else pr_qualid (Nametab.shortest_qualid_of_tactic kn)

let pr_evaluable_reference_env env = function
  | EvalVarRef id -> pr_id id
  | EvalConstRef sp ->
      Nametab.pr_global_env (Termops.vars_of_env env) (Globnames.ConstRef sp)

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

let pr_as_ipat pat = str "as " ++ Miscprint.pr_intro_pattern pat
let pr_eqn_ipat pat = str "eqn:" ++ Miscprint.pr_intro_pattern pat

let pr_with_induction_names = function
  | None, None -> mt ()
  | Some eqpat, None -> spc () ++ hov 1 (pr_eqn_ipat eqpat)
  | None, Some ipat -> spc () ++ hov 1 (pr_as_ipat ipat)
  | Some eqpat, Some ipat ->
    spc () ++ hov 1 (pr_as_ipat ipat ++ spc () ++ pr_eqn_ipat eqpat)

let pr_as_intro_pattern ipat =
  spc () ++ hov 1 (str "as" ++ spc () ++ Miscprint.pr_intro_pattern ipat)

let pr_with_inversion_names = function
  | None -> mt ()
  | Some ipat -> pr_as_intro_pattern ipat

let pr_as_ipat = function
  | None -> mt ()
  | Some ipat -> pr_as_intro_pattern ipat

let pr_as_name = function
  | Anonymous -> mt ()
  | Name id -> str " as " ++ pr_lident (Loc.ghost,id)

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
      spc() ++ prc c ++ pr_as_ipat ipat

let pr_assumption prlc prc ipat c = match ipat with
(* Use this "optimisation" or use only the general case ?
  | IntroIdentifier id ->
      spc() ++ surround (pr_intro_pattern ipat ++ str " :" ++ spc() ++ prlc c)
*)
  | ipat ->
      spc() ++ prc c ++ pr_as_ipat ipat

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

let pr_simple_hyp_clause pr_id = function
  | [] -> mt ()
  | l -> pr_in (spc () ++ prlist_with_sep spc pr_id l)

let pr_in_hyp_as pr_id = function
  | None -> mt ()
  | Some (id,ipat) -> pr_simple_hyp_clause pr_id [id] ++ pr_as_ipat ipat

let pr_clauses default_is_concl pr_id = function
  | { onhyps=Some []; concl_occs=AllOccurrences }
      when (match default_is_concl with Some true -> true | _ -> false) -> mt ()
  | { onhyps=None; concl_occs=AllOccurrences }
      when (match default_is_concl with Some false -> true | _ -> false) -> mt ()
  | { onhyps=None; concl_occs=NoOccurrences } ->
      pr_in (str " * |-")
  | { onhyps=None; concl_occs=occs } ->
      pr_in (pr_with_occurrences (fun () -> str " *") (occs,()))
  | { onhyps=Some l; concl_occs=occs } ->
      let pr_occs = match occs with
      | NoOccurrences -> mt ()
      | _ -> pr_with_occurrences (fun () -> str" |- *") (occs,())
      in
      pr_in
        (prlist_with_sep (fun () -> str",") (pr_hyp_location pr_id) l ++ pr_occs)

let pr_orient b = if b then mt () else str "<- "

let pr_multi = function
  | Precisely 1 -> mt ()
  | Precisely n -> int n ++ str "!"
  | UpTo n -> int n ++ str "?"
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

let pr_lazy lz = if lz then str "lazy" else mt ()

let pr_match_pattern pr_pat = function
  | Term a -> pr_pat a
  | Subterm (b,None,a) ->
    (** ppedrot: we don't make difference between [appcontext] and [context]
        anymore, and the interpretation is governed by a flag instead. *)
    str "context [" ++ pr_pat a ++ str "]"
  | Subterm (b,Some id,a) ->
    str "context " ++ pr_id id ++ str "[" ++ pr_pat a ++ str "]"

let pr_match_hyps pr_pat = function
  | Hyp (nal,mp) ->
      pr_lname nal ++ str ":" ++ pr_match_pattern pr_pat mp
  | Def (nal,mv,mp) ->
      pr_lname nal ++ str ":=" ++ pr_match_pattern pr_pat mv
      ++ str ":" ++ pr_match_pattern pr_pat mp

let pr_match_rule m pr pr_pat = function
  | Pat ([],mp,t) when m ->
      pr_match_pattern pr_pat mp ++
      spc () ++ str "=>" ++ brk (1,4) ++ pr t
(*
  | Pat (rl,mp,t) ->
      hv 0 (prlist_with_sep pr_comma (pr_match_hyps pr_pat) rl ++
        (if rl <> [] then spc () else mt ()) ++
         hov 0 (str "|-" ++ spc () ++ pr_match_pattern pr_pat mp ++ spc () ++
	 str "=>" ++ brk (1,4) ++ pr t))
*)
  | Pat (rl,mp,t) ->
      hov 0 (
	hv 0 (prlist_with_sep pr_comma (pr_match_hyps pr_pat) rl) ++
        (if not (List.is_empty rl) then spc () else mt ()) ++
        hov 0 (
	  str "|-" ++ spc () ++ pr_match_pattern pr_pat mp ++ spc () ++
	  str "=>" ++ brk (1,4) ++ pr t))
  | All t -> str "_" ++ spc () ++ str "=>" ++ brk (1,4) ++ pr t

let pr_funvar = function
  | None -> spc () ++ str "_"
  | Some id -> spc () ++ pr_id id

let pr_let_clause k pr (id,(bl,t)) =
  hov 0 (str k ++ pr_lident id ++ prlist pr_funvar bl ++
         str " :=" ++ brk (1,1) ++ pr (TacArg (Loc.ghost,t)))

let pr_let_clauses recflag pr = function
  | hd::tl ->
      hv 0
        (pr_let_clause (if recflag then "let rec " else "let ") pr hd ++
         prlist (fun t -> spc () ++ pr_let_clause "with " pr t) tl)
  | [] -> anomaly (Pp.str "LetIn must declare at least one binding")

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
      hov 2 (str "using" ++ spc () ++ prlist_with_sep pr_comma prc l)

let string_of_debug = function
  | Off -> ""
  | Debug -> "debug "
  | Info -> "info_"

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

(** A printer for tactics that polymorphically works on the three
    "raw", "glob" and "typed" levels *)

let make_pr_tac pr_tac_level
  (pr_constr,pr_lconstr,pr_pat,pr_lpat,
   pr_cst,pr_ind,pr_ref,pr_ident,pr_extend,pr_alias,strip_prod_binders, pr_gen) =

(* some shortcuts *)
let pr_bindings = pr_bindings pr_lconstr pr_constr in
let pr_ex_bindings = pr_bindings_gen true pr_lconstr pr_constr in
let pr_with_bindings = pr_with_bindings pr_lconstr pr_constr in
let pr_extend = pr_extend pr_constr pr_lconstr pr_tac_level pr_pat in
let pr_alias = pr_alias pr_constr pr_lconstr pr_tac_level pr_pat in
let pr_red_expr = pr_red_expr (pr_constr,pr_lconstr,pr_cst,pr_pat) in

let pr_constrarg c = spc () ++ pr_constr c in
let pr_lconstrarg c = spc () ++ pr_lconstr c in
let pr_intarg n = spc () ++ int n in

(* Some printing combinators *)
let pr_eliminator cb = str "using" ++ pr_arg pr_with_bindings cb in

let extract_binders = function
  | Tacexp (TacFun (lvar,body)) -> (lvar,Tacexp body)
  | body -> ([],body) in

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
          match List.chop (n-1) nal with
              _, (_,Name id) :: _ -> id, (nal,ty)::bll
            | bef, (loc,Anonymous) :: aft ->
                let id = next_ident_away (Id.of_string"y") avoid in
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
  let annot = match names with
  | [_] -> mt ()
  | _ -> spc() ++ str"{struct " ++ pr_id idarg ++ str"}"
  in
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
  | TacIntroMove (None,MoveLast) -> str "intro"
  | TacAssumption -> str "assumption"
  | TacAnyConstructor (false,None) -> str "constructor"
  | TacAnyConstructor (true,None) -> str "econstructor"
  | TacTrivial (d,[],Some []) -> str (string_of_debug d ^ "trivial")
  | TacAuto (d,None,[],Some []) -> str (string_of_debug d ^ "auto")
  | TacReflexivity -> str "reflexivity"
  | TacClear (true,[]) -> str "clear"
  | t -> str "(" ++ pr_atom1 t ++ str ")"

  (* Main tactic printer *)
and pr_atom1 = function
  | TacExtend (loc,s,l) ->
      pr_with_comments loc (pr_extend 1 s l)
  | TacAlias (loc,kn,l) ->
      pr_with_comments loc (pr_alias 1 kn (List.map snd l))

  (* Basic tactics *)
  | TacIntroPattern [] as t -> pr_atom0 t
  | TacIntroPattern (_::_ as p) ->
      hov 1 (str "intros" ++ spc () ++
             prlist_with_sep spc Miscprint.pr_intro_pattern p)
  | TacIntrosUntil h ->
      hv 1 (str "intros until" ++ pr_arg pr_quantified_hypothesis h)
  | TacIntroMove (None,MoveLast) as t -> pr_atom0 t
  | TacIntroMove (Some id,MoveLast) -> str "intro " ++ pr_id id
  | TacIntroMove (ido,hto) ->
      hov 1 (str"intro" ++ pr_opt pr_id ido ++
             Miscprint.pr_move_location pr_ident hto)
  | TacAssumption as t -> pr_atom0 t
  | TacExact c -> hov 1 (str "exact" ++ pr_constrarg c)
  | TacExactNoCheck c -> hov 1 (str "exact_no_check" ++ pr_constrarg c)
  | TacVmCastNoCheck c -> hov 1 (str "vm_cast_no_check" ++ pr_constrarg c)
  | TacApply (a,ev,cb,inhyp) ->
      hov 1 ((if a then mt() else str "simple ") ++
             str (with_evars ev "apply") ++ spc () ++
             prlist_with_sep pr_comma pr_with_bindings cb ++
             pr_in_hyp_as pr_ident inhyp)
  | TacElim (ev,cb,cbo) ->
      hov 1 (str (with_evars ev "elim") ++ pr_arg pr_with_bindings cb ++
        pr_opt pr_eliminator cbo)
  | TacElimType c -> hov 1 (str "elimtype" ++ pr_constrarg c)
  | TacCase (ev,cb) ->
      hov 1 (str (with_evars ev "case") ++ spc () ++ pr_with_bindings cb)
  | TacCaseType c -> hov 1 (str "casetype" ++ pr_constrarg c)
  | TacFix (ido,n) -> hov 1 (str "fix" ++ pr_opt pr_id ido ++ pr_intarg n)
  | TacMutualFix (id,n,l) ->
      hov 1 (str "fix" ++ spc () ++ pr_id id ++ pr_intarg n ++ spc() ++
             str"with " ++ prlist_with_sep spc pr_fix_tac l)
  | TacCofix ido -> hov 1 (str "cofix" ++ pr_opt pr_id ido)
  | TacMutualCofix (id,l) ->
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
             prlist_with_sep pr_comma (fun (cl,na) ->
	       pr_with_occurrences pr_constr cl ++ pr_as_name na)
	     l)
  | TacGeneralizeDep c ->
      hov 1 (str "generalize" ++ spc () ++ str "dependent" ++
             pr_constrarg c)
  | TacLetTac (na,c,cl,true,_) when Locusops.is_nowhere cl ->
      hov 1 (str "pose" ++ pr_pose pr_lconstr pr_constr na c)
  | TacLetTac (na,c,cl,b,e) ->
      hov 1 ((if b then str "set" else str "remember") ++
             (if b then pr_pose pr_lconstr else pr_pose_as_style)
	        pr_constr na c ++
             pr_opt (fun p -> pr_eqn_ipat p ++ spc ()) e ++
             pr_clauses (Some b) pr_ident cl)
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
  | TacSimpleInductionDestruct (isrec,h) ->
      hov 1 (str "simple " ++ str (if isrec then "induction" else "destruct")
             ++ pr_arg pr_quantified_hypothesis h)
  | TacInductionDestruct (isrec,ev,(l,el,cl)) ->
      hov 1 (str (with_evars ev (if isrec then "induction" else "destruct")) ++
             spc () ++
             prlist_with_sep pr_comma (fun (h,ids) ->
	       pr_induction_arg pr_lconstr pr_constr h ++
	       pr_with_induction_names ids) l ++
             pr_opt pr_eliminator el ++
	     pr_opt_no_spc (pr_clauses None pr_ident) cl)
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
  | TacTrivial (_,[],Some []) as x -> pr_atom0 x
  | TacTrivial (d,lems,db) ->
      hov 0 (str (string_of_debug d ^ "trivial") ++
             pr_auto_using pr_constr lems ++ pr_hintbases db)
  | TacAuto (_,None,[],Some []) as x -> pr_atom0 x
  | TacAuto (d,n,lems,db) ->
      hov 0 (str (string_of_debug d ^ "auto") ++
	     pr_opt (pr_or_var int) n ++
             pr_auto_using pr_constr lems ++ pr_hintbases db)

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
        (str "move" ++ brk (1,1) ++ pr_ident id1 ++
	 Miscprint.pr_move_location pr_ident id2)
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
  | TacSplit (ev,false,l) -> hov 1 (str (with_evars ev "split") ++ prlist_with_sep pr_comma pr_bindings l)
  | TacSplit (ev,true,l) -> hov 1 (str (with_evars ev "exists") ++ prlist_with_sep (fun () -> str",") pr_ex_bindings l)
  | TacAnyConstructor (ev,Some t) ->
      hov 1 (str (with_evars ev "constructor") ++ pr_arg (pr_tac_level (latom,E)) t)
  | TacAnyConstructor (ev,None) as t -> pr_atom0 t
  | TacConstructor (ev,n,l) ->
      hov 1 (str (with_evars ev "constructor") ++
             pr_or_var pr_intarg n ++ pr_bindings l)

  (* Conversion *)
  | TacReduce (r,h) ->
      hov 1 (pr_red_expr r ++
             pr_clauses (Some true) pr_ident h)
  | TacChange (op,c,h) ->
      hov 1 (str "change" ++ brk (1,1) ++
      (match op with
          None -> mt()
        | Some p -> pr_pat p ++ spc () ++ str "with ") ++
      pr_constr c ++ pr_clauses (Some true) pr_ident h)

  (* Equivalence relations *)
  | TacReflexivity as x -> pr_atom0 x
  | TacSymmetry cls -> str "symmetry" ++ pr_clauses (Some true) pr_ident cls
  | TacTransitivity (Some c) -> str "transitivity" ++ pr_constrarg c
  | TacTransitivity None -> str "etransitivity"

  (* Equality and inversion *)
  | TacRewrite (ev,l,cl,by) ->
      hov 1 (str (with_evars ev "rewrite") ++ spc () ++
	     prlist_with_sep
	     (fun () -> str ","++spc())
	     (fun (b,m,c) ->
		pr_orient b ++ pr_multi m ++ pr_with_bindings c)
	     l
	     ++ pr_clauses (Some true) pr_ident cl
	     ++	(match by with Some by -> pr_by_tactic (pr_tac_level ltop) by | None -> mt()))
  | TacInversion (DepInversion (k,c,ids),hyp) ->
      hov 1 (str "dependent " ++ pr_induction_kind k ++ spc () ++
      pr_quantified_hypothesis hyp ++
      pr_with_inversion_names ids ++ pr_with_constr pr_constr c)
  | TacInversion (NonDepInversion (k,cl,ids),hyp) ->
      hov 1 (pr_induction_kind k ++ spc () ++
      pr_quantified_hypothesis hyp ++
      pr_with_inversion_names ids ++ pr_simple_hyp_clause pr_ident cl)
  | TacInversion (InversionUsing (c,cl),hyp) ->
      hov 1 (str "inversion" ++ spc() ++ pr_quantified_hypothesis hyp ++
      spc () ++ str "using" ++ spc () ++ pr_constr c ++
      pr_simple_hyp_clause pr_ident cl)

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
      let llc = List.map (fun (id,t) -> (id,extract_binders t)) llc in
      v 0
       (hv 0 (pr_let_clauses recflag (pr_tac ltop) llc ++ str " in") ++
       fnl () ++ pr_tac (llet,E) u),
      llet
  | TacMatch (lz,t,lrul) ->
      hov 0 (pr_lazy lz ++ str "match " ++ pr_tac ltop t ++ str " with"
        ++ prlist
	  (fun r -> fnl () ++ str "| " ++
            pr_match_rule true (pr_tac ltop) pr_lpat r)
	lrul
        ++ fnl() ++ str "end"),
      lmatch
  | TacMatchGoal (lz,lr,lrul) ->
      hov 0 (pr_lazy lz ++
	str (if lr then "match reverse goal with" else "match goal with")
	++ prlist
	  (fun r -> fnl () ++ str "| " ++
            pr_match_rule false (pr_tac ltop) pr_lpat r)
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
  | TacTimeout (n,t) ->
      hov 1 (str "timeout " ++ pr_or_var int n ++ spc () ++
             pr_tac (ltactical,E) t),
      ltactical
  | TacRepeat t ->
      hov 1 (str "repeat" ++ spc () ++ pr_tac (ltactical,E) t),
      ltactical
  | TacProgress t ->
      hov 1 (str "progress" ++ spc () ++ pr_tac (ltactical,E) t),
      ltactical
  | TacShowHyps t ->
      hov 1 (str "infoH" ++ spc () ++ spc () ++ pr_tac (ltactical,E) t),
      ltactical
  | TacInfo t ->
      hov 1 (str "info" ++ spc () ++ pr_tac (ltactical,E) t),
      linfo
  | TacOr (t1,t2) ->
      hov 1 (pr_tac (lorelse,L) t1 ++ str " +" ++ brk (1,1) ++
             pr_tac (lorelse,E) t2),
      lorelse
  | TacOnce t ->
      hov 1 (str "once" ++ spc () ++ pr_tac (ltactical,E) t),
      ltactical
  | TacExactlyOnce t ->
      hov 1 (str "exactly_once" ++ spc () ++ pr_tac (ltactical,E) t),
      ltactical
  | TacOrelse (t1,t2) ->
      hov 1 (pr_tac (lorelse,L) t1 ++ str " ||" ++ brk (1,1) ++
             pr_tac (lorelse,E) t2),
      lorelse
  | TacFail (n,l) ->
      let arg = match n with ArgArg 0 -> mt () | _ -> pr_arg (pr_or_var int) n in
      hov 1 (str "fail" ++ arg ++
      prlist (pr_arg (pr_message_token pr_ident)) l), latom
  | TacFirst tl ->
      str "first" ++ spc () ++ pr_seq_body (pr_tac ltop) tl, llet
  | TacSolve tl ->
      str "solve" ++ spc () ++ pr_seq_body (pr_tac ltop) tl, llet
  | TacComplete t ->
      pr_tac (lcomplete,E) t, lcomplete
  | TacId l ->
      str "idtac" ++ prlist (pr_arg (pr_message_token pr_ident)) l, latom
  | TacAtom (loc,TacAlias (_,kn,l)) ->
      pr_with_comments loc
        (pr_alias (level_of inherited) kn (List.map snd l)),
      latom
  | TacAtom (loc,t) ->
      pr_with_comments loc (hov 1 (pr_atom1 t)), ltatom
  | TacArg(_,Tacexp e) -> pr_tac_level (latom,E) e, latom
  | TacArg(_,ConstrMayEval (ConstrTerm c)) ->
      str "constr:" ++ pr_constr c, latom
  | TacArg(_,ConstrMayEval c) ->
      pr_may_eval pr_constr pr_lconstr pr_cst pr_pat c, leval
  | TacArg(_,TacFreshId l) -> str "fresh" ++ pr_fresh_ids l, latom
  | TacArg(_,TacGeneric arg) -> pr_gen arg, latom
  | TacArg(_,TacCall(loc,f,[])) -> pr_ref f, latom
  | TacArg(_,TacCall(loc,f,l)) ->
      pr_with_comments loc
        (hov 1 (pr_ref f ++ spc () ++
         prlist_with_sep spc pr_tacarg l)),
      lcall
  | TacArg (_,a) -> pr_tacarg a, latom
  in
  if prec_less prec inherited then strm
  else str"(" ++ strm ++ str")"

and pr_tacarg = function
  | TacDynamic (loc,t) ->
      pr_with_comments loc (str ("<dynamic ["^(Dyn.tag t)^"]>"))
  | MetaIdArg (loc,true,s) -> pr_with_comments loc (str ("$" ^ s))
  | MetaIdArg (loc,false,s) -> pr_with_comments loc (str ("constr: $" ^ s))
  | Reference r -> pr_ref r
  | ConstrMayEval c -> pr_may_eval pr_constr pr_lconstr pr_cst pr_pat c
  | TacFreshId l -> str "fresh" ++ pr_fresh_ids l
  | TacExternal (_,com,req,la) ->
      str "external" ++ spc() ++ qs com ++ spc() ++ qs req ++
      spc() ++ prlist_with_sep spc pr_tacarg la
  | (TacCall _|Tacexp _ | TacGeneric _) as a ->
      str "ltac:" ++ pr_tac (latom,E) (TacArg (Loc.ghost,a))

in pr_tac

let strip_prod_binders_glob_constr n (ty,_) =
  let rec strip_ty acc n ty =
    if Int.equal n 0 then (List.rev acc, (ty,None)) else
      match ty with
          Glob_term.GProd(loc,na,Explicit,a,b) ->
            strip_ty (([Loc.ghost,na],(a,None))::acc) (n-1) b
        | _ -> error "Cannot translate fix tactic: not enough products" in
  strip_ty [] n ty

let raw_printers =
    (pr_constr_expr,
     pr_lconstr_expr,
     pr_constr_pattern_expr,
     pr_lconstr_pattern_expr,
     pr_or_by_notation pr_reference,
     pr_or_by_notation pr_reference,
     pr_reference,
     pr_or_metaid pr_lident,
     pr_raw_extend,
     pr_raw_alias,
     strip_prod_binders_expr,
     Genprint.generic_raw_print)

let rec pr_raw_tactic_level n (t:raw_tactic_expr) =
  make_pr_tac pr_raw_tactic_level raw_printers n t

let pr_raw_tactic = pr_raw_tactic_level ltop

let pr_and_constr_expr pr (c,_) = pr c

let pr_pat_and_constr_expr pr ((c,_),_) = pr c

let pr_glob_tactic_level env =
  let glob_printers =
    (pr_and_constr_expr (pr_glob_constr_env env),
     pr_and_constr_expr (pr_lglob_constr_env env),
     pr_pat_and_constr_expr (pr_glob_constr_env env),
     pr_pat_and_constr_expr (pr_lglob_constr_env env),
     pr_or_var (pr_and_short_name (pr_evaluable_reference_env env)),
     pr_or_var (pr_inductive env),
     pr_ltac_or_var (pr_located pr_ltac_constant),
     pr_lident,
     pr_glob_extend,
     pr_glob_alias,
     strip_prod_binders_glob_constr,
     Genprint.generic_glb_print)
  in
  let rec prtac n (t:glob_tactic_expr) =
    make_pr_tac prtac glob_printers n t
  in
  prtac

let pr_glob_tactic env = pr_glob_tactic_level env ltop

(** Registering *)

let () =
  let pr_bool b = if b then str "true" else str "false" in
  let pr_unit _ = str "()" in
  let pr_string s = str "\"" ++ str s ++ str "\"" in
  Genprint.register_print0 Constrarg.wit_ref
    pr_reference (pr_or_var (pr_located pr_global)) pr_global;
  Genprint.register_print0
    Constrarg.wit_intro_pattern
    Miscprint.pr_intro_pattern
    Miscprint.pr_intro_pattern
    Miscprint.pr_intro_pattern;
  Genprint.register_print0
    Constrarg.wit_clause_dft_concl
    (pr_clauses (Some true) (pr_or_metaid pr_lident))
    (pr_clauses (Some true) pr_lident)
    (pr_clauses (Some true) (fun id -> pr_lident (Loc.ghost,id)))
  ;
  Genprint.register_print0 Constrarg.wit_sort
    pr_glob_sort pr_glob_sort pr_sort;
  Genprint.register_print0 Stdarg.wit_int int int int;
  Genprint.register_print0 Stdarg.wit_bool pr_bool pr_bool pr_bool;
  Genprint.register_print0 Stdarg.wit_unit pr_unit pr_unit pr_unit;
  Genprint.register_print0 Stdarg.wit_pre_ident str str str;
  Genprint.register_print0 Stdarg.wit_string pr_string pr_string pr_string

let () =
  let printer _ _ prtac = prtac (0, E) in
  declare_extra_genarg_pprule wit_tactic printer printer printer

let _ = Hook.set Tactic_debug.tactic_printer
  (fun x -> pr_glob_tactic (Global.env()) x)

let _ = Hook.set Tactic_debug.match_pattern_printer
  (fun env hyp -> pr_match_pattern (pr_constr_pattern_env env) hyp)

let _ = Hook.set Tactic_debug.match_rule_printer
  (fun rl ->
    pr_match_rule false (pr_glob_tactic (Global.env()))
      (fun (_,p) -> pr_constr_pattern p) rl)
