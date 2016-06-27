(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Names
open Namegen
open CErrors
open Util
open Constrexpr
open Tacexpr
open Genarg
open Geninterp
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

type 'a grammar_tactic_prod_item_expr =
| TacTerm of string
| TacNonTerm of Loc.t * 'a * Names.Id.t

type grammar_terminals = Genarg.ArgT.any Extend.user_symbol grammar_tactic_prod_item_expr list

type pp_tactic = {
  pptac_level : int;
  pptac_prods : grammar_terminals;
}

(* Tactic notations *)
let prnotation_tab = Summary.ref ~name:"pptactic-notation" KNmap.empty

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
    (tolerability -> Val.t -> std_ppcmds) ->
    'a -> std_ppcmds

let genarg_pprule = ref String.Map.empty

let declare_extra_genarg_pprule wit f g h =
  let s = match wit with
    | ExtraArg s -> ArgT.repr s
    | _ -> error
      "Can declare a pretty-printing rule only for extra argument types."
  in
  let f prc prlc prtac x = f prc prlc prtac (out_gen (rawwit wit) x) in
  let g prc prlc prtac x = g prc prlc prtac (out_gen (glbwit wit) x) in
  let h prc prlc prtac x = h prc prlc prtac (out_gen (topwit wit) x) in
  genarg_pprule := String.Map.add s (f,g,h) !genarg_pprule

module Make
  (Ppconstr : Ppconstrsig.Pp)
  (Taggers : sig
      val tag_keyword
        : std_ppcmds -> std_ppcmds
      val tag_primitive
        : std_ppcmds -> std_ppcmds
      val tag_string
        : std_ppcmds -> std_ppcmds
      val tag_glob_tactic_expr
        : glob_tactic_expr -> std_ppcmds -> std_ppcmds
      val tag_glob_atomic_tactic_expr
        : glob_atomic_tactic_expr -> std_ppcmds -> std_ppcmds
      val tag_raw_tactic_expr
        : raw_tactic_expr -> std_ppcmds -> std_ppcmds
      val tag_raw_atomic_tactic_expr
        : raw_atomic_tactic_expr -> std_ppcmds -> std_ppcmds
      val tag_atomic_tactic_expr
        : atomic_tactic_expr -> std_ppcmds -> std_ppcmds
  end)
= struct

  open Taggers

  let keyword x = tag_keyword (str x)
  let primitive x = tag_primitive (str x)

  let has_type (Val.Dyn (tag, x)) t = match Val.eq tag t with
  | None -> false
  | Some _ -> true

  let unbox : type a. Val.t -> a Val.typ -> a= fun (Val.Dyn (tag, x)) t ->
  match Val.eq tag t with
  | None -> assert false
  | Some Refl -> x

  let rec pr_value lev v : std_ppcmds =
    if has_type v Val.typ_list then
      pr_sequence (fun x -> pr_value lev x) (unbox v Val.typ_list)
    else if has_type v Val.typ_opt then
      pr_opt_no_spc (fun x -> pr_value lev x) (unbox v Val.typ_opt)
    else if has_type v Val.typ_pair then
      let (v1, v2) = unbox v Val.typ_pair in
      str "(" ++ pr_value lev v1 ++ str ", " ++ pr_value lev v2 ++ str ")"
    else
      let Val.Dyn (tag, x) = v in
      let name = Val.repr tag in
      let default = str "<" ++ str name ++ str ">" in
      match ArgT.name name with
      | None -> default
      | Some (ArgT.Any arg) ->
        let wit = ExtraArg arg in
        match val_tag (Topwit wit) with
        | Val.Base t ->
          begin match Val.eq t tag with
          | None -> default
          | Some Refl -> Genprint.generic_top_print (in_gen (Topwit wit) x)
          end
        | _ -> default

  let pr_with_occurrences pr (occs,c) =
    match occs with
      | AllOccurrences ->
        pr c
      | NoOccurrences ->
        failwith "pr_with_occurrences: no occurrences"
      | OnlyOccurrences nl ->
        hov 1 (pr c ++ spc () ++ keyword "at" ++ spc () ++
                 hov 0 (prlist_with_sep spc (pr_or_var int) nl))
      | AllOccurrencesBut nl ->
        hov 1 (pr c ++ spc () ++ keyword "at" ++ str" - " ++
                 hov 0 (prlist_with_sep spc (pr_or_var int) nl))

  exception ComplexRedFlag

  let pr_short_red_flag pr r =
    if not r.rBeta ||  not r.rIota ||  not r.rZeta then raise ComplexRedFlag
    else if List.is_empty r.rConst then
      if r.rDelta then mt () else raise ComplexRedFlag
    else (if r.rDelta then str "-" else mt ()) ++
	   hov 0 (str "[" ++ prlist_with_sep spc pr r.rConst ++ str "]")

  let pr_red_flag pr r =
    try pr_short_red_flag pr r
    with complexRedFlags ->
      (if r.rBeta then pr_arg str "beta" else mt ()) ++
	(if r.rIota then pr_arg str "iota" else mt ()) ++
	(if r.rZeta then pr_arg str "zeta" else mt ()) ++
	(if List.is_empty r.rConst then
	   if r.rDelta then pr_arg str "delta"
	   else mt ()
	 else
	   pr_arg str "delta " ++ (if r.rDelta then str "-" else mt ()) ++
	     hov 0 (str "[" ++ prlist_with_sep spc pr r.rConst ++ str "]"))

  let pr_union pr1 pr2 = function
    | Inl a -> pr1 a
    | Inr b -> pr2 b

  let pr_red_expr (pr_constr,pr_lconstr,pr_ref,pr_pattern) = function
    | Red false -> keyword "red"
    | Hnf -> keyword "hnf"
    | Simpl (f,o) -> keyword "simpl" ++ (pr_short_red_flag pr_ref f)
		     ++ pr_opt (pr_with_occurrences (pr_union pr_ref pr_pattern)) o
    | Cbv f ->
      if f.rBeta && f.rIota && f.rZeta && f.rDelta && List.is_empty f.rConst then
        keyword "compute"
      else
        hov 1 (keyword "cbv" ++ pr_red_flag pr_ref f)
    | Lazy f ->
      hov 1 (keyword "lazy" ++ pr_red_flag pr_ref f)
    | Cbn f ->
      hov 1 (keyword "cbn" ++ pr_red_flag pr_ref f)
    | Unfold l ->
      hov 1 (keyword "unfold" ++ spc() ++
               prlist_with_sep pr_comma (pr_with_occurrences pr_ref) l)
    | Fold l -> hov 1 (keyword "fold" ++ prlist (pr_arg pr_constr) l)
    | Pattern l ->
      hov 1 (keyword "pattern" ++
               pr_arg (prlist_with_sep pr_comma (pr_with_occurrences pr_constr)) l)

    | Red true ->
      error "Shouldn't be accessible from user."
    | ExtraRedExpr s ->
      str s
    | CbvVm o ->
      keyword "vm_compute" ++ pr_opt (pr_with_occurrences (pr_union pr_ref pr_pattern)) o
    | CbvNative o ->
      keyword "native_compute" ++ pr_opt (pr_with_occurrences (pr_union pr_ref pr_pattern)) o

  let pr_may_eval test prc prlc pr2 pr3 = function
    | ConstrEval (r,c) ->
      hov 0
        (keyword "eval" ++ brk (1,1) ++
           pr_red_expr (prc,prlc,pr2,pr3) r ++ spc () ++
           keyword "in" ++ spc() ++ prc c)
    | ConstrContext ((_,id),c) ->
      hov 0
        (keyword "context" ++ spc () ++ pr_id id ++ spc () ++
           str "[" ++ prlc c ++ str "]")
    | ConstrTypeOf c ->
      hov 1 (keyword "type of" ++ spc() ++ prc c)
    | ConstrTerm c when test c ->
      h 0 (str "(" ++ prc c ++ str ")")
    | ConstrTerm c ->
      prc c

  let pr_may_eval a =
    pr_may_eval (fun _ -> false) a

  let pr_arg pr x = spc () ++ pr x

  let pr_or_var pr = function
    | ArgArg x -> pr x
    | ArgVar (_,s) -> pr_id s

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
      brk (1,1) ++ keyword "with" ++ brk (1,1) ++
        hv 0 (prlist_with_sep spc prc l)
    | ExplicitBindings l ->
      brk (1,1) ++ keyword "with" ++ brk (1,1) ++
        hv 0 (prlist_with_sep spc (fun b -> str"(" ++ pr_binding prlc b ++ str")") l)
    | NoBindings -> mt ()

  let pr_bindings_no_with prc prlc = function
    | ImplicitBindings l ->
      brk (0,1) ++
        prlist_with_sep spc prc l
    | ExplicitBindings l ->
      brk (0,1) ++
        prlist_with_sep spc (fun b -> str"(" ++ pr_binding prlc b ++ str")") l
    | NoBindings -> mt ()

  let pr_clear_flag clear_flag pp x =
    match clear_flag with
    | Some false -> surround (pp x)
    | Some true -> str ">" ++ pp x
    | None -> pp x

  let pr_with_bindings prc prlc (c,bl) =
    prc c ++ pr_bindings prc prlc bl

  let pr_with_bindings_arg prc prlc (clear_flag,c) =
    pr_clear_flag clear_flag (pr_with_bindings prc prlc) c

  let pr_with_constr prc = function
    | None -> mt ()
    | Some c -> spc () ++ hov 1 (keyword "with" ++ spc () ++ prc c)

  let pr_message_token prid = function
    | MsgString s -> tag_string (qs s)
    | MsgInt n -> int n
    | MsgIdent id -> prid id

  let pr_fresh_ids =
    prlist (fun s -> spc() ++ pr_or_var (fun s -> tag_string (qs s)) s)

  let with_evars ev s = if ev then "e" ^ s else s

  let hov_if_not_empty n p = if Pp.ismt p then p else hov n p

  let rec pr_raw_generic_rec prc prlc prtac prpat prref (GenArg (Rawwit wit, x)) =
    match wit with
      | ListArg wit ->
        let map x = pr_raw_generic_rec prc prlc prtac prpat prref (in_gen (rawwit wit) x) in
        let ans = pr_sequence map x in
        hov_if_not_empty 0 ans
      | OptArg wit ->
        let ans = match x with
          | None -> mt ()
          | Some x -> pr_raw_generic_rec prc prlc prtac prpat prref (in_gen (rawwit wit) x)
        in
        hov_if_not_empty 0 ans
      | PairArg (wit1, wit2) ->
        let p, q = x in
        let p = in_gen (rawwit wit1) p in
        let q = in_gen (rawwit wit2) q in
        hov_if_not_empty 0 (pr_sequence (pr_raw_generic_rec prc prlc prtac prpat prref) [p; q])
      | ExtraArg s ->
        try pi1 (String.Map.find (ArgT.repr s) !genarg_pprule) prc prlc prtac (in_gen (rawwit wit) x)
        with Not_found -> Genprint.generic_raw_print (in_gen (rawwit wit) x)


  let rec pr_glb_generic_rec prc prlc prtac prpat (GenArg (Glbwit wit, x)) =
    match wit with
      | ListArg wit ->
        let map x = pr_glb_generic_rec prc prlc prtac prpat (in_gen (glbwit wit) x) in
        let ans = pr_sequence map x in
        hov_if_not_empty 0 ans
      | OptArg wit ->
        let ans = match x with
          | None -> mt ()
          | Some x -> pr_glb_generic_rec prc prlc prtac prpat (in_gen (glbwit wit) x)
        in
        hov_if_not_empty 0 ans
      | PairArg (wit1, wit2) ->
        let p, q = x in
        let p = in_gen (glbwit wit1) p in
        let q = in_gen (glbwit wit2) q in
        let ans = pr_sequence (pr_glb_generic_rec prc prlc prtac prpat) [p; q] in
        hov_if_not_empty 0 ans
      | ExtraArg s ->
        try pi2 (String.Map.find (ArgT.repr s) !genarg_pprule) prc prlc prtac (in_gen (glbwit wit) x)
        with Not_found -> Genprint.generic_glb_print (in_gen (glbwit wit) x)

  let rec tacarg_using_rule_token pr_gen = function
    | [] -> []
    | TacTerm s :: l -> keyword s :: tacarg_using_rule_token pr_gen l
    | TacNonTerm (_, (symb, arg), _) :: l  ->
      pr_gen symb arg :: tacarg_using_rule_token pr_gen l

  let pr_tacarg_using_rule pr_gen l =
    let l = match l with
    | TacTerm s :: l ->
      (** First terminal token should be considered as the name of the tactic,
          so we tag it differently than the other terminal tokens. *)
      primitive s :: tacarg_using_rule_token pr_gen l
    | _ -> tacarg_using_rule_token pr_gen l
    in
    pr_sequence (fun x -> x) l

  let pr_extend_gen pr_gen lev { mltac_name = s; mltac_index = i } l =
      let name =
        str s.mltac_plugin ++ str "::" ++ str s.mltac_tactic ++
        str "@" ++ int i
      in
      let args = match l with
        | [] -> mt ()
        | _ -> spc() ++ pr_sequence pr_gen l
      in
      str "<" ++ name ++ str ">" ++ args

  let pr_alias_key key =
    try
      let prods = (KNmap.find key !prnotation_tab).pptac_prods in
      (* First printing strategy: only the head symbol *)
      match prods with
      | TacTerm s :: prods -> str s
      | _ ->
      (* Second printing strategy; if ever Tactic Notation is eventually *)
      (* accepting notations not starting with an identifier *)
      let rec pr = function
      | [] -> []
      | TacTerm s :: prods -> s :: pr prods
      | TacNonTerm (_,_,id) :: prods -> ".." :: pr prods in
      str (String.concat " " (pr prods))
    with Not_found ->
      KerName.print key

  let pr_alias_gen pr_gen lev key l =
    try
      let pp = KNmap.find key !prnotation_tab in
      let rec pack prods args = match prods, args with
      | [], [] -> []
      | TacTerm s :: prods, args -> TacTerm s :: pack prods args
      | TacNonTerm (loc, symb, id) :: prods, arg :: args ->
        TacNonTerm (loc, (symb, arg), id) :: pack prods args
      | _ -> raise Not_found
      in
      let prods = pack pp.pptac_prods l in
      let p = pr_tacarg_using_rule pr_gen prods in
      if pp.pptac_level > lev then surround p else p
    with Not_found ->
      let pr arg = str "_" in
      KerName.print key ++ spc() ++ pr_sequence pr l ++ str" (* Generic printer *)"

  let pr_farg prtac arg = prtac (1, Any) (TacArg (Loc.ghost, arg))

  let is_genarg tag wit =
    let ArgT.Any tag = tag in
    argument_type_eq (ArgumentType (ExtraArg tag)) wit

  let get_list : type l. l generic_argument -> l generic_argument list option =
  function (GenArg (wit, arg)) -> match wit with
  | Rawwit (ListArg wit) -> Some (List.map (in_gen (rawwit wit)) arg)
  | Glbwit (ListArg wit) -> Some (List.map (in_gen (glbwit wit)) arg)
  | _ -> None

  let get_opt : type l. l generic_argument -> l generic_argument option option =
  function (GenArg (wit, arg)) -> match wit with
  | Rawwit (OptArg wit) -> Some (Option.map (in_gen (rawwit wit)) arg)
  | Glbwit (OptArg wit) -> Some (Option.map (in_gen (glbwit wit)) arg)
  | _ -> None

  let rec pr_any_arg : type l. (_ -> l generic_argument -> std_ppcmds) -> _ -> l generic_argument -> std_ppcmds =
  fun prtac symb arg -> match symb with
  | Extend.Uentry tag when is_genarg tag (genarg_tag arg) -> prtac (1, Any) arg
  | Extend.Ulist1 s | Extend.Ulist0 s ->
    begin match get_list arg with
    | None -> str "ltac:(" ++ prtac (1, Any) arg ++ str ")"
    | Some l -> pr_sequence (pr_any_arg prtac s) l
    end
  | Extend.Ulist1sep (s, sep) | Extend.Ulist0sep (s, sep) ->
    begin match get_list arg with
    | None -> str "ltac:(" ++ prtac (1, Any) arg ++ str ")"
    | Some l -> prlist_with_sep (fun () -> str sep) (pr_any_arg prtac s) l
    end
  | Extend.Uopt s ->
    begin match get_opt arg with
    | None -> str "ltac:(" ++ prtac (1, Any) arg ++ str ")"
    | Some l -> pr_opt (pr_any_arg prtac s) l
    end
  | Extend.Uentry _ | Extend.Uentryl _ ->
    str "ltac:(" ++ prtac (1, Any) arg ++ str ")"

  let rec pr_targ prtac symb arg = match symb with
  | Extend.Uentry tag when is_genarg tag (ArgumentType wit_tactic) ->
    prtac (1, Any) arg
  | Extend.Uentryl (_, l) -> prtac (l, Any) arg
  | _ ->
    match arg with
    | TacGeneric arg ->
      let pr l arg = prtac l (TacGeneric arg) in
      pr_any_arg pr symb arg
    | _ -> str "ltac:(" ++ prtac (1, Any) arg ++ str ")"

  let pr_raw_extend_rec prc prlc prtac prpat =
    pr_extend_gen (pr_farg prtac)
  let pr_glob_extend_rec prc prlc prtac prpat =
    pr_extend_gen (pr_farg prtac)

  let pr_raw_alias prc prlc prtac prpat lev key args =
    pr_alias_gen (pr_targ (fun l a -> prtac l (TacArg (Loc.ghost, a)))) lev key args
  let pr_glob_alias prc prlc prtac prpat lev key args =
    pr_alias_gen (pr_targ (fun l a -> prtac l (TacArg (Loc.ghost, a)))) lev key args

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
    if !Flags.in_debugger then pr_kn kn
    else try
           pr_qualid (Nametab.shortest_qualid_of_tactic kn)
      with Not_found -> (* local tactic not accessible anymore *)
        str "<" ++ pr_kn kn ++ str ">"

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

  let pr_bindings_gen for_ex prc prlc = function
    | ImplicitBindings l ->
      spc () ++
        hv 2 ((if for_ex then mt() else keyword "with" ++ spc ()) ++
                 prlist_with_sep spc prc l)
    | ExplicitBindings l ->
      spc () ++
        hv 2 ((if for_ex then mt() else keyword "with" ++ spc ()) ++
                 pr_esubst prlc l)
    | NoBindings -> mt ()

  let pr_bindings prc prlc = pr_bindings_gen false prc prlc

  let pr_with_bindings prc prlc (c,bl) =
    hov 1 (prc c ++ pr_bindings prc prlc bl)

  let pr_as_disjunctive_ipat prc ipatl =
    keyword "as" ++ spc () ++
      pr_or_var (fun (loc,p) -> Miscprint.pr_or_and_intro_pattern prc p) ipatl

  let pr_eqn_ipat (_,ipat) = keyword "eqn:" ++ Miscprint.pr_intro_pattern_naming ipat

  let pr_with_induction_names prc = function
    | None, None -> mt ()
    | Some eqpat, None -> hov 1 (pr_eqn_ipat eqpat)
    | None, Some ipat -> hov 1 (pr_as_disjunctive_ipat prc ipat)
    | Some eqpat, Some ipat ->
        hov 1 (pr_as_disjunctive_ipat prc ipat ++ spc () ++ pr_eqn_ipat eqpat)

  let pr_as_intro_pattern prc ipat =
    spc () ++ hov 1 (keyword "as" ++ spc () ++ Miscprint.pr_intro_pattern prc ipat)

  let pr_with_inversion_names prc = function
    | None -> mt ()
    | Some ipat -> pr_as_disjunctive_ipat prc ipat

  let pr_as_ipat prc = function
    | None -> mt ()
    | Some ipat -> pr_as_intro_pattern prc ipat

  let pr_as_name = function
    | Anonymous -> mt ()
    | Name id -> spc () ++ keyword "as" ++ spc () ++ pr_lident (Loc.ghost,id)

  let pr_pose_as_style prc na c =
    spc() ++ prc c ++ pr_as_name na

  let pr_pose prc prlc na c = match na with
    | Anonymous -> spc() ++ prc c
    | Name id -> spc() ++ surround (pr_id id ++ str " :=" ++ spc() ++ prlc c)

  let pr_assertion prc prdc _prlc ipat c = match ipat with
    (* Use this "optimisation" or use only the general case ?
       | IntroIdentifier id ->
       spc() ++ surround (pr_intro_pattern ipat ++ str " :" ++ spc() ++ prlc c)
    *)
    | ipat ->
      spc() ++ prc c ++ pr_as_ipat prdc ipat

  let pr_assumption prc prdc prlc ipat c = match ipat with
    (* Use this "optimisation" or use only the general case ?*)
    (* it seems that this "optimisation" is somehow more natural *)
    | Some (_,IntroNaming (IntroIdentifier id)) ->
      spc() ++ surround (pr_id id ++ str " :" ++ spc() ++ prlc c)
    | ipat ->
      spc() ++ prc c ++ pr_as_ipat prdc ipat

  let pr_by_tactic prt = function
    | Some tac -> keyword "by" ++ spc () ++ prt tac
    | None -> mt()

  let pr_hyp_location pr_id = function
    | occs, InHyp -> spc () ++ pr_with_occurrences pr_id occs
    | occs, InHypTypeOnly ->
      spc () ++ pr_with_occurrences (fun id ->
        str "(" ++ keyword "type of" ++ spc () ++ pr_id id ++ str ")"
      ) occs
    | occs, InHypValueOnly ->
      spc () ++ pr_with_occurrences (fun id ->
        str "(" ++ keyword "value of" ++ spc () ++ pr_id id ++ str ")"
      ) occs

  let pr_in pp = hov 0 (keyword "in" ++ pp)

  let pr_simple_hyp_clause pr_id = function
    | [] -> mt ()
    | l -> pr_in (spc () ++ prlist_with_sep spc pr_id l)

  let pr_in_hyp_as prc pr_id = function
    | None -> mt ()
    | Some (id,ipat) -> pr_in (spc () ++ pr_id id) ++ pr_as_ipat prc ipat

  let pr_clauses default_is_concl pr_id = function
    | { onhyps=Some []; concl_occs=occs }
        when (match default_is_concl with Some true -> true | _ -> false) ->
      pr_with_occurrences mt (occs,())
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

  let pr_core_destruction_arg prc prlc = function
    | ElimOnConstr c -> pr_with_bindings prc prlc c
    | ElimOnIdent (loc,id) -> pr_with_comments loc (pr_id id)
    | ElimOnAnonHyp n -> int n

  let pr_destruction_arg prc prlc (clear_flag,h) =
    pr_clear_flag clear_flag (pr_core_destruction_arg prc prlc) h
                               
  let pr_inversion_kind = function
    | SimpleInversion -> primitive "simple inversion"
    | FullInversion -> primitive "inversion"
    | FullInversionClear -> primitive "inversion_clear"

  let pr_range_selector (i, j) =
    if Int.equal i j then int i
    else int i ++ str "-" ++ int j

  let pr_goal_selector = function
    | SelectNth i -> int i ++ str ":"
    | SelectList l -> str "[" ++ prlist_with_sep (fun () -> str ", ") pr_range_selector l ++
        str "]" ++ str ":"
    | SelectId id -> str "[" ++ Nameops.pr_id id ++ str "]" ++ str ":"
    | SelectAll -> str "all" ++ str ":"

  let pr_lazy = function
    | General -> keyword "multi"
    | Select -> keyword "lazy"
    | Once -> mt ()

  let pr_match_pattern pr_pat = function
    | Term a -> pr_pat a
    | Subterm (b,None,a) ->
    (** ppedrot: we don't make difference between [appcontext] and [context]
        anymore, and the interpretation is governed by a flag instead. *)
      keyword "context" ++ str" [" ++ pr_pat a ++ str "]"
    | Subterm (b,Some id,a) ->
      keyword "context" ++ spc () ++ pr_id id ++ str "[" ++ pr_pat a ++ str "]"

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
    hov 0 (keyword k ++ spc () ++ pr_lident id ++ prlist pr_funvar bl ++
             str " :=" ++ brk (1,1) ++ pr (TacArg (Loc.ghost,t)))

  let pr_let_clauses recflag pr = function
    | hd::tl ->
      hv 0
        (pr_let_clause (if recflag then "let rec" else "let") pr hd ++
           prlist (fun t -> spc () ++ pr_let_clause "with" pr t) tl)
    | [] -> anomaly (Pp.str "LetIn must declare at least one binding")

  let pr_seq_body pr tl =
    hv 0 (str "[ " ++
            prlist_with_sep (fun () -> spc () ++ str "| ") pr tl ++
            str " ]")

  let pr_dispatch pr tl =
    hv 0 (str "[>" ++
            prlist_with_sep (fun () -> spc () ++ str "| ") pr tl ++
            str " ]")

  let pr_opt_tactic pr = function
    | TacId [] -> mt ()
    | t -> pr t

  let pr_tac_extend_gen pr tf tm tl =
    prvect_with_sep mt (fun t -> pr t ++ spc () ++ str "| ") tf ++
      pr_opt_tactic pr tm ++ str ".." ++
      prvect_with_sep mt (fun t -> spc () ++ str "| " ++ pr t) tl

  let pr_then_gen pr tf tm tl =
    hv 0 (str "[ " ++
            pr_tac_extend_gen pr tf tm tl ++
            str " ]")

  let pr_tac_extend pr tf tm tl =
    hv 0 (str "[>" ++
            pr_tac_extend_gen pr tf tm tl ++
            str " ]")

  let pr_hintbases = function
    | None -> keyword "with" ++ str" *"
    | Some [] -> mt ()
    | Some l -> hov 2 (keyword "with" ++ prlist (fun s -> spc () ++ str s) l)

  let pr_auto_using prc = function
    | [] -> mt ()
    | l -> hov 2 (keyword "using" ++ spc () ++ prlist_with_sep pr_comma prc l)

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

  type 'a printer = {
    pr_tactic    : tolerability -> 'tacexpr -> std_ppcmds;
    pr_constr    : 'trm -> std_ppcmds;
    pr_lconstr   : 'trm -> std_ppcmds;
    pr_dconstr   : 'dtrm -> std_ppcmds;
    pr_pattern   : 'pat -> std_ppcmds;
    pr_lpattern  : 'pat -> std_ppcmds;
    pr_constant  : 'cst -> std_ppcmds;
    pr_reference : 'ref -> std_ppcmds;
    pr_name      : 'nam -> std_ppcmds;
    pr_generic   : 'lev generic_argument -> std_ppcmds;
    pr_extend    : int -> ml_tactic_entry -> 'a gen_tactic_arg list -> std_ppcmds;
    pr_alias     : int -> KerName.t -> 'a gen_tactic_arg list -> std_ppcmds;
  }

  constraint 'a = <
      term      :'trm;
      dterm     :'dtrm;
      pattern   :'pat;
      constant  :'cst;
      reference :'ref;
      name      :'nam;
      tacexpr   :'tacexpr;
      level     :'lev
    >

    let pr_atom pr strip_prod_binders tag_atom =
      let pr_with_bindings = pr_with_bindings pr.pr_constr pr.pr_lconstr in
      let pr_with_bindings_arg_full = pr_with_bindings_arg in
      let pr_with_bindings_arg = pr_with_bindings_arg pr.pr_constr pr.pr_lconstr in
      let pr_red_expr = pr_red_expr (pr.pr_constr,pr.pr_lconstr,pr.pr_constant,pr.pr_pattern) in

      let pr_constrarg c = spc () ++ pr.pr_constr c in
      let pr_lconstrarg c = spc () ++ pr.pr_lconstr c in
      let pr_intarg n = spc () ++ int n in

      (* Some printing combinators *)
      let pr_eliminator cb = keyword "using" ++ pr_arg pr_with_bindings cb in

      let pr_binder_fix (nal,t) =
        (*  match t with
            | CHole _ -> spc() ++ prlist_with_sep spc (pr_lname) nal
            | _ ->*)
        let s = prlist_with_sep spc pr_lname nal ++ str ":" ++ pr.pr_lconstr t in
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
          | [_] ->
            mt ()
          | _ ->
            spc() ++ str"{"
            ++ keyword "struct" ++ spc ()
            ++ pr_id idarg ++ str"}"
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
      let rec pr_atom0 a = tag_atom a (match a with
        | TacIntroPattern (false,[]) -> primitive "intros"
        | TacIntroPattern (true,[]) -> primitive "eintros"
        | t -> str "(" ++ pr_atom1 t ++ str ")"
      )

      (* Main tactic printer *)
      and pr_atom1 a = tag_atom a (match a with
        (* Basic tactics *)
        | TacIntroPattern (ev,[]) as t ->
          pr_atom0 t
        | TacIntroPattern (ev,(_::_ as p)) ->
           hov 1 (primitive (if ev then "eintros" else "intros") ++ spc () ++
                    prlist_with_sep spc (Miscprint.pr_intro_pattern pr.pr_dconstr) p)
        | TacApply (a,ev,cb,inhyp) ->
          hov 1 (
            (if a then mt() else primitive "simple ") ++
              primitive (with_evars ev "apply") ++ spc () ++
              prlist_with_sep pr_comma pr_with_bindings_arg cb ++
              pr_non_empty_arg (pr_in_hyp_as pr.pr_dconstr pr.pr_name) inhyp
          )
        | TacElim (ev,cb,cbo) ->
          hov 1 (
            primitive (with_evars ev "elim")
            ++ pr_arg pr_with_bindings_arg cb
            ++ pr_opt pr_eliminator cbo)
        | TacCase (ev,cb) ->
          hov 1 (primitive (with_evars ev "case") ++ spc () ++ pr_with_bindings_arg cb)
        | TacMutualFix (id,n,l) ->
          hov 1 (
            primitive "fix" ++ spc () ++ pr_id id ++ pr_intarg n ++ spc()
            ++ keyword "with" ++ spc () ++ prlist_with_sep spc pr_fix_tac l)
        | TacMutualCofix (id,l) ->
          hov 1 (
            primitive "cofix" ++ spc () ++ pr_id id ++ spc()
            ++ keyword "with" ++ spc () ++ prlist_with_sep spc pr_cofix_tac l
          )
        | TacAssert (b,Some tac,ipat,c) ->
          hov 1 (
            primitive (if b then "assert" else "enough") ++
              pr_assumption pr.pr_constr pr.pr_dconstr pr.pr_lconstr ipat c ++
              pr_non_empty_arg (pr_by_tactic (pr.pr_tactic (ltactical,E))) tac
          )
        | TacAssert (_,None,ipat,c) ->
          hov 1 (
            primitive "pose proof"
            ++ pr_assertion pr.pr_constr pr.pr_dconstr pr.pr_lconstr ipat c
          )
        | TacGeneralize l ->
          hov 1 (
            primitive "generalize" ++ spc ()
            ++ prlist_with_sep pr_comma (fun (cl,na) ->
              pr_with_occurrences pr.pr_constr cl ++ pr_as_name na)
              l
          )
        | TacLetTac (na,c,cl,true,_) when Locusops.is_nowhere cl ->
          hov 1 (primitive "pose" ++ pr_pose pr.pr_constr pr.pr_lconstr na c)
        | TacLetTac (na,c,cl,b,e) ->
          hov 1 (
            (if b then primitive "set" else primitive "remember") ++
              (if b then pr_pose pr.pr_constr pr.pr_lconstr na c
                else pr_pose_as_style pr.pr_constr na c) ++
              pr_opt (fun p -> pr_eqn_ipat p ++ spc ()) e ++
              pr_non_empty_arg (pr_clauses (Some b) pr.pr_name) cl)
        (*  | TacInstantiate (n,c,ConclLocation ()) ->
            hov 1 (str "instantiate" ++ spc() ++
            hov 1 (str"(" ++ pr_arg int n ++ str" :=" ++
            pr_lconstrarg c ++ str ")" ))
            | TacInstantiate (n,c,HypLocation (id,hloc)) ->
            hov 1 (str "instantiate" ++ spc() ++
            hov 1 (str"(" ++ pr_arg int n ++ str" :=" ++
            pr_lconstrarg c ++ str ")" )
            ++ str "in" ++ pr_hyp_location pr.pr_name (id,[],(hloc,ref None)))
        *)

        (* Derived basic tactics *)
        | TacInductionDestruct (isrec,ev,(l,el)) ->
          hov 1 (
            primitive (with_evars ev (if isrec then "induction" else "destruct"))
            ++ spc ()
            ++ prlist_with_sep pr_comma (fun (h,ids,cl) ->
              pr_destruction_arg pr.pr_dconstr pr.pr_dconstr h ++
                pr_non_empty_arg (pr_with_induction_names pr.pr_dconstr) ids ++
                pr_opt (pr_clauses None pr.pr_name) cl) l ++
              pr_opt pr_eliminator el
          )

        (* Conversion *)
        | TacReduce (r,h) ->
          hov 1 (
            pr_red_expr r
            ++ pr_non_empty_arg (pr_clauses (Some true) pr.pr_name) h
          )
        | TacChange (op,c,h) ->
          hov 1 (
            primitive "change" ++ brk (1,1)
            ++ (
              match op with
                  None ->
                    mt ()
                | Some p ->
                  pr.pr_pattern p ++ spc ()
                  ++ keyword "with" ++ spc ()
            ) ++ pr.pr_dconstr c ++ pr_non_empty_arg (pr_clauses (Some true) pr.pr_name) h
          )

        (* Equality and inversion *)
        | TacRewrite (ev,l,cl,tac) ->
          hov 1 (
            primitive (with_evars ev "rewrite") ++ spc ()
            ++ prlist_with_sep
              (fun () -> str ","++spc())
              (fun (b,m,c) ->
                pr_orient b ++ pr_multi m ++
                  pr_with_bindings_arg_full pr.pr_dconstr pr.pr_dconstr c)
              l
            ++ pr_non_empty_arg (pr_clauses (Some true) pr.pr_name) cl
            ++ pr_non_empty_arg (pr_by_tactic (pr.pr_tactic (ltactical,E))) tac
          )
        | TacInversion (DepInversion (k,c,ids),hyp) ->
          hov 1 (
            primitive "dependent " ++ pr_inversion_kind k ++ spc ()
            ++ pr_quantified_hypothesis hyp
            ++ pr_with_inversion_names pr.pr_dconstr ids
            ++ pr_with_constr pr.pr_constr c
          )
        | TacInversion (NonDepInversion (k,cl,ids),hyp) ->
          hov 1 (
            pr_inversion_kind k ++ spc ()
            ++ pr_quantified_hypothesis hyp
            ++ pr_non_empty_arg (pr_with_inversion_names pr.pr_dconstr) ids
            ++ pr_non_empty_arg (pr_simple_hyp_clause pr.pr_name) cl
          )
        | TacInversion (InversionUsing (c,cl),hyp) ->
          hov 1 (
            primitive "inversion" ++ spc()
            ++ pr_quantified_hypothesis hyp ++ spc ()
            ++ keyword "using" ++ spc () ++ pr.pr_constr c
            ++ pr_non_empty_arg (pr_simple_hyp_clause pr.pr_name) cl
          )
      )
      in
      pr_atom1

    let make_pr_tac pr strip_prod_binders tag_atom tag =

        let extract_binders = function
          | Tacexp (TacFun (lvar,body)) -> (lvar,Tacexp body)
          | body -> ([],body) in
        let rec pr_tac inherited tac =
          let return (doc, l) = (tag tac doc, l) in
          let (strm, prec) = return (match tac with
            | TacAbstract (t,None) ->
              keyword "abstract " ++ pr_tac (labstract,L) t, labstract
            | TacAbstract (t,Some s) ->
              hov 0 (
                keyword "abstract"
                ++ str" (" ++ pr_tac (labstract,L) t ++ str")" ++ spc ()
                ++ keyword "using" ++ spc () ++ pr_id s),
              labstract
            | TacLetIn (recflag,llc,u) ->
              let llc = List.map (fun (id,t) -> (id,extract_binders t)) llc in
              v 0
                (hv 0 (
                  pr_let_clauses recflag (pr_tac ltop) llc
                  ++ spc () ++ keyword "in"
                 ) ++ fnl () ++ pr_tac (llet,E) u),
              llet
            | TacMatch (lz,t,lrul) ->
              hov 0 (
                pr_lazy lz ++ keyword "match" ++ spc ()
                ++ pr_tac ltop t ++ spc () ++ keyword "with"
                ++ prlist (fun r ->
                  fnl () ++ str "| "
                  ++ pr_match_rule true (pr_tac ltop) pr.pr_lpattern r
                ) lrul
                ++ fnl() ++ keyword "end"),
              lmatch
            | TacMatchGoal (lz,lr,lrul) ->
              hov 0 (
                pr_lazy lz
                ++ keyword (if lr then "match reverse goal with" else "match goal with")
                ++ prlist (fun r ->
                  fnl () ++ str "| "
                  ++ pr_match_rule false (pr_tac ltop) pr.pr_lpattern r
                ) lrul ++ fnl() ++ keyword "end"),
              lmatch
            | TacFun (lvar,body) ->
              hov 2 (
                keyword "fun"
                ++ prlist pr_funvar lvar ++ str " =>" ++ spc ()
                ++ pr_tac (lfun,E) body),
              lfun
            | TacThens (t,tl) ->
              hov 1 (
                pr_tac (lseq,E) t ++ pr_then () ++ spc ()
                ++ pr_seq_body (pr_opt_tactic (pr_tac ltop)) tl),
              lseq
            | TacThen (t1,t2) ->
              hov 1 (
                pr_tac (lseq,E) t1 ++ pr_then () ++ spc ()
                ++ pr_tac (lseq,L) t2),
              lseq
            | TacDispatch tl ->
              pr_dispatch (pr_tac ltop) tl, lseq
            | TacExtendTac (tf,t,tr) ->
              pr_tac_extend (pr_tac ltop) tf t tr , lseq
            | TacThens3parts (t1,tf,t2,tl) ->
              hov 1 (
                pr_tac (lseq,E) t1 ++ pr_then () ++ spc ()
                ++ pr_then_gen (pr_tac ltop) tf t2 tl),
              lseq
            | TacTry t ->
              hov 1 (
                keyword "try" ++ spc () ++ pr_tac (ltactical,E) t),
              ltactical
            | TacDo (n,t) ->
              hov 1 (
                str "do" ++ spc ()
                ++ pr_or_var int n ++ spc ()
                ++ pr_tac (ltactical,E) t),
              ltactical
            | TacTimeout (n,t) ->
              hov 1 (
                keyword "timeout "
                ++ pr_or_var int n ++ spc ()
                ++ pr_tac (ltactical,E) t),
              ltactical
            | TacTime (s,t) ->
              hov 1 (
                keyword "time"
                ++ pr_opt str s ++ spc ()
                ++ pr_tac (ltactical,E) t),
              ltactical
            | TacRepeat t ->
              hov 1 (
                keyword "repeat" ++ spc ()
                ++ pr_tac (ltactical,E) t),
              ltactical
            | TacProgress t ->
              hov 1 (
                keyword "progress" ++ spc ()
                ++ pr_tac (ltactical,E) t),
              ltactical
            | TacShowHyps t ->
              hov 1 (
                keyword "infoH" ++ spc ()
                ++ pr_tac (ltactical,E) t),
              ltactical
            | TacInfo t ->
              hov 1 (
                keyword "info" ++ spc ()
                ++ pr_tac (ltactical,E) t),
              linfo
            | TacOr (t1,t2) ->
              hov 1 (
                pr_tac (lorelse,L) t1 ++ spc ()
                ++ str "+" ++ brk (1,1)
                ++ pr_tac (lorelse,E) t2),
              lorelse
            | TacOnce t ->
              hov 1 (
                keyword "once" ++ spc ()
                ++ pr_tac (ltactical,E) t),
              ltactical
            | TacExactlyOnce t ->
              hov 1 (
                keyword "exactly_once" ++ spc ()
                ++ pr_tac (ltactical,E) t),
              ltactical
            | TacIfThenCatch (t,tt,te) ->
                hov 1 (
                 str"tryif" ++ spc() ++ pr_tac (ltactical,E) t ++ brk(1,1) ++
                 str"then" ++ spc() ++ pr_tac (ltactical,E) tt ++ brk(1,1) ++
                 str"else" ++ spc() ++ pr_tac (ltactical,E) te ++ brk(1,1)),
                ltactical
            | TacOrelse (t1,t2) ->
              hov 1 (
                pr_tac (lorelse,L) t1 ++ spc ()
                ++ str "||" ++ brk (1,1)
                ++ pr_tac (lorelse,E) t2),
              lorelse
            | TacFail (g,n,l) ->
              let arg =
                match n with
                  | ArgArg 0 -> mt ()
                  | _ -> pr_arg (pr_or_var int) n
              in
              let name =
                match g with
                | TacGlobal -> keyword "gfail"
                | TacLocal -> keyword "fail"
              in
              hov 1 (
                name ++ arg
                ++ prlist (pr_arg (pr_message_token pr.pr_name)) l),
              latom
            | TacFirst tl ->
              keyword "first" ++ spc () ++ pr_seq_body (pr_tac ltop) tl, llet
            | TacSolve tl ->
              keyword "solve" ++ spc () ++ pr_seq_body (pr_tac ltop) tl, llet
            | TacComplete t ->
              pr_tac (lcomplete,E) t, lcomplete
            | TacSelect (s, tac) -> pr_goal_selector s ++ spc () ++ pr_tac ltop tac, latom
            | TacId l ->
              keyword "idtac" ++ prlist (pr_arg (pr_message_token pr.pr_name)) l, latom
            | TacAtom (loc,t) ->
              pr_with_comments loc (hov 1 (pr_atom pr strip_prod_binders tag_atom t)), ltatom
            | TacArg(_,Tacexp e) ->
              pr.pr_tactic (latom,E) e, latom
            | TacArg(_,ConstrMayEval (ConstrTerm c)) ->
              keyword "constr:" ++ pr.pr_constr c, latom
            | TacArg(_,ConstrMayEval c) ->
              pr_may_eval pr.pr_constr pr.pr_lconstr pr.pr_constant pr.pr_pattern c, leval
            | TacArg(_,TacFreshId l) ->
              primitive "fresh" ++ pr_fresh_ids l, latom
            | TacArg(_,TacGeneric arg) ->
              pr.pr_generic arg, latom
            | TacArg(_,TacCall(loc,f,[])) ->
              pr.pr_reference f, latom
            | TacArg(_,TacCall(loc,f,l)) ->
              pr_with_comments loc (hov 1 (
                pr.pr_reference f ++ spc ()
                ++ prlist_with_sep spc pr_tacarg l)),
              lcall
            | TacArg (_,a) ->
              pr_tacarg a, latom
            | TacML (loc,s,l) ->
              pr_with_comments loc (pr.pr_extend 1 s l), lcall
            | TacAlias (loc,kn,l) ->
              pr_with_comments loc (pr.pr_alias (level_of inherited) kn l), latom
          )
          in
          if prec_less prec inherited then strm
          else str"(" ++ strm ++ str")"

        and pr_tacarg = function
          | Reference r ->
            pr.pr_reference r
          | ConstrMayEval c ->
            pr_may_eval pr.pr_constr pr.pr_lconstr pr.pr_constant pr.pr_pattern c
          | TacFreshId l ->
            keyword "fresh" ++ pr_fresh_ids l
          | TacPretype c ->
            keyword "type_term" ++ pr.pr_constr c
          | TacNumgoals ->
            keyword "numgoals"
          | (TacCall _|Tacexp _ | TacGeneric _) as a ->
            keyword "ltac:" ++ pr_tac (latom,E) (TacArg (Loc.ghost,a))

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
    (strip_prod_binders_expr)

  let rec pr_raw_tactic_level n (t:raw_tactic_expr) =
    let pr = {
      pr_tactic = pr_raw_tactic_level;
      pr_constr = pr_constr_expr;
      pr_dconstr = pr_constr_expr;
      pr_lconstr = pr_lconstr_expr;
      pr_pattern = pr_constr_pattern_expr;
      pr_lpattern = pr_lconstr_pattern_expr;
      pr_constant = pr_or_by_notation pr_reference;
      pr_reference = pr_reference;
      pr_name = pr_lident;
      pr_generic = pr_raw_generic_rec pr_constr_expr pr_lconstr_expr pr_raw_tactic_level pr_constr_pattern_expr pr_reference;
      pr_extend = pr_raw_extend_rec pr_constr_expr pr_lconstr_expr pr_raw_tactic_level pr_constr_pattern_expr;
      pr_alias = pr_raw_alias pr_constr_expr pr_lconstr_expr pr_raw_tactic_level pr_constr_pattern_expr;
    } in
    make_pr_tac
      pr raw_printers
      tag_raw_atomic_tactic_expr tag_raw_tactic_expr
      n t

  let pr_raw_tactic = pr_raw_tactic_level ltop

  let pr_and_constr_expr pr (c,_) = pr c

  let pr_pat_and_constr_expr pr (_,(c,_),_) = pr c

  let pr_glob_tactic_level env n t =
    let glob_printers =
      (strip_prod_binders_glob_constr)
    in
    let rec prtac n (t:glob_tactic_expr) =
      let pr = {
        pr_tactic = prtac;
        pr_constr = pr_and_constr_expr (pr_glob_constr_env env);
        pr_dconstr = pr_and_constr_expr (pr_glob_constr_env env);
        pr_lconstr = pr_and_constr_expr (pr_lglob_constr_env env);
        pr_pattern = pr_pat_and_constr_expr (pr_glob_constr_env env);
        pr_lpattern = pr_pat_and_constr_expr (pr_lglob_constr_env env);
        pr_constant = pr_or_var (pr_and_short_name (pr_evaluable_reference_env env));
        pr_reference = pr_ltac_or_var (pr_located pr_ltac_constant);
        pr_name = pr_lident;
        pr_generic = pr_glb_generic_rec
          (pr_and_constr_expr (pr_glob_constr_env env)) (pr_and_constr_expr (pr_lglob_constr_env env))
          prtac (pr_pat_and_constr_expr (pr_glob_constr_env env));
        pr_extend = pr_glob_extend_rec
          (pr_and_constr_expr (pr_glob_constr_env env)) (pr_and_constr_expr (pr_lglob_constr_env env))
          prtac (pr_pat_and_constr_expr (pr_glob_constr_env env));
        pr_alias = pr_glob_alias
          (pr_and_constr_expr (pr_glob_constr_env env)) (pr_and_constr_expr (pr_lglob_constr_env env))
          prtac (pr_pat_and_constr_expr (pr_glob_constr_env env));
      } in
      make_pr_tac
        pr glob_printers
        tag_glob_atomic_tactic_expr tag_glob_tactic_expr
        n t
    in
    prtac n t

  let pr_glob_tactic env = pr_glob_tactic_level env ltop

  let strip_prod_binders_constr n ty =
    let rec strip_ty acc n ty =
      if n=0 then (List.rev acc, ty) else
        match Term.kind_of_term ty with
            Term.Prod(na,a,b) ->
              strip_ty (([Loc.ghost,na],a)::acc) (n-1) b
          | _ -> error "Cannot translate fix tactic: not enough products" in
    strip_ty [] n ty

  let pr_atomic_tactic_level env n t =
    let prtac n (t:atomic_tactic_expr) =
      let pr = {
        pr_tactic = (fun _ _ -> str "<tactic>");
        pr_constr = pr_constr_env env Evd.empty;
        pr_dconstr = pr_and_constr_expr (pr_glob_constr_env env);
        pr_lconstr = pr_lconstr_env env Evd.empty;
        pr_pattern = pr_constr_pattern_env env Evd.empty;
        pr_lpattern = pr_lconstr_pattern_env env Evd.empty;
        pr_constant = pr_evaluable_reference_env env;
        pr_reference = pr_located pr_ltac_constant;
        pr_name = pr_id;
        (** Those are not used by the atomic printer *)
        pr_generic = (fun _ -> assert false);
        pr_extend = (fun _ _ _ -> assert false);
        pr_alias = (fun _ _ _ -> assert false);
      }
      in
      pr_atom pr strip_prod_binders_constr tag_atomic_tactic_expr t
    in
    prtac n t

  let pr_raw_generic env = pr_raw_generic_rec
    pr_constr_expr pr_lconstr_expr pr_raw_tactic_level pr_constr_pattern_expr pr_reference

  let pr_glb_generic env = pr_glb_generic_rec
    (pr_and_constr_expr (pr_glob_constr_env env)) (pr_and_constr_expr (pr_lglob_constr_env env))
    (pr_glob_tactic_level env) (pr_pat_and_constr_expr (pr_glob_constr_env env))

  let pr_raw_extend env = pr_raw_extend_rec
    pr_constr_expr pr_lconstr_expr pr_raw_tactic_level pr_constr_pattern_expr

  let pr_glob_extend env = pr_glob_extend_rec
    (pr_and_constr_expr (pr_glob_constr_env env)) (pr_and_constr_expr (pr_lglob_constr_env env))
    (pr_glob_tactic_level env) (pr_pat_and_constr_expr (pr_glob_constr_env env))

  let pr_alias pr lev key args =
    pr_alias_gen (fun _ arg -> pr arg) lev key args

  let pr_extend pr lev ml args =
    pr_extend_gen pr lev ml args

  let pr_atomic_tactic env = pr_atomic_tactic_level env ltop

end

module Tag =
struct
  let keyword =
    let style = Terminal.make ~bold:true () in
    Ppstyle.make ~style ["tactic"; "keyword"]

  let primitive =
    let style = Terminal.make ~fg_color:`LIGHT_GREEN () in
    Ppstyle.make ~style ["tactic"; "primitive"]

  let string =
    let style = Terminal.make ~fg_color:`LIGHT_RED () in
    Ppstyle.make ~style ["tactic"; "string"]

end

include Make (Ppconstr) (struct
    let tag t s = Pp.tag (Pp.Tag.inj t Ppstyle.tag) s
    let do_not_tag _ x = x
    let tag_keyword                 = tag Tag.keyword
    let tag_primitive               = tag Tag.primitive
    let tag_string                  = tag Tag.string
    let tag_glob_tactic_expr        = do_not_tag
    let tag_glob_atomic_tactic_expr = do_not_tag
    let tag_raw_tactic_expr         = do_not_tag
    let tag_raw_atomic_tactic_expr  = do_not_tag
    let tag_atomic_tactic_expr      = do_not_tag
end)

(** Registering *)

let run_delayed c =
  Sigma.run Evd.empty { Sigma.run = fun sigma -> c.delayed (Global.env ()) sigma }

let run_delayed_destruction_arg = function (* HH: Using Evd.empty looks suspicious *)
  | clear_flag,ElimOnConstr g -> clear_flag,ElimOnConstr (fst (run_delayed g))
  | clear_flag,ElimOnAnonHyp n as x -> x
  | clear_flag,ElimOnIdent id as x -> x

let () =
  let pr_bool b = if b then str "true" else str "false" in
  let pr_unit _ = str "()" in
  let pr_string s = str "\"" ++ str s ++ str "\"" in
  Genprint.register_print0 Constrarg.wit_int_or_var
    (pr_or_var int) (pr_or_var int) int;
  Genprint.register_print0 Constrarg.wit_ref
    pr_reference (pr_or_var (pr_located pr_global)) pr_global;
  Genprint.register_print0 Constrarg.wit_ident
    pr_id pr_id pr_id;
  Genprint.register_print0 Constrarg.wit_var
    (pr_located pr_id) (pr_located pr_id) pr_id;
  Genprint.register_print0
    Constrarg.wit_intro_pattern
    (Miscprint.pr_intro_pattern pr_constr_expr)
    (Miscprint.pr_intro_pattern (fun (c,_) -> pr_glob_constr c))
    (Miscprint.pr_intro_pattern (fun c -> pr_constr (fst (run_delayed c))));
  Genprint.register_print0
    Constrarg.wit_clause_dft_concl
    (pr_clauses (Some true) pr_lident)
    (pr_clauses (Some true) pr_lident)
    (pr_clauses (Some true) (fun id -> pr_lident (Loc.ghost,id)))
  ;
  Genprint.register_print0
    Constrarg.wit_constr
    Ppconstr.pr_constr_expr
    (fun (c, _) -> Printer.pr_glob_constr c)
    Printer.pr_constr
  ;
  Genprint.register_print0
    Constrarg.wit_uconstr
    Ppconstr.pr_constr_expr
    (fun (c,_) -> Printer.pr_glob_constr c)
    Printer.pr_closed_glob
  ;
  Genprint.register_print0
    Constrarg.wit_open_constr
    Ppconstr.pr_constr_expr
    (fun (c, _) -> Printer.pr_glob_constr c)
    Printer.pr_constr
  ;
  Genprint.register_print0 Constrarg.wit_red_expr
    (pr_red_expr (pr_constr_expr, pr_lconstr_expr, pr_or_by_notation pr_reference, pr_constr_pattern_expr))
    (pr_red_expr (pr_and_constr_expr pr_glob_constr, pr_lglob_constr, pr_or_var (pr_and_short_name pr_evaluable_reference), pr_pat_and_constr_expr pr_glob_constr))
    (pr_red_expr (pr_constr, pr_lconstr, pr_evaluable_reference, pr_constr_pattern));
  Genprint.register_print0 Constrarg.wit_quant_hyp pr_quantified_hypothesis pr_quantified_hypothesis pr_quantified_hypothesis;
  Genprint.register_print0 Constrarg.wit_bindings
    (pr_bindings_no_with pr_constr_expr pr_lconstr_expr)
    (pr_bindings_no_with (pr_and_constr_expr pr_glob_constr) (pr_and_constr_expr pr_lglob_constr))
    (fun it -> pr_bindings_no_with pr_constr pr_lconstr (fst (run_delayed it)));
  Genprint.register_print0 Constrarg.wit_constr_with_bindings
    (pr_with_bindings pr_constr_expr pr_lconstr_expr)
    (pr_with_bindings (pr_and_constr_expr pr_glob_constr) (pr_and_constr_expr pr_lglob_constr))
    (fun it -> pr_with_bindings pr_constr pr_lconstr (fst (run_delayed it)));
  Genprint.register_print0 Constrarg.wit_destruction_arg
    (pr_destruction_arg pr_constr_expr pr_lconstr_expr)
    (pr_destruction_arg (pr_and_constr_expr pr_glob_constr) (pr_and_constr_expr pr_lglob_constr))
    (fun it -> pr_destruction_arg pr_constr pr_lconstr (run_delayed_destruction_arg it));
  Genprint.register_print0 Stdarg.wit_int int int int;
  Genprint.register_print0 Stdarg.wit_bool pr_bool pr_bool pr_bool;
  Genprint.register_print0 Stdarg.wit_unit pr_unit pr_unit pr_unit;
  Genprint.register_print0 Stdarg.wit_pre_ident str str str;
  Genprint.register_print0 Stdarg.wit_string pr_string pr_string pr_string

let () =
  let printer _ _ prtac = prtac (0, E) in
  declare_extra_genarg_pprule wit_tactic printer printer printer

let () =
  let pr_unit _ _ _ () = str "()" in
  let printer _ _ prtac = prtac (0, E) in
  declare_extra_genarg_pprule wit_ltac printer printer pr_unit

module Richpp = struct

  include Make (Ppconstr.Richpp) (struct
    open Ppannotation
    let do_not_tag _ x = x
    let tag e s = Pp.tag (Pp.Tag.inj e tag) s
    let tag_keyword                   = tag AKeyword
    let tag_primitive                 = tag AKeyword
    let tag_string                    = do_not_tag ()
    let tag_glob_tactic_expr        e = tag (AGlobTacticExpr e)
    let tag_glob_atomic_tactic_expr a = tag (AGlobAtomicTacticExpr a)
    let tag_raw_tactic_expr         e = tag (ARawTacticExpr e)
    let tag_raw_atomic_tactic_expr  a = tag (ARawAtomicTacticExpr a)
    let tag_atomic_tactic_expr      a = tag (AAtomicTacticExpr a)
  end)

end
