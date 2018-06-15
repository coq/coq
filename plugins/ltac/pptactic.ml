(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Names
open Namegen
open CErrors
open Util
open Constrexpr
open Genarg
open Geninterp
open Stdarg
open Notation_gram
open Tactypes
open Locus
open Decl_kinds
open Genredexpr
open Pputils
open Ppconstr
open Printer

open Tacexpr
open Tacarg
open Tactics

module Tag =
struct

  let keyword   = "tactic.keyword"
  let primitive = "tactic.primitive"
  let string    = "tactic.string"

end

let tag t s = Pp.tag t s
let do_not_tag _ x = x
let tag_keyword                 = tag Tag.keyword
let tag_primitive               = tag Tag.primitive
let tag_string                  = tag Tag.string
let tag_glob_tactic_expr        = do_not_tag
let tag_glob_atomic_tactic_expr = do_not_tag
let tag_raw_tactic_expr         = do_not_tag
let tag_raw_atomic_tactic_expr  = do_not_tag
let tag_atomic_tactic_expr      = do_not_tag

let pr_global x = Nametab.pr_global_env Id.Set.empty x

type 'a grammar_tactic_prod_item_expr =
| TacTerm of string
| TacNonTerm of ('a * Names.Id.t option) Loc.located

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
    (constr_expr -> Pp.t) ->
    (constr_expr -> Pp.t) ->
    (tolerability -> raw_tactic_expr -> Pp.t) ->
    'a -> Pp.t

type 'a glob_extra_genarg_printer =
    (glob_constr_and_expr -> Pp.t) ->
    (glob_constr_and_expr -> Pp.t) ->
    (tolerability -> glob_tactic_expr -> Pp.t) ->
    'a -> Pp.t

type 'a extra_genarg_printer =
    (EConstr.constr -> Pp.t) ->
    (EConstr.constr -> Pp.t) ->
    (tolerability -> Val.t -> Pp.t) ->
    'a -> Pp.t

type 'a raw_extra_genarg_printer_with_level =
    (constr_expr -> Pp.t) ->
    (constr_expr -> Pp.t) ->
    (tolerability -> raw_tactic_expr -> Pp.t) ->
    tolerability -> 'a -> Pp.t

type 'a glob_extra_genarg_printer_with_level =
    (glob_constr_and_expr -> Pp.t) ->
    (glob_constr_and_expr -> Pp.t) ->
    (tolerability -> glob_tactic_expr -> Pp.t) ->
    tolerability -> 'a -> Pp.t

type 'a extra_genarg_printer_with_level =
    (EConstr.constr -> Pp.t) ->
    (EConstr.constr -> Pp.t) ->
    (tolerability -> Val.t -> Pp.t) ->
    tolerability -> 'a -> Pp.t

let string_of_genarg_arg (ArgumentType arg) =
  let rec aux : type a b c. (a, b, c) genarg_type -> string = function
  | ListArg t -> aux t ^ "_list"
  | OptArg t -> aux t ^ "_opt"
  | PairArg (t1, t2) -> assert false (* No parsing/printing rule for it *)
  | ExtraArg s -> ArgT.repr s in
  aux arg

  let keyword x = tag_keyword (str x)
  let primitive x = tag_primitive (str x)

  let has_type (Val.Dyn (tag, _)) t = match Val.eq tag t with
  | None -> false
  | Some _ -> true

  let unbox : type a. Val.t -> a Val.typ -> a= fun (Val.Dyn (tag, x)) t ->
  match Val.eq tag t with
  | None -> assert false
  | Some Refl -> x

  let rec pr_value lev v : Pp.t =
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
          | Some Refl ->
             let open Genprint in
             match generic_top_print (in_gen (Topwit wit) x) with
             | TopPrinterBasic pr -> pr ()
             | TopPrinterNeedsContext pr ->
               let env = Global.env() in
               pr env (Evd.from_env env)
             | TopPrinterNeedsContextAndLevel { default_ensure_surrounded; printer } ->
               let env = Global.env() in
               printer env (Evd.from_env env) default_ensure_surrounded
          end
        | _ -> default

  let pr_with_occurrences pr c = pr_with_occurrences pr keyword c
  let pr_red_expr pr c = pr_red_expr pr keyword c

  let pr_may_eval test prc prlc pr2 pr3 = function
    | ConstrEval (r,c) ->
      hov 0
        (keyword "eval" ++ brk (1,1) ++
           pr_red_expr (prc,prlc,pr2,pr3) r ++ spc () ++
           keyword "in" ++ spc() ++ prc c)
    | ConstrContext ({CAst.v=id},c) ->
      hov 0
        (keyword "context" ++ spc () ++ pr_id id ++ spc () ++
           str "[ " ++ prlc c ++ str " ]")
    | ConstrTypeOf c ->
      hov 1 (keyword "type of" ++ spc() ++ prc c)
    | ConstrTerm c when test c ->
      h 0 (str "(" ++ prc c ++ str ")")
    | ConstrTerm c ->
      prc c

  let pr_may_eval a =
    pr_may_eval (fun _ -> false) a

  let pr_arg pr x = spc () ++ pr x

  let pr_and_short_name pr (c,_) = pr c

  let pr_or_by_notation f = CAst.with_val (function
    | AN v -> f v
    | ByNotation (s,sc) -> qs s ++ pr_opt (fun sc -> str "%" ++ str sc) sc)

  let pr_located pr (_,x) = pr x

  let pr_evaluable_reference = function
    | EvalVarRef id -> pr_id id
    | EvalConstRef sp -> pr_global (Globnames.ConstRef sp)

  let pr_quantified_hypothesis = function
    | AnonHyp n -> int n
    | NamedHyp id -> pr_id id

  let pr_clear_flag clear_flag pp x =
    match clear_flag with
    | Some false -> surround (pp x)
    | Some true -> str ">" ++ pp x
    | None -> pp x

  let pr_with_bindings prc prlc (c,bl) =
    prc c ++ Miscprint.pr_bindings prc prlc bl

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

  let rec tacarg_using_rule_token pr_gen = function
    | [] -> []
    | TacTerm s :: l -> keyword s :: tacarg_using_rule_token pr_gen l
    | TacNonTerm (_, ((symb, arg), _)) :: l  ->
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

  let pr_extend_gen pr_gen _ { mltac_name = s; mltac_index = i } l =
      let name =
        str s.mltac_plugin ++ str "::" ++ str s.mltac_tactic ++
        str "@" ++ int i
      in
      let args = match l with
        | [] -> mt ()
        | _ -> spc() ++ pr_sequence pr_gen l
      in
      str "<" ++ name ++ str ">" ++ args

  let rec pr_user_symbol = function
  | Extend.Ulist1 tkn -> "ne_" ^ pr_user_symbol tkn ^ "_list"
  | Extend.Ulist1sep (tkn, _) -> "ne_" ^ pr_user_symbol tkn ^ "_list"
  | Extend.Ulist0 tkn -> pr_user_symbol tkn ^ "_list"
  | Extend.Ulist0sep (tkn, _) -> pr_user_symbol tkn ^ "_list"
  | Extend.Uopt tkn -> pr_user_symbol tkn ^ "_opt"
  | Extend.Uentry tag ->
    let ArgT.Any tag = tag in
    ArgT.repr tag
  | Extend.Uentryl (_, lvl) -> "tactic" ^ string_of_int lvl

  let pr_alias_key key =
    try
      let prods = (KNmap.find key !prnotation_tab).pptac_prods in
      let pr = function
      | TacTerm s -> primitive s
      | TacNonTerm (_, (symb, _)) -> str (Printf.sprintf "(%s)" (pr_user_symbol symb))
      in
      pr_sequence pr prods
    with Not_found ->
      (* FIXME: This key, moreover printed with a low-level printer,
         has no meaning user-side *)
      KerName.print key

  let pr_alias_gen pr_gen lev key l =
    try
      let pp = KNmap.find key !prnotation_tab in
      let rec pack prods args = match prods, args with
      | [], [] -> []
      | TacTerm s :: prods, args -> TacTerm s :: pack prods args
      | TacNonTerm (_, (_, None)) :: prods, args -> pack prods args
      | TacNonTerm (loc, (symb, (Some _ as ido))) :: prods, arg :: args ->
        TacNonTerm (loc, ((symb, arg), ido)) :: pack prods args
      | _ -> raise Not_found
      in
      let prods = pack pp.pptac_prods l in
      let p = pr_tacarg_using_rule pr_gen prods in
      if pp.pptac_level > lev then surround p else p
    with Not_found ->
      let pr _ = str "_" in
      KerName.print key ++ spc() ++ pr_sequence pr l ++ str" (* Generic printer *)"

  let pr_farg prtac arg = prtac (1, Any) (TacArg (Loc.tag arg))

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

  let rec pr_any_arg : type l. (_ -> l generic_argument -> Pp.t) -> _ -> l generic_argument -> Pp.t =
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

  let pr_targ prtac symb arg = match symb with
  | Extend.Uentry tag when is_genarg tag (ArgumentType wit_tactic) ->
    prtac (1, Any) arg
  | Extend.Uentryl (_, l) -> prtac (l, Any) arg
  | _ ->
    match arg with
    | TacGeneric arg ->
      let pr l arg = prtac l (TacGeneric arg) in
      pr_any_arg pr symb arg
    | _ -> str "ltac:(" ++ prtac (1, Any) arg ++ str ")"

  let pr_raw_extend_rec prtac =
    pr_extend_gen (pr_farg prtac)
  let pr_glob_extend_rec prtac =
    pr_extend_gen (pr_farg prtac)

  let pr_raw_alias prtac lev key args =
    pr_alias_gen (pr_targ (fun l a -> prtac l (TacArg (Loc.tag a)))) lev key args
  let pr_glob_alias prtac lev key args =
    pr_alias_gen (pr_targ (fun l a -> prtac l (TacArg (Loc.tag a)))) lev key args

  (**********************************************************************)
  (* The tactic printer                                                 *)

  let strip_prod_binders_expr n ty =
    let rec strip_ty acc n ty =
      match ty.CAst.v with
          Constrexpr.CProdN(bll,a) ->
            let bll = List.map (function
            | CLocalAssum (nal,_,t) -> nal,t
            | _ -> user_err Pp.(str "Cannot translate fix tactic: not only products")) bll in
            let nb = List.fold_left (fun i (nal,t) -> i + List.length nal) 0 bll in
            if nb >= n then (List.rev (bll@acc)), a
            else strip_ty (bll@acc) (n-nb) a
        | _ -> user_err Pp.(str "Cannot translate fix tactic: not enough products") in
    strip_ty [] n ty

  let pr_ltac_or_var pr = function
    | ArgArg x -> pr x
    | ArgVar {CAst.loc;v=id} -> pr_with_comments ?loc (pr_id id)

  let pr_ltac_constant kn =
    if !Flags.in_debugger then KerName.print kn
    else try
           pr_qualid (Tacenv.shortest_qualid_of_tactic kn)
      with Not_found -> (* local tactic not accessible anymore *)
        str "<" ++ KerName.print kn ++ str ">"

  let pr_evaluable_reference_env env = function
    | EvalVarRef id -> pr_id id
    | EvalConstRef sp ->
      Nametab.pr_global_env (Termops.vars_of_env env) (Globnames.ConstRef sp)

  let pr_as_disjunctive_ipat prc ipatl =
    keyword "as" ++ spc () ++
      pr_or_var (fun {CAst.loc;v=p} -> Miscprint.pr_or_and_intro_pattern prc p) ipatl

  let pr_eqn_ipat {CAst.v=ipat} = keyword "eqn:" ++ Miscprint.pr_intro_pattern_naming ipat

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
    | Name id -> spc () ++ keyword "as" ++ spc () ++ pr_lident (CAst.make id)

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
    | Some {CAst.v=IntroNaming (IntroIdentifier id)} ->
      spc() ++ surround (pr_id id ++ str " :" ++ spc() ++ prlc c)
    | ipat ->
      spc() ++ prc c ++ pr_as_ipat prdc ipat

  let pr_by_tactic prt = function
    | Some tac -> keyword "by" ++ spc () ++ prt tac
    | None -> mt()

  let pr_hyp_location pr_id = function
    | occs, InHyp -> pr_with_occurrences pr_id occs
    | occs, InHypTypeOnly ->
      pr_with_occurrences (fun id ->
        str "(" ++ keyword "type of" ++ spc () ++ pr_id id ++ str ")"
      ) occs
    | occs, InHypValueOnly ->
      pr_with_occurrences (fun id ->
        str "(" ++ keyword "value of" ++ spc () ++ pr_id id ++ str ")"
      ) occs

  let pr_in pp = hov 0 (keyword "in" ++ pp)

  let pr_simple_hyp_clause pr_id = function
    | [] -> mt ()
    | l -> pr_in (spc () ++ prlist_with_sep spc pr_id l)

  let pr_in_hyp_as prc pr_id = function
    | None -> mt ()
    | Some (id,ipat) -> pr_in (spc () ++ pr_id id) ++ pr_as_ipat prc ipat

  let pr_in_clause pr_id = function
    | { onhyps=None; concl_occs=NoOccurrences } ->
      (str "* |-")
    | { onhyps=None; concl_occs=occs } ->
      (pr_with_occurrences (fun () -> str "*") (occs,()))
    | { onhyps=Some l; concl_occs=NoOccurrences } ->
      prlist_with_sep (fun () -> str ", ") (pr_hyp_location pr_id) l
    | { onhyps=Some l; concl_occs=occs } ->
      let pr_occs = pr_with_occurrences (fun () -> str" |- *") (occs,()) in
      (prlist_with_sep (fun () -> str", ") (pr_hyp_location pr_id) l ++ pr_occs)

  (* Some true = default is concl; Some false = default is all; None = no default *)
  let pr_clauses has_default pr_id = function
    | { onhyps=Some []; concl_occs=occs }
        when (match has_default with Some true -> true | _ -> false) ->
      pr_with_occurrences mt (occs,())
    | { onhyps=None; concl_occs=AllOccurrences }
        when (match has_default with Some false -> true | _ -> false) -> mt ()
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
        (prlist_with_sep (fun () -> str",")
           (fun id -> spc () ++ pr_hyp_location pr_id id) l ++ pr_occs)

  let pr_orient b = if b then mt () else str "<- "

  let pr_multi = let open Equality in function
    | Precisely 1 -> mt ()
    | Precisely n -> int n ++ str "!"
    | UpTo n -> int n ++ str "?"
    | RepeatStar -> str "?"
    | RepeatPlus -> str "!"

  let pr_core_destruction_arg prc prlc = function
    | ElimOnConstr c -> pr_with_bindings prc prlc c
    | ElimOnIdent {CAst.loc;v=id} -> pr_with_comments ?loc (pr_id id)
    | ElimOnAnonHyp n -> int n

  let pr_destruction_arg prc prlc (clear_flag,h) =
    pr_clear_flag clear_flag (pr_core_destruction_arg prc prlc) h

  let pr_inversion_kind = let open Inv in function
    | SimpleInversion -> primitive "simple inversion"
    | FullInversion -> primitive "inversion"
    | FullInversionClear -> primitive "inversion_clear"

  let pr_range_selector (i, j) =
    if Int.equal i j then int i
    else int i ++ str "-" ++ int j

let pr_goal_selector toplevel = let open Goal_select in function
  | SelectAlreadyFocused -> str "!:"
  | SelectNth i -> int i ++ str ":"
  | SelectList l -> prlist_with_sep (fun () -> str ", ") pr_range_selector l ++ str ":"
  | SelectId id -> str "[" ++ Id.print id ++ str "]:"
  | SelectAll -> assert toplevel; str "all:"

let pr_goal_selector ~toplevel s =
  (if toplevel then mt () else str "only ") ++ pr_goal_selector toplevel s

  let pr_lazy = function
    | General -> keyword "multi"
    | Select -> keyword "lazy"
    | Once -> mt ()

  let pr_match_pattern pr_pat = function
    | Term a -> pr_pat a
    | Subterm (None,a) ->
      keyword "context" ++ str" [ " ++ pr_pat a ++ str " ]"
    | Subterm (Some id,a) ->
      keyword "context" ++ spc () ++ pr_id id ++ str "[ " ++ pr_pat a ++ str " ]"

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

  let pr_funvar n = spc () ++ Name.print n

  let pr_let_clause k pr_gen pr_arg (na,(bl,t)) =
    let pr = function
      | TacGeneric arg ->
         let name = string_of_genarg_arg (genarg_tag arg) in
         if name = "unit" || name = "int" then
           (* Hard-wired parsing rules *)
           pr_gen  arg
         else
           str name ++ str ":" ++ surround (pr_gen arg)
      | _ -> pr_arg (TacArg (Loc.tag t)) in
    hov 0 (keyword k ++ spc () ++ pr_lname na ++ prlist pr_funvar bl ++
             str " :=" ++ brk (1,1) ++ pr t)

  let pr_let_clauses recflag pr_gen pr = function
    | hd::tl ->
      hv 0
        (pr_let_clause (if recflag then "let rec" else "let") pr_gen pr hd ++
           prlist (fun t -> spc () ++ pr_let_clause "with" pr_gen pr t) tl)
    | [] -> anomaly (Pp.str "LetIn must declare at least one binding.")

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
    pr_tactic    : tolerability -> 'tacexpr -> Pp.t;
    pr_constr    : 'trm -> Pp.t;
    pr_lconstr   : 'trm -> Pp.t;
    pr_dconstr   : 'dtrm -> Pp.t;
    pr_pattern   : 'pat -> Pp.t;
    pr_lpattern  : 'pat -> Pp.t;
    pr_constant  : 'cst -> Pp.t;
    pr_reference : 'ref -> Pp.t;
    pr_name      : 'nam -> Pp.t;
    pr_generic   : 'lev generic_argument -> Pp.t;
    pr_extend    : int -> ml_tactic_entry -> 'a gen_tactic_arg list -> Pp.t;
    pr_alias     : int -> KerName.t -> 'a gen_tactic_arg list -> Pp.t;
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

      let _pr_constrarg c = spc () ++ pr.pr_constr c in
      let pr_lconstrarg c = spc () ++ pr.pr_lconstr c in
      let pr_intarg n = spc () ++ int n in

      (* Some printing combinators *)
      let pr_eliminator cb = keyword "using" ++ pr_arg pr_with_bindings cb in

      let pr_binder_fix (nal,t) =
        (*  match t with
            | CHole _ -> spc() ++ prlist_with_sep spc (pr_lname) nal
            | _ ->*)
        let s = prlist_with_sep spc Ppconstr.pr_lname nal ++ str ":" ++ pr.pr_lconstr t in
        spc() ++ hov 1 (str"(" ++ s ++ str")") in

      let pr_fix_tac (id,n,c) =
        let rec set_nth_name avoid n = function
        (nal,ty)::bll ->
          if n <= List.length nal then
            match List.chop (n-1) nal with
                _, {CAst.v=Name id} :: _ -> id, (nal,ty)::bll
              | bef, {CAst.loc;v=Anonymous} :: aft ->
                let id = next_ident_away (Id.of_string"y") avoid in
                id, ((bef@(CAst.make ?loc @@ Name id)::aft, ty)::bll)
              | _ -> assert false
          else
            let (id,bll') = set_nth_name avoid (n-List.length nal) bll in
            (id,(nal,ty)::bll')
          | [] -> assert false in
        let (bll,ty) = strip_prod_binders n c in
        let names =
          List.fold_left
            (fun ln (nal,_) -> List.fold_left
              (fun ln na -> match na with { CAst.v=Name id } -> Id.Set.add id ln | _ -> ln)
              ln nal)
            Id.Set.empty bll in
        let idarg,bll = set_nth_name names n bll in
        let annot =
          if Int.equal (Id.Set.cardinal names) 1 then
            mt ()
          else
            spc() ++ str"{"
            ++ keyword "struct" ++ spc ()
            ++ pr_id idarg ++ str"}"
        in
        hov 1 (str"(" ++ pr_id id ++
                  prlist pr_binder_fix bll ++ annot ++ str" :" ++
                  pr_lconstrarg ty ++ str")") in
      (*  spc() ++
          hov 0 (pr_id id ++ pr_intarg n ++ str":" ++ _pr_constrarg
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
        | TacIntroPattern (_,[]) as t ->
          pr_atom0 t
        | TacIntroPattern (ev,(_::_ as p)) ->
           hov 1 (primitive (if ev then "eintros" else "intros") ++
                    (match p with
                    | [{CAst.v=IntroForthcoming false}] -> mt ()
                    | _ -> spc () ++ prlist_with_sep spc (Miscprint.pr_intro_pattern pr.pr_dconstr) p))
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
        | TacAssert (ev,b,Some tac,ipat,c) ->
          hov 1 (
            primitive (if b then if ev then "eassert" else "assert" else if ev then "eenough" else "enough") ++
              pr_assumption pr.pr_constr pr.pr_dconstr pr.pr_lconstr ipat c ++
              pr_non_empty_arg (pr_by_tactic (pr.pr_tactic (ltactical,E))) tac
          )
        | TacAssert (ev,_,None,ipat,c) ->
          hov 1 (
            primitive (if ev then "epose proof" else "pose proof")
            ++ pr_assertion pr.pr_constr pr.pr_dconstr pr.pr_lconstr ipat c
          )
        | TacGeneralize l ->
          hov 1 (
            primitive "generalize" ++ spc ()
            ++ prlist_with_sep pr_comma (fun (cl,na) ->
              pr_with_occurrences pr.pr_constr cl ++ pr_as_name na)
              l
          )
        | TacLetTac (ev,na,c,cl,true,_) when Locusops.is_nowhere cl ->
          hov 1 (primitive (if ev then "epose" else "pose") ++ pr_pose pr.pr_constr pr.pr_lconstr na c)
        | TacLetTac (ev,na,c,cl,b,e) ->
          hov 1 (
            primitive (if b then if ev then "eset" else "set" else if ev then "eremember" else "remember") ++
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
                  pr_let_clauses recflag pr.pr_generic (pr_tac ltop) llc
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
            | TacSelect (s, tac) -> pr_goal_selector ~toplevel:false s ++ spc () ++ pr_tac ltop tac, latom
            | TacId l ->
              keyword "idtac" ++ prlist (pr_arg (pr_message_token pr.pr_name)) l, latom
            | TacAtom (loc,t) ->
              pr_with_comments ?loc (hov 1 (pr_atom pr strip_prod_binders tag_atom t)), ltatom
            | TacArg(_,Tacexp e) ->
              pr_tac inherited e, latom
            | TacArg(_,ConstrMayEval (ConstrTerm c)) ->
              keyword "constr:" ++ pr.pr_constr c, latom
            | TacArg(_,ConstrMayEval c) ->
              pr_may_eval pr.pr_constr pr.pr_lconstr pr.pr_constant pr.pr_pattern c, leval
            | TacArg(_,TacFreshId l) ->
              primitive "fresh" ++ pr_fresh_ids l, latom
            | TacArg(_,TacGeneric arg) ->
              pr.pr_generic arg, latom
            | TacArg(_,TacCall(_,(f,[]))) ->
              pr.pr_reference f, latom
            | TacArg(_,TacCall(loc,(f,l))) ->
              pr_with_comments ?loc (hov 1 (
                pr.pr_reference f ++ spc ()
                ++ prlist_with_sep spc pr_tacarg l)),
              lcall
            | TacArg (_,a) ->
              pr_tacarg a, latom
            | TacML (loc,(s,l)) ->
              pr_with_comments ?loc (pr.pr_extend 1 s l), lcall
            | TacAlias (loc,(kn,l)) ->
              pr_with_comments ?loc (pr.pr_alias (level_of inherited) kn l), latom
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
            hov 0 (keyword "ltac:" ++ surround (pr_tac ltop (TacArg (Loc.tag a))))

        in pr_tac

  let strip_prod_binders_glob_constr n (ty,_) =
    let rec strip_ty acc n ty =
      if Int.equal n 0 then (List.rev acc, (ty,None)) else
        match DAst.get ty with
            Glob_term.GProd(na,Explicit,a,b) ->
              strip_ty (([CAst.make na],(a,None))::acc) (n-1) b
          | _ -> user_err Pp.(str "Cannot translate fix tactic: not enough products") in
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
      pr_constant = pr_or_by_notation pr_qualid;
      pr_reference = pr_qualid;
      pr_name = pr_lident;
      pr_generic = (fun arg -> Pputils.pr_raw_generic (Global.env ()) arg);
      pr_extend = pr_raw_extend_rec pr_raw_tactic_level;
      pr_alias = pr_raw_alias pr_raw_tactic_level;
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
        pr_generic = (fun arg -> Pputils.pr_glb_generic (Global.env ()) arg);
        pr_extend = pr_glob_extend_rec prtac;
        pr_alias = pr_glob_alias prtac;
      } in
      make_pr_tac
        pr glob_printers
        tag_glob_atomic_tactic_expr tag_glob_tactic_expr
        n t
    in
    prtac n t

  let pr_glob_tactic env = pr_glob_tactic_level env ltop

  let strip_prod_binders_constr n ty =
    let ty = EConstr.Unsafe.to_constr ty in
    let rec strip_ty acc n ty =
      if n=0 then (List.rev acc, EConstr.of_constr ty) else
        match Constr.kind ty with
        | Constr.Prod(na,a,b) ->
          strip_ty (([CAst.make na],EConstr.of_constr a)::acc) (n-1) b
        | _ -> user_err Pp.(str "Cannot translate fix tactic: not enough products") in
    strip_ty [] n ty

  let pr_atomic_tactic_level env sigma t =
    let prtac (t:atomic_tactic_expr) =
      let pr = {
        pr_tactic = (fun _ _ -> str "<tactic>");
        pr_constr = (fun c -> pr_econstr_env env sigma c);
        pr_dconstr = pr_and_constr_expr (pr_glob_constr_env env);
        pr_lconstr = (fun c -> pr_leconstr_env env sigma c);
        pr_pattern = pr_constr_pattern_env env sigma;
        pr_lpattern = pr_lconstr_pattern_env env sigma;
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
    prtac t

  let pr_raw_generic = Pputils.pr_raw_generic

  let pr_glb_generic = Pputils.pr_glb_generic

  let pr_raw_extend _ = pr_raw_extend_rec pr_raw_tactic_level

  let pr_glob_extend env = pr_glob_extend_rec (pr_glob_tactic_level env)

  let pr_alias pr lev key args =
    pr_alias_gen (fun _ arg -> pr arg) lev key args

  let pr_extend pr lev ml args =
    pr_extend_gen pr lev ml args

  let pr_atomic_tactic env sigma c = pr_atomic_tactic_level env sigma c

let declare_extra_genarg_pprule wit
  (f : 'a raw_extra_genarg_printer)
  (g : 'b glob_extra_genarg_printer)
  (h : 'c extra_genarg_printer) =
  begin match wit with
    | ExtraArg _ -> ()
    | _          -> user_err Pp.(str "Can declare a pretty-printing rule only for extra argument types.")
  end;
  let f x =
    Genprint.PrinterBasic (fun () ->
        f pr_constr_expr pr_lconstr_expr pr_raw_tactic_level x) in
  let g x =
    Genprint.PrinterBasic (fun () ->
    let env = Global.env () in
    g (pr_and_constr_expr (pr_glob_constr_env env)) (pr_and_constr_expr (pr_lglob_constr_env env)) (pr_glob_tactic_level env) x)
  in
  let h x =
    Genprint.TopPrinterNeedsContext (fun env sigma ->
        h (pr_econstr_env env sigma) (pr_leconstr_env env sigma) (fun _ _ -> str "<tactic>") x)
  in
  Genprint.register_print0 wit f g h

let declare_extra_genarg_pprule_with_level wit
  (f : 'a raw_extra_genarg_printer_with_level)
  (g : 'b glob_extra_genarg_printer_with_level)
  (h : 'c extra_genarg_printer_with_level) default_surrounded default_non_surrounded =
  begin match wit with
    | ExtraArg s -> ()
    | _          -> user_err Pp.(str "Can declare a pretty-printing rule only for extra argument types.")
  end;
  let open Genprint in
  let f x =
    PrinterNeedsLevel {
        default_already_surrounded = default_surrounded;
        default_ensure_surrounded = default_non_surrounded;
        printer = (fun n ->
          f pr_constr_expr pr_lconstr_expr pr_raw_tactic_level n x) } in
  let g x =
    let env = Global.env () in
    PrinterNeedsLevel {
        default_already_surrounded = default_surrounded;
        default_ensure_surrounded = default_non_surrounded;
        printer = (fun n ->
          g (pr_and_constr_expr (pr_glob_constr_env env)) (pr_and_constr_expr (pr_lglob_constr_env env)) (pr_glob_tactic_level env) n x) }
  in
  let h x =
    TopPrinterNeedsContextAndLevel {
        default_already_surrounded = default_surrounded;
        default_ensure_surrounded = default_non_surrounded;
        printer = (fun env sigma n ->
          h (pr_econstr_env env sigma) (pr_leconstr_env env sigma) (fun _ _ -> str "<tactic>") n x) }
  in
  Genprint.register_print0 wit f g h

let declare_extra_vernac_genarg_pprule wit f =
  let f x = Genprint.PrinterBasic (fun () -> f pr_constr_expr pr_lconstr_expr pr_raw_tactic_level x) in
  Genprint.register_vernac_print0 wit f

(** Registering *)

let pr_intro_pattern_env p = Genprint.TopPrinterNeedsContext (fun env sigma ->
  let print_constr c = let (sigma, c) = c env sigma in pr_econstr_env env sigma c in
  Miscprint.pr_intro_pattern print_constr p)

let pr_red_expr_env r = Genprint.TopPrinterNeedsContext (fun env sigma ->
  pr_red_expr (pr_econstr_env env sigma, pr_leconstr_env env sigma,
               pr_evaluable_reference_env env, pr_constr_pattern_env env sigma) r)

let pr_bindings_env bl = Genprint.TopPrinterNeedsContext (fun env sigma ->
  let sigma, bl = bl env sigma in
  Miscprint.pr_bindings
    (pr_econstr_env env sigma) (pr_leconstr_env env sigma) bl)

let pr_with_bindings_env bl = Genprint.TopPrinterNeedsContext (fun env sigma ->
  let sigma, bl = bl env sigma in
  pr_with_bindings
    (pr_econstr_env env sigma) (pr_leconstr_env env sigma) bl)

let pr_destruction_arg_env c = Genprint.TopPrinterNeedsContext (fun env sigma ->
  let sigma, c = match c with
  | clear_flag,ElimOnConstr g -> let sigma,c = g env sigma in sigma,(clear_flag,ElimOnConstr c)
  | clear_flag,ElimOnAnonHyp n as x -> sigma, x
  | clear_flag,ElimOnIdent id as x -> sigma, x in
  pr_destruction_arg
    (pr_econstr_env env sigma) (pr_leconstr_env env sigma) c)

let make_constr_printer f c =
  Genprint.TopPrinterNeedsContextAndLevel {
      Genprint.default_already_surrounded = Ppconstr.ltop;
      Genprint.default_ensure_surrounded = Ppconstr.lsimpleconstr;
      Genprint.printer = (fun env sigma n -> f env sigma n c)}

let lift f a = Genprint.PrinterBasic (fun () -> f a)
let lift_top f a = Genprint.TopPrinterBasic (fun () -> f a)

let register_basic_print0 wit f g h =
  Genprint.register_print0 wit (lift f) (lift g) (lift_top h)


let pr_glob_constr_pptac c =
  let _, env = Pfedit.get_current_context () in
  pr_glob_constr_env env c

let pr_lglob_constr_pptac c =
  let _, env = Pfedit.get_current_context () in
  pr_lglob_constr_env env c

let () =
  let pr_bool b = if b then str "true" else str "false" in
  let pr_unit _ = str "()" in
  let open Genprint in
  register_basic_print0 wit_int_or_var (pr_or_var int) (pr_or_var int) int;
  register_basic_print0 wit_ref
    pr_qualid (pr_or_var (pr_located pr_global)) pr_global;
  register_basic_print0 wit_ident pr_id pr_id pr_id;
  register_basic_print0 wit_var pr_lident pr_lident pr_id;
  register_print0
    wit_intro_pattern
    (lift (Miscprint.pr_intro_pattern pr_constr_expr))
    (lift (Miscprint.pr_intro_pattern (fun (c,_) -> pr_glob_constr_pptac c)))
    pr_intro_pattern_env;
  Genprint.register_print0
    wit_clause_dft_concl
    (lift (pr_clauses (Some true) pr_lident))
    (lift (pr_clauses (Some true) pr_lident))
    (fun c -> Genprint.TopPrinterBasic (fun () -> pr_clauses (Some true) (fun id -> pr_lident (CAst.make id)) c))
  ;
  Genprint.register_print0
    wit_constr
    (lift Ppconstr.pr_lconstr_expr)
    (lift (fun (c, _) -> pr_lglob_constr_pptac c))
    (make_constr_printer Printer.pr_econstr_n_env)
  ;
  Genprint.register_print0
    wit_uconstr
    (lift Ppconstr.pr_constr_expr)
    (lift (fun (c,_) -> pr_glob_constr_pptac c))
    (make_constr_printer Printer.pr_closed_glob_n_env)
  ;
  Genprint.register_print0
    wit_open_constr
    (lift Ppconstr.pr_constr_expr)
    (lift (fun (c, _) -> pr_glob_constr_pptac c))
    (make_constr_printer Printer.pr_econstr_n_env)
  ;
  Genprint.register_print0
    wit_red_expr
    (lift (pr_red_expr (pr_constr_expr, pr_lconstr_expr, pr_or_by_notation pr_qualid, pr_constr_pattern_expr)))
    (lift (pr_red_expr (pr_and_constr_expr pr_glob_constr_pptac, pr_and_constr_expr pr_lglob_constr_pptac, pr_or_var (pr_and_short_name pr_evaluable_reference), pr_pat_and_constr_expr pr_glob_constr_pptac)))
    pr_red_expr_env
  ;
  register_basic_print0 wit_quant_hyp pr_quantified_hypothesis pr_quantified_hypothesis pr_quantified_hypothesis;
  register_print0 wit_bindings
    (lift (Miscprint.pr_bindings_no_with pr_constr_expr pr_lconstr_expr))
    (lift (Miscprint.pr_bindings_no_with (pr_and_constr_expr pr_glob_constr_pptac) (pr_and_constr_expr pr_lglob_constr_pptac)))
    pr_bindings_env
  ;
  register_print0 wit_constr_with_bindings
    (lift (pr_with_bindings pr_constr_expr pr_lconstr_expr))
    (lift (pr_with_bindings (pr_and_constr_expr pr_glob_constr_pptac) (pr_and_constr_expr pr_lglob_constr_pptac)))
    pr_with_bindings_env
  ;
  register_print0 wit_open_constr_with_bindings
    (lift (pr_with_bindings pr_constr_expr pr_lconstr_expr))
    (lift (pr_with_bindings (pr_and_constr_expr pr_glob_constr_pptac) (pr_and_constr_expr pr_lglob_constr_pptac)))
    pr_with_bindings_env
  ;
  register_print0 Tacarg.wit_destruction_arg
    (lift (pr_destruction_arg pr_constr_expr pr_lconstr_expr))
    (lift (pr_destruction_arg (pr_and_constr_expr pr_glob_constr_pptac) (pr_and_constr_expr pr_lglob_constr_pptac)))
    pr_destruction_arg_env
  ;
  register_basic_print0 Stdarg.wit_int int int int;
  register_basic_print0 Stdarg.wit_bool pr_bool pr_bool pr_bool;
  register_basic_print0 Stdarg.wit_unit pr_unit pr_unit pr_unit;
  register_basic_print0 Stdarg.wit_pre_ident str str str;
  register_basic_print0 Stdarg.wit_string qstring qstring qstring

let () =
  let printer _ _ prtac = prtac in
  declare_extra_genarg_pprule_with_level wit_tactic printer printer printer
  ltop (0,E)

let () =
  let pr_unit _ _ _ _ () = str "()" in
  let printer _ _ prtac = prtac in
  declare_extra_genarg_pprule_with_level wit_ltac printer printer pr_unit
  ltop (0,E)
