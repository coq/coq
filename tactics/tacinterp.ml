(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Constrintern
open Pattern
open Patternops
open Matching
open Pp
open Genredexpr
open Glob_term
open Glob_ops
open Tacred
open Errors
open Util
open Names
open Nameops
open Libnames
open Globnames
open Nametab
open Pfedit
open Proof_type
open Refiner
open Tacmach
open Tactic_debug
open Constrexpr
open Term
open Termops
open Tacexpr
open Hiddentac
open Genarg
open Stdarg
open Constrarg
open Printer
open Pretyping
open Evd
open Misctypes
open Miscops
open Locus
open Tacintern
open Taccoerce
open Proofview.Notations

let safe_msgnl s =
  let _ =
    try ppnl s with any ->
    ppnl (str "bug in the debugger: an exception is raised while printing debug information")
  in
  pp_flush () 

type value = tlevel generic_argument

(* Values for interpretation *)
type tacvalue =
  | VRTactic (* variant of unit returned by match. For historical reasons. *)
  | VFun of ltac_trace * value Id.Map.t *
      Id.t option list * glob_tactic_expr
  | VRec of value Id.Map.t ref * glob_tactic_expr

let (wit_tacvalue : (Empty.t, Empty.t, tacvalue) Genarg.genarg_type) =
  Genarg.create_arg None "tacvalue"

let of_tacvalue v = in_gen (topwit wit_tacvalue) v
let to_tacvalue v = out_gen (topwit wit_tacvalue) v

module Value = Taccoerce.Value

let dloc = Loc.ghost

let catching_error call_trace fail e =
  let e = Errors.push e in
  let inner_trace, e = match Exninfo.get e ltac_trace_info with
  | Some inner_trace -> inner_trace, e
  | None -> [], e
  in
  if List.is_empty call_trace & List.is_empty inner_trace then fail e
  else begin
    assert (Errors.noncritical e); (* preserved invariant *)
    let new_trace = inner_trace @ call_trace in
    let located_exc = Exninfo.add e ltac_trace_info new_trace in
    fail located_exc
  end

module TacStore = Geninterp.TacStore

let f_avoid_ids : Id.t list TacStore.field = TacStore.field ()
(* ids inherited from the call context (needed to get fresh ids) *)
let f_debug : debug_info TacStore.field = TacStore.field ()
let f_trace : ltac_trace TacStore.field = TacStore.field ()

let catch_error call_trace f x =
  try f x with e when Errors.noncritical e -> catching_error call_trace raise e
let catch_error_tac call_trace tac =
  Proofview.tclORELSE
    tac
    (catching_error call_trace Proofview.tclZERO)

(* Signature for interpretation: val_interp and interpretation functions *)
type interp_sign = Geninterp.interp_sign = {
  lfun : value Id.Map.t;
  extra : TacStore.t }

let curr_debug ist = match TacStore.get ist.extra f_debug with
| None -> DebugOff
| Some level -> level

let check_is_value v =
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then
    let v = to_tacvalue v in
    match v with
    | VRTactic -> (* These are goals produced by Match *)
      error "Immediate match producing tactics not allowed in local definitions."
    | _ -> ()
  else ()

(** TODO: unify printing of generic Ltac values in case of coercion failure. *)

(* Displays a value *)
let pr_value env v =
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then str "a tactic"
  else if has_type v (topwit wit_constr_context) then
    let c = out_gen (topwit wit_constr_context) v in
    match env with
    | Some env -> pr_lconstr_env env c
    | _ -> str "a term"
  else if has_type v (topwit wit_constr) then
    let c = out_gen (topwit wit_constr) v in
    match env with
    | Some env -> pr_lconstr_env env c
    | _ -> str "a term"
  else if has_type v (topwit wit_constr_under_binders) then
    let c = out_gen (topwit wit_constr_under_binders) v in
    match env with
    | Some env -> pr_lconstr_under_binders_env  env c
    | _ -> str "a term"
  else
    str "a value of type" ++ spc () ++ pr_argument_type (genarg_tag v)

let pr_inspect env expr result =
  let pp_expr = Pptactic.pr_glob_tactic env expr in
  let pp_result =
    if has_type result (topwit wit_tacvalue) then
    match to_tacvalue result with
    | VRTactic _ -> str "a VRTactic"
    | VFun (_, il, ul, b) ->
      let pp_body = Pptactic.pr_glob_tactic env b in
      let pr_sep () = str ", " in
      let pr_iarg (id, _) = pr_id id in
      let pr_uarg = function
      | None -> str "_"
      | Some id -> pr_id id
      in
      let pp_iargs = prlist_with_sep pr_sep pr_iarg (Id.Map.bindings il) in
      let pp_uargs = prlist_with_sep pr_sep pr_uarg ul in
      str "a VFun with body " ++ fnl() ++ pp_body ++ fnl() ++
        str "instantiated arguments " ++ fnl() ++ pp_iargs ++ fnl () ++
        str "uninstantiated arguments " ++ fnl() ++ pp_uargs
    | VRec _ -> str "a VRec"
    else
      let pp_type = pr_argument_type (genarg_tag result) in
      str "an object of type" ++ spc () ++ pp_type
  in
  pp_expr ++ fnl() ++ str "this is " ++ pp_result

(* Transforms an id into a constr if possible, or fails with Not_found *)
let constr_of_id env id =
  Term.mkVar (let _ = Environ.lookup_named id env in id)

(* To embed tactics *)

let ((tactic_in : (interp_sign -> glob_tactic_expr) -> Dyn.t),
     (tactic_out : Dyn.t -> (interp_sign -> glob_tactic_expr))) =
  Dyn.create "tactic"

let ((value_in : value -> Dyn.t),
     (value_out : Dyn.t -> value)) = Dyn.create "value"

let valueIn t = TacDynamic (Loc.ghost, value_in t)

(* Tactics table (TacExtend). *)

let tac_tab = Hashtbl.create 17

let add_tactic s t =
  if Hashtbl.mem tac_tab s then
    errorlabstrm ("Refiner.add_tactic: ")
      (str ("Cannot redeclare tactic "^s^"."));
  Hashtbl.add tac_tab s t

let overwriting_add_tactic s t =
  if Hashtbl.mem tac_tab s then begin
    Hashtbl.remove tac_tab s;
    msg_warning (strbrk ("Overwriting definition of tactic "^s))
  end;
  Hashtbl.add tac_tab s t

let lookup_tactic s =
  try
    Hashtbl.find tac_tab s
  with Not_found ->
    errorlabstrm "Refiner.lookup_tactic"
      (str"The tactic " ++ str s ++ str" is not installed.")

let () =
  Tacintern.set_assert_tactic_installed (fun opn ->
     let _ignored = lookup_tactic opn in ())

(** Generic arguments : table of interpretation functions *)

let push_trace (loc, ck) ist = match TacStore.get ist.extra f_trace with
| None -> [1, loc, ck]
| Some trace ->
  match trace with
  | (n,loc',ck')::trl when Pervasives.(=) ck ck' -> (n+1,loc,ck)::trl (** FIXME *)
  | trl -> (1,loc,ck)::trl

let extract_trace ist = match TacStore.get ist.extra f_trace with
| None -> []
| Some l -> l

let propagate_trace ist loc id v =
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then
    let tacv = to_tacvalue v in
    match tacv with
    | VFun (_,lfun,it,b) ->
        let t = if List.is_empty it then b else TacFun (it,b) in
        let ans = VFun (push_trace(loc,LtacVarCall (id,t)) ist,lfun,it,b) in
        of_tacvalue ans
    | _ ->  v
  else v

let append_trace trace v =
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then
    match to_tacvalue v with
    | VFun (trace',lfun,it,b) -> of_tacvalue (VFun (trace'@trace,lfun,it,b))
    | _ -> v
  else v

(* Dynamically check that an argument is a tactic *)
let coerce_to_tactic loc id v =
  let v = Value.normalize v in
  let fail () = user_err_loc
    (loc, "", str "Variable " ++ pr_id id ++ str " should be bound to a tactic.")
  in
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then
    let tacv = to_tacvalue v in
    match tacv with
    | VFun _ | VRTactic -> v
    | _ -> fail ()
  else fail ()

(* External tactics *)
let print_xml_term = ref (fun _ -> failwith "print_xml_term unset")
let declare_xml_printer f = print_xml_term := f

let internalise_tacarg ch = G_xml.parse_tactic_arg ch

let extern_tacarg ch env sigma v = match Value.to_constr v with
| None ->
  error "Only externing of closed terms is implemented."
| Some c -> !print_xml_term ch env sigma c

let extern_request ch req gl la =
  output_string ch "<REQUEST req=\""; output_string ch req;
  output_string ch "\">\n";
  List.iter (pf_apply (extern_tacarg ch) gl) la;
  output_string ch "</REQUEST>\n"

let value_of_ident id =
  in_gen (topwit wit_intro_pattern) (Loc.ghost, IntroIdentifier id)

let (+++) lfun1 lfun2 = Id.Map.fold Id.Map.add lfun1 lfun2

let extend_values_with_bindings (ln,lm) lfun =
  let of_cub c = match c with
  | [], c -> Value.of_constr c
  | _ -> in_gen (topwit wit_constr_under_binders) c
  in
  (* For compatibility, bound variables are visible only if no other
     binding of the same name exists *)
  let accu = Id.Map.map value_of_ident ln in
  let accu = lfun +++ accu in
  Id.Map.fold (fun id c accu -> Id.Map.add id (of_cub c) accu) lm accu

(***************************************************************************)
(* Evaluation/interpretation *)

let is_variable env id =
  Id.List.mem id (ids_of_named_context (Environ.named_context env))

(* Debug reference *)
let debug = ref DebugOff

(* Sets the debugger mode *)
let set_debug pos = debug := pos

(* Gives the state of debug *)
let get_debug () = !debug

let debugging_step ist pp = match curr_debug ist with
  | DebugOn lev ->
      safe_msgnl (str "Level " ++ int lev ++ str": " ++ pp () ++ fnl())
  | _ -> ()

let debugging_exception_step ist signal_anomaly e pp =
  let explain_exc =
    if signal_anomaly then explain_logic_error
    else explain_logic_error_no_anomaly in
  debugging_step ist (fun () ->
    pp() ++ spc() ++ str "raised the exception" ++ fnl() ++ !explain_exc e)

let error_ltac_variable loc id env v s =
   user_err_loc (loc, "", str "Ltac variable " ++ pr_id id ++
   strbrk " is bound to" ++ spc () ++ pr_value env v ++ spc () ++
   strbrk "which cannot be coerced to " ++ str s ++ str".")

(* Raise Not_found if not in interpretation sign *)
let try_interp_ltac_var coerce ist env (loc,id) =
  let v = Id.Map.find id ist.lfun in
  try coerce v with CannotCoerceTo s -> error_ltac_variable loc id env v s

let interp_ltac_var coerce ist env locid =
  try try_interp_ltac_var coerce ist env locid
  with Not_found -> anomaly (str "Detected '" ++ Id.print (snd locid) ++ str "' as ltac var at interning time")

let interp_ident_gen fresh ist env id =
  try try_interp_ltac_var (coerce_to_ident fresh env) ist (Some env) (dloc,id)
  with Not_found -> id

let interp_ident = interp_ident_gen false
let interp_fresh_ident = interp_ident_gen true
let pf_interp_ident id gl = interp_ident_gen false id (pf_env gl)
let pf_interp_fresh_ident id gl = interp_ident_gen true id (pf_env gl)

(* Interprets an optional identifier which must be fresh *)
let interp_fresh_name ist env = function
  | Anonymous -> Anonymous
  | Name id -> Name (interp_fresh_ident ist env id)

let interp_intro_pattern_var loc ist env id =
  try try_interp_ltac_var (coerce_to_intro_pattern env) ist (Some env) (loc,id)
  with Not_found -> IntroIdentifier id

let interp_hint_base ist s =
  try try_interp_ltac_var coerce_to_hint_base ist None (dloc,Id.of_string s)
  with Not_found -> s

let interp_int ist locid =
  try try_interp_ltac_var coerce_to_int ist None locid
  with Not_found ->
    user_err_loc(fst locid,"interp_int",
      str "Unbound variable "  ++ pr_id (snd locid) ++ str".")

let interp_int_or_var ist = function
  | ArgVar locid -> interp_int ist locid
  | ArgArg n -> n

let interp_int_or_var_as_list ist = function
  | ArgVar (_,id as locid) ->
      (try coerce_to_int_or_var_list (Id.Map.find id ist.lfun)
       with Not_found | CannotCoerceTo _ -> [ArgArg (interp_int ist locid)])
  | ArgArg n as x -> [x]

let interp_int_or_var_list ist l =
  List.flatten (List.map (interp_int_or_var_as_list ist) l)

(* Interprets a bound variable (especially an existing hypothesis) *)
let interp_hyp ist gl (loc,id as locid) =
  let env = pf_env gl in
  (* Look first in lfun for a value coercible to a variable *)
  try try_interp_ltac_var (coerce_to_hyp env) ist (Some env) locid
  with Not_found ->
  (* Then look if bound in the proof context at calling time *)
  if is_variable env id then id
  else user_err_loc (loc,"eval_variable",
    str "No such hypothesis: " ++ pr_id id ++ str ".")

let interp_hyp_list_as_list ist gl (loc,id as x) =
  try coerce_to_hyp_list (pf_env gl) (Id.Map.find id ist.lfun)
  with Not_found | CannotCoerceTo _ -> [interp_hyp ist gl x]

let interp_hyp_list ist gl l =
  List.flatten (List.map (interp_hyp_list_as_list ist gl) l)

let interp_move_location ist gl = function
  | MoveAfter id -> MoveAfter (interp_hyp ist gl id)
  | MoveBefore id -> MoveBefore (interp_hyp ist gl id)
  | MoveFirst -> MoveFirst
  | MoveLast -> MoveLast

let interp_reference ist env = function
  | ArgArg (_,r) -> r
  | ArgVar (loc, id) ->
    try try_interp_ltac_var (coerce_to_reference env) ist (Some env) (loc, id)
    with Not_found ->
      try
        let (v, _, _) = Environ.lookup_named id env in
        VarRef v
      with Not_found -> error_global_not_found_loc loc (qualid_of_ident id)

let pf_interp_reference ist gl = interp_reference ist (pf_env gl)

let interp_inductive ist = function
  | ArgArg r -> r
  | ArgVar locid -> interp_ltac_var coerce_to_inductive ist None locid

let try_interp_evaluable env (loc, id) =
  let v = Environ.lookup_named id env in
  match v with
  | (_, Some _, _) -> EvalVarRef id
  | _ -> error_not_evaluable (VarRef id)

let interp_evaluable ist env = function
  | ArgArg (r,Some (loc,id)) ->
    (* Maybe [id] has been introduced by Intro-like tactics *)
    begin
      try try_interp_evaluable env (loc, id)
      with Not_found ->
        match r with
        | EvalConstRef _ -> r
        | _ -> error_global_not_found_loc loc (qualid_of_ident id)
    end
  | ArgArg (r,None) -> r
  | ArgVar (loc, id) ->
    try try_interp_ltac_var (coerce_to_evaluable_ref env) ist (Some env) (loc, id)
    with Not_found ->
      try try_interp_evaluable env (loc, id)
      with Not_found -> error_global_not_found_loc loc (qualid_of_ident id)

(* Interprets an hypothesis name *)
let interp_occurrences ist occs =
  Locusops.occurrences_map (interp_int_or_var_list ist) occs

let interp_hyp_location ist gl ((occs,id),hl) =
  ((interp_occurrences ist occs,interp_hyp ist gl id),hl)

let interp_clause ist gl { onhyps=ol; concl_occs=occs } =
  { onhyps=Option.map(List.map (interp_hyp_location ist gl)) ol;
    concl_occs=interp_occurrences ist occs }

(* Interpretation of constructions *)

(* Extract the constr list from lfun *)
let extract_ltac_constr_values ist env =
  let fold id v accu =
    try
      let c = coerce_to_constr env v in
      Id.Map.add id c accu
    with CannotCoerceTo _ -> accu
  in
  Id.Map.fold fold ist.lfun Id.Map.empty
(** ppedrot: I have changed the semantics here. Before this patch, closure was
    implemented as a list and a variable could be bound several times with
    different types, resulting in its possible appearance on both sides. This
    could barely be defined as a feature... *)

(* Extract the identifier list from lfun: join all branches (what to do else?)*)
let rec intropattern_ids (loc,pat) = match pat with
  | IntroIdentifier id -> [id]
  | IntroOrAndPattern ll ->
      List.flatten (List.map intropattern_ids (List.flatten ll))
  | IntroInjection l ->
      List.flatten (List.map intropattern_ids l)
  | IntroWildcard | IntroAnonymous | IntroFresh _ | IntroRewrite _
  | IntroForthcoming _ -> []

let rec extract_ids ids lfun =
  let fold id v accu =
    let v = Value.normalize v in
    if has_type v (topwit wit_intro_pattern) then
      let (_, ipat) = out_gen (topwit wit_intro_pattern) v in
      if Id.List.mem id ids then accu
      else accu @ intropattern_ids (dloc, ipat)
    else accu
  in
  Id.Map.fold fold lfun []

let default_fresh_id = Id.of_string "H"

let interp_fresh_id ist env l =
  let ids = List.map_filter (function ArgVar (_, id) -> Some id | _ -> None) l in
  let avoid = match TacStore.get ist.extra f_avoid_ids with
  | None -> []
  | Some l -> l
  in
  let avoid = (extract_ids ids ist.lfun) @ avoid in
  let id =
    if List.is_empty l then default_fresh_id
    else
      let s =
	String.concat "" (List.map (function
	  | ArgArg s -> s
	  | ArgVar (_,id) -> Id.to_string (interp_ident ist env id)) l) in
      let s = if Lexer.is_keyword s then s^"0" else s in
      Id.of_string s in
  Tactics.fresh_id_in_env avoid id env

let pf_interp_fresh_id ist gl = interp_fresh_id ist (pf_env gl)

let interp_gen kind ist allow_patvar flags env sigma (c,ce) =
  let constrvars = extract_ltac_constr_values ist env in
  let vars = (constrvars, ist.lfun) in
  let c = match ce with
  | None -> c
    (* If at toplevel (ce<>None), the error can be due to an incorrect
       context at globalization time: we retype with the now known
       intros/lettac/inversion hypothesis names *)
  | Some c ->
      let ltacvars = Id.Map.domain constrvars in
      let bndvars = Id.Map.domain ist.lfun in
      let ltacdata = (ltacvars, bndvars) in
      intern_gen kind ~allow_patvar ~ltacvars:ltacdata sigma env c
  in
  let trace =
    push_trace (loc_of_glob_constr c,LtacConstrInterp (c,vars)) ist in
  let (evd,c) =
    catch_error trace (understand_ltac flags sigma env vars kind) c
  in
  db_constr (curr_debug ist) env c;
  (evd,c)

let constr_flags = {
  use_typeclasses = true;
  use_unif_heuristics = true;
  use_hook = Some solve_by_implicit_tactic;
  fail_evar = true;
  expand_evars = true }

(* Interprets a constr; expects evars to be solved *)
let interp_constr_gen kind ist env sigma c =
  interp_gen kind ist false constr_flags env sigma c

let interp_constr = interp_constr_gen WithoutTypeConstraint

let interp_type = interp_constr_gen IsType

let open_constr_use_classes_flags = {
  use_typeclasses = true;
  use_unif_heuristics = true;
  use_hook = Some solve_by_implicit_tactic;
  fail_evar = false;
  expand_evars = true }

let open_constr_no_classes_flags = {
  use_typeclasses = false;
  use_unif_heuristics = true;
  use_hook = Some solve_by_implicit_tactic;
  fail_evar = false;
  expand_evars = true }

let pure_open_constr_flags = {
  use_typeclasses = false;
  use_unif_heuristics = true;
  use_hook = None;
  fail_evar = false;
  expand_evars = false }

(* Interprets an open constr *)
let interp_open_constr ?(expected_type=WithoutTypeConstraint) ist =
  let flags =
    if expected_type == WithoutTypeConstraint then open_constr_no_classes_flags
    else open_constr_use_classes_flags in
  interp_gen expected_type ist false flags

let interp_pure_open_constr ist =
  interp_gen WithoutTypeConstraint ist false pure_open_constr_flags

let interp_typed_pattern ist env sigma (c,_) =
  let sigma, c =
    interp_gen WithoutTypeConstraint ist true pure_open_constr_flags env sigma c in
  pattern_of_constr sigma c

(* Interprets a constr expression casted by the current goal *)
let pf_interp_casted_constr ist gl c =
  interp_constr_gen (OfType (pf_concl gl)) ist (pf_env gl) (project gl) c

(* Interprets a constr expression *)
let pf_interp_constr ist gl =
  interp_constr ist (pf_env gl) (project gl)

let interp_constr_in_compound_list inj_fun dest_fun interp_fun ist env sigma l =
  let try_expand_ltac_var sigma x =
    try match dest_fun x with
    | GVar (_,id), _ ->
      let v = Id.Map.find id ist.lfun in
      sigma, List.map inj_fun (coerce_to_constr_list env v)
    | _ ->
        raise Not_found
    with CannotCoerceTo _ | Not_found ->
      (* dest_fun, List.assoc may raise Not_found *)
      let sigma, c = interp_fun ist env sigma x in
      sigma, [c] in
  let sigma, l = List.fold_map try_expand_ltac_var sigma l in
  sigma, List.flatten l

let interp_constr_list ist env sigma c =
  interp_constr_in_compound_list (fun x -> x) (fun x -> x) interp_constr ist env sigma c

let interp_open_constr_list =
  interp_constr_in_compound_list (fun x -> x) (fun x -> x) interp_open_constr

let interp_auto_lemmas ist env sigma lems =
  let local_sigma, lems = interp_open_constr_list ist env sigma lems in
  List.map (fun lem -> (local_sigma,lem)) lems

(* Interprets a type expression *)
let pf_interp_type ist gl =
  interp_type ist (pf_env gl) (project gl)

(* Interprets a reduction expression *)
let interp_unfold ist env (occs,qid) =
  (interp_occurrences ist occs,interp_evaluable ist env qid)

let interp_flag ist env red =
  { red with rConst = List.map (interp_evaluable ist env) red.rConst }

let interp_constr_with_occurrences ist sigma env (occs,c) =
  let (sigma,c_interp) = interp_constr ist sigma env c in
  sigma , (interp_occurrences ist occs, c_interp)

let interp_typed_pattern_with_occurrences ist env sigma (occs,c) =
  let sign,p = interp_typed_pattern ist env sigma c in
  sign, (interp_occurrences ist occs, p)

let interp_closed_typed_pattern_with_occurrences ist env sigma occl =
  snd (interp_typed_pattern_with_occurrences ist env sigma occl)

let interp_constr_with_occurrences_and_name_as_list =
  interp_constr_in_compound_list
    (fun c -> ((AllOccurrences,c),Anonymous))
    (function ((occs,c),Anonymous) when occs == AllOccurrences -> c
      | _ -> raise Not_found)
    (fun ist env sigma (occ_c,na) ->
      let (sigma,c_interp) = interp_constr_with_occurrences ist env sigma occ_c in
      sigma, (c_interp,
       interp_fresh_name ist env na))

let interp_red_expr ist sigma env = function
  | Unfold l -> sigma , Unfold (List.map (interp_unfold ist env) l)
  | Fold l ->
    let (sigma,l_interp) = interp_constr_list ist env sigma l in
    sigma , Fold l_interp
  | Cbv f -> sigma , Cbv (interp_flag ist env f)
  | Cbn f -> sigma , Cbn (interp_flag ist env f)
  | Lazy f -> sigma , Lazy (interp_flag ist env f)
  | Pattern l ->
    let (sigma,l_interp) =
      List.fold_right begin fun c (sigma,acc) ->
	let (sigma,c_interp) = interp_constr_with_occurrences ist env sigma c in
	sigma , c_interp :: acc
      end l (sigma,[])
    in
    sigma , Pattern l_interp
  | Simpl o ->
    sigma , Simpl (Option.map (interp_closed_typed_pattern_with_occurrences ist env sigma) o)
  | CbvVm o ->
    sigma , CbvVm (Option.map (interp_closed_typed_pattern_with_occurrences ist env sigma) o)
  | CbvNative o ->
    sigma , CbvNative (Option.map (interp_closed_typed_pattern_with_occurrences ist env sigma) o)
  | (Red _ |  Hnf | ExtraRedExpr _ as r) -> sigma , r

let pf_interp_red_expr ist gl = interp_red_expr ist (project gl) (pf_env gl)

let interp_may_eval f ist gl = function
  | ConstrEval (r,c) ->
      let (sigma,redexp) = pf_interp_red_expr ist gl r in
      let (sigma,c_interp) = f ist { gl with sigma=sigma } c in
      sigma , pf_reduction_of_red_expr gl redexp c_interp
  | ConstrContext ((loc,s),c) ->
      (try
	let (sigma,ic) = f ist gl c
	and ctxt = coerce_to_constr_context (Id.Map.find s ist.lfun) in
	sigma , subst_meta [special_meta,ic] ctxt
      with
	| Not_found ->
	    user_err_loc (loc, "interp_may_eval",
	    str "Unbound context identifier" ++ pr_id s ++ str"."))
  | ConstrTypeOf c ->
      let (sigma,c_interp) = f ist gl c in
      sigma , pf_type_of gl c_interp
  | ConstrTerm c ->
     try
	f ist gl c
     with reraise ->
       let reraise = Errors.push reraise in
       debugging_exception_step ist false reraise (fun () ->
         str"interpretation of term " ++ pr_glob_constr_env (pf_env gl) (fst c));
       raise reraise

(* Interprets a constr expression possibly to first evaluate *)
let interp_constr_may_eval ist gl c =
  let (sigma,csr) =
    try
      interp_may_eval pf_interp_constr ist gl c
    with reraise ->
      let reraise = Errors.push reraise in
      debugging_exception_step ist false reraise
        (fun () -> str"evaluation of term");
      raise reraise
  in
  begin
    db_constr (curr_debug ist) (pf_env gl) csr;
    sigma , csr
  end

(** TODO: should use dedicated printers *)
let rec message_of_value gl v =
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then str "<tactic>"
  else if has_type v (topwit wit_constr) then
    pr_constr_env (pf_env gl) (out_gen (topwit wit_constr) v)
  else if has_type v (topwit wit_constr_under_binders) then
    let c = out_gen (topwit wit_constr_under_binders) v in
    pr_constr_under_binders_env (pf_env gl) c
  else if has_type v (topwit wit_unit) then str "()"
  else if has_type v (topwit wit_int) then int (out_gen (topwit wit_int) v)
  else if has_type v (topwit wit_intro_pattern) then
    pr_intro_pattern (out_gen (topwit wit_intro_pattern) v)
  else if has_type v (topwit wit_constr_context) then
    pr_constr_env (pf_env gl) (out_gen (topwit wit_constr_context) v)
  else match Value.to_list v with
  | Some l ->
    let print v = message_of_value gl v in
    prlist_with_sep spc print l
  | None ->
    str "<abstr>" (** TODO *)

let interp_message_token ist gl = function
  | MsgString s -> str s
  | MsgInt n -> int n
  | MsgIdent (loc,id) ->
      let v =
	try Id.Map.find id ist.lfun
	with Not_found -> user_err_loc (loc,"",pr_id id ++ str" not found.") in
      message_of_value gl v

let interp_message_nl ist gl = function
  | [] -> mt()
  | l -> prlist_with_sep spc (interp_message_token ist gl) l ++ fnl()

let interp_message ist gl l =
  (* Force evaluation of interp_message_token so that potential errors
     are raised now and not at printing time *)
  prlist (fun x -> spc () ++ x) (List.map (interp_message_token ist gl) l)

let rec interp_intro_pattern ist gl = function
  | loc, IntroOrAndPattern l ->
      loc, IntroOrAndPattern (interp_or_and_intro_pattern ist gl l)
  | loc, IntroInjection l ->
      loc, IntroInjection (interp_intro_pattern_list_as_list ist gl l)
  | loc, IntroIdentifier id ->
      loc, interp_intro_pattern_var loc ist (pf_env gl) id
  | loc, IntroFresh id ->
      loc, IntroFresh (interp_fresh_ident ist (pf_env gl) id)
  | loc, (IntroWildcard | IntroAnonymous | IntroRewrite _ | IntroForthcoming _)
      as x -> x

and interp_or_and_intro_pattern ist gl =
  List.map (interp_intro_pattern_list_as_list ist gl)

and interp_intro_pattern_list_as_list ist gl = function
  | [loc,IntroIdentifier id] as l ->
      (try coerce_to_intro_pattern_list loc (pf_env gl) (Id.Map.find id ist.lfun)
       with Not_found | CannotCoerceTo _ ->
	List.map (interp_intro_pattern ist gl) l)
  | l -> List.map (interp_intro_pattern ist gl) l

let interp_in_hyp_as ist gl (id,ipat) =
  (interp_hyp ist gl id,Option.map (interp_intro_pattern ist gl) ipat)

let interp_quantified_hypothesis ist = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp id ->
      try try_interp_ltac_var coerce_to_quantified_hypothesis ist None(dloc,id)
      with Not_found -> NamedHyp id

let interp_binding_name ist = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp id ->
      (* If a name is bound, it has to be a quantified hypothesis *)
      (* user has to use other names for variables if these ones clash with *)
      (* a name intented to be used as a (non-variable) identifier *)
      try try_interp_ltac_var coerce_to_quantified_hypothesis ist None(dloc,id)
      with Not_found -> NamedHyp id

let interp_declared_or_quantified_hypothesis ist gl = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp id ->
      let env = pf_env gl in
      try try_interp_ltac_var
	    (coerce_to_decl_or_quant_hyp env) ist (Some env) (dloc,id)
      with Not_found -> NamedHyp id

let interp_binding ist env sigma (loc,b,c) =
  let sigma, c = interp_open_constr ist env sigma c in
  sigma, (loc,interp_binding_name ist b,c)

let interp_bindings ist env sigma = function
| NoBindings ->
    sigma, NoBindings
| ImplicitBindings l ->
    let sigma, l = interp_open_constr_list ist env sigma l in   
    sigma, ImplicitBindings l
| ExplicitBindings l ->
    let sigma, l = List.fold_map (interp_binding ist env) sigma l in
    sigma, ExplicitBindings l

let interp_constr_with_bindings ist env sigma (c,bl) =
  let sigma, bl = interp_bindings ist env sigma bl in
  let sigma, c = interp_open_constr ist env sigma c in
  sigma, (c,bl)

let interp_open_constr_with_bindings ist env sigma (c,bl) =
  let sigma, bl = interp_bindings ist env sigma bl in
  let sigma, c = interp_open_constr ist env sigma c in
  sigma, (c, bl)

let loc_of_bindings = function
| NoBindings -> Loc.ghost
| ImplicitBindings l -> loc_of_glob_constr (fst (List.last l))
| ExplicitBindings l -> pi1 (List.last l)

let interp_open_constr_with_bindings_loc ist env sigma ((c,_),bl as cb) =
  let loc1 = loc_of_glob_constr c in
  let loc2 = loc_of_bindings bl in
  let loc = if Loc.is_ghost loc2 then loc1 else Loc.merge loc1 loc2 in
  let sigma, cb = interp_open_constr_with_bindings ist env sigma cb in
  sigma, (loc,cb)

let interp_induction_arg ist gl arg =
  let env = pf_env gl and sigma = project gl in
  match arg with
  | ElimOnConstr c ->
      ElimOnConstr (interp_constr_with_bindings ist env sigma c)
  | ElimOnAnonHyp n as x -> x
  | ElimOnIdent (loc,id) ->
      let error () = user_err_loc (loc, "",
        strbrk "Cannot coerce " ++ pr_id id ++
        strbrk " neither to a quantified hypothesis nor to a term.")
      in
      let try_cast_id id' =
        if Tactics.is_quantified_hypothesis id' gl
        then ElimOnIdent (loc,id')
        else
          (try ElimOnConstr (sigma,(constr_of_id env id',NoBindings))
          with Not_found ->
            user_err_loc (loc,"",
            pr_id id ++ strbrk " binds to " ++ pr_id id' ++ strbrk " which is neither a declared or a quantified hypothesis."))
      in
      try
        (** FIXME: should be moved to taccoerce *)
        let v = Id.Map.find id ist.lfun in
        let v = Value.normalize v in
        if has_type v (topwit wit_intro_pattern) then
          let v = out_gen (topwit wit_intro_pattern) v in
          match v with
          | _, IntroIdentifier id -> try_cast_id id
          | _ -> error ()
        else if has_type v (topwit wit_var) then
          let id = out_gen (topwit wit_var) v in
          try_cast_id id
        else if has_type v (topwit wit_int) then
          ElimOnAnonHyp (out_gen (topwit wit_int) v)
        else match Value.to_constr v with
        | None -> error ()
        | Some c -> ElimOnConstr (sigma,(c,NoBindings))
      with Not_found ->
	(* We were in non strict (interactive) mode *)
	if Tactics.is_quantified_hypothesis id gl then
          ElimOnIdent (loc,id)
	else
          let c = (GVar (loc,id),Some (CRef (Ident (loc,id)))) in
          let (sigma,c) = interp_constr ist env sigma c in
          ElimOnConstr (sigma,(c,NoBindings))

(* Associates variables with values and gives the remaining variables and
   values *)
let head_with_value (lvar,lval) =
  let rec head_with_value_rec lacc = function
    | ([],[]) -> (lacc,[],[])
    | (vr::tvr,ve::tve) ->
      (match vr with
      |	None -> head_with_value_rec lacc (tvr,tve)
      | Some v -> head_with_value_rec ((v,ve)::lacc) (tvr,tve))
    | (vr,[]) -> (lacc,vr,[])
    | ([],ve) -> (lacc,[],ve)
  in
  head_with_value_rec [] (lvar,lval)

(* Gives a context couple if there is a context identifier *)
let give_context ctxt = function
  | None -> Id.Map.empty
  | Some id -> Id.Map.singleton id (in_gen (topwit wit_constr_context) ctxt)

(* Reads a pattern by substituting vars of lfun *)
let use_types = false

let eval_pattern lfun ist env sigma (_,pat as c) =
  if use_types then
    snd (interp_typed_pattern ist env sigma c)
  else
    instantiate_pattern sigma lfun pat

let read_pattern lfun ist env sigma = function
  | Subterm (b,ido,c) -> Subterm (b,ido,eval_pattern lfun ist env sigma c)
  | Term c -> Term (eval_pattern lfun ist env sigma c)

(* Reads the hypotheses of a Match Context rule *)
let cons_and_check_name id l =
  if Id.List.mem id l then
    user_err_loc (dloc,"read_match_goal_hyps",
      strbrk ("Hypothesis pattern-matching variable "^(Id.to_string id)^
      " used twice in the same pattern."))
  else id::l

let rec read_match_goal_hyps lfun ist env sigma lidh = function
  | (Hyp ((loc,na) as locna,mp))::tl ->
      let lidh' = name_fold cons_and_check_name na lidh in
      Hyp (locna,read_pattern lfun ist env sigma mp)::
	(read_match_goal_hyps lfun ist env sigma lidh' tl)
  | (Def ((loc,na) as locna,mv,mp))::tl ->
      let lidh' = name_fold cons_and_check_name na lidh in
      Def (locna,read_pattern lfun ist env sigma mv, read_pattern lfun ist env sigma mp)::
	(read_match_goal_hyps lfun ist env sigma lidh' tl)
  | [] -> []

(* Reads the rules of a Match Context or a Match *)
let rec read_match_rule lfun ist env sigma = function
  | (All tc)::tl -> (All tc)::(read_match_rule lfun ist env sigma tl)
  | (Pat (rl,mp,tc))::tl ->
      Pat (read_match_goal_hyps lfun ist env sigma [] rl, read_pattern lfun ist env sigma mp,tc)
      :: read_match_rule lfun ist env sigma tl
  | [] -> []

(* For Match Context and Match *)
exception Not_coherent_metas
exception Eval_fail of std_ppcmds

let is_match_catchable = function
  | PatternMatchingFailure | Eval_fail _ -> true
  | e -> Logic.catchable_exception e

let equal_instances gl (ctx',c') (ctx,c) =
  (* How to compare instances? Do we want the terms to be convertible?
     unifiable? Do we want the universe levels to be relevant? 
     (historically, conv_x is used) *)
  List.equal Id.equal ctx ctx' && pf_conv_x gl c' c

(* Verifies if the matched list is coherent with respect to lcm *)
(* While non-linear matching is modulo eq_constr in matches, merge of *)
(* different instances of the same metavars is here modulo conversion... *)
let verify_metas_coherence gl (ln1,lcm) (ln,lm) =
  let merge id oc1 oc2 = match oc1, oc2 with
  | None, None -> None
  | None, Some c | Some c, None -> Some c
  | Some c1, Some c2 ->
    if equal_instances gl c1 c2 then Some c1
    else raise Not_coherent_metas
  in
  (** ppedrot: Is that even correct? *)
  let merged = ln +++ ln1 in
  (merged, Id.Map.merge merge lcm lm)

let adjust (l, lc) = (l, Id.Map.map (fun c -> [], c) lc)


(* spiwack: a small wrapper around the [Matching] module *)

type 'a _matching_result =
    { s_sub : bound_ident_map * patvar_map ;
      s_ctx : 'a ;
      s_nxt : 'a matching_result }
and 'a matching_result = 'a _matching_result Proofview.glist Proofview.tactic

type 'a _extended_matching_result =
    { e_ctx : 'a;
      e_sub : bound_ident_map * extended_patvar_map; }

let push_id_couple id name env = match name with
| Name idpat ->
  Id.Map.add idpat (Value.of_constr (mkVar id)) env
| Anonymous -> env

let match_pat refresh lmatch hyp gl = function
| Term t ->
  let hyp = if refresh then refresh_universes_strict hyp else hyp in
  begin
    try
      let lmeta = extended_matches t hyp in
      let lmeta = verify_metas_coherence gl lmatch lmeta in
      let ans = { e_ctx = Id.Map.empty; e_sub = lmeta; } in
      IStream.cons ans IStream.empty
    with PatternMatchingFailure | Not_coherent_metas -> IStream.empty
  end
| Subterm (b,ic,t) ->
  let hyp = if refresh then refresh_universes_strict hyp else hyp in
  let matches = match_subterm_gen b t hyp in
  let filter s =
    try
      let lmeta = verify_metas_coherence gl lmatch (adjust s.m_sub) in
      let context = give_context s.m_ctx ic in
      Some { e_ctx = context; e_sub = lmeta; }
    with Not_coherent_metas -> None
  in
  IStream.map_filter filter matches

(* Tries to match one hypothesis pattern with a list of hypotheses *)
let apply_one_mhyp_context gl lmatch (hypname,patv,pat) lhyps =
  let rec apply_one_mhyp_context_rec = function
    | [] ->
      IStream.empty
    | (id, b, hyp as hd) :: tl ->
      (match patv with
      | None ->
        let refresh = not (Option.is_empty b) in
        let ans = IStream.thunk (lazy (match_pat refresh lmatch hyp gl pat)) in
        let map s =
          let context = (push_id_couple id hypname s.e_ctx), hd in
          { e_ctx = context; e_sub = s.e_sub; }
        in
        let next = lazy (apply_one_mhyp_context_rec tl) in
        IStream.app (IStream.map map ans) (IStream.thunk next)
      | Some patv ->
        match b with
        | Some body ->
          let body = match_pat false lmatch body gl patv in
          let map_body s1 =
            let types = lazy (match_pat true s1.e_sub hyp gl pat) in
            let map_types s2 =
              let env = push_id_couple id hypname s1.e_ctx in
              let context = (env +++ s2.e_ctx), hd in
              { e_ctx = context; e_sub = s2.e_sub; }
            in
            IStream.map map_types (IStream.thunk types)
          in
          let next = IStream.thunk (lazy (apply_one_mhyp_context_rec tl)) in
          let body = IStream.map map_body body in
          IStream.app (IStream.concat body) next
        | None -> apply_one_mhyp_context_rec tl)
  in
  apply_one_mhyp_context_rec lhyps

(* misc *)

let mk_constr_value ist gl c =
  let (sigma,c_interp) = pf_interp_constr ist gl c in
  sigma, Value.of_constr c_interp
let mk_open_constr_value ist gl c = 
  let (sigma,c_interp) = pf_apply (interp_open_constr ist) gl c in
  sigma, Value.of_constr c_interp
let mk_hyp_value ist gl c = Value.of_constr (mkVar (interp_hyp ist gl c))
let mk_int_or_var_value ist c = in_gen (topwit wit_int) (interp_int_or_var ist c)

let pack_sigma (sigma,c) = {it=c;sigma=sigma;}

let extend_gl_hyps { it=gl ; sigma=sigma } sign =
  Goal.V82.new_goal_with sigma gl sign

(* Interprets an l-tac expression into a value *)
let rec val_interp ist (tac:glob_tactic_expr) : typed_generic_argument Proofview.glist Proofview.tactic =
  let value_interp ist = match tac with
  (* Immediate evaluation *)
  | TacFun (it,body) ->
    let v = VFun (extract_trace ist,ist.lfun,it,body) in
    (Proofview.Goal.return (of_tacvalue v))
  | TacLetIn (true,l,u) -> interp_letrec ist l u
  | TacLetIn (false,l,u) -> interp_letin ist l u
  | TacMatchGoal (lz,lr,lmr) -> interp_match_goal ist lz lr lmr
  | TacMatch (lz,c,lmr) -> interp_match ist lz c lmr
  | TacArg (loc,a) -> interp_tacarg ist a
  (* Delayed evaluation *)
  | t ->
    let v = VFun (extract_trace ist,ist.lfun,[],t) in
    (Proofview.Goal.return (of_tacvalue v))
  in check_for_interrupt ();
  match curr_debug ist with
      (* arnaud: todo: debug
  | DebugOn lev ->
      debug_prompt lev gl tac (fun v -> value_interp {ist with debug=v})
      *)
  | _ -> value_interp ist
      

and eval_tactic ist = function
  | TacAtom (loc,t) ->
      let call = LtacAtomCall t in
      catch_error_tac (push_trace(loc,call) ist) (interp_atomic ist t)
  | TacFun _ | TacLetIn _ -> assert false
  | TacMatchGoal _ | TacMatch _ -> assert false
  | TacId s -> Proofview.V82.tactic begin fun gl ->
    let res = tclIDTAC_MESSAGE (interp_message_nl ist gl s) gl in
    db_breakpoint (curr_debug ist) s; res
  end
  | TacFail (n,s) ->
      Proofview.V82.tactic begin fun gl ->
        tclFAIL (interp_int_or_var ist n) (interp_message ist gl s) gl
      end
  | TacProgress tac -> Proofview.tclPROGRESS (interp_tactic ist tac)
  | TacShowHyps tac ->
      (* arnaud: todo:
         tclSHOWHYPS (interp_tactic ist tac)*)
      assert false
  | TacAbstract (tac,ido) ->
      Proofview.V82.tactic begin fun gl -> Tactics.tclABSTRACT
        (Option.map (pf_interp_ident ist gl) ido) (interp_tactic ist tac) gl
      end
  | TacThen (t1,tf,t,tl) ->
      Tacticals.New.tclTHENS3PARTS (interp_tactic ist t1)
	(Array.map (interp_tactic ist) tf) (interp_tactic ist t) (Array.map (interp_tactic ist) tl)
  | TacThens (t1,tl) -> Tacticals.New.tclTHENS (interp_tactic ist t1) (List.map (interp_tactic ist) tl)
  | TacDo (n,tac) -> Tacticals.New.tclDO (interp_int_or_var ist n) (interp_tactic ist tac)
  | TacTimeout (n,tac) -> Tacticals.New.tclTIMEOUT (interp_int_or_var ist n) (interp_tactic ist tac)
  | TacTry tac -> Tacticals.New.tclTRY (interp_tactic ist tac)
  | TacRepeat tac -> Tacticals.New.tclREPEAT (interp_tactic ist tac)
  | TacOrelse (tac1,tac2) ->
      Tacticals.New.tclORELSE (interp_tactic ist tac1) (interp_tactic ist tac2)
  | TacFirst l -> Tacticals.New.tclFIRST (List.map (interp_tactic ist) l)
  | TacSolve l -> Tacticals.New.tclSOLVE (List.map (interp_tactic ist) l)
  | TacComplete tac -> Tacticals.New.tclCOMPLETE (interp_tactic ist tac)
  | TacArg a -> interp_tactic ist (TacArg a)
  | TacInfo tac ->
      msg_warning
	(strbrk "The general \"info\" tactic is currently not working." ++ fnl () ++
	   strbrk "Some specific verbose tactics may exist instead, such as info_trivial, info_auto, info_eauto.");
      eval_tactic ist tac

and force_vrec ist v =
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then
    let v = to_tacvalue v in
    match v with
    | VRec (lfun,body) -> val_interp {ist with lfun = !lfun} body
    | v -> (Proofview.Goal.return (of_tacvalue v))
  else (Proofview.Goal.return v)

and interp_ltac_reference loc' mustbetac ist = function
  | ArgVar (loc,id) ->
      let v =
        try Id.Map.find id ist.lfun
        with Not_found -> in_gen (topwit wit_var) id
      in
      force_vrec ist v >>== fun v ->
      let v = propagate_trace ist loc id v in
      if mustbetac then (Proofview.Goal.return (coerce_to_tactic loc id v)) else (Proofview.Goal.return v)
  | ArgArg (loc,r) ->
      let ids = extract_ids [] ist.lfun in
      let loc_info = ((if Loc.is_ghost loc' then loc else loc'),LtacNameCall r) in
      let extra = TacStore.set ist.extra f_avoid_ids ids in 
      let extra = TacStore.set extra f_trace (push_trace loc_info ist) in
      let ist = { lfun = Id.Map.empty; extra = extra; } in
      val_interp ist (lookup_ltacref r)

and interp_tacarg ist arg =
  let tac_of_old f =
    Tacmach.New.of_old f >>== fun (sigma,v) ->
    Proofview.V82.tactic (tclEVARS sigma) <*>
    (Proofview.Goal.return v)
  in
  match arg with
  | TacGeneric arg ->
      tac_of_old (fun gl ->
        Geninterp.generic_interp ist gl arg)
  | Reference r -> interp_ltac_reference dloc false ist r
  | ConstrMayEval c ->
      tac_of_old (fun gl -> interp_constr_may_eval ist gl c) >>== fun c_interp ->
      (Proofview.Goal.return (Value.of_constr c_interp))
  | MetaIdArg (loc,_,id) -> assert false
  | TacCall (loc,r,[]) ->
      interp_ltac_reference loc true ist r
  | TacCall (loc,f,l) ->
      Proofview.tclEVARMAP >= fun sigma ->
      interp_ltac_reference loc true ist f >>== fun fv ->
      List.fold_right begin fun a acc ->
        interp_tacarg ist a >>== fun a_interp ->
        acc >>== fun acc -> (Proofview.Goal.return (a_interp::acc))
      end l ((Proofview.Goal.return [])) >>== fun largs ->
      interp_app loc ist fv largs
  | TacExternal (loc,com,req,la) ->
      List.fold_right begin fun a acc ->
        interp_tacarg ist a >>== fun a_interp ->
        acc >>== fun acc -> (Proofview.Goal.return (a_interp::acc))
      end la ((Proofview.Goal.return [])) >>== fun la_interp ->
      tac_of_old (fun gl -> interp_external loc ist { gl with sigma=project gl } com req la_interp)
  | TacFreshId l ->
      Tacmach.New.of_old (fun gl -> pf_interp_fresh_id ist gl l) >>== fun id ->
      (Proofview.Goal.return (in_gen (topwit wit_intro_pattern) (dloc, IntroIdentifier id)))
  | Tacexp t -> val_interp ist t
  | TacDynamic(_,t) ->
      let tg = (Dyn.tag t) in
      if String.equal tg "tactic" then
        val_interp ist (tactic_out t ist)
      else if String.equal tg "value" then
        (Proofview.Goal.return (value_out t))
      else if String.equal tg "constr" then
        (Proofview.Goal.return (Value.of_constr (constr_out t)))
      else
        Errors.anomaly ~loc:dloc ~label:"Tacinterp.val_interp"
	  (str "Unknown dynamic: <" ++ str (Dyn.tag t) ++ str ">")

(* Interprets an application node *)
and interp_app loc ist fv largs =
  let fail =
      (* spiwack: quick hack, can be inlined. *)
      try
      user_err_loc (loc, "Tacinterp.interp_app",
                    (str"Illegal tactic application."))
      with e -> Proofview.tclZERO e
  in
  let fv = Value.normalize fv in
  if has_type fv (topwit wit_tacvalue) then
  match to_tacvalue fv with
     (* if var=[] and body has been delayed by val_interp, then body
         is not a tactic that expects arguments.
         Otherwise Ltac goes into an infinite loop (val_interp puts
         a VFun back on body, and then interp_app is called again...) *)
    | (VFun(trace,olfun,(_::_ as var),body)
      |VFun(trace,olfun,([] as var),
         (TacFun _|TacLetIn _|TacMatchGoal _|TacMatch _| TacArg _ as body))) ->
	let (extfun,lvar,lval)=head_with_value (var,largs) in
        let fold accu (id, v) = Id.Map.add id v accu in
	let newlfun = List.fold_left fold olfun extfun in
      if List.is_empty lvar then
        begin Proofview.tclORELSE
            begin
              let ist = {
                lfun = newlfun;
                extra = TacStore.set ist.extra f_trace []; } in
              catch_error_tac trace (val_interp ist body)
            end
	    begin fun e ->
              (* spiwack: [Errors.push] here is unlikely to do what
                 it's intended to, or anything meaningful for that
                 matter. *)
              let e = Errors.push e in
              (* arnaud: todo: debugging: debugging_exception_step ist false e (fun () -> str "evaluation"); *)
	      Proofview.tclZERO e
            end
        end >>== fun v ->
        (* arnaud: todo: debugging:
          (* No errors happened, we propagate the trace *)
          let v = append_trace trace v in
        debugging_step ist
	  (fun () ->
	    str"evaluation returns"++fnl()++pr_value (Some (pf_env gl)) v);
        *)
        if List.is_empty lval then (Proofview.Goal.return v) else interp_app loc ist v lval
      else
        Proofview.Goal.return (of_tacvalue (VFun(trace,newlfun,lvar,body)))
    | _ -> fail
  else fail

(* Gives the tactic corresponding to the tactic value *)
and tactic_of_value ist vle =
  let vle = Value.normalize vle in
  if has_type vle (topwit wit_tacvalue) then
  match to_tacvalue vle with
  | VRTactic -> Proofview.tclUNIT ()
  | VFun (trace,lfun,[],t) ->
      let ist = {
        lfun = lfun;
        extra = TacStore.set ist.extra f_trace []; } in
      let tac = eval_tactic ist t in
      catch_error_tac trace tac
  | (VFun _|VRec _) -> Proofview.tclZERO (UserError ("" , str "A fully applied tactic is expected."))
  else Proofview.tclZERO (UserError ("" , str"Expression does not evaluate to a tactic."))

(* Evaluation with FailError catching *)
and eval_with_fail ist is_lazy tac =
  Proofview.tclORELSE
    begin
      val_interp ist tac >>== fun v ->
      (if has_type v (topwit wit_tacvalue) then match to_tacvalue v with
      | VFun (trace,lfun,[],t) when not is_lazy ->
          let ist = {
            lfun = lfun;
            extra = TacStore.set ist.extra f_trace trace; } in
	  let tac = eval_tactic ist t in
	  catch_error_tac trace (tac <*> Proofview.Goal.return (of_tacvalue VRTactic))
      | _ -> Proofview.Goal.return v
       else Proofview.Goal.return v)
    end
    begin function
      (** FIXME: Should we add [Errors.push]? *)
      | FailError (0,s)  ->
          Proofview.tclZERO (Eval_fail (Lazy.force s))
      | FailError (lvl,s) as e ->
          Proofview.tclZERO (Exninfo.copy e (FailError (lvl - 1, s)))
      | e -> Proofview.tclZERO e
    end

(* Interprets the clauses of a recursive LetIn *)
and interp_letrec ist llc u =
  Proofview.tclUNIT () >= fun () -> (* delay for the effects of [lref], just in case. *)
  let lref = ref ist.lfun in
  let fold accu ((_, id), b) =
    let v = of_tacvalue (VRec (lref, TacArg (dloc, b))) in
    Id.Map.add id v accu
  in
  let lfun = List.fold_left fold ist.lfun llc in
  let () = lref := lfun in
  let ist = { ist with lfun } in
  val_interp ist u

(* Interprets the clauses of a LetIn *)
and interp_letin ist llc u =
  let fold ((_, id), body) acc =
    interp_tacarg ist body >>== fun v ->
    acc >>== fun acc ->
    let () = check_is_value v in
    Proofview.Goal.return (Id.Map.add id v acc)
  in
  List.fold_right fold llc (Proofview.Goal.return ist.lfun) >>== fun lfun ->
  let ist = { ist with lfun } in
  val_interp ist u

(* Interprets the Match Context expressions *)
and interp_match_goal ist lz lr lmr =
  Proofview.Goal.hyps >>== fun hyps ->
  let hyps = Environ.named_context_of_val hyps in
  let hyps = if lr then List.rev hyps else hyps in
  Proofview.Goal.concl >>== fun concl ->
  Proofview.Goal.env >>== fun env ->
  let rec apply_goal_sub app ist (id,c) csr mt mhyps hyps =
    let rec match_next_pattern next = match IStream.peek next with
    | None -> Proofview.tclZERO PatternMatchingFailure
    | Some ({ m_sub=lgoal; m_ctx=ctxt }, next) ->
      let lctxt = give_context ctxt id in
      Proofview.tclORELSE
        (apply_hyps_context ist env lz mt lctxt (adjust lgoal) mhyps hyps)
        begin function
          | e when is_match_catchable e -> match_next_pattern next
          | e -> Proofview.tclZERO e
        end
    in
    match_next_pattern (match_subterm_gen app c csr) in
  let rec apply_match_goal ist env nrs lex lpt =
    begin
      let () = match lex with
      | r :: _ -> db_pattern_rule (curr_debug ist) nrs r
      | _ -> ()
      in
      match lpt with
      | (All t)::tl ->
	  begin
            db_mc_pattern_success (curr_debug ist);
            Proofview.tclORELSE (eval_with_fail ist lz t)
              begin function
                | e when is_match_catchable e ->
	      apply_match_goal ist env (nrs+1) (List.tl lex) tl
                | e -> Proofview.tclZERO e
              end
	  end
      | (Pat (mhyps,mgoal,mt))::tl ->
          let mhyps = List.rev mhyps (* Sens naturel *) in
	  begin match mgoal with
          | Term mg ->
              let matches =
                try Some (extended_matches mg concl)
                with PatternMatchingFailure -> None
              in
                            begin match matches with
              | None ->
                db_matching_failure (curr_debug ist);
                apply_match_goal ist env (nrs+1) (List.tl lex) tl
              | Some lmatch ->
                Proofview.tclORELSE
                  begin
                    db_matched_concl (curr_debug ist) env concl;
                    apply_hyps_context ist env lz mt Id.Map.empty lmatch mhyps hyps
                  end
                 begin function
                   | e when is_match_catchable e ->
                       ((match e with
                       | PatternMatchingFailure -> db_matching_failure (curr_debug ist)
                       | Eval_fail s -> db_eval_failure (curr_debug ist) s
                       | _ -> db_logic_failure (curr_debug ist) e);
                        apply_match_goal ist env (nrs+1) (List.tl lex) tl)
                   | e -> Proofview.tclZERO e
                 end
                end
	  | Subterm (b,id,mg) ->
	      Proofview.tclORELSE (apply_goal_sub b ist (id,mg) concl mt mhyps hyps)
                begin function
	       | PatternMatchingFailure ->
		   apply_match_goal ist env (nrs+1) (List.tl lex) tl
               | e -> Proofview.tclZERO e
                end
          end
      | _ ->
          Proofview.tclZERO (UserError (
	    "Tacinterp.apply_match_goal" ,
            (v 0 (str "No matching clauses for match goal" ++
		    (if curr_debug ist==DebugOff then
			fnl() ++ str "(use \"Set Ltac Debug\" for more info)"
		     else mt()) ++ str"."))
          ))
    end in
  Proofview.tclEVARMAP >= fun sigma ->
  apply_match_goal ist env 0 lmr
    (read_match_rule (extract_ltac_constr_values ist env)
       ist env sigma lmr)

(* Tries to match the hypotheses in a Match Context *)
and apply_hyps_context ist env lz mt lctxt lgmatch mhyps hyps =
  Proofview.Goal.env >>== fun env ->
  let rec apply_hyps_context_rec lfun lmatch lhyps_rest = function
    | hyp_pat::tl ->
	let (hypname, _, pat as hyp_pat) =
	  match hyp_pat with
	  | Hyp ((_,hypname),mhyp) -> hypname,  None, mhyp
	  | Def ((_,hypname),mbod,mhyp) -> hypname, Some mbod, mhyp
	in
        let rec match_next_pattern next = match IStream.peek next with
        | None ->
          db_hyp_pattern_failure (curr_debug ist) env (hypname, pat);
          Proofview.tclZERO PatternMatchingFailure
        | Some (s, next) ->
          let lids, hyp_match = s.e_ctx in
          db_matched_hyp (curr_debug ist) env hyp_match hypname;
          Proofview.tclORELSE
            begin
              let id_match = pi1 hyp_match in
              let select_match (id,_,_) = Id.equal id id_match in
              let nextlhyps = List.remove_first select_match lhyps_rest in
              let lfun = lfun +++ lids in
              apply_hyps_context_rec lfun s.e_sub nextlhyps tl
            end
            begin function
              | e when is_match_catchable e ->
                  match_next_pattern next
              | e -> Proofview.tclZERO e
            end
        in
        let init_match_pattern = Tacmach.New.of_old (fun gl ->
          apply_one_mhyp_context gl lmatch hyp_pat lhyps_rest) in
        init_match_pattern >>== match_next_pattern
    | [] ->
        let lfun = lfun +++ ist.lfun in
        let lfun = extend_values_with_bindings lmatch lfun in
        db_mc_pattern_success (curr_debug ist);
        eval_with_fail {ist with lfun } lz mt
  in
  apply_hyps_context_rec lctxt lgmatch hyps mhyps

and interp_external loc ist gl com req la = assert false
(* arnaud: todo
  let f ch = extern_request ch req gl la in
  let g ch = internalise_tacarg ch in
  interp_tacarg ist (System.connect f g com)
*)

(* Interprets extended tactic generic arguments *)
and interp_genarg ist gl x =
  let evdref = ref (project gl) in
  let rec interp_genarg ist gl x =
    let gl = { gl with sigma = !evdref } in
    match genarg_tag x with
    | IntOrVarArgType ->
      in_gen (topwit wit_int_or_var)
        (ArgArg (interp_int_or_var ist (out_gen (glbwit wit_int_or_var) x)))
    | IdentArgType b ->
      in_gen (topwit (wit_ident_gen b))
        (pf_interp_fresh_ident ist gl (out_gen (glbwit (wit_ident_gen b)) x))
    | VarArgType ->
      in_gen (topwit wit_var) (interp_hyp ist gl (out_gen (glbwit wit_var) x))
    | RefArgType ->
      in_gen (topwit wit_ref) (pf_interp_reference ist gl (out_gen (glbwit wit_ref) x))
    | GenArgType ->
      in_gen (topwit wit_genarg) (interp_genarg ist gl (out_gen (glbwit wit_genarg) x))
    | ConstrArgType ->
      let (sigma,c_interp) = pf_interp_constr ist gl (out_gen (glbwit wit_constr) x) in
      evdref := sigma;
      in_gen (topwit wit_constr) c_interp
    | ConstrMayEvalArgType ->
      let (sigma,c_interp) = interp_constr_may_eval ist gl (out_gen (glbwit wit_constr_may_eval) x) in
      evdref := sigma;
      in_gen (topwit wit_constr_may_eval) c_interp
    | QuantHypArgType ->
      in_gen (topwit wit_quant_hyp)
        (interp_declared_or_quantified_hypothesis ist gl
           (out_gen (glbwit wit_quant_hyp) x))
    | RedExprArgType ->
      let (sigma,r_interp) = pf_interp_red_expr ist gl (out_gen (glbwit wit_red_expr) x) in
      evdref := sigma;
      in_gen (topwit wit_red_expr) r_interp
    | OpenConstrArgType casted ->
      let expected_type =
        if casted then OfType (pf_concl gl) else WithoutTypeConstraint in
      in_gen (topwit (wit_open_constr_gen casted))
        (interp_open_constr ~expected_type
           ist (pf_env gl) (project gl)
           (snd (out_gen (glbwit (wit_open_constr_gen casted)) x)))
    | ConstrWithBindingsArgType ->
      in_gen (topwit wit_constr_with_bindings)
        (pack_sigma (interp_constr_with_bindings ist (pf_env gl) (project gl)
		       (out_gen (glbwit wit_constr_with_bindings) x)))
    | BindingsArgType ->
      in_gen (topwit wit_bindings)
        (pack_sigma (interp_bindings ist (pf_env gl) (project gl) (out_gen (glbwit wit_bindings) x)))
    | ListArgType ConstrArgType ->
        let (sigma,v) = interp_genarg_constr_list ist gl x in
	evdref := sigma;
	v
    | ListArgType VarArgType -> interp_genarg_var_list ist gl x
    | ListArgType _ -> app_list (interp_genarg ist gl) x
    | OptArgType _ -> app_opt (interp_genarg ist gl) x
    | PairArgType _ -> app_pair (interp_genarg ist gl) (interp_genarg ist gl) x
    | ExtraArgType s ->
        let (sigma,v) = Geninterp.generic_interp ist gl x in
	evdref:=sigma;
	v
  in
  let v = interp_genarg ist gl x in
  !evdref , v

and interp_genarg_constr_list ist gl x =
  let lc = out_gen (glbwit (wit_list wit_constr)) x in
  let (sigma,lc) = pf_apply (interp_constr_list ist) gl lc in
  sigma , in_gen (topwit (wit_list wit_constr)) lc

and interp_genarg_var_list ist gl x =
  let lc = out_gen (glbwit (wit_list wit_var)) x in
  let lc = interp_hyp_list ist gl lc in
  in_gen (topwit (wit_list wit_var)) lc

(* Interprets the Match expressions *)
and interp_match ist lz constr lmr =
  let apply_match_subterm app ist (id,c) csr mt =
    let rec match_next_pattern next = match IStream.peek next with
    | None -> Proofview.tclZERO PatternMatchingFailure
    | Some ({ m_sub=lmatch; m_ctx=ctxt; }, next) ->
      let lctxt = give_context ctxt id in
      let lfun = extend_values_with_bindings (adjust lmatch) (lctxt +++ ist.lfun) in
      Proofview.tclORELSE
        (eval_with_fail {ist with lfun=lfun} lz mt)
        begin function
          | e when is_match_catchable e ->
              match_next_pattern next
          | e -> Proofview.tclZERO e
        end
    in
    match_next_pattern (match_subterm_gen app c csr) in

  let rec apply_match ist csr = function
    | (All t)::tl ->
        Proofview.tclORELSE
        (eval_with_fail ist lz t)
          begin function
            | e when is_match_catchable e -> apply_match ist csr tl
            | e -> Proofview.tclZERO e
          end
    | (Pat ([],Term c,mt))::tl ->
        let matches =
          try Some (extended_matches c csr)
          with PatternMatchingFailure -> None
        in
        Proofview.tclORELSE begin match matches with
        | None -> Proofview.tclZERO PatternMatchingFailure
        | Some lmatch ->
           Proofview.tclORELSE
             begin
               let lfun = extend_values_with_bindings lmatch ist.lfun in
               eval_with_fail { ist with lfun=lfun } lz mt
             end
             begin function
               | e ->
                   (* arnaud: todo: debugging
                      debugging_exception_step ist false e (fun () ->
                      str "rule body for pattern" ++
                      pr_constr_pattern_env (pf_env g) c);*)
                   Proofview.tclZERO e
             end
        end
        begin function 
          | e when is_match_catchable e ->
              debugging_step ist (fun () -> str "switching to the next rule");
              apply_match ist csr tl
          | e -> Proofview.tclZERO e
        end

    | (Pat ([],Subterm (b,id,c),mt))::tl ->
        Proofview.tclORELSE
          (apply_match_subterm b ist (id,c) csr mt)
          begin function
            | PatternMatchingFailure -> apply_match ist csr tl
            | e -> Proofview.tclZERO e
          end
    | _ ->
        Proofview.tclZERO (UserError ("Tacinterp.apply_match" , str
                                                "No matching clauses for match.")) in
  begin Proofview.tclORELSE
    (interp_ltac_constr ist constr)
    begin function
      | e ->
          (* spiwack: [Errors.push] here is unlikely to do what
             it's intended to, or anything meaningful for that
             matter. *)
          let e = Errors.push e in
          debugging_exception_step ist true e
            (fun () -> str "evaluation of the matched expression");
          Proofview.tclZERO e
    end
  end >>== fun csr ->
  Proofview.tclEVARMAP >= fun sigma ->
  Proofview.Goal.env >>== fun env ->
  let ilr = read_match_rule (extract_ltac_constr_values ist env) ist env sigma lmr in
  Proofview.tclORELSE
    (apply_match ist csr ilr)
    begin function
      | e ->
          debugging_exception_step ist true e (fun () -> str "match expression");
          Proofview.tclZERO e
    end >>== fun res ->
  debugging_step ist (fun () ->
    str "match expression returns " ++ pr_value (Some env) res);
  (Proofview.Goal.return res)

(* Interprets tactic expressions : returns a "constr" *)
and interp_ltac_constr ist e =
  begin Proofview.tclORELSE
      (val_interp ist e)
      begin function
        | Not_found ->
            (* arnaud: todo: debugging
            debugging_step ist (fun () ->
              str "evaluation failed for" ++ fnl() ++
                Pptactic.pr_glob_tactic (pf_env gl) e);
            *)
            Proofview.tclZERO Not_found
        | e -> Proofview.tclZERO e
      end
  end >>== fun result ->
  Proofview.Goal.env >>== fun env ->
  let result = Value.normalize result in
  try
    let cresult = coerce_to_closed_constr env result in
    debugging_step ist (fun () ->
      Pptactic.pr_glob_tactic env e ++ fnl() ++
        str " has value " ++ fnl() ++
        pr_constr_env env cresult);
    (Proofview.Goal.return cresult)
  with CannotCoerceTo _ ->
    Proofview.Goal.env >>== fun env ->
    Proofview.tclZERO (UserError ( "",
      errorlabstrm ""
      (str "Must evaluate to a closed term" ++ fnl() ++
      str "offending expression: " ++ fnl() ++ pr_inspect env e result)))

(* Interprets tactic expressions : returns a "tactic" *)
and interp_tactic ist tac =
  val_interp ist tac >>= fun v ->
  tactic_of_value ist v

(* Interprets a primitive tactic *)
and interp_atomic ist tac =
  match tac with
  (* Basic tactics *)
  | TacIntroPattern l ->
      Tacmach.New.of_old (fun gl -> interp_intro_pattern_list_as_list ist gl l) >>= fun patterns ->
      h_intro_patterns patterns
  | TacIntrosUntil hyp ->
      h_intros_until (interp_quantified_hypothesis ist hyp)
  | TacIntroMove (ido,hto) ->
      Proofview.Goal.env >>= fun env ->
      Tacmach.New.of_old (fun gl -> interp_move_location ist gl hto) >>= fun mloc ->
      h_intro_move (Option.map (interp_fresh_ident ist env) ido) mloc
  | TacAssumption -> Proofview.V82.tactic h_assumption
  | TacExact c ->
      Proofview.V82.tactic begin fun gl -> 
        let (sigma,c_interp) = pf_interp_casted_constr ist gl c in
        tclTHEN
	  (tclEVARS sigma)
	  (h_exact c_interp)
          gl
      end
  | TacExactNoCheck c ->
      Proofview.V82.tactic begin fun gl -> 
        let (sigma,c_interp) = pf_interp_constr ist gl c in
        tclTHEN
	  (tclEVARS sigma)
	  (h_exact_no_check c_interp)
          gl
      end
  | TacVmCastNoCheck c ->
      Proofview.V82.tactic begin fun gl -> 
        let (sigma,c_interp) = pf_interp_constr ist gl c in
        tclTHEN
	  (tclEVARS sigma)
	  (h_vm_cast_no_check c_interp)
          gl
      end
  | TacApply (a,ev,cb,cl) ->
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.env >>= fun env ->
      let sigma, l =
        List.fold_map (interp_open_constr_with_bindings_loc ist env) sigma cb
      in
      let tac = match cl with
        | None -> fun l -> Proofview.V82.tactic (h_apply a ev l)
        | Some cl ->
            (fun l ->
              Tacmach.New.of_old (fun gl -> interp_in_hyp_as ist gl cl) >>= fun cl ->
              h_apply_in a ev l cl) in
      Tacticals.New.tclWITHHOLES ev tac sigma l
  | TacElim (ev,cb,cbo) ->
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.env >>= fun env ->
      let sigma, cb = interp_constr_with_bindings ist env sigma cb in
      let sigma, cbo = Option.fold_map (interp_constr_with_bindings ist env) sigma cbo in
      Tacticals.New.tclWITHHOLES ev (h_elim ev cb) sigma cbo
  | TacElimType c ->
      Proofview.V82.tactic begin fun gl -> 
        let (sigma,c_interp) = pf_interp_type ist gl c in
        tclTHEN
	  (tclEVARS sigma)
	  (h_elim_type c_interp)
          gl
      end
  | TacCase (ev,cb) ->
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.env >>= fun env ->
      let sigma, cb = interp_constr_with_bindings ist env sigma cb in
      Tacticals.New.tclWITHHOLES ev (h_case ev) sigma cb
  | TacCaseType c ->
      Proofview.V82.tactic begin fun gl -> 
        let (sigma,c_interp) = pf_interp_type ist gl c in
        tclTHEN
	  (tclEVARS sigma)
	  (h_case_type c_interp)
          gl
      end
  | TacFix (idopt,n) ->
      Proofview.Goal.env >>= fun env ->
      Proofview.V82.tactic (h_fix (Option.map (interp_fresh_ident ist env) idopt) n)
  | TacMutualFix (id,n,l) ->
      Proofview.Goal.env >>= fun env ->
      Proofview.V82.tactic begin fun gl -> 
        let f sigma (id,n,c) =
	  let (sigma,c_interp) = pf_interp_type ist { gl with sigma=sigma } c in
	  sigma , (interp_fresh_ident ist env id,n,c_interp) in
        let (sigma,l_interp) =
	  List.fold_right begin fun c (sigma,acc) ->
	    let (sigma,c_interp) = f sigma c in
	    sigma , c_interp::acc
	  end l (project gl,[])
        in
        tclTHEN
	  (tclEVARS sigma)
	  (h_mutual_fix (interp_fresh_ident ist env id) n l_interp)
          gl
      end
  | TacCofix idopt ->
      Proofview.Goal.env >>= fun env ->
      Proofview.V82.tactic (h_cofix (Option.map (interp_fresh_ident ist env) idopt))
  | TacMutualCofix (id,l) ->
      Proofview.Goal.env >>= fun env ->
      Proofview.V82.tactic begin fun gl -> 
        let f sigma (id,c) =
	  let (sigma,c_interp) = pf_interp_type ist { gl with sigma=sigma } c in
	  sigma , (interp_fresh_ident ist env id,c_interp) in
        let (sigma,l_interp) =
	  List.fold_right begin fun c (sigma,acc) ->
	    let (sigma,c_interp) = f sigma c in
	    sigma , c_interp::acc
	  end l (project gl,[])
        in
        tclTHEN
	  (tclEVARS sigma)
	  (h_mutual_cofix (interp_fresh_ident ist env id) l_interp)
          gl
      end
  | TacCut c ->
      Proofview.V82.tactic begin fun gl -> 
        let (sigma,c_interp) = pf_interp_type ist gl c in
        tclTHEN
	  (tclEVARS sigma)
	  (h_cut c_interp)
          gl
      end
  | TacAssert (t,ipat,c) ->
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.env >>= fun env ->
      let (sigma,c) = (if Option.is_empty t then interp_constr else interp_type) ist env sigma c in
      Tacmach.New.of_old (fun gl -> interp_intro_pattern ist gl) >>= fun patt ->
      Tacticals.New.tclTHEN
	(Proofview.V82.tactic (tclEVARS sigma))
        (Tactics.forward (Option.map (interp_tactic ist) t)
	   (Option.map patt ipat) c)
  | TacGeneralize cl ->
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.env >>= fun env ->
      Proofview.V82.tactic begin fun gl -> 
        let sigma, cl = interp_constr_with_occurrences_and_name_as_list ist env sigma cl in
        tclWITHHOLES false (h_generalize_gen) sigma cl gl
      end
  | TacGeneralizeDep c ->
      Proofview.V82.tactic begin fun gl -> 
        let (sigma,c_interp) = pf_interp_constr ist gl c in
        tclTHEN
	  (tclEVARS sigma)
	  (h_generalize_dep c_interp)
          gl
      end
  | TacLetTac (na,c,clp,b,eqpat) ->
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.env >>= fun env ->
      Tacmach.New.of_old (fun gl -> interp_clause ist gl clp) >>= fun clp ->Tacmach.New.of_old (fun gl -> Option.map (interp_intro_pattern ist gl) eqpat) >>= fun eqpat ->
      if Locusops.is_nowhere clp then
        (* We try to fully-typecheck the term *)
        Tacmach.New.of_old (fun gl -> pf_interp_constr ist gl c) >>= fun (sigma,c_interp) ->
	Tacticals.New.tclTHEN
	  (Proofview.V82.tactic (tclEVARS sigma))
          (h_let_tac b (interp_fresh_name ist env na) c_interp clp eqpat)
      else
        (* We try to keep the pattern structure as much as possible *)
        h_let_pat_tac b (interp_fresh_name ist env na)
          (interp_pure_open_constr ist env sigma c) clp eqpat

  (* Automation tactics *)
  | TacTrivial (debug,lems,l) ->
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.env >>= fun env ->
      Auto.h_trivial ~debug
	(interp_auto_lemmas ist env sigma lems)
	(Option.map (List.map (interp_hint_base ist)) l)
  | TacAuto (debug,n,lems,l) ->
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.env >>= fun env ->
      Auto.h_auto ~debug (Option.map (interp_int_or_var ist) n)
	(interp_auto_lemmas ist env sigma lems)
	(Option.map (List.map (interp_hint_base ist)) l)

  (* Derived basic tactics *)
  | TacSimpleInductionDestruct (isrec,h) ->
      h_simple_induction_destruct isrec (interp_quantified_hypothesis ist h)
  | TacInductionDestruct (isrec,ev,(l,el,cls)) ->
      Proofview.Goal.env >>= fun env ->
      let l =
        Goal.sensitive_list_map begin fun (c,(ipato,ipats)) ->
          Goal.V82.to_sensitive (fun gl -> interp_induction_arg ist gl c) >- fun c ->
          Goal.V82.to_sensitive (fun gl -> interp_intro_pattern ist gl) >- fun interp_intro_pattern ->
          Goal.return begin
            c,
            (Option.map interp_intro_pattern ipato,
             Option.map interp_intro_pattern ipats)
          end
        end l
      in
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.lift l >>= fun l ->
      let sigma,el =
        Option.fold_map (interp_constr_with_bindings ist env) sigma el in
      Tacmach.New.of_old (fun gl -> interp_clause ist gl) >>= fun interp_clause ->
      let cls = Option.map interp_clause cls in
      Tacticals.New.tclWITHHOLES ev (h_induction_destruct isrec ev) sigma (l,el,cls)
  | TacDoubleInduction (h1,h2) ->
      let h1 = interp_quantified_hypothesis ist h1 in
      let h2 = interp_quantified_hypothesis ist h2 in
      Elim.h_double_induction h1 h2
  | TacDecomposeAnd c ->
      Tacmach.New.of_old (fun gl -> pf_interp_constr ist gl c) >>= fun (sigma,c_interp) ->
      Tacticals.New.tclTHEN
	(Proofview.V82.tactic (tclEVARS sigma))
	(Elim.h_decompose_and c_interp)
  | TacDecomposeOr c ->
      Tacmach.New.of_old (fun gl -> pf_interp_constr ist gl c) >>= fun (sigma,c_interp) ->
      Tacticals.New.tclTHEN
	(Proofview.V82.tactic (tclEVARS sigma))
	(Elim.h_decompose_or c_interp)
  | TacDecompose (l,c) ->
      let l = List.map (interp_inductive ist) l in
      Tacmach.New.of_old (fun gl -> pf_interp_constr ist gl c) >>= fun (sigma,c_interp) ->
      Tacticals.New.tclTHEN
	(Proofview.V82.tactic (tclEVARS sigma))
	(Elim.h_decompose l c_interp)
  | TacSpecialize (n,cb) ->
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.env >>= fun env ->
      Proofview.V82.tactic begin fun gl -> 
        let sigma, cb = interp_constr_with_bindings ist env sigma cb in
        tclWITHHOLES false (h_specialize n) sigma cb gl
      end
  | TacLApply c ->
      Proofview.V82.tactic begin fun gl -> 
        let (sigma,c_interp) = pf_interp_constr ist gl c in
        tclTHEN
	  (tclEVARS sigma)
	  (h_lapply c_interp)
          gl
      end

  (* Context management *)
  | TacClear (b,l) ->
      Proofview.V82.tactic begin fun gl ->
        h_clear b (interp_hyp_list ist gl l) gl
      end
  | TacClearBody l ->
      Proofview.V82.tactic begin fun gl ->
        h_clear_body (interp_hyp_list ist gl l) gl
      end
  | TacMove (dep,id1,id2) ->
      Proofview.V82.tactic begin fun gl -> 
        h_move dep (interp_hyp ist gl id1) (interp_move_location ist gl id2) gl
      end
  | TacRename l ->
      Proofview.Goal.env >>= fun env ->
      Proofview.V82.tactic begin fun gl -> 
        h_rename (List.map (fun (id1,id2) ->
	  interp_hyp ist gl id1,
	  interp_fresh_ident ist env (snd id2)) l)
          gl
      end
  | TacRevert l ->
      Proofview.V82.tactic begin fun gl -> 
        h_revert (interp_hyp_list ist gl l) gl
      end

  (* Constructors *)
  | TacLeft (ev,bl) ->
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.env >>= fun env ->
      let sigma, bl = interp_bindings ist env sigma bl in
      Tacticals.New.tclWITHHOLES ev (h_left ev) sigma bl
  | TacRight (ev,bl) ->
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.env >>= fun env ->
      let sigma, bl = interp_bindings ist env sigma bl in
      Tacticals.New.tclWITHHOLES ev (h_right ev) sigma bl
  | TacSplit (ev,_,bll) ->
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.env >>= fun env ->
      let sigma, bll = List.fold_map (interp_bindings ist env) sigma bll in
      Tacticals.New.tclWITHHOLES ev (h_split ev) sigma bll
  | TacAnyConstructor (ev,t) ->
      Tactics.any_constructor ev (Option.map (interp_tactic ist) t)
  | TacConstructor (ev,n,bl) ->
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.env >>= fun env ->
      let sigma, bl = interp_bindings ist env sigma bl in
      Tacticals.New.tclWITHHOLES ev (h_constructor ev (interp_int_or_var ist n)) sigma bl

  (* Conversion *)
  | TacReduce (r,cl) ->
      Proofview.V82.tactic begin fun gl -> 
        let (sigma,r_interp) = pf_interp_red_expr ist gl r in
        tclTHEN
	  (tclEVARS sigma)
	  (h_reduce r_interp (interp_clause ist gl cl))
          gl
      end
  | TacChange (None,c,cl) ->
      Proofview.V82.tactic begin fun gl ->
        let is_onhyps = match cl.onhyps with
          | None | Some [] -> true
          | _ -> false
        in
        let is_onconcl = match cl.concl_occs with
          | AllOccurrences | NoOccurrences -> true
          | _ -> false
        in
        let (sigma,c_interp) =
	  if is_onhyps && is_onconcl
	  then pf_interp_type ist gl c
	  else pf_interp_constr ist gl c
        in
        tclTHEN
	  (tclEVARS sigma)
	  (h_change None c_interp (interp_clause ist gl cl))
          gl
      end
  | TacChange (Some op,c,cl) ->
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.env >>= fun env ->
      Proofview.V82.tactic begin fun gl -> 
        let sign,op = interp_typed_pattern ist env sigma op in
      (* spiwack: (2012/04/18) the evar_map output by pf_interp_constr
	 is dropped as the evar_map taken as input (from
	 extend_gl_hyps) is incorrect.  This means that evar
	 instantiated by pf_interp_constr may be lost, there. *)
      let to_catch = function Not_found -> true | e -> Errors.is_anomaly e in
      let (_,c_interp) =
	  try pf_interp_constr ist (extend_gl_hyps gl sign) c
	  with e when to_catch e (* Hack *) ->
	    errorlabstrm "" (strbrk "Failed to get enough information from the left-hand side to type the right-hand side.")
        in
        tclTHEN
	  (tclEVARS sigma)
	  (h_change (Some op) c_interp (interp_clause ist { gl with sigma=sigma } cl))
          gl
      end

  (* Equivalence relations *)
  | TacReflexivity -> h_reflexivity
  | TacSymmetry c ->
      Tacmach.New.of_old (fun gl -> interp_clause ist gl c) >>= fun cl ->
      h_symmetry cl
  | TacTransitivity c ->
      begin match c with
      | None -> h_transitivity None
      | Some c ->
          Tacmach.New.of_old (fun gl -> pf_interp_constr ist gl c) >>= fun (sigma,c_interp) ->
          Tacticals.New.tclTHEN
	    (Proofview.V82.tactic (tclEVARS sigma))
	    (h_transitivity (Some c_interp))
      end

  (* Equality and inversion *)
  | TacRewrite (ev,l,cl,by) ->
      let l = List.map (fun (b,m,c) ->
        let f env sigma = interp_open_constr_with_bindings ist env sigma c in
	(b,m,f)) l in
      Tacmach.New.of_old (fun gl -> interp_clause ist gl cl) >>= fun cl ->
      Equality.general_multi_multi_rewrite ev l cl
        (Option.map (fun by -> Tacticals.New.tclCOMPLETE (interp_tactic ist by), Equality.Naive) by)
  | TacInversion (DepInversion (k,c,ids),hyp) ->
      Proofview.tclEVARMAP >= fun sigma ->
      Proofview.Goal.lift begin match c with
      | None -> Goal.return (sigma , None)
      | Some c ->
          Goal.V82.to_sensitive (fun gl -> pf_interp_constr ist gl c) >- fun (sigma,c_interp) ->
	  Goal.return (sigma , Some c_interp)
      end >>= fun (sigma,c_interp) ->
      Tacmach.New.of_old (interp_intro_pattern ist) >>= fun interp_intro_pattern ->
      Tacmach.New.of_old (fun gl -> interp_declared_or_quantified_hypothesis ist gl hyp) >>= fun dqhyps ->
      Inv.dinv k c_interp
        (Option.map interp_intro_pattern ids)
        dqhyps
  | TacInversion (NonDepInversion (k,idl,ids),hyp) ->
      Tacmach.New.of_old (interp_intro_pattern ist) >>= fun interp_intro_pattern ->
      Tacmach.New.of_old (fun gl -> interp_hyp_list ist gl idl) >>= fun hyps ->
      Tacmach.New.of_old (fun gl -> interp_declared_or_quantified_hypothesis ist gl hyp) >>= fun dqhyps ->
      Inv.inv_clause k
        (Option.map interp_intro_pattern ids)
        hyps
        dqhyps
  | TacInversion (InversionUsing (c,idl),hyp) ->
      Tacmach.New.of_old (fun gl -> pf_interp_constr ist gl c) >>= fun (sigma,c_interp) ->
      Tacmach.New.of_old (fun gl -> interp_declared_or_quantified_hypothesis ist gl hyp) >>= fun dqhyps ->
      Tacmach.New.of_old (fun gl -> interp_hyp_list ist gl idl) >>= fun hyps ->
      Leminv.lemInv_clause dqhyps
        c_interp
        hyps

  (* For extensions *)
  | TacExtend (loc,opn,l) ->
      Proofview.tclEVARMAP >= fun goal_sigma ->
      let tac = lookup_tactic opn in
      Tacmach.New.of_old begin fun gl ->
	List.fold_right begin fun a (sigma,acc) ->
	  let (sigma,a_interp) = interp_genarg ist { gl with sigma=sigma } a in
	  sigma , a_interp::acc
	end l (goal_sigma,[])
      end >>= fun (sigma,args) ->
      Proofview.V82.tactic (tclEVARS sigma) <*>
      tac args ist
  | TacAlias (loc,s,l,(_,body)) ->
      Proofview.Goal.env >>= fun env ->
      let rec f x = match genarg_tag x with
          | IntOrVarArgType ->
              (Proofview.Goal.return (mk_int_or_var_value ist (out_gen (glbwit wit_int_or_var) x)))
          | IdentArgType b ->
              Proofview.Goal.lift begin
	        Goal.return (value_of_ident (interp_fresh_ident ist env
	                                       (out_gen (glbwit (wit_ident_gen b)) x)))
              end
          | VarArgType ->
              Tacmach.New.of_old (fun gl -> mk_hyp_value ist gl (out_gen (glbwit wit_var) x))
          | RefArgType ->
              Tacmach.New.of_old (fun gl -> 
                Value.of_constr (constr_of_global
                                   (pf_interp_reference ist gl (out_gen (glbwit wit_ref) x))))
          | GenArgType -> f (out_gen (glbwit wit_genarg) x)
          | ConstrArgType ->
              Tacmach.New.of_old (fun gl -> mk_constr_value ist gl (out_gen (glbwit wit_constr) x)) >>== fun (sigma,v) ->
              Proofview.V82.tactic (tclEVARS sigma) <*>
	      (Proofview.Goal.return v)
          | OpenConstrArgType false ->
              Tacmach.New.of_old (fun gl -> mk_open_constr_value ist gl (snd (out_gen (glbwit wit_open_constr) x))) >>== fun (sigma,v) ->
              Proofview.V82.tactic (tclEVARS sigma) <*>
	      (Proofview.Goal.return v)
          | ConstrMayEvalArgType ->
              Tacmach.New.of_old (fun gl -> interp_constr_may_eval ist gl (out_gen (glbwit wit_constr_may_eval) x)) >>== fun (sigma,c_interp) ->
              Proofview.V82.tactic (tclEVARS sigma) <*>
	      Proofview.Goal.return (Value.of_constr c_interp)
          | ListArgType ConstrArgType ->
              let wit = glbwit (wit_list wit_constr) in
              Tacmach.New.of_old begin fun gl ->
	        List.fold_right begin fun c (sigma,acc) ->
	          let (sigma,c_interp) = mk_constr_value ist { gl with sigma=sigma } c in
	          sigma , c_interp::acc
	        end (out_gen wit x) (project gl,[])
              end >>== fun (sigma,l_interp) ->
              Proofview.V82.tactic (tclEVARS sigma) <*>
              (Proofview.Goal.return (in_gen (topwit (wit_list wit_genarg)) l_interp))
          | ListArgType VarArgType ->
              let wit = glbwit (wit_list wit_var) in
              Tacmach.New.of_old (fun gl ->
                let ans = List.map (mk_hyp_value ist gl) (out_gen wit x) in
                in_gen (topwit (wit_list wit_genarg)) ans
              )
          | ListArgType IntOrVarArgType ->
              let wit = glbwit (wit_list wit_int_or_var) in
              let ans = List.map (mk_int_or_var_value ist) (out_gen wit x) in
              (Proofview.Goal.return (in_gen (topwit (wit_list wit_genarg)) ans))
          | ListArgType (IdentArgType b) ->
              let wit = glbwit (wit_list (wit_ident_gen b)) in
	      let mk_ident x = value_of_ident (interp_fresh_ident ist env x) in
	      let ans = List.map mk_ident (out_gen wit x) in
              (Proofview.Goal.return (in_gen (topwit (wit_list wit_genarg)) ans))
          | ListArgType t  ->
              (* arnaud: unsafe, faire avec des combinateurs. Dans la version originale c'était juste [Genarg.app_list f x] *)
              fold_list begin fun a l ->
                f a >>== fun a' ->
                l >>== fun l ->
                 Proofview.Goal.return (a'::l)
              end x (Proofview.Goal.return []) >>== fun l ->
              Proofview.Goal.return (in_gen
                                       (topwit (wit_list (Obj.magic t)))
                                       l)
          | ExtraArgType _ ->
              (** Special treatment of tactics *)
              if has_type x (glbwit wit_tactic) then
                let tac = out_gen (glbwit wit_tactic) x in
                val_interp ist tac >>== fun v ->
                Proofview.Goal.return v
              else
                Tacmach.New.of_old (fun gl ->
                  Geninterp.generic_interp ist gl x) >>== fun (newsigma,v) ->
                Proofview.V82.tactic (tclEVARS newsigma) <*>
                Proofview.Goal.return v
          | QuantHypArgType | RedExprArgType
          | OpenConstrArgType _ | ConstrWithBindingsArgType
          | BindingsArgType
          | OptArgType _ | PairArgType _
	    -> Proofview.tclZERO (UserError("" , str"This argument type is not supported in tactic notations."))
      in
      let addvar (x, v) accu =
        accu >>== fun accu ->
        f v >>== fun v ->
        Proofview.Goal.return (Id.Map.add x v accu)
      in
      List.fold_right addvar l (Proofview.Goal.return ist.lfun) >>= fun lfun ->
      let trace = push_trace (loc,LtacNotationCall s) ist in
      let ist = {
        lfun = lfun;
        extra = TacStore.set ist.extra f_trace trace; } in
      interp_tactic ist body

(* Initial call for interpretation *)

let default_ist () =
  let extra = TacStore.set TacStore.empty f_debug (get_debug ()) in
  { lfun = Id.Map.empty; extra = extra }

let eval_tactic t =
  Proofview.tclUNIT () >= fun () -> (* delay for [db_initialize] and [default_ist] *)
  db_initialize ();
  interp_tactic (default_ist ()) t

(* globalization + interpretation *)


let interp_tac_gen lfun avoid_ids debug t =
  Proofview.tclEVARMAP >= fun sigma ->
  Proofview.Goal.env >>= fun env ->
  let extra = TacStore.set TacStore.empty f_debug debug in
  let extra = TacStore.set extra f_avoid_ids avoid_ids in
  let ist = { lfun = lfun; extra = extra } in
  let ltacvars = Id.Map.domain lfun in
  interp_tactic ist
    (intern_pure_tactic {
      ltacvars; ltacrecvars = Id.Map.empty;
      gsigma = sigma; genv = env } t)

let interp t = interp_tac_gen Id.Map.empty [] (get_debug()) t
let _ = Proof_global.set_interp_tac interp

let eval_ltac_constr t =
  Proofview.tclUNIT () >= fun () -> (* delay for [make_empty_glob_sign] and [default_ist] *)
  interp_ltac_constr  (default_ist ())
    (intern_tactic_or_tacarg (make_empty_glob_sign ()) t )

(* Used to hide interpretation for pretty-print, now just launch tactics *)
let hide_interp t ot =
  Proofview.tclEVARMAP >= fun sigma ->
  Proofview.Goal.env >>= fun env ->
  let ist = { ltacvars = Id.Set.empty; ltacrecvars = Id.Map.empty;
            gsigma = sigma; genv = env } in
  let te = intern_pure_tactic ist t in
  let t = eval_tactic te in
  match ot with
  | None -> t
  | Some t' -> Tacticals.New.tclTHEN t t'

(***************************************************************************)
(** Register standard arguments *)

let def_intern ist x = (ist, x)
let def_subst _ x = x
let def_interp ist gl x = (gl.Evd.sigma, x)

let declare_uniform t pr =
  Genintern.register_intern0 t def_intern;
  Genintern.register_subst0 t def_subst;
  Geninterp.register_interp0 t def_interp;
  Genprint.register_print0 t pr pr pr

let () =
  let pr_unit _ = str "()" in
  declare_uniform wit_unit pr_unit

let () =
  declare_uniform wit_int int

let () =
  let pr_bool b = if b then str "true" else str "false" in
  declare_uniform wit_bool pr_bool

let () =
  let pr_string s = str "\"" ++ str s ++ str "\"" in
  declare_uniform wit_string pr_string

let () =
  declare_uniform wit_pre_ident str

let () =
  let interp ist gl pat = (gl.sigma, interp_intro_pattern ist gl pat) in
  Geninterp.register_interp0 wit_intro_pattern interp;
  let interp ist gl s = (gl.sigma, interp_sort s) in
  Geninterp.register_interp0 wit_sort interp

let () =
  let interp ist gl tac =
    let f = VFun (extract_trace ist, ist.lfun, [], tac) in
    (gl.sigma, TacArg (dloc, valueIn (of_tacvalue f)))
  in
  Geninterp.register_interp0 wit_tactic interp

(***************************************************************************)
(* Other entry points *)

let interp_redexp env sigma r =
  let ist = default_ist () in
  let gist = { fully_empty_glob_sign with genv = env; gsigma = sigma } in
  interp_red_expr ist sigma env (intern_red_expr gist r)

(***************************************************************************)
(* Embed tactics in raw or glob tactic expr *)

let globTacticIn t = TacArg (dloc,TacDynamic (dloc,tactic_in t))
let tacticIn t =
  globTacticIn (fun ist ->
    try glob_tactic (t ist)
    with e when Errors.noncritical e -> anomaly ~label:"tacticIn"
      (str "Incorrect tactic expression. Received exception is:" ++
       Errors.print e))

(***************************************************************************)
(* Backwarding recursive needs of tactic glob/interp/eval functions *)

let _ = Hook.set Auto.extern_interp
  (fun l ->
    let lfun = Id.Map.map (fun c -> Value.of_constr c) l in
    let ist = { (default_ist ()) with lfun; } in
    interp_tactic ist)
