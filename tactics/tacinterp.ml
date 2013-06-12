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
open Printer
open Pretyping
open Extrawit
open Evd
open Misctypes
open Miscops
open Locus
open Tacintern
open Taccoerce

let safe_msgnl s =
  let _ =
    try ppnl s with any ->
    ppnl (str "bug in the debugger: an exception is raised while printing debug information")
  in
  pp_flush () 

type value = tlevel generic_argument

(* Values for interpretation *)
type tacvalue =
  | VRTactic of (goal list sigma) (* For Match results *)
                                               (* Not a true tacvalue *)
  | VFun of ltac_trace * (Id.t * value) list *
      Id.t option list * glob_tactic_expr
  | VRec of (Id.t * value) list ref * glob_tactic_expr

let (wit_tacvalue : (Empty.t, Empty.t, tacvalue) Genarg.genarg_type) =
  Genarg.create_arg None "tacvalue"

let of_tacvalue v = in_gen (topwit wit_tacvalue) v
let to_tacvalue v = out_gen (topwit wit_tacvalue) v

module Value = Taccoerce.Value

let dloc = Loc.ghost

let catch_error call_trace tac g =
  try tac g with e when Errors.noncritical e ->
  let e = Errors.push e in
  let inner_trace, e = match Exninfo.get e ltac_trace_info with
  | Some inner_trace -> inner_trace, e
  | None -> [], e
  in
  if List.is_empty call_trace && List.is_empty inner_trace then raise e
  else begin
    assert (Errors.noncritical e); (* preserved invariant *)
    let new_trace = inner_trace @ call_trace in
    let located_exc = Exninfo.add e ltac_trace_info new_trace in
    raise located_exc
  end

(* Signature for interpretation: val_interp and interpretation functions *)
type interp_sign =
    { lfun : (Id.t * value) list;
      avoid_ids : Id.t list; (* ids inherited from the call context
				      (needed to get fresh ids) *)
      debug : debug_info;
      trace : ltac_trace }

let check_is_value v =
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then
    let v = to_tacvalue v in
    match v with
    | VRTactic _ -> (* These are goals produced by Match *)
      error "Immediate match producing tactics not allowed in local definitions."
    | _ -> ()
  else ()

(* Displays a value *)
let rec pr_value env v = str "a tactic"

let pr_value env v =
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then
    pr_value env (to_tacvalue v)
  else if has_type v (topwit wit_constr_context) then
    let c = out_gen (topwit wit_constr_context) v in
    match env with Some env -> pr_lconstr_env env c | _ -> str "a term"
  else if has_type v (topwit wit_constr) then
    let c = out_gen (topwit wit_constr) v in
    match env with Some env -> pr_lconstr_env env c | _ -> str "a term"
  else if has_type v (topwit wit_constr_under_binders) then
    let c = out_gen (topwit wit_constr_under_binders) v in
    match env with Some env -> pr_lconstr_under_binders_env  env c | _ -> str "a term"
  else
    str "an unknown type" (** TODO *)

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

type interp_genarg_type =
  interp_sign -> goal sigma -> glob_generic_argument ->
    Evd.evar_map * typed_generic_argument

let extragenargtab =
  ref (String.Map.empty : interp_genarg_type String.Map.t)
let add_interp_genarg id f =
  extragenargtab := String.Map.add id f !extragenargtab
let lookup_interp_genarg id =
  try String.Map.find id !extragenargtab
  with Not_found ->
    let msg = "No interpretation function found for entry " ^ id in
    msg_warning (strbrk msg);
    let f = fun _ _ _ -> failwith msg in
    add_interp_genarg id f;
    f

let push_trace (loc,ck) = function
  | (n,loc',ck')::trl when Pervasives.(=) ck ck' -> (n+1,loc,ck)::trl (** FIXME *)
  | trl -> (1,loc,ck)::trl

let propagate_trace ist loc id v =
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then
    let tacv = to_tacvalue v in
    match tacv with
    | VFun (_,lfun,it,b) ->
        let t = if List.is_empty it then b else TacFun (it,b) in
        let ans = VFun (push_trace(loc,LtacVarCall (id,t)) ist.trace,lfun,it,b) in
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
    | VFun _ | VRTactic _ -> v
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

let extend_values_with_bindings (ln,lm) lfun =
  let of_cub c = match c with
  | [], c -> Value.of_constr c
  | _ -> in_gen (topwit wit_constr_under_binders) c
  in
  let lnames = Id.Map.fold (fun id id' accu -> (id,value_of_ident id') :: accu) ln [] in
  let lmatch = Id.Map.fold (fun id c accu -> (id, of_cub c) :: accu) lm [] in
  (* For compatibility, bound variables are visible only if no other
     binding of the same name exists *)
  lmatch@lfun@lnames

(***************************************************************************)
(* Evaluation/interpretation *)

let is_variable env id =
  List.mem id (ids_of_named_context (Environ.named_context env))

(* Debug reference *)
let debug = ref DebugOff

(* Sets the debugger mode *)
let set_debug pos = debug := pos

(* Gives the state of debug *)
let get_debug () = !debug

let debugging_step ist pp =
  match ist.debug with
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
  let v = List.assoc id ist.lfun in
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
      (try coerce_to_int_or_var_list (List.assoc id ist.lfun)
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
  try coerce_to_hyp_list (pf_env gl) (List.assoc id ist.lfun)
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
  | ArgVar locid ->
      interp_ltac_var (coerce_to_reference env) ist (Some env) locid

let pf_interp_reference ist gl = interp_reference ist (pf_env gl)

let interp_inductive ist = function
  | ArgArg r -> r
  | ArgVar locid -> interp_ltac_var coerce_to_inductive ist None locid

let interp_evaluable ist env = function
  | ArgArg (r,Some (loc,id)) ->
      (* Maybe [id] has been introduced by Intro-like tactics *)
      (try match Environ.lookup_named id env with
       | (_,Some _,_) -> EvalVarRef id
       | _ -> error_not_evaluable (VarRef id)
       with Not_found ->
       match r with
       | EvalConstRef _ -> r
       | _ -> error_global_not_found_loc loc (qualid_of_ident id))
  | ArgArg (r,None) -> r
  | ArgVar locid ->
      interp_ltac_var (coerce_to_evaluable_ref env) ist (Some env) locid

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
  let fold (id, v) (vars1, vars2) =
    try
      let c = coerce_to_constr env v in
      (Id.Map.add id c vars1, vars2)
    with Not_found ->
      let ido =
        let v = Value.normalize v in
        if has_type v (topwit wit_intro_pattern) then
          match out_gen (topwit wit_intro_pattern) v with
          | _, IntroIdentifier id0 -> Some id0
          | _ -> None
        else None
      in
      (vars1, (id, ido) :: vars2)
  in
  List.fold_right fold ist.lfun (Id.Map.empty, [])

(* Extract the identifier list from lfun: join all branches (what to do else?)*)
let rec intropattern_ids (loc,pat) = match pat with
  | IntroIdentifier id -> [id]
  | IntroOrAndPattern ll ->
      List.flatten (List.map intropattern_ids (List.flatten ll))
  | IntroWildcard | IntroAnonymous | IntroFresh _ | IntroRewrite _
  | IntroForthcoming _ -> []

let rec extract_ids ids lfun =
  let fold accu (id, v) =
    let v = Value.normalize v in
    if has_type v (topwit wit_intro_pattern) then
      let (_, ipat) = out_gen (topwit wit_intro_pattern) v in
      if List.mem id ids then accu
      else accu @ intropattern_ids (dloc, ipat)
    else accu
  in
  List.fold_left fold [] lfun

let default_fresh_id = Id.of_string "H"

let interp_fresh_id ist env l =
  let ids = List.map_filter (function ArgVar (_, id) -> Some id | _ -> None) l in
  let avoid = (extract_ids ids ist.lfun) @ ist.avoid_ids in
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
  let (ltacvars,unbndltacvars as vars) = extract_ltac_constr_values ist env in
  let ltacbnd = Id.Map.bindings ltacvars in
  let c = match ce with
  | None -> c
    (* If at toplevel (ce<>None), the error can be due to an incorrect
       context at globalization time: we retype with the now known
       intros/lettac/inversion hypothesis names *)
  | Some c ->
      let ltacdata = (List.map fst ltacbnd, unbndltacvars) in
      intern_gen kind ~allow_patvar ~ltacvars:ltacdata sigma env c
  in
  let trace =
    push_trace (loc_of_glob_constr c,LtacConstrInterp (c,vars)) ist.trace in
  let (evd,c) =
    (** FIXME: we should propagate the use of Id.Map.t everywhere *)
    let vars = (ltacbnd, unbndltacvars) in
    catch_error trace (understand_ltac flags sigma env vars kind) c
  in
  db_constr ist.debug env c;
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
        sigma,
        List.map inj_fun (coerce_to_constr_list env (List.assoc id ist.lfun))
    | _ ->
        raise Not_found
    with Not_found ->
      (*all of dest_fun, List.assoc, coerce_to_constr_list may raise Not_found*)
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
	and ctxt = coerce_to_constr_context (List.assoc s ist.lfun) in
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
    db_constr ist.debug (pf_env gl) csr;
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
	try List.assoc id ist.lfun
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
      (try coerce_to_intro_pattern_list loc (pf_env gl) (List.assoc id ist.lfun)
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
      try
        let v = List.assoc id ist.lfun in
        let v = Value.normalize v in
        if has_type v (topwit wit_intro_pattern) then
          let v = out_gen (topwit wit_intro_pattern) v in
          match v with
          | _, IntroIdentifier id' ->
              if Tactics.is_quantified_hypothesis id' gl
              then ElimOnIdent (loc,id')
              else
                (try ElimOnConstr (sigma,(constr_of_id env id',NoBindings))
                with Not_found ->
                  user_err_loc (loc,"",
                  pr_id id ++ strbrk " binds to " ++ pr_id id' ++ strbrk " which is neither a declared or a quantified hypothesis."))
          | _ -> error ()
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
  | None -> []
  | Some id -> [id, in_gen (topwit wit_constr_context) ctxt]

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
  if List.mem id l then
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
  let merged = Id.Map.fold Id.Map.add ln ln1 in
  (merged, Id.Map.merge merge lcm lm)

let adjust (l, lc) = (l, Id.Map.map (fun c -> [], c) lc)

type 'a extended_matching_result =
    { e_ctx : 'a;
      e_sub : bound_ident_map * extended_patvar_map; }

let push_id_couple id name env = match name with
| Name idpat ->
  let binding = idpat, Value.of_constr (mkVar id) in
  binding :: env
| Anonymous -> env

let match_pat refresh lmatch hyp gl = function
| Term t ->
  let hyp = if refresh then refresh_universes_strict hyp else hyp in
  begin
    try
      let lmeta = extended_matches t hyp in
      let lmeta = verify_metas_coherence gl lmatch lmeta in
      let ans = { e_ctx = []; e_sub = lmeta; } in
      IStream.cons ans IStream.lempty
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
              let context = (env @s2.e_ctx), hd in
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

let pack_sigma (sigma,c) = {it=c;sigma=sigma}

let extend_gl_hyps { it=gl ; sigma=sigma } sign =
  Goal.V82.new_goal_with sigma gl sign

(* Interprets an l-tac expression into a value *)
let rec val_interp ist gl (tac:glob_tactic_expr) : Evd.evar_map * typed_generic_argument =
  let value_interp ist = match tac with
  (* Immediate evaluation *)
  | TacFun (it,body) ->
    let v = VFun (ist.trace,ist.lfun,it,body) in
    project gl, of_tacvalue v
  | TacLetIn (true,l,u) -> interp_letrec ist gl l u
  | TacLetIn (false,l,u) -> interp_letin ist gl l u
  | TacMatchGoal (lz,lr,lmr) -> interp_match_goal ist gl lz lr lmr
  | TacMatch (lz,c,lmr) -> interp_match ist gl lz c lmr
  | TacArg (loc,a) -> interp_tacarg ist gl a
  (* Delayed evaluation *)
  | t ->
    let v = VFun (ist.trace,ist.lfun,[],t) in
    project gl, of_tacvalue v

  in check_for_interrupt ();
    match ist.debug with
    | DebugOn lev ->
	debug_prompt lev gl tac (fun v -> value_interp {ist with debug=v})
    | _ -> value_interp ist

and eval_tactic ist = function
  | TacAtom (loc,t) ->
      fun gl ->
	let call = LtacAtomCall t in
	let tac = (* catch error in the interpretation *)
	  catch_error (push_trace(dloc,call)ist.trace)
	    (interp_atomic ist gl) t	in
	(* catch error in the evaluation *)
	catch_error (push_trace(loc,call)ist.trace) tac gl
  | TacFun _ | TacLetIn _ -> assert false
  | TacMatchGoal _ | TacMatch _ -> assert false
  | TacId s -> fun gl ->
      let res = tclIDTAC_MESSAGE (interp_message_nl ist gl s) gl in
      db_breakpoint ist.debug s; res
  | TacFail (n,s) -> fun gl -> tclFAIL (interp_int_or_var ist n) (interp_message ist gl s) gl
  | TacProgress tac -> tclPROGRESS (interp_tactic ist tac)
  | TacShowHyps tac -> tclSHOWHYPS (interp_tactic ist tac)
  | TacAbstract (tac,ido) ->
      fun gl -> Tactics.tclABSTRACT
        (Option.map (pf_interp_ident ist gl) ido) (interp_tactic ist tac) gl
  | TacThen (t1,tf,t,tl) ->
      tclTHENS3PARTS (interp_tactic ist t1)
	(Array.map (interp_tactic ist) tf) (interp_tactic ist t) (Array.map (interp_tactic ist) tl)
  | TacThens (t1,tl) -> tclTHENS (interp_tactic ist t1) (List.map (interp_tactic ist) tl)
  | TacDo (n,tac) -> tclDO (interp_int_or_var ist n) (interp_tactic ist tac)
  | TacTimeout (n,tac) -> tclTIMEOUT (interp_int_or_var ist n) (interp_tactic ist tac)
  | TacTry tac -> tclTRY (interp_tactic ist tac)
  | TacRepeat tac -> tclREPEAT (interp_tactic ist tac)
  | TacOrelse (tac1,tac2) ->
        tclORELSE (interp_tactic ist tac1) (interp_tactic ist tac2)
  | TacFirst l -> tclFIRST (List.map (interp_tactic ist) l)
  | TacSolve l -> tclSOLVE (List.map (interp_tactic ist) l)
  | TacComplete tac -> tclCOMPLETE (interp_tactic ist tac)
  | TacArg a -> interp_tactic ist (TacArg a)
  | TacInfo tac ->
      msg_warning
	(strbrk "The general \"info\" tactic is currently not working." ++ fnl () ++
	 strbrk "Some specific verbose tactics may exist instead, such as info_trivial, info_auto, info_eauto.");
      eval_tactic ist tac

and force_vrec ist gl v =
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then
    let v = to_tacvalue v in
    match v with
    | VRec (lfun,body) -> val_interp {ist with lfun = !lfun} gl body
    | v -> project gl , of_tacvalue v
  else project gl, v

and interp_ltac_reference loc' mustbetac ist gl = function
  | ArgVar (loc,id) ->
      let v = List.assoc id ist.lfun in
      let (sigma,v) = force_vrec ist gl v in
      let v = propagate_trace ist loc id v in
      sigma , if mustbetac then coerce_to_tactic loc id v else v
  | ArgArg (loc,r) ->
      let ids = extract_ids [] ist.lfun in
      let loc_info = ((if Loc.is_ghost loc' then loc else loc'),LtacNameCall r) in
      let ist =
        { lfun=[]; debug=ist.debug; avoid_ids=ids;
          trace = push_trace loc_info ist.trace } in
      val_interp ist gl (lookup_ltacref r)

and interp_tacarg ist gl arg =
  let evdref = ref (project gl) in
  let v = match arg with
    | TacVoid -> in_gen (topwit wit_unit) ()
    | Reference r ->
      let (sigma,v) = interp_ltac_reference dloc false ist gl r in
      evdref := sigma;
      v
    | Integer n -> in_gen (topwit wit_int) n
    | IntroPattern ipat ->
      let ans = interp_intro_pattern ist gl ipat in
      in_gen (topwit wit_intro_pattern) ans
    | ConstrMayEval c ->
      let (sigma,c_interp) = interp_constr_may_eval ist gl c in
      evdref := sigma;
      Value.of_constr c_interp
    | MetaIdArg (loc,_,id) -> assert false
    | TacCall (loc,r,[]) ->
      let (sigma,v) = interp_ltac_reference loc true ist gl r in
      evdref := sigma;
      v
    | TacCall (loc,f,l) ->
        let (sigma,fv) = interp_ltac_reference loc true ist gl f in
	let (sigma,largs) =
	  List.fold_right begin fun a (sigma',acc) ->
	    let (sigma', a_interp) = interp_tacarg ist gl a in
	    sigma' , a_interp::acc
	  end l (sigma,[])
	in
	List.iter check_is_value largs;
	let (sigma,v) = interp_app loc ist { gl with sigma=sigma } fv largs in
	evdref:= sigma;
	v
    | TacExternal (loc,com,req,la) ->
        let (sigma,la_interp) =
	  List.fold_right begin fun a (sigma,acc) ->
	    let (sigma,a_interp) = interp_tacarg ist {gl with sigma=sigma} a in
	    sigma , a_interp::acc
	  end la (project gl,[])
	in
        let (sigma,v) = interp_external loc ist { gl with sigma=sigma } com req la_interp in
	evdref := sigma;
	v
    | TacFreshId l ->
        let id = pf_interp_fresh_id ist gl l in
	in_gen (topwit wit_intro_pattern) (dloc, IntroIdentifier id)
    | Tacexp t ->
      let (sigma,v) = val_interp ist gl t in
      evdref := sigma;
      v
    | TacDynamic(_,t) ->
        let tg = (Dyn.tag t) in
	if String.equal tg "tactic" then
          let (sigma,v) = val_interp ist gl (tactic_out t ist) in
	  evdref := sigma;
	  v
	else if String.equal tg "value" then
          value_out t
	else if String.equal tg "constr" then
          Value.of_constr (constr_out t)
	else
          anomaly ~loc:dloc ~label:"Tacinterp.val_interp"
		       (str "Unknown dynamic: <" ++ str (Dyn.tag t) ++ str ">")
  in
  !evdref , v

(* Interprets an application node *)
and interp_app loc ist gl fv largs =
  let fail () = user_err_loc (loc, "Tacinterp.interp_app",
          (str"Illegal tactic application.")) in
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
	let (newlfun,lvar,lval)=head_with_value (var,largs) in
	if List.is_empty lvar then
          (* Check evaluation and report problems with current trace *)
	  let (sigma,v) =
	    try
              catch_error trace
		(val_interp {ist with lfun=newlfun@olfun; trace=[]} gl) body
	    with reraise ->
              let reraise = Errors.push reraise in
              debugging_exception_step ist false reraise
                (fun () -> str "evaluation");
	      raise reraise
          in
          (* No errors happened, we propagate the trace *)
          let v = append_trace trace v in

	  let gl = { gl with sigma=sigma } in
          debugging_step ist
	    (fun () ->
	       str"evaluation returns"++fnl()++pr_value (Some (pf_env gl)) v);
          if List.is_empty lval then sigma,v else interp_app loc ist gl v lval
	else
          project gl , of_tacvalue (VFun(trace,newlfun@olfun,lvar,body))
    | _ -> fail ()
  else fail ()

(* Gives the tactic corresponding to the tactic value *)
and tactic_of_value ist vle g =
  let vle = Value.normalize vle in
  if has_type vle (topwit wit_tacvalue) then
  match to_tacvalue vle with
  | VRTactic res -> res
  | VFun (trace,lfun,[],t) ->
      let tac = eval_tactic {ist with lfun=lfun; trace=[]} t in
      catch_error trace tac g
  | (VFun _|VRec _) -> error "A fully applied tactic is expected."
  else errorlabstrm "" (str"Expression does not evaluate to a tactic.")

(* Evaluation with FailError catching *)
and eval_with_fail ist is_lazy goal tac =
  try
    let (sigma,v) = val_interp ist goal tac in
    let v = Value.normalize v in
    sigma ,
    (if has_type v (topwit wit_tacvalue) then match to_tacvalue v with
    | VFun (trace,lfun,[],t) when not is_lazy ->
	let tac = eval_tactic {ist with lfun=lfun; trace=trace} t in
	of_tacvalue (VRTactic (catch_error trace tac { goal with sigma=sigma }))
    | _ -> v
    else v)
  with
    (** FIXME: Should we add [Errors.push]? *)
    | FailError (0,s) ->
	raise (Eval_fail (Lazy.force s))
    | FailError (lvl,s) as e ->
        raise (Exninfo.copy e (FailError (lvl - 1, s)))

(* Interprets the clauses of a recursive LetIn *)
and interp_letrec ist gl llc u =
  let lref = ref ist.lfun in
  let map ((_, id), b) = (id, of_tacvalue (VRec (lref,TacArg (dloc,b)))) in
  let lve = List.map_left map llc in
  lref := lve@ist.lfun;
  let ist = { ist with lfun = lve@ist.lfun } in
  val_interp ist gl u

(* Interprets the clauses of a LetIn *)
and interp_letin ist gl llc u =
  let (sigma,lve) =
    List.fold_right begin fun ((_,id),body) (sigma,acc) ->
      let (sigma,v) = interp_tacarg ist { gl with sigma=sigma } body in
      check_is_value v;
      sigma, (id,v)::acc
    end llc (project gl,[])
  in
  let ist = { ist with lfun = lve@ist.lfun } in
  val_interp ist { gl with sigma=sigma } u

(* Interprets the Match Context expressions *)
and interp_match_goal ist goal lz lr lmr =
  let (gl,sigma) = Goal.V82.nf_evar (project goal) (sig_it goal) in
  let goal = { it = gl ; sigma = sigma } in
  let hyps = pf_hyps goal in
  let hyps = if lr then List.rev hyps else hyps in
  let concl = pf_concl goal in
  let env = pf_env goal in
  let apply_goal_sub app ist (id,c) csr mt mhyps hyps =
    let matches = match_subterm_gen app c csr in
    let rec match_next_pattern next = match IStream.peek next with
    | None -> raise PatternMatchingFailure
    | Some ({ m_sub=lgoal; m_ctx=ctxt }, next) ->
      let lctxt = give_context ctxt id in
      try apply_hyps_context ist env lz goal mt lctxt (adjust lgoal) mhyps hyps
      with e when is_match_catchable e -> match_next_pattern next in
    match_next_pattern matches
  in
  let rec apply_match_goal ist env goal nrs lex lpt =
    begin
      let () = match lex with
      | r :: _ -> db_pattern_rule ist.debug nrs r
      | _ -> ()
      in
      match lpt with
	| (All t)::tl ->
	    begin
              db_mc_pattern_success ist.debug;
              try eval_with_fail ist lz goal t
              with e when is_match_catchable e ->
		apply_match_goal ist env goal (nrs+1) (List.tl lex) tl
	    end
	| (Pat (mhyps,mgoal,mt))::tl ->
            let mhyps = List.rev mhyps (* Sens naturel *) in
	    (match mgoal with
             | Term mg ->
		 (try
		     let lmatch = extended_matches mg concl in
		     db_matched_concl ist.debug env concl;
		     apply_hyps_context ist env lz goal mt [] lmatch mhyps hyps
		   with e when is_match_catchable e ->
		     (match e with
		       | PatternMatchingFailure -> db_matching_failure ist.debug
		       | Eval_fail s -> db_eval_failure ist.debug s
		       | _ -> db_logic_failure ist.debug e);
		     apply_match_goal ist env goal (nrs+1) (List.tl lex) tl)
	     | Subterm (b,id,mg) ->
		 (try apply_goal_sub b ist (id,mg) concl mt mhyps hyps
		   with
		     | PatternMatchingFailure ->
			 apply_match_goal ist env goal (nrs+1) (List.tl lex) tl))
	| _ ->
	    errorlabstrm "Tacinterp.apply_match_goal"
              (v 0 (str "No matching clauses for match goal" ++
		      (if ist.debug == DebugOff then
			 fnl() ++ str "(use \"Set Ltac Debug\" for more info)"
		       else mt()) ++ str"."))
    end in
    apply_match_goal ist env goal 0 lmr
      (read_match_rule (fst (extract_ltac_constr_values ist env))
	ist env (project goal) lmr)

(* Tries to match the hypotheses in a Match Context *)
and apply_hyps_context ist env lz goal mt lctxt lgmatch mhyps hyps =
  let rec apply_hyps_context_rec lfun lmatch lhyps_rest = function
    | hyp_pat::tl ->
	let (hypname, _, pat as hyp_pat) =
	  match hyp_pat with
	  | Hyp ((_,hypname),mhyp) -> hypname,  None, mhyp
	  | Def ((_,hypname),mbod,mhyp) -> hypname, Some mbod, mhyp
	in
        let rec match_next_pattern next = match IStream.peek next with
        | None ->
          db_hyp_pattern_failure ist.debug env (hypname, pat);
          raise PatternMatchingFailure
        | Some (s, next) ->
	  let lids,hyp_match = s.e_ctx in
          db_matched_hyp ist.debug (pf_env goal) hyp_match hypname;
	  try
            let id_match = pi1 hyp_match in
            let nextlhyps = List.remove_assoc_in_triple id_match lhyps_rest in
            apply_hyps_context_rec (lfun@lids) s.e_sub nextlhyps tl
          with e when is_match_catchable e ->
	    match_next_pattern next in
        let init_match_pattern = apply_one_mhyp_context goal lmatch hyp_pat lhyps_rest in
        match_next_pattern init_match_pattern
    | [] ->
        let lfun = extend_values_with_bindings lmatch (lfun@ist.lfun) in
        db_mc_pattern_success ist.debug;
        eval_with_fail {ist with lfun=lfun} lz goal mt
  in
  apply_hyps_context_rec lctxt lgmatch hyps mhyps

and interp_external loc ist gl com req la =
  let f ch = extern_request ch req gl la in
  let g ch = internalise_tacarg ch in
  interp_tacarg ist gl (System.connect f g com)

  (* Interprets extended tactic generic arguments *)
and interp_genarg ist gl x =
  let evdref = ref (project gl) in
  let rec interp_genarg ist gl x =
    let gl = { gl with sigma = !evdref } in
    match genarg_tag x with
    | BoolArgType -> in_gen (topwit wit_bool) (out_gen (glbwit wit_bool) x)
    | IntArgType -> in_gen (topwit wit_int) (out_gen (glbwit wit_int) x)
    | IntOrVarArgType ->
      in_gen (topwit wit_int_or_var)
        (ArgArg (interp_int_or_var ist (out_gen (glbwit wit_int_or_var) x)))
    | StringArgType ->
      in_gen (topwit wit_string) (out_gen (glbwit wit_string) x)
    | PreIdentArgType ->
      in_gen (topwit wit_pre_ident) (out_gen (glbwit wit_pre_ident) x)
    | IntroPatternArgType ->
      in_gen (topwit wit_intro_pattern)
        (interp_intro_pattern ist gl (out_gen (glbwit wit_intro_pattern) x))
    | IdentArgType b ->
      in_gen (topwit (wit_ident_gen b))
        (pf_interp_fresh_ident ist gl (out_gen (glbwit (wit_ident_gen b)) x))
    | VarArgType ->
      in_gen (topwit wit_var) (interp_hyp ist gl (out_gen (glbwit wit_var) x))
    | RefArgType ->
      in_gen (topwit wit_ref) (pf_interp_reference ist gl (out_gen (glbwit wit_ref) x))
    | GenArgType ->
      in_gen (topwit wit_genarg) (interp_genarg ist gl (out_gen (glbwit wit_genarg) x))
    | SortArgType ->
      let (sigma,c_interp) =
	pf_interp_constr ist gl
	  (GSort (dloc,out_gen (glbwit wit_sort) x), None)
      in
      evdref := sigma;
      in_gen (topwit wit_sort)
        (destSort c_interp)
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
    | List0ArgType ConstrArgType ->
        let (sigma,v) = interp_genarg_constr_list0 ist gl x in
	evdref := sigma;
	v
    | List1ArgType ConstrArgType ->
        let (sigma,v) = interp_genarg_constr_list1 ist gl x in
	evdref := sigma;
	v
    | List0ArgType VarArgType -> interp_genarg_var_list0 ist gl x
    | List1ArgType VarArgType -> interp_genarg_var_list1 ist gl x
    | List0ArgType _ -> app_list0 (interp_genarg ist gl) x
    | List1ArgType _ -> app_list1 (interp_genarg ist gl) x
    | OptArgType _ -> app_opt (interp_genarg ist gl) x
    | PairArgType _ -> app_pair (interp_genarg ist gl) (interp_genarg ist gl) x
    | ExtraArgType s ->
      match tactic_genarg_level s with
      | Some n ->
        let f = VFun(ist.trace,ist.lfun,[],
          out_gen (glbwit (wit_tactic n)) x)
        in
        (* Special treatment of tactic arguments *)
        in_gen (topwit (wit_tactic n)) 
	  (TacArg(dloc,valueIn (of_tacvalue f)))
      | None ->
        let (sigma,v) = lookup_interp_genarg s ist gl x in
	evdref:=sigma;
	v
  in
  let v = interp_genarg ist gl x in
  !evdref , v

and interp_genarg_constr_list0 ist gl x =
  let lc = out_gen (glbwit (wit_list0 wit_constr)) x in
  let (sigma,lc) = pf_apply (interp_constr_list ist) gl lc in
  sigma , in_gen (topwit (wit_list0 wit_constr)) lc

and interp_genarg_constr_list1 ist gl x =
  let lc = out_gen (glbwit (wit_list1 wit_constr)) x in
  let (sigma,lc) = pf_apply (interp_constr_list ist) gl lc in
  sigma , in_gen (topwit (wit_list1 wit_constr)) lc

and interp_genarg_var_list0 ist gl x =
  let lc = out_gen (glbwit (wit_list0 wit_var)) x in
  let lc = interp_hyp_list ist gl lc in
  in_gen (topwit (wit_list0 wit_var)) lc

and interp_genarg_var_list1 ist gl x =
  let lc = out_gen (glbwit (wit_list1 wit_var)) x in
  let lc = interp_hyp_list ist gl lc in
  in_gen (topwit (wit_list1 wit_var)) lc

(* Interprets the Match expressions *)
and interp_match ist g lz constr lmr =
  let apply_match_subterm app ist (id,c) csr mt =
    let rec match_next_pattern next = match IStream.peek next with
    | None -> raise PatternMatchingFailure
    | Some ({ m_sub=lmatch; m_ctx=ctxt; }, next) ->
      let lctxt = give_context ctxt id in
      let lfun = extend_values_with_bindings (adjust lmatch) (lctxt@ist.lfun) in
      try eval_with_fail {ist with lfun=lfun} lz g mt
      with e when is_match_catchable e -> match_next_pattern next in
    match_next_pattern (match_subterm_gen app c csr) in
  let rec apply_match ist sigma csr = let g = { g with sigma=sigma } in function
    | (All t)::tl ->
        (try eval_with_fail ist lz g t
         with e when is_match_catchable e -> apply_match ist sigma csr tl)
    | (Pat ([],Term c,mt))::tl ->
        (try
            let lmatch =
              try extended_matches c csr
              with reraise ->
                let reraise = Errors.push reraise in
                debugging_exception_step ist false reraise (fun () ->
                  str "matching with pattern" ++ fnl () ++
                  pr_constr_pattern_env (pf_env g) c);
                raise reraise
            in
            try
              let lfun = extend_values_with_bindings lmatch ist.lfun in
              eval_with_fail { ist with lfun=lfun } lz g mt
            with reraise ->
              let reraise = Errors.push reraise in
              debugging_exception_step ist false reraise (fun () ->
                str "rule body for pattern" ++
                pr_constr_pattern_env (pf_env g) c);
              raise reraise
         with e when is_match_catchable e ->
           debugging_step ist (fun () -> str "switching to the next rule");
           apply_match ist sigma csr tl)

    | (Pat ([],Subterm (b,id,c),mt))::tl ->
        (try apply_match_subterm b ist (id,c) csr mt
         with PatternMatchingFailure -> apply_match ist sigma csr tl)
    | _ ->
      errorlabstrm "Tacinterp.apply_match" (str
        "No matching clauses for match.") in
  let (sigma,csr) =
      try interp_ltac_constr ist g constr
      with reraise ->
       let reraise = Errors.push reraise in
        debugging_exception_step ist true reraise
          (fun () -> str "evaluation of the matched expression");
        raise reraise
  in
  let ilr = read_match_rule (fst (extract_ltac_constr_values ist (pf_env g))) ist (pf_env g) sigma lmr in
  let res =
     try apply_match ist sigma csr ilr
     with reraise ->
       let reraise = Errors.push reraise in
       debugging_exception_step ist true reraise
         (fun () -> str "match expression");
       raise reraise
  in
  debugging_step ist (fun () ->
    str "match expression returns " ++ pr_value (Some (pf_env g)) (snd res));
  res

(* Interprets tactic expressions : returns a "constr" *)
and interp_ltac_constr ist gl e =
  let (sigma, result) =
  try val_interp ist gl e with Not_found ->
    debugging_step ist (fun () ->
      str "evaluation failed for" ++ fnl() ++
      Pptactic.pr_glob_tactic (pf_env gl) e);
    raise Not_found in
  let result = Value.normalize result in
  try
    let cresult = coerce_to_constr (pf_env gl) result in
    debugging_step ist (fun () ->
      Pptactic.pr_glob_tactic (pf_env gl) e ++ fnl() ++
      str " has value " ++ fnl() ++
      pr_constr_under_binders_env (pf_env gl) cresult);
    if not (List.is_empty (fst cresult)) then raise Not_found;
    sigma , snd cresult
  with Not_found ->
    errorlabstrm ""
      (str "Must evaluate to a closed term" ++ fnl() ++
	  str "offending expression: " ++ fnl() ++
          Pptactic.pr_glob_tactic (pf_env gl) e ++ fnl() ++ str "this is a " ++
          (if has_type result (topwit wit_tacvalue) then match to_tacvalue result with
            | VRTactic _ -> str "VRTactic"
            | VFun (_,il,ul,b) ->
                (str "VFun with body " ++ fnl() ++
                    Pptactic.pr_glob_tactic (pf_env gl) b ++ fnl() ++
		    str "instantiated arguments " ++ fnl() ++
                    List.fold_right
                    (fun p s ->
                      let (i,v) = p in str (Id.to_string i) ++ str ", " ++ s)
                    il (str "") ++
                    str "uninstantiated arguments " ++ fnl() ++
                    List.fold_right
                    (fun opt_id s ->
                      (match opt_id with
                          Some id -> str (Id.to_string id)
                        | None -> str "_") ++ str ", " ++ s)
                    ul (mt()))
(*             | VVoid -> str "VVoid" *)
(*             | VInteger _ -> str "VInteger" *)
(*             | VConstr _ -> str "VConstr" *)
(*             | VIntroPattern _ -> str "VIntroPattern" *)
(*             | VConstr_context _ -> str "VConstrr_context" *)
            | VRec _ -> str "VRec"
(*            | VList _ -> str "VList"*)
          else str "unknown object") ++ str".")

(* Interprets tactic expressions : returns a "tactic" *)
and interp_tactic ist tac gl =
  let (sigma,v) = val_interp ist gl tac in
  tactic_of_value ist v { gl with sigma=sigma }

(* Interprets a primitive tactic *)
and interp_atomic ist gl tac =
  let env = pf_env gl and sigma = project gl in
  match tac with
  (* Basic tactics *)
  | TacIntroPattern l ->
      h_intro_patterns (interp_intro_pattern_list_as_list ist gl l)
  | TacIntrosUntil hyp ->
      h_intros_until (interp_quantified_hypothesis ist hyp)
  | TacIntroMove (ido,hto) ->
      h_intro_move (Option.map (interp_fresh_ident ist env) ido)
                   (interp_move_location ist gl hto)
  | TacAssumption -> h_assumption
  | TacExact c ->
      let (sigma,c_interp) = pf_interp_casted_constr ist gl c in
      tclTHEN
	(tclEVARS sigma)
	(h_exact c_interp)
  | TacExactNoCheck c ->
      let (sigma,c_interp) = pf_interp_constr ist gl c in
      tclTHEN
	(tclEVARS sigma)
	(h_exact_no_check c_interp)
  | TacVmCastNoCheck c ->
      let (sigma,c_interp) = pf_interp_constr ist gl c in
      tclTHEN
	(tclEVARS sigma)
	(h_vm_cast_no_check c_interp)
  | TacApply (a,ev,cb,cl) ->
      let sigma, l =
        List.fold_map (interp_open_constr_with_bindings_loc ist env) sigma cb
      in
      let tac = match cl with
        | None -> h_apply a ev
        | Some cl ->
            (fun l -> h_apply_in a ev l (interp_in_hyp_as ist gl cl)) in
      tclWITHHOLES ev tac sigma l
  | TacElim (ev,cb,cbo) ->
      let sigma, cb = interp_constr_with_bindings ist env sigma cb in
      let sigma, cbo = Option.fold_map (interp_constr_with_bindings ist env) sigma cbo in
      tclWITHHOLES ev (h_elim ev cb) sigma cbo
  | TacElimType c ->
      let (sigma,c_interp) = pf_interp_type ist gl c in
      tclTHEN
	(tclEVARS sigma)
	(h_elim_type c_interp)
  | TacCase (ev,cb) ->
      let sigma, cb = interp_constr_with_bindings ist env sigma cb in
      tclWITHHOLES ev (h_case ev) sigma cb
  | TacCaseType c ->
      let (sigma,c_interp) = pf_interp_type ist gl c in
      tclTHEN
	(tclEVARS sigma)
	(h_case_type c_interp)
  | TacFix (idopt,n) -> h_fix (Option.map (interp_fresh_ident ist env) idopt) n
  | TacMutualFix (id,n,l) ->
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
  | TacCofix idopt -> h_cofix (Option.map (interp_fresh_ident ist env) idopt)
  | TacMutualCofix (id,l) ->
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
  | TacCut c ->
      let (sigma,c_interp) = pf_interp_type ist gl c in
      tclTHEN
	(tclEVARS sigma)
	(h_cut c_interp)
  | TacAssert (t,ipat,c) ->
      let (sigma,c) = (if Option.is_empty t then interp_constr else interp_type) ist env sigma c in
      tclTHEN
	(tclEVARS sigma)
        (Tactics.forward (Option.map (interp_tactic ist) t)
	   (Option.map (interp_intro_pattern ist gl) ipat) c)
  | TacGeneralize cl ->
      let sigma, cl = interp_constr_with_occurrences_and_name_as_list ist env sigma cl in
      tclWITHHOLES false (h_generalize_gen) sigma cl
  | TacGeneralizeDep c ->
      let (sigma,c_interp) = pf_interp_constr ist gl c in
      tclTHEN
	(tclEVARS sigma)
	(h_generalize_dep c_interp)
  | TacLetTac (na,c,clp,b,eqpat) ->
      let clp = interp_clause ist gl clp in
      let eqpat = Option.map (interp_intro_pattern ist gl) eqpat in
      if Locusops.is_nowhere clp then
        (* We try to fully-typecheck the term *)
	let (sigma,c_interp) = pf_interp_constr ist gl c in
	tclTHEN
	  (tclEVARS sigma)
          (h_let_tac b (interp_fresh_name ist env na) c_interp clp eqpat)
      else
        (* We try to keep the pattern structure as much as possible *)
        h_let_pat_tac b (interp_fresh_name ist env na)
          (interp_pure_open_constr ist env sigma c) clp eqpat

  (* Automation tactics *)
  | TacTrivial (debug,lems,l) ->
      Auto.h_trivial ~debug
	(interp_auto_lemmas ist env sigma lems)
	(Option.map (List.map (interp_hint_base ist)) l)
  | TacAuto (debug,n,lems,l) ->
      Auto.h_auto ~debug (Option.map (interp_int_or_var ist) n)
	(interp_auto_lemmas ist env sigma lems)
	(Option.map (List.map (interp_hint_base ist)) l)

  (* Derived basic tactics *)
  | TacSimpleInductionDestruct (isrec,h) ->
      h_simple_induction_destruct isrec (interp_quantified_hypothesis ist h)
  | TacInductionDestruct (isrec,ev,(l,el,cls)) ->
      let sigma, l =
        List.fold_map (fun sigma (c,(ipato,ipats)) ->
          let c = interp_induction_arg ist gl c in
          (sigma,(c,
            (Option.map (interp_intro_pattern ist gl) ipato,
	     Option.map (interp_intro_pattern ist gl) ipats)))) sigma l in
      let sigma,el =
        Option.fold_map (interp_constr_with_bindings ist env) sigma el in
      let cls = Option.map (interp_clause ist gl) cls in
      tclWITHHOLES ev (h_induction_destruct isrec ev) sigma (l,el,cls)
  | TacDoubleInduction (h1,h2) ->
      let h1 = interp_quantified_hypothesis ist h1 in
      let h2 = interp_quantified_hypothesis ist h2 in
      Elim.h_double_induction h1 h2
  | TacDecomposeAnd c ->
      let (sigma,c_interp) = pf_interp_constr ist gl c in
      tclTHEN
	(tclEVARS sigma)
	(Elim.h_decompose_and c_interp)
  | TacDecomposeOr c ->
      let (sigma,c_interp) = pf_interp_constr ist gl c in
      tclTHEN
	(tclEVARS sigma)
	(Elim.h_decompose_or c_interp)
  | TacDecompose (l,c) ->
      let l = List.map (interp_inductive ist) l in
      let (sigma,c_interp) = pf_interp_constr ist gl c in
      tclTHEN
	(tclEVARS sigma)
	(Elim.h_decompose l c_interp)
  | TacSpecialize (n,cb) ->
      let sigma, cb = interp_constr_with_bindings ist env sigma cb in
      tclWITHHOLES false (h_specialize n) sigma cb
  | TacLApply c ->
      let (sigma,c_interp) = pf_interp_constr ist gl c in
      tclTHEN
	(tclEVARS sigma)
	(h_lapply c_interp)

  (* Context management *)
  | TacClear (b,l) -> h_clear b (interp_hyp_list ist gl l)
  | TacClearBody l -> h_clear_body (interp_hyp_list ist gl l)
  | TacMove (dep,id1,id2) ->
      h_move dep (interp_hyp ist gl id1) (interp_move_location ist gl id2)
  | TacRename l ->
      h_rename (List.map (fun (id1,id2) ->
			    interp_hyp ist gl id1,
			    interp_fresh_ident ist env (snd id2)) l)
  | TacRevert l -> h_revert (interp_hyp_list ist gl l)

  (* Constructors *)
  | TacLeft (ev,bl) ->
      let sigma, bl = interp_bindings ist env sigma bl in
      tclWITHHOLES ev (h_left ev) sigma bl
  | TacRight (ev,bl) ->
      let sigma, bl = interp_bindings ist env sigma bl in
      tclWITHHOLES ev (h_right ev) sigma bl
  | TacSplit (ev,_,bll) ->
      let sigma, bll = List.fold_map (interp_bindings ist env) sigma bll in
      tclWITHHOLES ev (h_split ev) sigma bll
  | TacAnyConstructor (ev,t) ->
      Tactics.any_constructor ev (Option.map (interp_tactic ist) t)
  | TacConstructor (ev,n,bl) ->
      let sigma, bl = interp_bindings ist env sigma bl in
      tclWITHHOLES ev (h_constructor ev (interp_int_or_var ist n)) sigma bl

  (* Conversion *)
  | TacReduce (r,cl) ->
      let (sigma,r_interp) = pf_interp_red_expr ist gl r in
      tclTHEN
	(tclEVARS sigma)
	(h_reduce r_interp (interp_clause ist gl cl))
  | TacChange (None,c,cl) ->
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
  | TacChange (Some op,c,cl) ->
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

  (* Equivalence relations *)
  | TacReflexivity -> h_reflexivity
  | TacSymmetry c -> h_symmetry (interp_clause ist gl c)
  | TacTransitivity c ->
    begin match c with
    | None -> h_transitivity None
    | Some c ->
      let (sigma,c_interp) = pf_interp_constr ist gl c in
      tclTHEN
	(tclEVARS sigma)
	(h_transitivity (Some c_interp))
    end

  (* Equality and inversion *)
  | TacRewrite (ev,l,cl,by) ->
      let l = List.map (fun (b,m,c) ->
        let f env sigma = interp_open_constr_with_bindings ist env sigma c in
	(b,m,f)) l in
      let cl = interp_clause ist gl cl in
      Equality.general_multi_multi_rewrite ev l cl
        (Option.map (fun by -> tclCOMPLETE (interp_tactic ist by), Equality.Naive) by)
  | TacInversion (DepInversion (k,c,ids),hyp) ->
      let (sigma,c_interp) =
	match c with
	| None -> sigma , None
	| Some c ->
	  let (sigma,c_interp) = pf_interp_constr ist gl c in
	  sigma , Some c_interp
      in
      Inv.dinv k c_interp
        (Option.map (interp_intro_pattern ist gl) ids)
        (interp_declared_or_quantified_hypothesis ist gl hyp)
  | TacInversion (NonDepInversion (k,idl,ids),hyp) ->
      Inv.inv_clause k
        (Option.map (interp_intro_pattern ist gl) ids)
        (interp_hyp_list ist gl idl)
        (interp_declared_or_quantified_hypothesis ist gl hyp)
  | TacInversion (InversionUsing (c,idl),hyp) ->
      let (sigma,c_interp) = pf_interp_constr ist gl c in
      Leminv.lemInv_clause (interp_declared_or_quantified_hypothesis ist gl hyp)
        c_interp
        (interp_hyp_list ist gl idl)

  (* For extensions *)
  | TacExtend (loc,opn,l) ->
      let tac = lookup_tactic opn in
      let (sigma,args) = 
	List.fold_right begin fun a (sigma,acc) ->
	  let (sigma,a_interp) = interp_genarg ist { gl with sigma=sigma } a in
	  sigma , a_interp::acc
	end l (project gl,[])
      in
      tac args ist
  | TacAlias (loc,s,l,(_,body)) -> fun gl ->
    let evdref = ref gl.sigma in
    let rec f x = match genarg_tag x with
    | IntArgType ->
        in_gen (topwit wit_int) (out_gen (glbwit wit_int) x)
    | IntOrVarArgType ->
        mk_int_or_var_value ist (out_gen (glbwit wit_int_or_var) x)
    | PreIdentArgType ->
	failwith "pre-identifiers cannot be bound"
    | IntroPatternArgType ->
	let ipat = interp_intro_pattern ist gl (out_gen (glbwit wit_intro_pattern) x) in
	in_gen (topwit wit_intro_pattern) ipat
    | IdentArgType b ->
	value_of_ident (interp_fresh_ident ist env
	  (out_gen (glbwit (wit_ident_gen b)) x))
    | VarArgType ->
        mk_hyp_value ist gl (out_gen (glbwit wit_var) x)
    | RefArgType ->
        Value.of_constr (constr_of_global
          (pf_interp_reference ist gl (out_gen (glbwit wit_ref) x)))
    | GenArgType -> f (out_gen (glbwit wit_genarg) x)
    | SortArgType ->
        Value.of_constr (mkSort (interp_sort (out_gen (glbwit wit_sort) x)))
    | ConstrArgType ->
        let (sigma,v) = mk_constr_value ist gl (out_gen (glbwit wit_constr) x) in
	evdref := sigma;
	v
    | OpenConstrArgType false ->
        let (sigma,v) = mk_open_constr_value ist gl (snd (out_gen (glbwit wit_open_constr) x)) in
	evdref := sigma;
	v
    | ConstrMayEvalArgType ->
        let (sigma,c_interp) = interp_constr_may_eval ist gl (out_gen (glbwit wit_constr_may_eval) x) in
	evdref := sigma;
	Value.of_constr c_interp
    | ExtraArgType s when not (Option.is_empty (tactic_genarg_level s)) ->
          (* Special treatment of tactic arguments *)
	let (sigma,v) = val_interp ist gl
          (out_gen (glbwit (wit_tactic (Option.get (tactic_genarg_level s)))) x)
	in
	evdref := sigma;
	v
    | List0ArgType ConstrArgType ->
        let wit = glbwit (wit_list0 wit_constr) in
	let (sigma,l_interp) =
	  List.fold_right begin fun c (sigma,acc) ->
	    let (sigma,c_interp) = mk_constr_value ist { gl with sigma=sigma } c in
	    sigma , c_interp::acc
	  end (out_gen wit x) (project gl,[])
	in
	evdref := sigma;
        in_gen (topwit (wit_list0 wit_genarg)) l_interp
    | List0ArgType VarArgType ->
        let wit = glbwit (wit_list0 wit_var) in
        let ans = List.map (mk_hyp_value ist gl) (out_gen wit x) in
        in_gen (topwit (wit_list0 wit_genarg)) ans
    | List0ArgType IntArgType ->
        let wit = glbwit (wit_list0 wit_int) in
        let ans = List.map (fun x -> in_gen (topwit wit_int) x) (out_gen wit x) in
        in_gen (topwit (wit_list0 wit_genarg)) ans
    | List0ArgType IntOrVarArgType ->
        let wit = glbwit (wit_list0 wit_int_or_var) in
        let ans = List.map (mk_int_or_var_value ist) (out_gen wit x) in
        in_gen (topwit (wit_list0 wit_genarg)) ans
    | List0ArgType (IdentArgType b) ->
        let wit = glbwit (wit_list0 (wit_ident_gen b)) in
	let mk_ident x = value_of_ident (interp_fresh_ident ist env x) in
	let ans = List.map mk_ident (out_gen wit x) in
        in_gen (topwit (wit_list0 wit_genarg)) ans
    | List0ArgType IntroPatternArgType ->
        let wit = glbwit (wit_list0 wit_intro_pattern) in
	let mk_ipat x = interp_intro_pattern ist gl x in
	let ans = List.map mk_ipat (out_gen wit x) in
        in_gen (topwit (wit_list0 wit_intro_pattern)) ans
    | List1ArgType ConstrArgType ->
        let wit = glbwit (wit_list1 wit_constr) in
	let (sigma, l_interp) =
	  List.fold_right begin fun c (sigma,acc) ->
	    let (sigma,c_interp) = mk_constr_value ist { gl with sigma=sigma } c in
	    sigma , c_interp::acc
	  end (out_gen wit x) (project gl,[])
	in
	evdref:=sigma;
        in_gen (topwit (wit_list1 wit_genarg)) l_interp
    | List1ArgType VarArgType ->
        let wit = glbwit (wit_list1 wit_var) in
        let ans = List.map (mk_hyp_value ist gl) (out_gen wit x) in
        in_gen (topwit (wit_list1 wit_genarg)) ans
    | List1ArgType IntArgType ->
        let wit = glbwit (wit_list1 wit_int) in
        let ans = List.map (fun x -> in_gen (topwit wit_int) x) (out_gen wit x) in
        in_gen (topwit (wit_list1 wit_genarg)) ans
    | List1ArgType IntOrVarArgType ->
        let wit = glbwit (wit_list1 wit_int_or_var) in
        let ans = List.map (mk_int_or_var_value ist) (out_gen wit x) in
        in_gen (topwit (wit_list1 wit_genarg)) ans
    | List1ArgType (IdentArgType b) ->
        let wit = glbwit (wit_list1 (wit_ident_gen b)) in
	let mk_ident x = value_of_ident (interp_fresh_ident ist env x) in
	let ans = List.map mk_ident (out_gen wit x) in
        in_gen (topwit (wit_list1 wit_genarg)) ans
    | List1ArgType IntroPatternArgType ->
        let wit = glbwit (wit_list1 wit_intro_pattern) in
	let mk_ipat x = interp_intro_pattern ist gl x in
	let ans = List.map mk_ipat (out_gen wit x) in
        in_gen (topwit (wit_list1 wit_intro_pattern)) ans
    | StringArgType | BoolArgType
    | QuantHypArgType | RedExprArgType
    | OpenConstrArgType _ | ConstrWithBindingsArgType
    | ExtraArgType _ | BindingsArgType
    | OptArgType _ | PairArgType _
    | List0ArgType _ | List1ArgType _
	-> error "This argument type is not supported in tactic notations."

    in
    let lfun = (List.map (fun (x,c) -> (x,f c)) l)@ist.lfun in
    let trace = push_trace (loc,LtacNotationCall s) ist.trace in
    let gl = { gl with sigma = !evdref } in
    interp_tactic { ist with lfun=lfun; trace=trace } body gl

(* Initial call for interpretation *)

let eval_tactic t gls =
  db_initialize ();
  interp_tactic { lfun=[]; avoid_ids=[]; debug=get_debug(); trace=[] }
    t gls

(* globalization + interpretation *)

let interp_tac_gen lfun avoid_ids debug t gl =
  interp_tactic { lfun=lfun; avoid_ids=avoid_ids; debug=debug; trace=[] }
    (intern_pure_tactic {
      ltacvars = (List.map fst lfun, []); ltacrecvars = [];
      gsigma = project gl; genv = pf_env gl } t) gl

let interp t = interp_tac_gen [] [] (get_debug()) t

let eval_ltac_constr gl t =
  interp_ltac_constr
    { lfun=[]; avoid_ids=[]; debug=get_debug(); trace=[] } gl
    (intern_tactic_or_tacarg (make_empty_glob_sign ()) t )

(* Used to hide interpretation for pretty-print, now just launch tactics *)
let hide_interp t ot gl =
  let ist = { ltacvars = ([],[]); ltacrecvars = [];
            gsigma = project gl; genv = pf_env gl } in
  let te = intern_pure_tactic ist t in
  let t = eval_tactic te in
  match ot with
  | None -> t gl
  | Some t' -> (tclTHEN t t') gl


(***************************************************************************)
(* Other entry points *)

let interp_redexp env sigma r =
  let ist = { lfun=[]; avoid_ids=[]; debug=get_debug (); trace=[] } in
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
    let l = Id.Map.map (fun c -> Value.of_constr c) l in
    interp_tactic {lfun=Id.Map.bindings l;avoid_ids=[];debug=get_debug(); trace=[]})
