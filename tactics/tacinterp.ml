(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Constrintern
open Patternops
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
open Genarg
open Stdarg
open Constrarg
open Printer
open Pretyping
module Monad_ = Monad
open Evd
open Misctypes
open Locus
open Tacintern
open Taccoerce
open Proofview.Notations

let safe_msgnl s =
  Proofview.NonLogical.catch
    (Proofview.NonLogical.print (s++fnl()))
    (fun _ -> Proofview.NonLogical.print (str "bug in the debugger: an exception is raised while printing debug information"++fnl()))

type value = tlevel generic_argument

(* Values for interpretation *)
type tacvalue =
  | VFun of ltac_trace * value Id.Map.t *
      Id.t option list * glob_tactic_expr
  | VRec of value Id.Map.t ref * glob_tactic_expr

let (wit_tacvalue : (Empty.t, Empty.t, tacvalue) Genarg.genarg_type) =
  Genarg.create_arg None "tacvalue"

let of_tacvalue v = in_gen (topwit wit_tacvalue) v
let to_tacvalue v = out_gen (topwit wit_tacvalue) v

module TacStore = Geninterp.TacStore

let f_avoid_ids : Id.t list TacStore.field = TacStore.field ()
(* ids inherited from the call context (needed to get fresh ids) *)
let f_debug : debug_info TacStore.field = TacStore.field ()
let f_trace : ltac_trace TacStore.field = TacStore.field ()

(* Signature for interpretation: val_interp and interpretation functions *)
type interp_sign = Geninterp.interp_sign = {
  lfun : value Id.Map.t;
  extra : TacStore.t }

let extract_trace ist = match TacStore.get ist.extra f_trace with
| None -> []
| Some l -> l

module Value = struct

  include Taccoerce.Value

  let of_closure ist tac =
    let closure = VFun (extract_trace ist, ist.lfun, [], tac) in
    of_tacvalue closure

end

let dloc = Loc.ghost

let catching_error call_trace fail e =
  let inner_trace =
    Option.default [] (Exninfo.get e ltac_trace_info)
  in
  if List.is_empty call_trace && List.is_empty inner_trace then fail e
  else begin
    assert (Errors.noncritical e); (* preserved invariant *)
    let new_trace = inner_trace @ call_trace in
    let located_exc = Exninfo.add e ltac_trace_info new_trace in
    fail located_exc
  end

let catch_error call_trace f x =
  try f x
  with e when Errors.noncritical e ->
    let e = Errors.push e in
    catching_error call_trace raise e

let catch_error_tac call_trace tac =
  Proofview.tclORELSE
    tac
    (catching_error call_trace Proofview.tclZERO)

let curr_debug ist = match TacStore.get ist.extra f_debug with
| None -> DebugOff
| Some level -> level

(** TODO: unify printing of generic Ltac values in case of coercion failure. *)

(* Displays a value *)
let pr_value env v =
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then str "a tactic"
  else if has_type v (topwit wit_constr_context) then
    let c = out_gen (topwit wit_constr_context) v in
    match env with
    | Some (env,sigma) -> pr_lconstr_env env sigma c
    | _ -> str "a term"
  else if has_type v (topwit wit_constr) then
    let c = out_gen (topwit wit_constr) v in
    match env with
    | Some (env,sigma) -> pr_lconstr_env env sigma c
    | _ -> str "a term"
  else if has_type v (topwit wit_constr_under_binders) then
    let c = out_gen (topwit wit_constr_under_binders) v in
    match env with
    | Some (env,sigma) -> pr_lconstr_under_binders_env env sigma c
    | _ -> str "a term"
  else
    str "a value of type" ++ spc () ++ pr_argument_type (genarg_tag v)

let pr_closure env ist body =
  let pp_body = Pptactic.pr_glob_tactic env body in
  let pr_sep () = fnl () in
  let pr_iarg (id, arg) =
    let arg = pr_argument_type (genarg_tag arg) in
    hov 0 (pr_id id ++ spc () ++ str ":" ++ spc () ++ arg)
  in
  let pp_iargs = v 0 (prlist_with_sep pr_sep pr_iarg (Id.Map.bindings ist)) in
  pp_body ++ fnl() ++ str "in environment " ++ fnl() ++ pp_iargs

let pr_inspect env expr result =
  let pp_expr = Pptactic.pr_glob_tactic env expr in
  let pp_result =
    if has_type result (topwit wit_tacvalue) then
    match to_tacvalue result with
    | VFun (_, ist, ul, b) ->
      let body = if List.is_empty ul then b else (TacFun (ul, b)) in
      str "a closure with body " ++ fnl() ++ pr_closure env ist body
    | VRec (ist, body) ->
      str "a recursive closure" ++ fnl () ++ pr_closure env !ist body
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

(** Generic arguments : table of interpretation functions *)

let push_trace call ist = match TacStore.get ist.extra f_trace with
| None -> [call]
| Some trace -> call :: trace

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
    | VFun _ -> v
    | _ -> fail ()
  else fail ()

let value_of_ident id =
  in_gen (topwit wit_intro_pattern)
    (Loc.ghost, IntroNaming (IntroIdentifier id))

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
  | _ -> Proofview.NonLogical.ret ()

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

let interp_ident_gen fresh ist env sigma id =
  try try_interp_ltac_var (coerce_to_ident fresh env) ist (Some (env,sigma)) (dloc,id)
  with Not_found -> id

let interp_ident = interp_ident_gen false
let interp_fresh_ident = interp_ident_gen true
let pf_interp_ident id gl = interp_ident_gen false id (pf_env gl) (project gl)

(* Interprets an optional identifier which must be fresh *)
let interp_fresh_name ist env sigma = function
  | Anonymous -> Anonymous
  | Name id -> Name (interp_fresh_ident ist env sigma id)

let interp_intro_pattern_var loc ist env sigma id =
  try try_interp_ltac_var (coerce_to_intro_pattern env) ist (Some (env,sigma)) (loc,id)
  with Not_found -> IntroNaming (IntroIdentifier id)

let interp_intro_pattern_naming_var loc ist env sigma id =
  try try_interp_ltac_var (coerce_to_intro_pattern_naming env) ist (Some (env,sigma)) (loc,id)
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
let interp_hyp ist env sigma (loc,id as locid) =
  (* Look first in lfun for a value coercible to a variable *)
  try try_interp_ltac_var (coerce_to_hyp env) ist (Some (env,sigma)) locid
  with Not_found ->
  (* Then look if bound in the proof context at calling time *)
  if is_variable env id then id
  else Loc.raise loc (Logic.RefinerError (Logic.NoSuchHyp id))

let interp_hyp_list_as_list ist env sigma (loc,id as x) =
  try coerce_to_hyp_list env (Id.Map.find id ist.lfun)
  with Not_found | CannotCoerceTo _ -> [interp_hyp ist env sigma x]

let interp_hyp_list ist env sigma l =
  List.flatten (List.map (interp_hyp_list_as_list ist env sigma) l)

let interp_move_location ist env sigma = function
  | MoveAfter id -> MoveAfter (interp_hyp ist env sigma id)
  | MoveBefore id -> MoveBefore (interp_hyp ist env sigma id)
  | MoveFirst -> MoveFirst
  | MoveLast -> MoveLast

let interp_reference ist env sigma = function
  | ArgArg (_,r) -> r
  | ArgVar (loc, id) ->
    try try_interp_ltac_var (coerce_to_reference env) ist (Some (env,sigma)) (loc, id)
    with Not_found ->
      try
        let (v, _, _) = Environ.lookup_named id env in
        VarRef v
      with Not_found -> error_global_not_found_loc loc (qualid_of_ident id)

let try_interp_evaluable env (loc, id) =
  let v = Environ.lookup_named id env in
  match v with
  | (_, Some _, _) -> EvalVarRef id
  | _ -> error_not_evaluable (VarRef id)

let interp_evaluable ist env sigma = function
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
    try try_interp_ltac_var (coerce_to_evaluable_ref env) ist (Some (env,sigma)) (loc, id)
    with Not_found ->
      try try_interp_evaluable env (loc, id)
      with Not_found -> error_global_not_found_loc loc (qualid_of_ident id)

(* Interprets an hypothesis name *)
let interp_occurrences ist occs =
  Locusops.occurrences_map (interp_int_or_var_list ist) occs

let interp_hyp_location ist env sigma ((occs,id),hl) =
  ((interp_occurrences ist occs,interp_hyp ist env sigma id),hl)

let interp_hyp_location_list_as_list ist env sigma ((occs,id),hl as x) =
  match occs,hl with
  | AllOccurrences,InHyp ->
      List.map (fun id -> ((AllOccurrences,id),InHyp))
        (interp_hyp_list_as_list ist env sigma id)
  | _,_ -> [interp_hyp_location ist env sigma x]

let interp_hyp_location_list ist env sigma l =
  List.flatten (List.map (interp_hyp_location_list_as_list ist env sigma) l)

let interp_clause ist env sigma { onhyps=ol; concl_occs=occs } : clause =
  { onhyps=Option.map (interp_hyp_location_list ist env sigma) ol;
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
  | IntroNaming (IntroIdentifier id) -> [id]
  | IntroAction (IntroOrAndPattern ll) ->
      List.flatten (List.map intropattern_ids (List.flatten ll))
  | IntroAction (IntroInjection l) ->
      List.flatten (List.map intropattern_ids l)
  | IntroAction (IntroApplyOn (c,pat)) -> intropattern_ids pat
  | IntroNaming (IntroAnonymous | IntroFresh _)
  | IntroAction (IntroWildcard | IntroRewrite _)
  | IntroForthcoming _ -> []

let extract_ids ids lfun =
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

let interp_fresh_id ist env sigma l =
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
	  | ArgVar (_,id) -> Id.to_string (interp_ident ist env sigma id)) l) in
      let s = if Lexer.is_keyword s then s^"0" else s in
      Id.of_string s in
  Tactics.fresh_id_in_env avoid id env



(* Extract the uconstr list from lfun *)
let extract_ltac_constr_context ist env =
  let open Glob_term in
  let add_uconstr id env v map =
    try Id.Map.add id (coerce_to_uconstr env v) map
    with CannotCoerceTo _ -> map
  in
  let add_constr id env v map =
    try Id.Map.add id (coerce_to_constr env v) map
    with CannotCoerceTo _ -> map
  in
  let add_ident id env v map =
    try Id.Map.add id (coerce_to_ident false env v) map
    with CannotCoerceTo _ -> map
  in
  let fold id v {idents;typed;untyped} =
    let idents = add_ident id env v idents in
    let typed = add_constr id env v typed in
    let untyped = add_uconstr id env v untyped in
    { idents ; typed ; untyped }
  in
  let empty =  { idents = Id.Map.empty ;typed = Id.Map.empty ; untyped = Id.Map.empty } in
  Id.Map.fold fold ist.lfun empty

(** Significantly simpler than [interp_constr], to interpret an
    untyped constr, it suffices to adjoin a closure environment. *)
let interp_uconstr ist env = function
  | (term,None) ->
      { closure = extract_ltac_constr_context ist env ; term }
  | (_,Some ce) ->
      let ( {typed ; untyped } as closure) = extract_ltac_constr_context ist env in
      let ltacvars = {
        Constrintern.ltac_vars = Id.(Set.union (Map.domain typed) (Map.domain untyped));
        ltac_bound = Id.Map.domain ist.lfun;
      } in
      { closure ; term =  intern_gen WithoutTypeConstraint ~ltacvars env ce }

let interp_gen kind ist allow_patvar flags env sigma (c,ce) =
  let constrvars = extract_ltac_constr_context ist env in
  let vars = {
    Pretyping.ltac_constrs = constrvars.typed;
    Pretyping.ltac_uconstrs = constrvars.untyped;
    Pretyping.ltac_idents = constrvars.idents;
    Pretyping.ltac_genargs = ist.lfun;
  } in
  let c = match ce with
  | None -> c
    (* If at toplevel (ce<>None), the error can be due to an incorrect
       context at globalization time: we retype with the now known
       intros/lettac/inversion hypothesis names *)
  | Some c ->
      let constr_context =
        Id.Set.union
          (Id.Map.domain constrvars.typed)
       (Id.Set.union
          (Id.Map.domain constrvars.untyped)
          (Id.Map.domain constrvars.idents))
      in
      let ltacvars = {
        ltac_vars = constr_context;
        ltac_bound = Id.Map.domain ist.lfun;
      } in
      intern_gen kind ~allow_patvar ~ltacvars env c
  in
  let trace =
    push_trace (loc_of_glob_constr c,LtacConstrInterp (c,vars)) ist in
  let (evd,c) =
    catch_error trace (understand_ltac flags env sigma vars kind) c
  in
  (* spiwack: to avoid unnecessary modifications of tacinterp, as this
     function already use effect, I call [run] hoping it doesn't mess
     up with any assumption. *)
  Proofview.NonLogical.run (db_constr (curr_debug ist) env c);
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
  pattern_of_constr env sigma c

(* Interprets a constr expression casted by the current goal *)
let pf_interp_casted_constr ist gl c =
  interp_constr_gen (OfType (pf_concl gl)) ist (pf_env gl) (project gl) c

(* Interprets a constr expression *)
let pf_interp_constr ist gl =
  interp_constr ist (pf_env gl) (project gl)

let new_interp_constr ist c k =
  let open Proofview in
  Proofview.Goal.enter begin fun gl ->
    let (sigma, c) = interp_constr ist (Goal.env gl) (Goal.sigma gl) c in
    Proofview.tclTHEN (Proofview.V82.tclEVARS sigma) (k c)
  end

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
let interp_unfold ist env sigma (occs,qid) =
  (interp_occurrences ist occs,interp_evaluable ist env sigma qid)

let interp_flag ist env sigma red =
  { red with rConst = List.map (interp_evaluable ist env sigma) red.rConst }

let interp_constr_with_occurrences ist env sigma (occs,c) =
  let (sigma,c_interp) = interp_constr ist env sigma c in
  sigma , (interp_occurrences ist occs, c_interp)

let interp_closed_typed_pattern_with_occurrences ist env sigma (occs, c) =
  let _, p = interp_typed_pattern ist env sigma c in
  interp_occurrences ist occs, p

let interp_constr_with_occurrences_and_name_as_list =
  interp_constr_in_compound_list
    (fun c -> ((AllOccurrences,c),Anonymous))
    (function ((occs,c),Anonymous) when occs == AllOccurrences -> c
      | _ -> raise Not_found)
    (fun ist env sigma (occ_c,na) ->
      let (sigma,c_interp) = interp_constr_with_occurrences ist env sigma occ_c in
      sigma, (c_interp,
       interp_fresh_name ist env sigma na))

let interp_red_expr ist env sigma = function
  | Unfold l -> sigma , Unfold (List.map (interp_unfold ist env sigma) l)
  | Fold l ->
    let (sigma,l_interp) = interp_constr_list ist env sigma l in
    sigma , Fold l_interp
  | Cbv f -> sigma , Cbv (interp_flag ist env sigma f)
  | Cbn f -> sigma , Cbn (interp_flag ist env sigma f)
  | Lazy f -> sigma , Lazy (interp_flag ist env sigma f)
  | Pattern l ->
      let (sigma,l_interp) =
        Evd.MonadR.List.map_right
          (fun c sigma -> interp_constr_with_occurrences ist env sigma c) l sigma
      in
      sigma , Pattern l_interp
  | Simpl o ->
    sigma , Simpl (Option.map (interp_closed_typed_pattern_with_occurrences ist env sigma) o)
  | CbvVm o ->
    sigma , CbvVm (Option.map (interp_closed_typed_pattern_with_occurrences ist env sigma) o)
  | CbvNative o ->
    sigma , CbvNative (Option.map (interp_closed_typed_pattern_with_occurrences ist env sigma) o)
  | (Red _ |  Hnf | ExtraRedExpr _ as r) -> sigma , r

let interp_may_eval f ist env sigma = function
  | ConstrEval (r,c) ->
      let (sigma,redexp) = interp_red_expr ist env sigma r in
      let (sigma,c_interp) = f ist env sigma c in
      sigma , (fst (Redexpr.reduction_of_red_expr env redexp) env sigma c_interp)
  | ConstrContext ((loc,s),c) ->
      (try
	let (sigma,ic) = f ist env sigma c in
	let ctxt = coerce_to_constr_context (Id.Map.find s ist.lfun) in
	let evdref = ref sigma in
	let c = subst_meta [ConstrMatching.special_meta,ic] ctxt in
	let c = Typing.solve_evars env evdref c in
	!evdref , c
      with
	| Not_found ->
	    user_err_loc (loc, "interp_may_eval",
	    str "Unbound context identifier" ++ pr_id s ++ str"."))
  | ConstrTypeOf c ->
      let (sigma,c_interp) = f ist env sigma c in
      Typing.e_type_of ~refresh:true env sigma c_interp
  | ConstrTerm c ->
     try
	f ist env sigma c
     with reraise ->
       let reraise = Errors.push reraise in
       (* spiwack: to avoid unnecessary modifications of tacinterp, as this
          function already use effect, I call [run] hoping it doesn't mess
          up with any assumption. *)
       Proofview.NonLogical.run (debugging_exception_step ist false reraise (fun () ->
         str"interpretation of term " ++ pr_glob_constr_env env (fst c)));
       raise reraise

(* Interprets a constr expression possibly to first evaluate *)
let interp_constr_may_eval ist env sigma c =
  let (sigma,csr) =
    try
      interp_may_eval interp_constr ist env sigma c
    with reraise ->
      let reraise = Errors.push reraise in
      (* spiwack: to avoid unnecessary modifications of tacinterp, as this
          function already use effect, I call [run] hoping it doesn't mess
          up with any assumption. *)
       Proofview.NonLogical.run (debugging_exception_step ist false reraise (fun () -> str"evaluation of term"));
      raise reraise
  in
  begin
    (* spiwack: to avoid unnecessary modifications of tacinterp, as this
       function already use effect, I call [run] hoping it doesn't mess
       up with any assumption. *)
    Proofview.NonLogical.run (db_constr (curr_debug ist) env csr);
    sigma , csr
  end

(** TODO: should use dedicated printers *)
let rec message_of_value v =
  let v = Value.normalize v in
  let open Tacmach.New in
  let open Ftactic in
  if has_type v (topwit wit_tacvalue) then
    Ftactic.return (str "<tactic>")
  else if has_type v (topwit wit_constr) then
    let v = out_gen (topwit wit_constr) v in
    Ftactic.nf_enter begin fun gl -> Ftactic.return (pr_constr_env (pf_env gl) (Proofview.Goal.sigma gl) v) end
  else if has_type v (topwit wit_constr_under_binders) then
    let c = out_gen (topwit wit_constr_under_binders) v in
    Ftactic.nf_enter begin fun gl ->
      Ftactic.return (pr_constr_under_binders_env (pf_env gl) (Proofview.Goal.sigma gl) c)
    end
  else if has_type v (topwit wit_unit) then
    Ftactic.return (str "()")
  else if has_type v (topwit wit_int) then
    Ftactic.return (int (out_gen (topwit wit_int) v))
  else if has_type v (topwit wit_intro_pattern) then
    let p = out_gen (topwit wit_intro_pattern) v in
    let print env sigma c = pr_constr_env env sigma (snd (c env Evd.empty)) in
    Ftactic.nf_enter begin fun gl ->
      Ftactic.return (Miscprint.pr_intro_pattern (fun c -> print (pf_env gl) (Proofview.Goal.sigma gl) c) p)
    end
  else if has_type v (topwit wit_constr_context) then
    let c = out_gen (topwit wit_constr_context) v in
    Ftactic.nf_enter begin fun gl -> Ftactic.return (pr_constr_env (pf_env gl) (Proofview.Goal.sigma gl) c) end
  else match Value.to_list v with
  | Some l ->
    Ftactic.List.map message_of_value l >>= fun l ->
    Ftactic.return (prlist_with_sep spc (fun x -> x) l)
  | None ->
    let tag = pr_argument_type (genarg_tag v) in
    Ftactic.return (str "<" ++ tag ++ str ">") (** TODO *)

let interp_message_token ist = function
  | MsgString s -> Ftactic.return (str s)
  | MsgInt n -> Ftactic.return (int n)
  | MsgIdent (loc,id) ->
    let v = try Some (Id.Map.find id ist.lfun) with Not_found -> None in
    match v with
    | None -> Ftactic.lift (Tacticals.New.tclZEROMSG (pr_id id ++ str" not found."))
    | Some v -> message_of_value v

let interp_message_nl ist l =
  let open Ftactic in
  Ftactic.List.map (interp_message_token ist) l >>= function
  | [] -> Ftactic.return (mt ())
  | l -> Ftactic.return (prlist_with_sep spc (fun x -> x) l ++ fnl ())

let interp_message ist l =
  let open Ftactic in
  Ftactic.List.map (interp_message_token ist) l >>= fun l ->
  Ftactic.return (prlist_with_sep spc (fun x -> x) l)

let rec interp_intro_pattern ist env sigma = function
  | loc, IntroAction pat ->
      let (sigma,pat) = interp_intro_pattern_action ist env sigma pat in
      sigma, (loc, IntroAction pat)
  | loc, IntroNaming (IntroIdentifier id) ->
      sigma, (loc, interp_intro_pattern_var loc ist env sigma id)
  | loc, IntroNaming pat ->
      sigma, (loc, IntroNaming (interp_intro_pattern_naming loc ist env sigma pat))
  | loc, IntroForthcoming _  as x -> sigma, x

and interp_intro_pattern_naming loc ist env sigma = function
  | IntroFresh id -> IntroFresh (interp_fresh_ident ist env sigma id)
  | IntroIdentifier id -> interp_intro_pattern_naming_var loc ist env sigma id
  | IntroAnonymous as x -> x

and interp_intro_pattern_action ist env sigma = function
  | IntroOrAndPattern l ->
      let (sigma,l) = interp_or_and_intro_pattern ist env sigma l in
      sigma, IntroOrAndPattern l
  | IntroInjection l ->
      let sigma,l = interp_intro_pattern_list_as_list ist env sigma l in
      sigma, IntroInjection l
  | IntroApplyOn (c,ipat) ->
      let c = fun env sigma -> interp_constr ist env sigma c in
      let sigma,ipat = interp_intro_pattern ist env sigma ipat in
      sigma, IntroApplyOn (c,ipat)
  | IntroWildcard | IntroRewrite _ as x -> sigma, x

and interp_or_and_intro_pattern ist env sigma =
  List.fold_map (interp_intro_pattern_list_as_list ist env) sigma

and interp_intro_pattern_list_as_list ist env sigma = function
  | [loc,IntroNaming (IntroIdentifier id)] as l ->
      (try sigma, coerce_to_intro_pattern_list loc env (Id.Map.find id ist.lfun)
       with Not_found | CannotCoerceTo _ ->
         List.fold_map (interp_intro_pattern ist env) sigma l)
  | l -> List.fold_map (interp_intro_pattern ist env) sigma l

let interp_intro_pattern_naming_option ist env sigma = function
  | None -> None
  | Some (loc,pat) -> Some (loc, interp_intro_pattern_naming loc ist env sigma pat)

let interp_or_and_intro_pattern_option ist env sigma = function
  | None -> sigma, None
  | Some (ArgVar (loc,id)) ->
      (match coerce_to_intro_pattern env (Id.Map.find id ist.lfun) with
      | IntroAction (IntroOrAndPattern l) -> sigma, Some (loc,l)
      | _ ->
        raise (CannotCoerceTo "a disjunctive/conjunctive introduction pattern"))
  | Some (ArgArg (loc,l)) ->
      let sigma,l = interp_or_and_intro_pattern ist env sigma l in
      sigma, Some (loc,l)

let interp_intro_pattern_option ist env sigma = function
  | None -> sigma, None
  | Some ipat ->
      let sigma, ipat = interp_intro_pattern ist env sigma ipat in
      sigma, Some ipat

let interp_in_hyp_as ist env sigma (clear,id,ipat) =
  let sigma, ipat = interp_intro_pattern_option ist env sigma ipat in
  sigma,(clear,interp_hyp ist env sigma id,ipat)

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

let interp_declared_or_quantified_hypothesis ist env sigma = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp id ->
      try try_interp_ltac_var
	    (coerce_to_decl_or_quant_hyp env) ist (Some (env,sigma)) (dloc,id)
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

let interp_constr_with_bindings_arg ist env sigma (keep,c) =
  let sigma, c = interp_constr_with_bindings ist env sigma c in
  sigma, (keep,c)

let interp_open_constr_with_bindings ist env sigma (c,bl) =
  let sigma, bl = interp_bindings ist env sigma bl in
  let sigma, c = interp_open_constr ist env sigma c in
  sigma, (c, bl)

let interp_open_constr_with_bindings_arg ist env sigma (keep,c) =
  let sigma, c = interp_open_constr_with_bindings ist env sigma c in
  sigma,(keep,c)

let loc_of_bindings = function
| NoBindings -> Loc.ghost
| ImplicitBindings l -> loc_of_glob_constr (fst (List.last l))
| ExplicitBindings l -> pi1 (List.last l)

let interp_open_constr_with_bindings_loc ist ((c,_),bl as cb) =
  let loc1 = loc_of_glob_constr c in
  let loc2 = loc_of_bindings bl in
  let loc = if Loc.is_ghost loc2 then loc1 else Loc.merge loc1 loc2 in
  let f env sigma = interp_open_constr_with_bindings ist env sigma cb in
    (loc,f)

let interp_induction_arg ist gl arg =
  let env = pf_env gl and sigma = project gl in
  match arg with
  | keep,ElimOnConstr c ->
      keep,ElimOnConstr (interp_constr_with_bindings ist env sigma c)
  | keep,ElimOnAnonHyp n as x -> x
  | keep,ElimOnIdent (loc,id) ->
      let error () = user_err_loc (loc, "",
        strbrk "Cannot coerce " ++ pr_id id ++
        strbrk " neither to a quantified hypothesis nor to a term.")
      in
      let try_cast_id id' =
        if Tactics.is_quantified_hypothesis id' gl
        then keep,ElimOnIdent (loc,id')
        else
          (try keep,ElimOnConstr (sigma,(constr_of_id env id',NoBindings))
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
          | _, IntroNaming (IntroIdentifier id) -> try_cast_id id
          | _ -> error ()
        else if has_type v (topwit wit_var) then
          let id = out_gen (topwit wit_var) v in
          try_cast_id id
        else if has_type v (topwit wit_int) then
          keep,ElimOnAnonHyp (out_gen (topwit wit_int) v)
        else match Value.to_constr v with
        | None -> error ()
        | Some c -> keep,ElimOnConstr (sigma,(c,NoBindings))
      with Not_found ->
	(* We were in non strict (interactive) mode *)
	if Tactics.is_quantified_hypothesis id gl then
          keep,ElimOnIdent (loc,id)
	else
          let c = (GVar (loc,id),Some (CRef (Ident (loc,id),None))) in
          let (sigma,c) = interp_constr ist env sigma c in
          keep,ElimOnConstr (sigma,(c,NoBindings))

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

(** [interp_context ctxt] interprets a context (as in
    {!Matching.matching_result}) into a context value of Ltac.  *)
let interp_context ctxt = in_gen (topwit wit_constr_context) ctxt

(* Reads a pattern by substituting vars of lfun *)
let use_types = false

let eval_pattern lfun ist env sigma (_,pat as c) =
  if use_types then
    snd (interp_typed_pattern ist env sigma c)
  else
    instantiate_pattern env sigma lfun pat

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


(* misc *)

let mk_constr_value ist gl c =
  let (sigma,c_interp) = pf_interp_constr ist gl c in
  sigma, Value.of_constr c_interp
let mk_open_constr_value ist gl c = 
  let (sigma,c_interp) = pf_apply (interp_open_constr ist) gl c in
  sigma, Value.of_constr c_interp
let mk_hyp_value ist env sigma c =
  Value.of_constr (mkVar (interp_hyp ist env sigma c))
let mk_int_or_var_value ist c = in_gen (topwit wit_int) (interp_int_or_var ist c)

let pack_sigma (sigma,c) = {it=c;sigma=sigma;}

(* Interprets an l-tac expression into a value *)
let rec val_interp ist (tac:glob_tactic_expr) : typed_generic_argument Ftactic.t =
  let value_interp ist = match tac with
  | TacFun (it, body) ->
    Ftactic.return (of_tacvalue (VFun (extract_trace ist, ist.lfun, it, body)))
  | TacLetIn (true,l,u) -> interp_letrec ist l u
  | TacLetIn (false,l,u) -> interp_letin ist l u
  | TacMatchGoal (lz,lr,lmr) -> interp_match_goal ist lz lr lmr
  | TacMatch (lz,c,lmr) -> interp_match ist lz c lmr
  | TacArg (loc,a) -> interp_tacarg ist a
  | t ->
    (** Delayed evaluation *)
    Ftactic.return (of_tacvalue (VFun (extract_trace ist, ist.lfun, [], t)))
  in
  Control.check_for_interrupt ();
  match curr_debug ist with
  | DebugOn lev ->
        let eval v =
          let ist = { ist with extra = TacStore.set ist.extra f_debug v } in
          value_interp ist
        in
	Ftactic.debug_prompt lev tac eval
  | _ -> value_interp ist
      

and eval_tactic ist tac : unit Proofview.tactic = match tac with
  | TacAtom (loc,t) ->
      let call = LtacAtomCall t in
      catch_error_tac (push_trace(loc,call) ist) (interp_atomic ist t)
  | TacFun _ | TacLetIn _ -> assert false
  | TacMatchGoal _ | TacMatch _ -> assert false
  | TacId [] ->
      (** Optimization *)
      Proofview.tclLIFT (db_breakpoint (curr_debug ist) [])
  | TacId s ->
      let msg = interp_message_nl ist s in
      let tac l = Proofview.tclLIFT (Proofview.NonLogical.print (hov 0 l)) in
      Proofview.tclTHEN
        (Ftactic.run msg tac)
        (Proofview.tclLIFT (db_breakpoint (curr_debug ist) s))
  | TacFail (n,s) ->
      let msg = interp_message ist s in
      let tac l = Proofview.V82.tactic (fun gl -> tclFAIL (interp_int_or_var ist n) l gl) in
      Ftactic.run msg tac
  | TacProgress tac -> Tacticals.New.tclPROGRESS (interp_tactic ist tac)
  | TacShowHyps tac ->
         Proofview.V82.tactic begin
           tclSHOWHYPS (Proofview.V82.of_tactic (interp_tactic ist tac))
         end
  | TacAbstract (tac,ido) ->
      Proofview.Goal.nf_enter begin fun gl -> Tactics.tclABSTRACT
        (Option.map (Tacmach.New.of_old (pf_interp_ident ist) gl) ido) (interp_tactic ist tac)
      end
  | TacThen (t1,t) ->
      Tacticals.New.tclTHEN (interp_tactic ist t1) (interp_tactic ist t)
  | TacDispatch tl ->
      Proofview.tclDISPATCH (List.map (interp_tactic ist) tl)
  | TacExtendTac (tf,t,tl) ->
      Proofview.tclEXTEND (Array.map_to_list (interp_tactic ist) tf)
                          (interp_tactic ist t)
                          (Array.map_to_list (interp_tactic ist) tl)
  | TacThens (t1,tl) -> Tacticals.New.tclTHENS (interp_tactic ist t1) (List.map (interp_tactic ist) tl)
  | TacThens3parts (t1,tf,t,tl) ->
      Tacticals.New.tclTHENS3PARTS (interp_tactic ist t1)
	(Array.map (interp_tactic ist) tf) (interp_tactic ist t) (Array.map (interp_tactic ist) tl)
  | TacDo (n,tac) -> Tacticals.New.tclDO (interp_int_or_var ist n) (interp_tactic ist tac)
  | TacTimeout (n,tac) -> Tacticals.New.tclTIMEOUT (interp_int_or_var ist n) (interp_tactic ist tac)
  | TacTime (s,tac) -> Tacticals.New.tclTIME s (interp_tactic ist tac)
  | TacTry tac -> Tacticals.New.tclTRY (interp_tactic ist tac)
  | TacRepeat tac -> Tacticals.New.tclREPEAT (interp_tactic ist tac)
  | TacOr (tac1,tac2) ->
      Tacticals.New.tclOR (interp_tactic ist tac1) (interp_tactic ist tac2)
  | TacOnce tac ->
      Tacticals.New.tclONCE (interp_tactic ist tac)
  | TacExactlyOnce tac ->
      Tacticals.New.tclEXACTLY_ONCE (interp_tactic ist tac)
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
  (* For extensions *)
  | TacAlias (loc,s,l) ->
      let body = Tacenv.interp_alias s in
      let rec f x = match genarg_tag x with
      | QuantHypArgType | RedExprArgType
      | ConstrWithBindingsArgType
      | BindingsArgType
      | OptArgType _ | PairArgType _ -> (** generic handler *)
        Ftactic.nf_enter begin fun gl ->
          let sigma = Proofview.Goal.sigma gl in
          let env = Proofview.Goal.env gl in
          let concl = Proofview.Goal.concl gl in
          let goal = Proofview.Goal.goal gl in
          let (sigma, arg) = interp_genarg ist env sigma concl goal x in
          Ftactic.(lift (Proofview.V82.tclEVARS sigma) <*> return arg)
        end
      | _ as tag -> (** Special treatment. TODO: use generic handler  *)
        Ftactic.nf_enter begin fun gl ->
          let sigma = Proofview.Goal.sigma gl in
          let env = Proofview.Goal.env gl in
          match tag with
          | IntOrVarArgType ->
              Ftactic.return (mk_int_or_var_value ist (out_gen (glbwit wit_int_or_var) x))
          | IdentArgType ->
              Ftactic.return (value_of_ident (interp_fresh_ident ist env sigma
                                               (out_gen (glbwit wit_ident) x)))
          | VarArgType ->
              Ftactic.return (mk_hyp_value ist env sigma (out_gen (glbwit wit_var) x))
          | GenArgType -> f (out_gen (glbwit wit_genarg) x)
          | ConstrArgType ->
              let (sigma,v) =
                Tacmach.New.of_old (fun gl -> mk_constr_value ist gl (out_gen (glbwit wit_constr) x)) gl
              in
              Ftactic.(lift (Proofview.V82.tclEVARS sigma) <*> return v)
          | OpenConstrArgType ->
              let (sigma,v) =
                Tacmach.New.of_old (fun gl -> mk_open_constr_value ist gl (snd (out_gen (glbwit wit_open_constr) x))) gl in
              Ftactic.(lift (Proofview.V82.tclEVARS sigma) <*> return v)
          | ConstrMayEvalArgType ->
              let (sigma,c_interp) =
                interp_constr_may_eval ist env sigma
                  (out_gen (glbwit wit_constr_may_eval) x)
              in
              Ftactic.(lift (Proofview.V82.tclEVARS sigma) <*> return (Value.of_constr c_interp))
          | ListArgType ConstrArgType ->
              let wit = glbwit (wit_list wit_constr) in
              let (sigma,l_interp) = Tacmach.New.of_old begin fun gl ->
                Evd.MonadR.List.map_right
                  (fun c sigma -> mk_constr_value ist { gl with sigma=sigma } c)
                  (out_gen wit x)
                  (project gl)
              end gl in
              Ftactic.(lift (Proofview.V82.tclEVARS sigma) <*> return (in_gen (topwit (wit_list wit_genarg)) l_interp))
          | ListArgType VarArgType ->
              let wit = glbwit (wit_list wit_var) in
              Ftactic.return (
                let ans = List.map (mk_hyp_value ist env sigma) (out_gen wit x) in
                in_gen (topwit (wit_list wit_genarg)) ans
              )
          | ListArgType IntOrVarArgType ->
              let wit = glbwit (wit_list wit_int_or_var) in
              let ans = List.map (mk_int_or_var_value ist) (out_gen wit x) in
              Ftactic.return (in_gen (topwit (wit_list wit_genarg)) ans)
          | ListArgType IdentArgType ->
              let wit = glbwit (wit_list wit_ident) in
              let mk_ident x = value_of_ident (interp_fresh_ident ist env sigma x) in
              let ans = List.map mk_ident (out_gen wit x) in
              Ftactic.return (in_gen (topwit (wit_list wit_genarg)) ans)
          | ListArgType t  ->
              let open Ftactic in
              let list_unpacker wit l =
                let map x =
                  f (in_gen (glbwit wit) x) >>= fun v ->
                  Ftactic.return (out_gen (topwit wit) v)
                in
                Ftactic.List.map map (glb l) >>= fun l ->
                Ftactic.return (in_gen (topwit (wit_list wit)) l)
              in
              list_unpack { list_unpacker } x
          | ExtraArgType _ ->
              (** Special treatment of tactics *)
              if has_type x (glbwit wit_tactic) then
                let tac = out_gen (glbwit wit_tactic) x in
                val_interp ist tac
              else
                let goal = Proofview.Goal.goal gl in
                let (newsigma,v) = Geninterp.generic_interp ist {Evd.it=goal;sigma} x in
                Ftactic.(lift (Proofview.V82.tclEVARS newsigma) <*> return v)
          | _ -> assert false
        end
      in
      let (>>=) = Ftactic.bind in
      let addvar (x, v) accu =
        f v >>= fun v ->
        Ftactic.return (Id.Map.add x v accu)
      in
      let tac = Ftactic.List.fold_right addvar l ist.lfun >>= fun lfun ->
        let trace = push_trace (loc,LtacNotationCall s) ist in
        let ist = {
          lfun = lfun;
          extra = TacStore.set ist.extra f_trace trace; } in
        val_interp ist body
      in
      Ftactic.run tac (fun v -> tactic_of_value ist v)

  | TacML (loc,opn,l) when List.for_all global_genarg l ->
      let trace = push_trace (loc,LtacMLCall tac) ist in
      let ist = { ist with extra = TacStore.set ist.extra f_trace trace; } in
      (* spiwack: a special case for tactics (from TACTIC EXTEND) when
         every argument can be interpreted without a
         [Proofview.Goal.nf_enter]. *)
      let tac = Tacenv.interp_ml_tactic opn in
      (* dummy values, will be ignored *)
      let env = Environ.empty_env in
      let sigma = Evd.empty in
      let concl = Term.mkRel (-1) in
      let goal = sig_it Goal.V82.dummy_goal in
      (* /dummy values *)
      let args = List.map (fun a -> snd(interp_genarg ist env sigma concl goal a)) l in
      catch_error_tac trace (tac args ist)
  | TacML (loc,opn,l) ->
      let trace = push_trace (loc,LtacMLCall tac) ist in
      let ist = { ist with extra = TacStore.set ist.extra f_trace trace; } in
      Proofview.Goal.nf_enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let goal_sigma = Proofview.Goal.sigma gl in
        let concl = Proofview.Goal.concl gl in
        let goal = Proofview.Goal.goal gl in
        let tac = Tacenv.interp_ml_tactic opn in
        let (sigma,args) =
          Evd.MonadR.List.map_right
            (fun a sigma -> interp_genarg ist env sigma concl goal a) l goal_sigma
        in
        Proofview.V82.tclEVARS sigma <*>
        catch_error_tac trace (tac args ist)
      end

and force_vrec ist v : typed_generic_argument Ftactic.t =
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then
    let v = to_tacvalue v in
    match v with
    | VRec (lfun,body) -> val_interp {ist with lfun = !lfun} body
    | v -> Ftactic.return (of_tacvalue v)
  else Ftactic.return v

and interp_ltac_reference loc' mustbetac ist r : typed_generic_argument Ftactic.t =
  match r with
  | ArgVar (loc,id) ->
      let v =
        try Id.Map.find id ist.lfun
        with Not_found -> in_gen (topwit wit_var) id
      in
      Ftactic.bind (force_vrec ist v) begin fun v ->
      let v = propagate_trace ist loc id v in
      if mustbetac then Ftactic.return (coerce_to_tactic loc id v) else Ftactic.return v
      end
  | ArgArg (loc,r) ->
      let ids = extract_ids [] ist.lfun in
      let loc_info = ((if Loc.is_ghost loc' then loc else loc'),LtacNameCall r) in
      let extra = TacStore.set ist.extra f_avoid_ids ids in 
      let extra = TacStore.set extra f_trace (push_trace loc_info ist) in
      let ist = { lfun = Id.Map.empty; extra = extra; } in
      val_interp ist (Tacenv.interp_ltac r)

and interp_tacarg ist arg : typed_generic_argument Ftactic.t =
  match arg with
  | TacGeneric arg ->
      Ftactic.nf_enter begin fun gl ->
        let sigma = Proofview.Goal.sigma gl in
        let goal = Proofview.Goal.goal gl in
        let (sigma,v) = Geninterp.generic_interp ist {Evd.it=goal;sigma} arg in
        Ftactic.(lift (Proofview.V82.tclEVARS sigma) <*> return v)
      end
  | Reference r -> interp_ltac_reference dloc false ist r
  | ConstrMayEval c ->
      Ftactic.enter begin fun gl ->
        let sigma = Proofview.Goal.sigma gl in
        let env = Proofview.Goal.env gl in
        let (sigma,c_interp) = interp_constr_may_eval ist env sigma c in
        Ftactic.(lift (Proofview.V82.tclEVARS sigma) <*> return (Value.of_constr c_interp))
      end
  | UConstr c ->
      Ftactic.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        Ftactic.return (Value.of_uconstr (interp_uconstr ist env c))
      end
  | MetaIdArg (loc,_,id) -> assert false
  | TacCall (loc,r,[]) ->
      interp_ltac_reference loc true ist r
  | TacCall (loc,f,l) ->
      let (>>=) = Ftactic.bind in
      interp_ltac_reference loc true ist f >>= fun fv ->
      Ftactic.List.map (fun a -> interp_tacarg ist a) l >>= fun largs ->
      interp_app loc ist fv largs
  | TacFreshId l ->
      Ftactic.enter begin fun gl ->
        let id = interp_fresh_id ist (Tacmach.New.pf_env gl) (Proofview.Goal.sigma gl) l in
        Ftactic.return (in_gen (topwit wit_intro_pattern) (dloc, IntroNaming (IntroIdentifier id)))
      end
  | TacPretype c ->
      Ftactic.enter begin fun gl ->
        let sigma = Proofview.Goal.sigma gl in
        let env = Proofview.Goal.env gl in
        let {closure;term} = interp_uconstr ist env c in
        let vars = {
          Pretyping.ltac_constrs = closure.typed;
          Pretyping.ltac_uconstrs = closure.untyped;
          Pretyping.ltac_idents = closure.idents;
          Pretyping.ltac_genargs = ist.lfun;
        } in
        let (sigma,c_interp) =
          Pretyping.understand_ltac constr_flags env sigma vars WithoutTypeConstraint term
        in
        Ftactic.(lift (Proofview.V82.tclEVARS sigma) <*> return (Value.of_constr c_interp))
      end
  | TacNumgoals ->
      Ftactic.lift begin
        let open Proofview.Notations in
        Proofview.numgoals >>= fun i ->
        Proofview.tclUNIT (Value.of_int i)
      end
  | Tacexp t -> val_interp ist t
  | TacDynamic(_,t) ->
      let tg = (Dyn.tag t) in
      if String.equal tg "tactic" then
        val_interp ist (tactic_out t ist)
      else if String.equal tg "value" then
        Ftactic.return (value_out t)
      else if String.equal tg "constr" then
        Ftactic.return (Value.of_constr (constr_out t))
      else
        Errors.anomaly ~loc:dloc ~label:"Tacinterp.val_interp"
	  (str "Unknown dynamic: <" ++ str (Dyn.tag t) ++ str ">")

(* Interprets an application node *)
and interp_app loc ist fv largs : typed_generic_argument Ftactic.t =
  let (>>=) = Ftactic.bind in
  let fail = Tacticals.New.tclZEROMSG (str "Illegal tactic application.") in
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
              Proofview.tclLIFT (debugging_exception_step ist false e (fun () -> str "evaluation")) <*>
	      Proofview.tclZERO e
            end
        end >>= fun v ->
        (* No errors happened, we propagate the trace *)
        let v = append_trace trace v in
        Proofview.tclLIFT begin
          debugging_step ist
	    (fun () ->
	      str"evaluation returns"++fnl()++pr_value None v)
        end <*>
        if List.is_empty lval then Ftactic.return v else interp_app loc ist v lval
      else
        Ftactic.return (of_tacvalue (VFun(trace,newlfun,lvar,body)))
    | _ -> fail
  else fail

(* Gives the tactic corresponding to the tactic value *)
and tactic_of_value ist vle =
  let vle = Value.normalize vle in
  if has_type vle (topwit wit_tacvalue) then
  match to_tacvalue vle with
  | VFun (trace,lfun,[],t) ->
      let ist = {
        lfun = lfun;
        extra = TacStore.set ist.extra f_trace []; } in
      let tac = eval_tactic ist t in
      catch_error_tac trace tac
  | (VFun _|VRec _) -> Proofview.tclZERO (UserError ("" , str "A fully applied tactic is expected."))
  else if has_type vle (topwit wit_tactic) then
    let tac = out_gen (topwit wit_tactic) vle in
    eval_tactic ist tac
  else Proofview.tclZERO (UserError ("" , str"Expression does not evaluate to a tactic."))

(* Interprets the clauses of a recursive LetIn *)
and interp_letrec ist llc u =
  Proofview.tclUNIT () >>= fun () -> (* delay for the effects of [lref], just in case. *)
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
  let rec fold lfun = function
  | [] ->
    let ist = { ist with lfun } in
    val_interp ist u
  | ((_, id), body) :: defs ->
    Ftactic.bind (interp_tacarg ist body) (fun v ->
    fold (Id.Map.add id v lfun) defs)
  in
  fold ist.lfun llc

(** [interp_match_success lz ist succ] interprets a single matching success
    (of type {!TacticMatching.t}). *)
and interp_match_success ist { TacticMatching.subst ; context ; terms ; lhs } =
  let (>>=) = Ftactic.bind in
  let lctxt = Id.Map.map interp_context context in
  let hyp_subst = Id.Map.map Value.of_constr terms in
  let lfun = extend_values_with_bindings subst (lctxt +++ hyp_subst +++ ist.lfun) in
  let ist = { ist with lfun } in
  val_interp ist lhs >>= fun v ->
  if has_type v (topwit wit_tacvalue) then match to_tacvalue v with
  | VFun (trace,lfun,[],t) ->
      let ist = {
        lfun = lfun;
        extra = TacStore.set ist.extra f_trace trace; } in
      let tac = eval_tactic ist t in
      let dummy = VFun (extract_trace ist, Id.Map.empty, [], TacId []) in
      catch_error_tac trace (tac <*> Ftactic.return (of_tacvalue dummy))
  | _ -> Ftactic.return v
  else Ftactic.return v


(** [interp_match_successes lz ist s] interprets the stream of
    matching of successes [s]. If [lz] is set to true, then only the
    first success is considered, otherwise further successes are tried
    if the left-hand side fails. *)
and interp_match_successes lz ist tac =
    if lz then
      (** Only keep the first matching result, we don't backtrack on it *)
      let tac = Proofview.tclONCE tac in
      tac >>= fun ans -> interp_match_success ist ans
    else
      let decrease e = match e with
      | FailError (0, _) -> e
      | FailError (n, s) -> FailError (pred n, s)
      | _ -> e
      in
      let break e = match e with
      | FailError (0, _) -> false
      | FailError (n, s) -> true
      | _ -> false
      in
      let tac = Proofview.tclBREAK break tac >>= fun ans -> interp_match_success ist ans in
      (** Once a tactic has succeeded, do not backtrack anymore *)
      Proofview.tclONCE (Proofview.tclOR tac (fun e -> Proofview.tclZERO (decrease e)))

(* Interprets the Match expressions *)
and interp_match ist lz constr lmr =
  let (>>=) = Ftactic.bind in
  begin Proofview.tclORELSE
    (interp_ltac_constr ist constr)
    begin function
      | e ->
          Proofview.tclLIFT (debugging_exception_step ist true e
          (fun () -> str "evaluation of the matched expression")) <*>
          Proofview.tclZERO e
    end
  end >>= fun constr ->
  Ftactic.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let ilr = read_match_rule (extract_ltac_constr_values ist env) ist env sigma lmr in
    interp_match_successes lz ist (TacticMatching.match_term env sigma constr ilr)
  end

(* Interprets the Match Context expressions *)
and interp_match_goal ist lz lr lmr =
    Ftactic.nf_enter begin fun gl ->
      let sigma = Proofview.Goal.sigma gl in
      let env = Proofview.Goal.env gl in
      let hyps = Proofview.Goal.hyps gl in
      let hyps = if lr then List.rev hyps else hyps in
      let concl = Proofview.Goal.concl gl in
      let ilr = read_match_rule (extract_ltac_constr_values ist env) ist env sigma lmr in
      interp_match_successes lz ist (TacticMatching.match_goal env sigma hyps concl ilr)
    end

(* Interprets extended tactic generic arguments *)
(* spiwack: interp_genarg has an argument [concl] for the case of
   "casted open constr". And [gl] for [Geninterp]. I haven't changed
   the interface for geninterp yet as it is used by ARGUMENT EXTEND
   (in turn used by plugins). At the time I'm writing this comment
   though, the only concerned plugins are the declarative mode (which
   needs the [extra] field of goals to interprete rules) and ssreflect
   (a handful of time). I believe we'd need to address "casted open
   constr" and the declarative mode rules to provide a reasonable
   interface. *)
and interp_genarg ist env sigma concl gl x =
  let evdref = ref sigma in
  let rec interp_genarg x =
    match genarg_tag x with
    | IntOrVarArgType ->
      in_gen (topwit wit_int_or_var)
        (ArgArg (interp_int_or_var ist (out_gen (glbwit wit_int_or_var) x)))
    | IdentArgType ->
      in_gen (topwit wit_ident)
        (interp_fresh_ident ist env sigma (out_gen (glbwit wit_ident) x))
    | VarArgType ->
      in_gen (topwit wit_var) (interp_hyp ist env sigma (out_gen (glbwit wit_var) x))
    | GenArgType ->
      in_gen (topwit wit_genarg) (interp_genarg (out_gen (glbwit wit_genarg) x))
    | ConstrArgType ->
      let (sigma,c_interp) =
        interp_constr ist env !evdref (out_gen (glbwit wit_constr) x)
      in
      evdref := sigma;
      in_gen (topwit wit_constr) c_interp
    | ConstrMayEvalArgType ->
      let (sigma,c_interp) = interp_constr_may_eval ist env !evdref (out_gen (glbwit wit_constr_may_eval) x) in
      evdref := sigma;
      in_gen (topwit wit_constr_may_eval) c_interp
    | QuantHypArgType ->
      in_gen (topwit wit_quant_hyp)
        (interp_declared_or_quantified_hypothesis ist env sigma
           (out_gen (glbwit wit_quant_hyp) x))
    | RedExprArgType ->
      let (sigma,r_interp) =
        interp_red_expr ist env !evdref (out_gen (glbwit wit_red_expr) x)
      in
      evdref := sigma;
      in_gen (topwit wit_red_expr) r_interp
    | OpenConstrArgType ->
      let expected_type = WithoutTypeConstraint in
      in_gen (topwit wit_open_constr)
        (interp_open_constr ~expected_type
           ist env !evdref
           (snd (out_gen (glbwit wit_open_constr) x)))
    | ConstrWithBindingsArgType ->
      in_gen (topwit wit_constr_with_bindings)
        (pack_sigma (interp_constr_with_bindings ist env !evdref
		       (out_gen (glbwit wit_constr_with_bindings) x)))
    | BindingsArgType ->
      in_gen (topwit wit_bindings)
        (pack_sigma (interp_bindings ist env !evdref (out_gen (glbwit wit_bindings) x)))
    | ListArgType ConstrArgType ->
        let (sigma,v) = interp_genarg_constr_list ist env !evdref x in
	evdref := sigma;
	v
    | ListArgType VarArgType -> interp_genarg_var_list ist env sigma x
    | ListArgType _ ->
      let list_unpacker wit l =
        let map x =
          out_gen (topwit wit) (interp_genarg (in_gen (glbwit wit) x))
        in
        in_gen (topwit (wit_list wit)) (List.map map (glb l))
      in
      list_unpack { list_unpacker } x
    | OptArgType _ ->
      let opt_unpacker wit o = match glb o with
      | None -> in_gen (topwit (wit_opt wit)) None
      | Some x ->
        let x = out_gen (topwit wit) (interp_genarg (in_gen (glbwit wit) x)) in
        in_gen (topwit (wit_opt wit)) (Some x)
      in
      opt_unpack { opt_unpacker } x
    | PairArgType _ ->
      let pair_unpacker wit1 wit2 o =
        let (p, q) = glb o in
        let p = out_gen (topwit wit1) (interp_genarg (in_gen (glbwit wit1) p)) in
        let q = out_gen (topwit wit2) (interp_genarg (in_gen (glbwit wit2) q)) in
        in_gen (topwit (wit_pair wit1 wit2)) (p, q)
      in
      pair_unpack { pair_unpacker } x
    | ExtraArgType s ->
        let (sigma,v) = Geninterp.generic_interp ist { Evd.it=gl;sigma=(!evdref) } x in
	evdref:=sigma;
	v
  in
  let v = interp_genarg x in
  !evdref , v


(** returns [true] for genargs which have the same meaning
    independently of goals. *)

and global_genarg =
  let rec global_tag = function
    | IntOrVarArgType | GenArgType -> true
    | ListArgType t | OptArgType t -> global_tag t
    | PairArgType (t1,t2) -> global_tag t1 && global_tag t2
    | _ -> false
  in
  fun x -> global_tag (genarg_tag x)

and interp_genarg_constr_list ist env sigma x =
  let lc = out_gen (glbwit (wit_list wit_constr)) x in
  let (sigma,lc) = interp_constr_list ist env sigma lc in
  sigma , in_gen (topwit (wit_list wit_constr)) lc

and interp_genarg_var_list ist env sigma x =
  let lc = out_gen (glbwit (wit_list wit_var)) x in
  let lc = interp_hyp_list ist env sigma lc in
  in_gen (topwit (wit_list wit_var)) lc

(* Interprets tactic expressions : returns a "constr" *)
and interp_ltac_constr ist e : constr Ftactic.t =
  let (>>=) = Ftactic.bind in
  begin Proofview.tclORELSE
      (val_interp ist e)
      begin function
        | Not_found ->
            Ftactic.enter begin fun gl ->
              let env = Proofview.Goal.env gl in
              Proofview.tclLIFT begin
                debugging_step ist (fun () ->
                  str "evaluation failed for" ++ fnl() ++
                    Pptactic.pr_glob_tactic env e)
              end
            <*> Proofview.tclZERO Not_found
            end
        | e -> Proofview.tclZERO e
      end
  end >>= fun result ->
  Ftactic.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let result = Value.normalize result in
  try
    let cresult = coerce_to_closed_constr env result in
    Proofview.tclLIFT begin
      debugging_step ist (fun () ->
        Pptactic.pr_glob_tactic env e ++ fnl() ++
          str " has value " ++ fnl() ++
          pr_constr_env env sigma cresult)
    end <*>
    Ftactic.return cresult
  with CannotCoerceTo _ ->
    let env = Proofview.Goal.env gl in
    Proofview.tclZERO (UserError ( "",
      errorlabstrm ""
      (str "Must evaluate to a closed term" ++ fnl() ++
      str "offending expression: " ++ fnl() ++ pr_inspect env e result)))
  end


(* Interprets tactic expressions : returns a "tactic" *)
and interp_tactic ist tac : unit Proofview.tactic =
  Ftactic.run (val_interp ist tac) (fun v -> tactic_of_value ist v)

(* Interprets a primitive tactic *)
and interp_atomic ist tac : unit Proofview.tactic =
  match tac with
  (* Basic tactics *)
  | TacIntroPattern l ->
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        let sigma,l' = interp_intro_pattern_list_as_list ist env sigma l in
        Proofview.V82.tclEVARS sigma <*> Tactics.intros_patterns l'
      end
  | TacIntroMove (ido,hto) ->
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        let mloc = interp_move_location ist env sigma hto in
        Tactics.intro_move (Option.map (interp_fresh_ident ist env sigma) ido) mloc
      end
  | TacExact c ->
      Proofview.V82.tactic begin fun gl -> 
        let (sigma,c_interp) = pf_interp_casted_constr ist gl c in
        tclTHEN
	  (tclEVARS sigma)
	  (Tactics.exact_no_check c_interp)
          gl
      end
  | TacApply (a,ev,cb,cl) ->
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
	let l = List.map (fun (k,c) ->
          let loc, f = interp_open_constr_with_bindings_loc ist c in
	    (k,(loc,f))) cb 
	in
        let sigma,tac = match cl with
          | None -> sigma, fun l -> Tactics.apply_with_delayed_bindings_gen a ev l
          | Some cl ->
              let sigma,(clear,id,cl) = interp_in_hyp_as ist env sigma cl in
              sigma, fun l -> Tactics.apply_delayed_in a ev clear id l cl in
        Tacticals.New.tclWITHHOLES ev tac sigma l
      end
  | TacElim (ev,(keep,cb),cbo) ->
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in 
        let sigma, cb = interp_constr_with_bindings ist env sigma cb in
        let sigma, cbo = Option.fold_map (interp_constr_with_bindings ist env) sigma cbo in
        Tacticals.New.tclWITHHOLES ev (Tactics.elim ev keep cb) sigma cbo
      end
  | TacCase (ev,(keep,cb)) ->
      Proofview.Goal.enter begin fun gl ->
        let sigma = Proofview.Goal.sigma gl in
        let env = Proofview.Goal.env gl in
        let sigma, cb = interp_constr_with_bindings ist env sigma cb in
        Tacticals.New.tclWITHHOLES ev (Tactics.general_case_analysis ev keep) sigma cb
      end
  | TacFix (idopt,n) ->
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        Proofview.V82.tactic (Tactics.fix (Option.map (interp_fresh_ident ist env sigma) idopt) n)
      end
  | TacMutualFix (id,n,l) ->
      Proofview.V82.tactic begin fun gl ->
        let env = pf_env gl in
        let f sigma (id,n,c) =
	  let (sigma,c_interp) = pf_interp_type ist { gl with sigma=sigma } c in
	  sigma , (interp_fresh_ident ist env sigma id,n,c_interp) in
        let (sigma,l_interp) =
          Evd.MonadR.List.map_right (fun c sigma -> f sigma c) l (project gl)
        in
        tclTHEN
	  (tclEVARS sigma)
	  (Tactics.mutual_fix (interp_fresh_ident ist env sigma id) n l_interp 0)
          gl
      end
  | TacCofix idopt ->
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        Proofview.V82.tactic (Tactics.cofix (Option.map (interp_fresh_ident ist env sigma) idopt))
      end
  | TacMutualCofix (id,l) ->
      Proofview.V82.tactic begin fun gl ->
        let env = pf_env gl in
        let f sigma (id,c) =
	  let (sigma,c_interp) = pf_interp_type ist { gl with sigma=sigma } c in
	  sigma , (interp_fresh_ident ist env sigma id,c_interp) in
        let (sigma,l_interp) =
          Evd.MonadR.List.map_right (fun c sigma -> f sigma c) l (project gl)
        in
        tclTHEN
	  (tclEVARS sigma)
	  (Tactics.mutual_cofix (interp_fresh_ident ist env sigma id) l_interp 0)
          gl
      end
  | TacAssert (b,t,ipat,c) ->
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        let (sigma,c) = 
          (if Option.is_empty t then interp_constr else interp_type) ist env sigma c
        in
        let sigma, ipat = interp_intro_pattern_option ist env sigma ipat in
        let tac = Option.map (interp_tactic ist) t in
        Proofview.V82.tclEVARS sigma <*> Tactics.forward b tac ipat c
      end
  | TacGeneralize cl ->
      let tac arg = Proofview.V82.tactic (Tactics.Simple.generalize_gen arg) in
      Proofview.Goal.enter begin fun gl ->
        let sigma = Proofview.Goal.sigma gl in
        let env = Proofview.Goal.env gl in
        let sigma, cl = interp_constr_with_occurrences_and_name_as_list ist env sigma cl in
        Proofview.V82.tclEVARS sigma <*> tac cl
      end
  | TacGeneralizeDep c ->
      (new_interp_constr ist c)
        (fun c -> Proofview.V82.tactic (Tactics.generalize_dep c))
  | TacLetTac (na,c,clp,b,eqpat) ->
      Proofview.V82.nf_evar_goals <*>
      Proofview.Goal.nf_enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        let clp = interp_clause ist env sigma clp in
        let eqpat = interp_intro_pattern_naming_option ist env sigma eqpat in
        if Locusops.is_nowhere clp then
        (* We try to fully-typecheck the term *)
          let (sigma,c_interp) =
            Tacmach.New.of_old (fun gl -> pf_interp_constr ist gl c) gl
          in
          let let_tac b na c cl eqpat =
            let id = Option.default (Loc.ghost,IntroAnonymous) eqpat in
            let with_eq = if b then None else Some (true,id) in
            Tactics.letin_tac with_eq na c None cl
          in
	  Proofview.V82.tclEVARS sigma <*>
            let_tac b (interp_fresh_name ist env sigma na) c_interp clp eqpat
        else
        (* We try to keep the pattern structure as much as possible *)
          let let_pat_tac b na c cl eqpat =
            let id = Option.default (Loc.ghost,IntroAnonymous) eqpat in
            let with_eq = if b then None else Some (true,id) in
            Tactics.letin_pat_tac with_eq na c cl
          in
	  Tacticals.New.tclWITHHOLES false (*in hope of a future "eset/epose"*)
            (let_pat_tac b (interp_fresh_name ist env sigma na)
            (interp_pure_open_constr ist env sigma c) clp) sigma eqpat
      end

  (* Automation tactics *)
  | TacTrivial (debug,lems,l) ->
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        Auto.h_trivial ~debug
	  (interp_auto_lemmas ist env sigma lems)
	  (Option.map (List.map (interp_hint_base ist)) l)
      end
  | TacAuto (debug,n,lems,l) ->
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        Auto.h_auto ~debug (Option.map (interp_int_or_var ist) n)
	  (interp_auto_lemmas ist env sigma lems)
	  (Option.map (List.map (interp_hint_base ist)) l)
      end

  (* Derived basic tactics *)
  | TacInductionDestruct (isrec,ev,(l,el,cls)) ->
      (* spiwack: some unknown part of destruct needs the goal to be
         prenormalised. *)
      Proofview.V82.nf_evar_goals <*>
      Proofview.Goal.nf_enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        let sigma,l =
          List.fold_map begin fun sigma (c,(ipato,ipats)) ->
            (* TODO: move sigma as a side-effect *)
            let c = Tacmach.New.of_old (fun gl -> interp_induction_arg ist gl c) gl in
            let ipato = interp_intro_pattern_naming_option ist env sigma ipato in
            let sigma,ipats = interp_or_and_intro_pattern_option ist env sigma ipats in
            sigma,(c,(ipato,ipats))
          end sigma l
        in
        let sigma,el =
          Option.fold_map (interp_constr_with_bindings ist env) sigma el in
        let interp_clause = interp_clause ist env sigma in
        let cls = Option.map interp_clause cls in
        Tacticals.New.tclWITHHOLES ev (Tactics.induction_destruct isrec ev) sigma (l,el,cls)
      end
  | TacDoubleInduction (h1,h2) ->
      let h1 = interp_quantified_hypothesis ist h1 in
      let h2 = interp_quantified_hypothesis ist h2 in
      Elim.h_double_induction h1 h2
  (* Context management *)
  | TacClear (b,l) ->
      Proofview.V82.tactic begin fun gl ->
        let l = interp_hyp_list ist (pf_env gl) (project gl) l in
        if b then Tactics.keep l gl else Tactics.clear l gl
      end
  | TacClearBody l ->
      Proofview.Goal.enter begin fun gl ->
        Tactics.clear_body (interp_hyp_list ist (Tacmach.New.pf_env gl) (Proofview.Goal.sigma gl) l)
      end
  | TacMove (dep,id1,id2) ->
      Proofview.V82.tactic begin fun gl -> 
        Tactics.move_hyp dep (interp_hyp ist (pf_env gl) (project gl) id1)
                   (interp_move_location ist (pf_env gl) (project gl) id2)
                   gl
      end
  | TacRename l ->
      Proofview.V82.tactic begin fun gl ->
        let env = pf_env gl in
        let sigma = project gl in
        Tactics.rename_hyp (List.map (fun (id1,id2) ->
	  interp_hyp ist env sigma id1,
	  interp_fresh_ident ist env sigma (snd id2)) l)
          gl
      end

  (* Constructors *)
  | TacSplit (ev,bll) ->
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        let sigma, bll = List.fold_map (interp_bindings ist env) sigma bll in
        Tacticals.New.tclWITHHOLES ev (Tactics.split_with_bindings ev) sigma bll
      end
  (* Conversion *)
  | TacReduce (r,cl) ->
      Proofview.V82.tactic begin fun gl -> 
        let (sigma,r_interp) = interp_red_expr ist (pf_env gl) (project gl) r in
        tclTHEN
	  (tclEVARS sigma)
	  (Tactics.reduce r_interp (interp_clause ist (pf_env gl) (project gl) cl))
          gl
      end
  | TacChange (None,c,cl) ->
      Proofview.V82.nf_evar_goals <*>
      Proofview.V82.tactic begin fun gl ->
        let is_onhyps = match cl.onhyps with
          | None | Some [] -> true
          | _ -> false
        in
        let is_onconcl = match cl.concl_occs with
          | AllOccurrences | NoOccurrences -> true
          | _ -> false
        in
        let c_interp env sigma =
	  if is_onhyps && is_onconcl
	  then interp_type ist env sigma c
	  else interp_constr ist env sigma c
        in
	  (Tactics.change None c_interp (interp_clause ist (pf_env gl) (project gl) cl))
          gl
      end
  | TacChange (Some op,c,cl) ->
      Proofview.V82.nf_evar_goals <*>
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        Proofview.V82.tactic begin fun gl -> 
          let sign,op = interp_typed_pattern ist env sigma op in
          let to_catch = function Not_found -> true | e -> Errors.is_anomaly e in
          let c_interp env sigma =
	    let env' = Environ.push_named_context sign env in
	      try interp_constr ist env' sigma c
	      with e when to_catch e (* Hack *) ->
		errorlabstrm "" (strbrk "Failed to get enough information from the left-hand side to type the right-hand side.")
          in
	      (Tactics.change (Some op) c_interp (interp_clause ist env sigma cl))
		gl
        end
      end

  (* Equivalence relations *)
  | TacSymmetry c ->
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        let cl = interp_clause ist env sigma c in
        Tactics.intros_symmetry cl
      end

  (* Equality and inversion *)
  | TacRewrite (ev,l,cl,by) ->
      Proofview.Goal.enter begin fun gl ->
        let l = List.map (fun (b,m,(keep,c)) ->
          let f env sigma = interp_open_constr_with_bindings ist env sigma c in
	  (b,m,keep,f)) l in
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        let cl = interp_clause ist env sigma cl in
        Equality.general_multi_rewrite ev l cl
          (Option.map (fun by -> Tacticals.New.tclCOMPLETE (interp_tactic ist by),
                                 Equality.Naive)
                      by)
      end
  | TacInversion (DepInversion (k,c,ids),hyp) ->
      Proofview.Goal.nf_enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        let (sigma,c_interp) =
          match c with
          | None -> sigma , None
          | Some c ->
              let (sigma,c_interp) =
                Tacmach.New.of_old (fun gl -> pf_interp_constr ist gl c) gl
              in
              sigma , Some c_interp
        in
        let dqhyps = interp_declared_or_quantified_hypothesis ist env sigma hyp in
        let sigma,ids = interp_or_and_intro_pattern_option ist env sigma ids in
        Proofview.V82.tclEVARS sigma <*> Inv.dinv k c_interp ids dqhyps
      end
  | TacInversion (NonDepInversion (k,idl,ids),hyp) ->
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        let hyps = interp_hyp_list ist env sigma idl in
        let dqhyps = interp_declared_or_quantified_hypothesis ist env sigma hyp in
        let sigma, ids = interp_or_and_intro_pattern_option ist env sigma ids in
        Proofview.V82.tclEVARS sigma <*> Inv.inv_clause k ids hyps dqhyps
      end
  | TacInversion (InversionUsing (c,idl),hyp) ->
      Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        let (sigma,c_interp) = interp_constr ist env sigma c in
        let dqhyps = interp_declared_or_quantified_hypothesis ist env sigma hyp in
        let hyps = interp_hyp_list ist env sigma idl in
        Proofview.V82.tclEVARS sigma <*>
        Leminv.lemInv_clause dqhyps
          c_interp
          hyps
      end

(* Initial call for interpretation *)

let default_ist () =
  let extra = TacStore.set TacStore.empty f_debug (get_debug ()) in
  { lfun = Id.Map.empty; extra = extra }

let eval_tactic t =
  Proofview.tclUNIT () >>= fun () -> (* delay for [default_ist] *)
  Proofview.tclLIFT db_initialize <*>
  interp_tactic (default_ist ()) t

let eval_tactic_ist ist t =
  Proofview.tclLIFT db_initialize <*>
  interp_tactic ist t

(* globalization + interpretation *)


let interp_tac_gen lfun avoid_ids debug t =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let extra = TacStore.set TacStore.empty f_debug debug in
  let extra = TacStore.set extra f_avoid_ids avoid_ids in
  let ist = { lfun = lfun; extra = extra } in
  let ltacvars = Id.Map.domain lfun in
  interp_tactic ist
    (intern_pure_tactic {
      ltacvars; ltacrecvars = Id.Map.empty;
      genv = env } t)
  end

let interp t = interp_tac_gen Id.Map.empty [] (get_debug()) t
let _ = Proof_global.set_interp_tac interp

(* Used to hide interpretation for pretty-print, now just launch tactics *)
(* [global] means that [t] should be internalized outside of goals. *)
let hide_interp global t ot =
  let hide_interp env =
    let ist = { ltacvars = Id.Set.empty; ltacrecvars = Id.Map.empty;
                genv = env } in
    let te = intern_pure_tactic ist t in
    let t = eval_tactic te in
    match ot with
    | None -> t
    | Some t' -> Tacticals.New.tclTHEN t t'
  in
  if global then
    Proofview.tclENV >>= fun env ->
    hide_interp env
  else
    Proofview.Goal.enter begin fun gl ->
      hide_interp (Proofview.Goal.env gl)
    end

(***************************************************************************)
(** Register standard arguments *)

let def_intern ist x = (ist, x)
let def_subst _ x = x
let def_interp ist gl x = (project gl, x)

let declare_uniform t =
  Genintern.register_intern0 t def_intern;
  Genintern.register_subst0 t def_subst;
  Geninterp.register_interp0 t def_interp

let () =
  declare_uniform wit_unit

let () =
  declare_uniform wit_int

let () =
  declare_uniform wit_bool

let () =
  declare_uniform wit_string

let () =
  declare_uniform wit_pre_ident

let () =
  let interp ist gl ref = (project gl, interp_reference ist (pf_env gl) (project gl) ref) in
  Geninterp.register_interp0 wit_ref interp;
  let interp ist gl pat = interp_intro_pattern ist (pf_env gl) (project gl) pat in
  Geninterp.register_interp0 wit_intro_pattern interp;
  let interp ist gl pat = (project gl, interp_clause ist (pf_env gl) (project gl) pat) in
  Geninterp.register_interp0 wit_clause_dft_concl interp;
  let interp ist gl s = interp_sort (project gl) s in
  Geninterp.register_interp0 wit_sort interp

let () =
  let interp ist gl tac =
    let f = VFun (extract_trace ist, ist.lfun, [], tac) in
    (project gl, TacArg (dloc, valueIn (of_tacvalue f)))
  in
  Geninterp.register_interp0 wit_tactic interp

let () =
  Geninterp.register_interp0 wit_uconstr (fun ist gl c ->
     project gl , interp_uconstr ist (pf_env gl) c
  )

(***************************************************************************)
(* Other entry points *)

let val_interp ist tac k = Ftactic.run (val_interp ist tac) k

let interp_ltac_constr ist c k = Ftactic.run (interp_ltac_constr ist c) k

let interp_redexp env sigma r =
  let ist = default_ist () in
  let gist = { fully_empty_glob_sign with genv = env; } in
  interp_red_expr ist env sigma (intern_red_expr gist r)

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

let _ =
  let eval ty env sigma lfun arg =
    let ist = { lfun = lfun; extra = TacStore.empty; } in
    if has_type arg (glbwit wit_tactic) then
      let tac = out_gen (glbwit wit_tactic) arg in
      let tac = interp_tactic ist tac in
      let prf = Proof.start sigma [env, ty] in
      let (prf, _) =
        try Proof.run_tactic env tac prf
        with Proofview_monad.TacticFailure e as src ->
          (** Catch the inner error of the monad tactic *)
          let src = Errors.push src in
          let e = Backtrace.app_backtrace ~src ~dst:e in
          raise e
      in
      let sigma = Proof.in_proof prf (fun sigma -> sigma) in
      let ans = match Proof.initial_goals prf with
      | [c, _] -> c
      | _ -> assert false
      in
      ans, sigma
    else
      failwith "not a tactic"
  in
  Hook.set Pretyping.genarg_interp_hook eval

let _ = Hook.set Auto.extern_interp
  (fun l ->
    let lfun = Id.Map.map (fun c -> Value.of_constr c) l in
    let ist = { (default_ist ()) with lfun; } in
    interp_tactic ist)

(** Used in tactic extension **)

let dummy_id = Id.of_string "_"

let lift_constr_tac_to_ml_tac vars tac =
  let tac _ ist = Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let map = function
    | None -> None
    | Some id ->
      let c = Id.Map.find id ist.lfun in
      try Some (coerce_to_closed_constr env c)
      with CannotCoerceTo ty ->
        error_ltac_variable Loc.ghost dummy_id (Some (env,sigma)) c ty
    in
    let args = List.map_filter map vars in
    tac args ist
  end in
  tac
