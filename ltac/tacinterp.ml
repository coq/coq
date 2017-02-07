(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
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
open CErrors
open Util
open Names
open Nameops
open Libnames
open Globnames
open Nametab
open Pfedit
open Refiner
open Tacmach.New
open Tactic_debug
open Constrexpr
open Term
open Termops
open Tacexpr
open Genarg
open Geninterp
open Stdarg
open Tacarg
open Printer
open Pretyping
open Misctypes
open Locus
open Tacintern
open Taccoerce
open Sigma.Notations
open Proofview.Notations
open Context.Named.Declaration

let ltac_trace_info = Tactic_debug.ltac_trace_info

let has_type : type a. Val.t -> a typed_abstract_argument_type -> bool = fun v wit ->
  let Val.Dyn (t, _) = v in
  let t' = match val_tag wit with
  | Val.Base t' -> t'
  | _ -> assert false (** not used in this module *)
  in
  match Val.eq t t' with
  | None -> false
  | Some Refl -> true

let prj : type a. a Val.typ -> Val.t -> a option = fun t v ->
  let Val.Dyn (t', x) = v in
  match Val.eq t t' with
  | None -> None
  | Some Refl -> Some x

let in_list tag v =
  let tag = match tag with Val.Base tag -> tag | _ -> assert false in
  Val.Dyn (Val.typ_list, List.map (fun x -> Val.Dyn (tag, x)) v)
let in_gen wit v =
  let t = match val_tag wit with
  | Val.Base t -> t
  | _ -> assert false (** not used in this module *)
  in
  Val.Dyn (t, v)
let out_gen wit v =
  let t = match val_tag wit with
  | Val.Base t -> t
  | _ -> assert false (** not used in this module *)
  in
  match prj t v with None -> assert false | Some x -> x

let val_tag wit = val_tag (topwit wit)

let pr_argument_type arg =
  let Val.Dyn (tag, _) = arg in
  Val.pr tag

let safe_msgnl s =
  Proofview.NonLogical.catch
    (Proofview.NonLogical.print_debug (s++fnl()))
    (fun _ -> Proofview.NonLogical.print_warning (str "bug in the debugger: an exception is raised while printing debug information"++fnl()))

type value = Val.t

(** Abstract application, to print ltac functions *)
type appl =
  | UnnamedAppl (** For generic applications: nothing is printed *)
  | GlbAppl of (Names.kernel_name * Val.t list) list
       (** For calls to global constants, some may alias other. *)
let push_appl appl args =
  match appl with
  | UnnamedAppl -> UnnamedAppl
  | GlbAppl l -> GlbAppl (List.map (fun (h,vs) -> (h,vs@args)) l)
let pr_generic arg =
    let Val.Dyn (tag, _) = arg in
    str"<" ++ Val.pr tag ++ str ":(" ++ Pptactic.pr_value Pptactic.ltop arg ++ str ")>"
let pr_appl h vs =
  Pptactic.pr_ltac_constant  h ++ spc () ++
  Pp.prlist_with_sep spc pr_generic vs
let rec name_with_list appl t =
  match appl with
  | [] -> t
  | (h,vs)::l -> Proofview.Trace.name_tactic (fun () -> pr_appl h vs) (name_with_list l t)
let name_if_glob appl t =
  match appl with
  | UnnamedAppl -> t
  | GlbAppl l -> name_with_list l t
let combine_appl appl1 appl2 =
  match appl1,appl2 with
  | UnnamedAppl,a | a,UnnamedAppl -> a
  | GlbAppl l1 , GlbAppl l2 -> GlbAppl (l2@l1)

(* Values for interpretation *)
type tacvalue =
  | VFun of appl*ltac_trace * value Id.Map.t *
      Id.t option list * glob_tactic_expr
  | VRec of value Id.Map.t ref * glob_tactic_expr

let (wit_tacvalue : (Empty.t, tacvalue, tacvalue) Genarg.genarg_type) =
  let wit = Genarg.create_arg "tacvalue" in
  let () = register_val0 wit None in
  wit

let of_tacvalue v = in_gen (topwit wit_tacvalue) v
let to_tacvalue v = out_gen (topwit wit_tacvalue) v

(** More naming applications *)
let name_vfun appl vle =
  let vle = Value.normalize vle in
  if has_type vle (topwit wit_tacvalue) then
    match to_tacvalue vle with
    | VFun (appl0,trace,lfun,vars,t) -> of_tacvalue (VFun (combine_appl appl0 appl,trace,lfun,vars,t))
    | _ -> vle
  else vle

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
    let closure = VFun (UnnamedAppl,extract_trace ist, ist.lfun, [], tac) in
    of_tacvalue closure

  let cast_error wit v =
    let pr_v = Pptactic.pr_value Pptactic.ltop v in
    let Val.Dyn (tag, _) = v in
    let tag = Val.pr tag in
    user_err  (str "Type error: value " ++ pr_v ++ str " is a " ++ tag
      ++ str " while type " ++ Val.pr wit ++ str " was expected.")

  let unbox wit v ans = match ans with
  | None -> cast_error wit v
  | Some x -> x

  let rec prj : type a. a Val.tag -> Val.t -> a = fun tag v -> match tag with
  | Val.List tag -> List.map (fun v -> prj tag v) (unbox Val.typ_list v (to_list v))
  | Val.Opt tag -> Option.map (fun v -> prj tag v) (unbox Val.typ_opt v (to_option v))
  | Val.Pair (tag1, tag2) ->
    let (x, y) = unbox Val.typ_pair v (to_pair v) in
    (prj tag1 x, prj tag2 y)
  | Val.Base t ->
    let Val.Dyn (t', x) = v in
    match Val.eq t t' with
    | None -> cast_error t v
    | Some Refl -> x

  let rec tag_of_arg : type a b c. (a, b, c) genarg_type -> c Val.tag = fun wit -> match wit with
  | ExtraArg _ -> val_tag wit
  | ListArg t -> Val.List (tag_of_arg t)
  | OptArg t -> Val.Opt (tag_of_arg t)
  | PairArg (t1, t2) -> Val.Pair (tag_of_arg t1, tag_of_arg t2)

  let val_cast arg v = prj (tag_of_arg arg) v

  let cast (Topwit wit) v = val_cast wit v

end

let print_top_val env v = Pptactic.pr_value Pptactic.ltop v

let dloc = Loc.ghost

let catching_error call_trace fail (e, info) =
  let inner_trace =
    Option.default [] (Exninfo.get info ltac_trace_info)
  in
  if List.is_empty call_trace && List.is_empty inner_trace then fail (e, info)
  else begin
    assert (CErrors.noncritical e); (* preserved invariant *)
    let new_trace = inner_trace @ call_trace in
    let located_exc = (e, Exninfo.add info ltac_trace_info new_trace) in
    fail located_exc
  end

let catch_error call_trace f x =
  try f x
  with e when CErrors.noncritical e ->
    let e = CErrors.push e in
    catching_error call_trace iraise e

let catch_error_tac call_trace tac =
  Proofview.tclORELSE
    tac
    (catching_error call_trace (fun (e, info) -> Proofview.tclZERO ~info e))

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
    str "a value of type" ++ spc () ++ pr_argument_type v

let pr_closure env ist body =
  let pp_body = Pptactic.pr_glob_tactic env body in
  let pr_sep () = fnl () in
  let pr_iarg (id, arg) =
    let arg = pr_argument_type arg in
    hov 0 (pr_id id ++ spc () ++ str ":" ++ spc () ++ arg)
  in
  let pp_iargs = v 0 (prlist_with_sep pr_sep pr_iarg (Id.Map.bindings ist)) in
  pp_body ++ fnl() ++ str "in environment " ++ fnl() ++ pp_iargs

let pr_inspect env expr result =
  let pp_expr = Pptactic.pr_glob_tactic env expr in
  let pp_result =
    if has_type result (topwit wit_tacvalue) then
    match to_tacvalue result with
    | VFun (_,_, ist, ul, b) ->
      let body = if List.is_empty ul then b else (TacFun (ul, b)) in
      str "a closure with body " ++ fnl() ++ pr_closure env ist body
    | VRec (ist, body) ->
      str "a recursive closure" ++ fnl () ++ pr_closure env !ist body
    else
      let pp_type = pr_argument_type result in
      str "an object of type" ++ spc () ++ pp_type
  in
  pp_expr ++ fnl() ++ str "this is " ++ pp_result

(* Transforms an id into a constr if possible, or fails with Not_found *)
let constr_of_id env id =
  Term.mkVar (let _ = Environ.lookup_named id env in id)

(** Generic arguments : table of interpretation functions *)

(* Some of the code further down depends on the fact that push_trace does not modify sigma (the evar map) *)
let push_trace call ist = match TacStore.get ist.extra f_trace with
| None -> Proofview.tclUNIT [call]
| Some trace -> Proofview.tclUNIT (call :: trace)

let propagate_trace ist loc id v =
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then
    let tacv = to_tacvalue v in
    match tacv with
    | VFun (appl,_,lfun,it,b) ->
        let t = if List.is_empty it then b else TacFun (it,b) in
        push_trace(loc,LtacVarCall (id,t)) ist >>= fun trace ->
        let ans = VFun (appl,trace,lfun,it,b) in
        Proofview.tclUNIT (of_tacvalue ans)
    | _ ->  Proofview.tclUNIT v
  else Proofview.tclUNIT v

let append_trace trace v =
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then
    match to_tacvalue v with
    | VFun (appl,trace',lfun,it,b) -> of_tacvalue (VFun (appl,trace'@trace,lfun,it,b))
    | _ -> v
  else v

(* Dynamically check that an argument is a tactic *)
let coerce_to_tactic loc id v =
  let v = Value.normalize v in
  let fail () = user_err ~loc 
    (str "Variable " ++ pr_id id ++ str " should be bound to a tactic.")
  in
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then
    let tacv = to_tacvalue v in
    match tacv with
    | VFun _ -> v
    | _ -> fail ()
  else fail ()

let intro_pattern_of_ident id = (Loc.ghost, IntroNaming (IntroIdentifier id))
let value_of_ident id =
  in_gen (topwit wit_intro_pattern) (intro_pattern_of_ident id)

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
  | _ -> Proofview.NonLogical.return ()

let debugging_exception_step ist signal_anomaly e pp =
  let explain_exc =
    if signal_anomaly then explain_logic_error
    else explain_logic_error_no_anomaly in
  debugging_step ist (fun () ->
    pp() ++ spc() ++ str "raised the exception" ++ fnl() ++ explain_exc e)

let error_ltac_variable loc id env v s =
   user_err ~loc  (str "Ltac variable " ++ pr_id id ++
   strbrk " is bound to" ++ spc () ++ pr_value env v ++ spc () ++
   strbrk "which cannot be coerced to " ++ str s ++ str".")

(* Raise Not_found if not in interpretation sign *)
let try_interp_ltac_var coerce ist env (loc,id) =
  let v = Id.Map.find id ist.lfun in
  try coerce v with CannotCoerceTo s -> error_ltac_variable loc id env v s

let interp_ltac_var coerce ist env locid =
  try try_interp_ltac_var coerce ist env locid
  with Not_found -> anomaly (str "Detected '" ++ Id.print (snd locid) ++ str "' as ltac var at interning time")

let interp_ident ist env sigma id =
  try try_interp_ltac_var (coerce_var_to_ident false env) ist (Some (env,sigma)) (dloc,id)
  with Not_found -> id

(* Interprets an optional identifier, bound or fresh *)
let interp_name ist env sigma = function
  | Anonymous -> Anonymous
  | Name id -> Name (interp_ident ist env sigma id)

let interp_intro_pattern_var loc ist env sigma id =
  try try_interp_ltac_var (coerce_to_intro_pattern env) ist (Some (env,sigma)) (loc,id)
  with Not_found -> IntroNaming (IntroIdentifier id)

let interp_intro_pattern_naming_var loc ist env sigma id =
  try try_interp_ltac_var (coerce_to_intro_pattern_naming env) ist (Some (env,sigma)) (loc,id)
  with Not_found -> IntroIdentifier id

let interp_int ist locid =
  try try_interp_ltac_var coerce_to_int ist None locid
  with Not_found ->
    user_err ~loc:(fst locid) ~hdr:"interp_int"
     (str "Unbound variable "  ++ pr_id (snd locid) ++ str".")

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
  else Loc.raise ~loc (Logic.RefinerError (Logic.NoSuchHyp id))

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
        VarRef (get_id (Environ.lookup_named id env))
      with Not_found -> error_global_not_found ~loc (qualid_of_ident id)

let try_interp_evaluable env (loc, id) =
  let v = Environ.lookup_named id env in
  match v with
  | LocalDef _ -> EvalVarRef id
  | _ -> error_not_evaluable (VarRef id)

let interp_evaluable ist env sigma = function
  | ArgArg (r,Some (loc,id)) ->
    (* Maybe [id] has been introduced by Intro-like tactics *)
    begin
      try try_interp_evaluable env (loc, id)
      with Not_found ->
        match r with
        | EvalConstRef _ -> r
        | _ -> error_global_not_found ~loc (qualid_of_ident id)
    end
  | ArgArg (r,None) -> r
  | ArgVar (loc, id) ->
    try try_interp_ltac_var (coerce_to_evaluable_ref env) ist (Some (env,sigma)) (loc, id)
    with Not_found ->
      try try_interp_evaluable env (loc, id)
      with Not_found -> error_global_not_found ~loc (qualid_of_ident id)

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
  | IntroAction (IntroOrAndPattern (IntroAndPattern l)) ->
      List.flatten (List.map intropattern_ids l)
  | IntroAction (IntroOrAndPattern (IntroOrPattern ll)) ->
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
  let extract_ident ist env sigma id =
    try try_interp_ltac_var (coerce_to_ident_not_fresh sigma env)
			    ist (Some (env,sigma)) (dloc,id)
    with Not_found -> id in
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
	  | ArgVar (_,id) -> Id.to_string (extract_ident ist env sigma id)) l) in
      let s = if CLexer.is_keyword s then s^"0" else s in
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
    try Id.Map.add id (coerce_var_to_ident false env v) map
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
      let kind_for_intern =
        match kind with OfType _ -> WithoutTypeConstraint | _ -> kind in
      intern_gen kind_for_intern ~allow_patvar ~ltacvars env c
  in
  (* Jason Gross: To avoid unnecessary modifications to tacinterp, as
      suggested by Arnaud Spiwack, we run push_trace immediately.  We do
      this with the kludge of an empty proofview, and rely on the
      invariant that running the tactic returned by push_trace does
      not modify sigma. *)
  let (_, dummy_proofview) = Proofview.init sigma [] in
  let (trace,_,_,_) = Proofview.apply env (push_trace (loc_of_glob_constr c,LtacConstrInterp (c,vars)) ist) dummy_proofview in
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
  solve_unification_constraints = true;
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
  solve_unification_constraints = true;
  use_hook = Some solve_by_implicit_tactic;
  fail_evar = false;
  expand_evars = true }

let open_constr_no_classes_flags = {
  use_typeclasses = false;
  solve_unification_constraints = true;
  use_hook = Some solve_by_implicit_tactic;
  fail_evar = false;
  expand_evars = true }

let pure_open_constr_flags = {
  use_typeclasses = false;
  solve_unification_constraints = true;
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

let interp_typed_pattern ist env sigma (_,c,_) =
  let sigma, c =
    interp_gen WithoutTypeConstraint ist true pure_open_constr_flags env sigma c in
  pattern_of_constr env sigma c

(* Interprets a constr expression *)
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

(* Interprets a reduction expression *)
let interp_unfold ist env sigma (occs,qid) =
  (interp_occurrences ist occs,interp_evaluable ist env sigma qid)

let interp_flag ist env sigma red =
  { red with rConst = List.map (interp_evaluable ist env sigma) red.rConst }

let interp_constr_with_occurrences ist env sigma (occs,c) =
  let (sigma,c_interp) = interp_constr ist env sigma c in
  sigma , (interp_occurrences ist occs, c_interp)

let interp_closed_typed_pattern_with_occurrences ist env sigma (occs, a) =
  let p = match a with
  | Inl (ArgVar (loc,id)) ->
      (* This is the encoding of an ltac var supposed to be bound
         prioritary to an evaluable reference and otherwise to a constr
         (it is an encoding to satisfy the "union" type given to Simpl) *)
    let coerce_eval_ref_or_constr x =
      try Inl (coerce_to_evaluable_ref env x)
      with CannotCoerceTo _ ->
        let c = coerce_to_closed_constr env x in
        Inr (pattern_of_constr env sigma c) in
    (try try_interp_ltac_var coerce_eval_ref_or_constr ist (Some (env,sigma)) (loc,id)
     with Not_found ->
       error_global_not_found ~loc (qualid_of_ident id))
  | Inl (ArgArg _ as b) -> Inl (interp_evaluable ist env sigma b)
  | Inr c -> Inr (interp_typed_pattern ist env sigma c) in
  interp_occurrences ist occs, p

let interp_constr_with_occurrences_and_name_as_list =
  interp_constr_in_compound_list
    (fun c -> ((AllOccurrences,c),Anonymous))
    (function ((occs,c),Anonymous) when occs == AllOccurrences -> c
      | _ -> raise Not_found)
    (fun ist env sigma (occ_c,na) ->
      let (sigma,c_interp) = interp_constr_with_occurrences ist env sigma occ_c in
      sigma, (c_interp,
       interp_name ist env sigma na))

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
  | Simpl (f,o) ->
     sigma , Simpl (interp_flag ist env sigma f,
		    Option.map (interp_closed_typed_pattern_with_occurrences ist env sigma) o)
  | CbvVm o ->
    sigma , CbvVm (Option.map (interp_closed_typed_pattern_with_occurrences ist env sigma) o)
  | CbvNative o ->
    sigma , CbvNative (Option.map (interp_closed_typed_pattern_with_occurrences ist env sigma) o)
  | (Red _ |  Hnf | ExtraRedExpr _ as r) -> sigma , r

let interp_may_eval f ist env sigma = function
  | ConstrEval (r,c) ->
      let (sigma,redexp) = interp_red_expr ist env sigma r in
      let (sigma,c_interp) = f ist env sigma c in
      let (redfun, _) = Redexpr.reduction_of_red_expr env redexp in
      let sigma = Sigma.Unsafe.of_evar_map sigma in
      let Sigma (c, sigma, _) = redfun.Reductionops.e_redfun env sigma c_interp in
      (Sigma.to_evar_map sigma, c)
  | ConstrContext ((loc,s),c) ->
      (try
	let (sigma,ic) = f ist env sigma c in
	let ctxt = coerce_to_constr_context (Id.Map.find s ist.lfun) in
	let evdref = ref sigma in
	let c = subst_meta [Constr_matching.special_meta,ic] ctxt in
	let c = Typing.e_solve_evars env evdref c in
	!evdref , c
      with
	| Not_found ->
	    user_err ~loc ~hdr:"interp_may_eval"
	    (str "Unbound context identifier" ++ pr_id s ++ str"."))
  | ConstrTypeOf c ->
      let (sigma,c_interp) = f ist env sigma c in
      Typing.type_of ~refresh:true env sigma c_interp
  | ConstrTerm c ->
     try
	f ist env sigma c
     with reraise ->
       let reraise = CErrors.push reraise in
       (* spiwack: to avoid unnecessary modifications of tacinterp, as this
          function already use effect, I call [run] hoping it doesn't mess
          up with any assumption. *)
       Proofview.NonLogical.run (debugging_exception_step ist false (fst reraise) (fun () ->
         str"interpretation of term " ++ pr_glob_constr_env env (fst c)));
       iraise reraise

(* Interprets a constr expression possibly to first evaluate *)
let interp_constr_may_eval ist env sigma c =
  let (sigma,csr) =
    try
      interp_may_eval interp_constr ist env sigma c
    with reraise ->
      let reraise = CErrors.push reraise in
      (* spiwack: to avoid unnecessary modifications of tacinterp, as this
          function already use effect, I call [run] hoping it doesn't mess
          up with any assumption. *)
       Proofview.NonLogical.run (debugging_exception_step ist false (fst reraise) (fun () -> str"evaluation of term"));
      iraise reraise
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
  let open Ftactic in
  if has_type v (topwit wit_tacvalue) then
    Ftactic.return (str "<tactic>")
  else if has_type v (topwit wit_constr) then
    let v = out_gen (topwit wit_constr) v in
    Ftactic.nf_enter {enter = begin fun gl -> Ftactic.return (pr_constr_env (pf_env gl) (project gl) v) end }
  else if has_type v (topwit wit_constr_under_binders) then
    let c = out_gen (topwit wit_constr_under_binders) v in
    Ftactic.nf_enter { enter = begin fun gl ->
      Ftactic.return (pr_constr_under_binders_env (pf_env gl) (project gl) c)
    end }
  else if has_type v (topwit wit_unit) then
    Ftactic.return (str "()")
  else if has_type v (topwit wit_int) then
    Ftactic.return (int (out_gen (topwit wit_int) v))
  else if has_type v (topwit wit_intro_pattern) then
    let p = out_gen (topwit wit_intro_pattern) v in
    let print env sigma c = pr_constr_env env sigma (fst (Tactics.run_delayed env Evd.empty c)) in
    Ftactic.nf_enter { enter = begin fun gl ->
      Ftactic.return (Miscprint.pr_intro_pattern (fun c -> print (pf_env gl) (project gl) c) p)
    end }
  else if has_type v (topwit wit_constr_context) then
    let c = out_gen (topwit wit_constr_context) v in
    Ftactic.nf_enter { enter = begin fun gl -> Ftactic.return (pr_constr_env (pf_env gl) (project gl) c) end }
  else if has_type v (topwit wit_uconstr) then
    let c = out_gen (topwit wit_uconstr) v in
    Ftactic.nf_enter { enter = begin fun gl ->
      Ftactic.return (pr_closed_glob_env (pf_env gl)
                        (project gl) c)
    end }
  else if has_type v (topwit wit_var) then
    let id = out_gen (topwit wit_var) v in
    Ftactic.nf_enter { enter = begin fun gl -> Ftactic.return (pr_id id) end }
  else match Value.to_list v with
  | Some l ->
    Ftactic.List.map message_of_value l >>= fun l ->
    Ftactic.return (prlist_with_sep spc (fun x -> x) l)
  | None ->
    let tag = pr_argument_type v in
    Ftactic.return (str "<" ++ tag ++ str ">") (** TODO *)

let interp_message_token ist = function
  | MsgString s -> Ftactic.return (str s)
  | MsgInt n -> Ftactic.return (int n)
  | MsgIdent (loc,id) ->
    let v = try Some (Id.Map.find id ist.lfun) with Not_found -> None in
    match v with
    | None -> Ftactic.lift (Tacticals.New.tclZEROMSG (pr_id id ++ str" not found."))
    | Some v -> message_of_value v

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
  | IntroFresh id -> IntroFresh (interp_ident ist env sigma id)
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
      let c = { delayed = fun env sigma ->
        let sigma = Sigma.to_evar_map sigma in
        let (sigma, c) = interp_open_constr ist env sigma c in
        Sigma.Unsafe.of_pair (c, sigma)
      } in
      let sigma,ipat = interp_intro_pattern ist env sigma ipat in
      sigma, IntroApplyOn (c,ipat)
  | IntroWildcard | IntroRewrite _ as x -> sigma, x

and interp_or_and_intro_pattern ist env sigma = function
  | IntroAndPattern l ->
      let sigma, l = List.fold_map (interp_intro_pattern ist env) sigma l in
      sigma, IntroAndPattern l
  | IntroOrPattern ll ->
      let sigma, ll = List.fold_map (interp_intro_pattern_list_as_list ist env) sigma ll in
      sigma, IntroOrPattern ll

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
        user_err ~loc (str "Cannot coerce to a disjunctive/conjunctive pattern."))
  | Some (ArgArg (loc,l)) ->
      let sigma,l = interp_or_and_intro_pattern ist env sigma l in
      sigma, Some (loc,l)

let interp_intro_pattern_option ist env sigma = function
  | None -> sigma, None
  | Some ipat ->
      let sigma, ipat = interp_intro_pattern ist env sigma ipat in
      sigma, Some ipat

let interp_in_hyp_as ist env sigma (id,ipat) =
  let sigma, ipat = interp_intro_pattern_option ist env sigma ipat in
  sigma,(interp_hyp ist env sigma id,ipat)

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

let interp_open_constr_with_bindings ist env sigma (c,bl) =
  let sigma, bl = interp_bindings ist env sigma bl in
  let sigma, c = interp_open_constr ist env sigma c in
  sigma, (c, bl)

let loc_of_bindings = function
| NoBindings -> Loc.ghost
| ImplicitBindings l -> loc_of_glob_constr (fst (List.last l))
| ExplicitBindings l -> pi1 (List.last l)

let interp_open_constr_with_bindings_loc ist ((c,_),bl as cb) =
  let loc1 = loc_of_glob_constr c in
  let loc2 = loc_of_bindings bl in
  let loc = if Loc.is_ghost loc2 then loc1 else Loc.merge loc1 loc2 in
  let f = { delayed = fun env sigma ->
    let sigma = Sigma.to_evar_map sigma in
    let (sigma, c) = interp_open_constr_with_bindings ist env sigma cb in
    Sigma.Unsafe.of_pair (c, sigma)
  } in
    (loc,f)

let interp_destruction_arg ist gl arg =
  match arg with
  | keep,ElimOnConstr c ->
      keep,ElimOnConstr { delayed = fun env sigma ->
        let sigma = Sigma.to_evar_map sigma in
        let (sigma, c) = interp_constr_with_bindings ist env sigma c in
        Sigma.Unsafe.of_pair (c, sigma)
      }
  | keep,ElimOnAnonHyp n as x -> x
  | keep,ElimOnIdent (loc,id) ->
      let error () = user_err ~loc 
       (strbrk "Cannot coerce " ++ pr_id id ++
        strbrk " neither to a quantified hypothesis nor to a term.")
      in
      let try_cast_id id' =
        if Tactics.is_quantified_hypothesis id' gl
        then keep,ElimOnIdent (loc,id')
        else
          (keep, ElimOnConstr { delayed = begin fun env sigma ->
          try Sigma.here (constr_of_id env id', NoBindings) sigma
          with Not_found ->
            user_err ~loc  ~hdr:"interp_destruction_arg" (
            pr_id id ++ strbrk " binds to " ++ pr_id id' ++ strbrk " which is neither a declared nor a quantified hypothesis.")
          end })
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
        | Some c -> keep,ElimOnConstr { delayed = fun env sigma -> Sigma ((c,NoBindings), sigma, Sigma.refl) }
      with Not_found ->
	(* We were in non strict (interactive) mode *)
	if Tactics.is_quantified_hypothesis id gl then
          keep,ElimOnIdent (loc,id)
	else
          let c = (GVar (loc,id),Some (CRef (Ident (loc,id),None))) in
          let f = { delayed = fun env sigma ->
            let sigma = Sigma.to_evar_map sigma in
            let (sigma,c) = interp_open_constr ist env sigma c in
            Sigma.Unsafe.of_pair ((c,NoBindings), sigma)
          } in
          keep,ElimOnConstr f

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

let eval_pattern lfun ist env sigma (bvars,(glob,_),pat as c) =
  if use_types then
    (bvars,interp_typed_pattern ist env sigma c)
  else
    (bvars,instantiate_pattern env sigma lfun pat)

let read_pattern lfun ist env sigma = function
  | Subterm (b,ido,c) -> Subterm (b,ido,eval_pattern lfun ist env sigma c)
  | Term c -> Term (eval_pattern lfun ist env sigma c)

(* Reads the hypotheses of a Match Context rule *)
let cons_and_check_name id l =
  if Id.List.mem id l then
    user_err ~hdr:"read_match_goal_hyps" (
      str "Hypothesis pattern-matching variable " ++ pr_id id ++
      str " used twice in the same pattern.")
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

let warn_deprecated_info =
  CWarnings.create ~name:"deprecated-info-tactical" ~category:"deprecated"
         (fun () ->
          strbrk "The general \"info\" tactic is currently not working." ++ spc()++
            strbrk "There is an \"Info\" command to replace it." ++fnl () ++
            strbrk "Some specific verbose tactics may also exist, such as info_eauto.")

(* Interprets an l-tac expression into a value *)
let rec val_interp ist ?(appl=UnnamedAppl) (tac:glob_tactic_expr) : Val.t Ftactic.t =
  (* The name [appl] of applied top-level Ltac names is ignored in
     [value_interp]. It is installed in the second step by a call to
     [name_vfun], because it gives more opportunities to detect a
     [VFun]. Otherwise a [Ltac t := let x := .. in tac] would never
     register its name since it is syntactically a let, not a
     function.  *)
  let value_interp ist = match tac with
  | TacFun (it, body) ->
    Ftactic.return (of_tacvalue (VFun (UnnamedAppl,extract_trace ist, ist.lfun, it, body)))
  | TacLetIn (true,l,u) -> interp_letrec ist l u
  | TacLetIn (false,l,u) -> interp_letin ist l u
  | TacMatchGoal (lz,lr,lmr) -> interp_match_goal ist lz lr lmr
  | TacMatch (lz,c,lmr) -> interp_match ist lz c lmr
  | TacArg (loc,a) -> interp_tacarg ist a
  | t ->
    (** Delayed evaluation *)
    Ftactic.return (of_tacvalue (VFun (UnnamedAppl,extract_trace ist, ist.lfun, [], t)))
  in
  let open Ftactic in
  Control.check_for_interrupt ();
  match curr_debug ist with
  | DebugOn lev ->
        let eval v =
          let ist = { ist with extra = TacStore.set ist.extra f_debug v } in
          value_interp ist >>= fun v -> return (name_vfun appl v)
        in
	Tactic_debug.debug_prompt lev tac eval
  | _ -> value_interp ist >>= fun v -> return (name_vfun appl v)
      

and eval_tactic ist tac : unit Proofview.tactic = match tac with
  | TacAtom (loc,t) ->
      let call = LtacAtomCall t in
      push_trace(loc,call) ist >>= fun trace ->
      Profile_ltac.do_profile "eval_tactic:2" trace
        (catch_error_tac trace (interp_atomic ist t))
  | TacFun _ | TacLetIn _ -> assert false
  | TacMatchGoal _ | TacMatch _ -> assert false
  | TacId [] -> Proofview.tclLIFT (db_breakpoint (curr_debug ist) [])
  | TacId s ->
      let msgnl =
        let open Ftactic in
        interp_message ist s >>= fun msg ->
        return (hov 0 msg , hov 0 msg)
      in
      let print (_,msgnl) = Proofview.(tclLIFT (NonLogical.print_info msgnl)) in
      let log (msg,_) = Proofview.Trace.log (fun () -> msg) in
      let break = Proofview.tclLIFT (db_breakpoint (curr_debug ist) s) in
      Ftactic.run msgnl begin fun msgnl ->
        print msgnl <*> log msgnl <*> break
      end
  | TacFail (g,n,s) ->
      let msg = interp_message ist s in
      let tac l = Tacticals.New.tclFAIL (interp_int_or_var ist n) l in
      let tac =
        match g with
        | TacLocal -> fun l -> Proofview.tclINDEPENDENT (tac l)
        | TacGlobal -> tac
      in
      Ftactic.run msg tac
  | TacProgress tac -> Tacticals.New.tclPROGRESS (interp_tactic ist tac)
  | TacShowHyps tac ->
         Proofview.V82.tactic begin
           tclSHOWHYPS (Proofview.V82.of_tactic (interp_tactic ist tac))
         end
  | TacAbstract (tac,ido) ->
      Proofview.Goal.nf_enter { enter = begin fun gl -> Tactics.tclABSTRACT
        (Option.map (interp_ident ist (pf_env gl) (project gl)) ido) (interp_tactic ist tac)
      end }
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
  | TacIfThenCatch (t,tt,te) ->
      Tacticals.New.tclIFCATCH
        (interp_tactic ist t)
        (fun () -> interp_tactic ist tt)
        (fun () -> interp_tactic ist te)
  | TacOrelse (tac1,tac2) ->
      Tacticals.New.tclORELSE (interp_tactic ist tac1) (interp_tactic ist tac2)
  | TacFirst l -> Tacticals.New.tclFIRST (List.map (interp_tactic ist) l)
  | TacSolve l -> Tacticals.New.tclSOLVE (List.map (interp_tactic ist) l)
  | TacComplete tac -> Tacticals.New.tclCOMPLETE (interp_tactic ist tac)
  | TacArg a -> interp_tactic ist (TacArg a)
  | TacInfo tac ->
      warn_deprecated_info ();
      eval_tactic ist tac
  | TacSelect (sel, tac) -> Tacticals.New.tclSELECT sel (interp_tactic ist tac)
  (* For extensions *)
  | TacAlias (loc,s,l) ->
      let (ids, body) = Tacenv.interp_alias s in
      let (>>=) = Ftactic.bind in
      let interp_vars = Ftactic.List.map (fun v -> interp_tacarg ist v) l in
      let tac l =
        let addvar x v accu = Id.Map.add x v accu in
        let lfun = List.fold_right2 addvar ids l ist.lfun in
        Ftactic.lift (push_trace (loc,LtacNotationCall s) ist) >>= fun trace ->
        let ist = {
          lfun = lfun;
          extra = TacStore.set ist.extra f_trace trace; } in
        val_interp ist body >>= fun v ->
        Ftactic.lift (tactic_of_value ist v)
      in
      let tac =
        Ftactic.with_env interp_vars >>= fun (env, lr) ->
        let name () = Pptactic.pr_alias (fun v -> print_top_val env v) 0 s lr in
        Proofview.Trace.name_tactic name (tac lr)
      (* spiwack: this use of name_tactic is not robust to a
         change of implementation of [Ftactic]. In such a situation,
         some more elaborate solution will have to be used. *)
      in
      let tac =
        let len1 = List.length ids in
        let len2 = List.length l in
        if len1 = len2 then tac
        else Tacticals.New.tclZEROMSG (str "Arguments length mismatch: \
          expected " ++ int len1 ++ str ", found " ++ int len2)
      in
      Ftactic.run tac (fun () -> Proofview.tclUNIT ())

  | TacML (loc,opn,l) ->
      push_trace (loc,LtacMLCall tac) ist >>= fun trace ->
      let ist = { ist with extra = TacStore.set ist.extra f_trace trace; } in
      let tac = Tacenv.interp_ml_tactic opn in
      let args = Ftactic.List.map_right (fun a -> interp_tacarg ist a) l in
      let tac args =
        let name () = Pptactic.pr_extend (fun v -> print_top_val () v) 0 opn args in
        Proofview.Trace.name_tactic name (catch_error_tac trace (tac args ist))
      in
      Ftactic.run args tac

and force_vrec ist v : Val.t Ftactic.t =
  let v = Value.normalize v in
  if has_type v (topwit wit_tacvalue) then
    let v = to_tacvalue v in
    match v with
    | VRec (lfun,body) -> val_interp {ist with lfun = !lfun} body
    | v -> Ftactic.return (of_tacvalue v)
  else Ftactic.return v

and interp_ltac_reference loc' mustbetac ist r : Val.t Ftactic.t =
  match r with
  | ArgVar (loc,id) ->
      let v =
        try Id.Map.find id ist.lfun
        with Not_found -> in_gen (topwit wit_var) id
      in
      let open Ftactic in
      force_vrec ist v >>= begin fun v ->
      Ftactic.lift (propagate_trace ist loc id v) >>= fun v ->
      if mustbetac then Ftactic.return (coerce_to_tactic loc id v) else Ftactic.return v
      end
  | ArgArg (loc,r) ->
      let ids = extract_ids [] ist.lfun in
      let loc_info = ((if Loc.is_ghost loc' then loc else loc'),LtacNameCall r) in
      let extra = TacStore.set ist.extra f_avoid_ids ids in
      push_trace loc_info ist >>= fun trace ->
      let extra = TacStore.set extra f_trace trace in
      let ist = { lfun = Id.Map.empty; extra = extra; } in
      let appl = GlbAppl[r,[]] in
      val_interp ~appl ist (Tacenv.interp_ltac r)

and interp_tacarg ist arg : Val.t Ftactic.t =
  match arg with
  | TacGeneric arg -> interp_genarg ist arg
  | Reference r -> interp_ltac_reference dloc false ist r
  | ConstrMayEval c ->
      Ftactic.s_enter { s_enter = begin fun gl ->
        let sigma = project gl in
        let env = Proofview.Goal.env gl in
        let (sigma,c_interp) = interp_constr_may_eval ist env sigma c in
        Sigma.Unsafe.of_pair (Ftactic.return (Value.of_constr c_interp), sigma)
      end }
  | TacCall (loc,r,[]) ->
      interp_ltac_reference loc true ist r
  | TacCall (loc,f,l) ->
      let (>>=) = Ftactic.bind in
      interp_ltac_reference loc true ist f >>= fun fv ->
      Ftactic.List.map (fun a -> interp_tacarg ist a) l >>= fun largs ->
      interp_app loc ist fv largs
  | TacFreshId l ->
      Ftactic.enter { enter = begin fun gl ->
        let id = interp_fresh_id ist (pf_env gl) (project gl) l in
        Ftactic.return (in_gen (topwit wit_intro_pattern) (dloc, IntroNaming (IntroIdentifier id)))
      end }
  | TacPretype c ->
      Ftactic.s_enter { s_enter = begin fun gl ->
        let sigma = Proofview.Goal.sigma gl in
        let env = Proofview.Goal.env gl in
        let c = interp_uconstr ist env c in
        let Sigma (c, sigma, p) = (type_uconstr ist c).delayed env sigma in
        Sigma (Ftactic.return (Value.of_constr c), sigma, p)
      end }
  | TacNumgoals ->
      Ftactic.lift begin
        let open Proofview.Notations in
        Proofview.numgoals >>= fun i ->
        Proofview.tclUNIT (Value.of_int i)
      end
  | Tacexp t -> val_interp ist t

(* Interprets an application node *)
and interp_app loc ist fv largs : Val.t Ftactic.t =
  let (>>=) = Ftactic.bind in
  let fail = Tacticals.New.tclZEROMSG (str "Illegal tactic application.") in
  let fv = Value.normalize fv in
  if has_type fv (topwit wit_tacvalue) then
  match to_tacvalue fv with
     (* if var=[] and body has been delayed by val_interp, then body
         is not a tactic that expects arguments.
         Otherwise Ltac goes into an infinite loop (val_interp puts
         a VFun back on body, and then interp_app is called again...) *)
    | (VFun(appl,trace,olfun,(_::_ as var),body)
      |VFun(appl,trace,olfun,([] as var),
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
              catch_error_tac trace (val_interp ist body) >>= fun v ->
              Ftactic.return (name_vfun (push_appl appl largs) v)
            end
	    begin fun (e, info) ->
              Proofview.tclLIFT (debugging_exception_step ist false e (fun () -> str "evaluation")) <*>
	      Proofview.tclZERO ~info e
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
        Ftactic.return (of_tacvalue (VFun(push_appl appl largs,trace,newlfun,lvar,body)))
    | _ -> fail
  else fail

(* Gives the tactic corresponding to the tactic value *)
and tactic_of_value ist vle =
  let vle = Value.normalize vle in
  if has_type vle (topwit wit_tacvalue) then
  match to_tacvalue vle with
  | VFun (appl,trace,lfun,[],t) ->
      let ist = {
        lfun = lfun;
        extra = TacStore.set ist.extra f_trace []; } in
      let tac = name_if_glob appl (eval_tactic ist t) in
      Profile_ltac.do_profile "tactic_of_value" trace (catch_error_tac trace tac)
  | (VFun _|VRec _) -> Tacticals.New.tclZEROMSG (str "A fully applied tactic is expected.")
  else if has_type vle (topwit wit_tactic) then
    let tac = out_gen (topwit wit_tactic) vle in
    tactic_of_value ist tac
  else Tacticals.New.tclZEROMSG (str "Expression does not evaluate to a tactic.")

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
    (of type {!Tactic_matching.t}). *)
and interp_match_success ist { Tactic_matching.subst ; context ; terms ; lhs } =
  let (>>=) = Ftactic.bind in
  let lctxt = Id.Map.map interp_context context in
  let hyp_subst = Id.Map.map Value.of_constr terms in
  let lfun = extend_values_with_bindings subst (lctxt +++ hyp_subst +++ ist.lfun) in
  let ist = { ist with lfun } in
  val_interp ist lhs >>= fun v ->
  if has_type v (topwit wit_tacvalue) then match to_tacvalue v with
  | VFun (appl,trace,lfun,[],t) ->
      let ist = {
        lfun = lfun;
        extra = TacStore.set ist.extra f_trace trace; } in
      let tac = eval_tactic ist t in
      let dummy = VFun (appl,extract_trace ist, Id.Map.empty, [], TacId []) in
      catch_error_tac trace (tac <*> Ftactic.return (of_tacvalue dummy))
  | _ -> Ftactic.return v
  else Ftactic.return v


(** [interp_match_successes lz ist s] interprets the stream of
    matching of successes [s]. If [lz] is set to true, then only the
    first success is considered, otherwise further successes are tried
    if the left-hand side fails. *)
and interp_match_successes lz ist s =
   let general =
     let break (e, info) = match e with
       | FailError (0, _) -> None
       | FailError (n, s) -> Some (FailError (pred n, s), info)
       | _ -> None
     in
     Proofview.tclBREAK break s >>= fun ans -> interp_match_success ist ans
   in
    match lz with
    | General ->
        general
    | Select ->
      begin
        (** Only keep the first matching result, we don't backtrack on it *)
        let s = Proofview.tclONCE s in
        s >>= fun ans -> interp_match_success ist ans
      end
    | Once ->
        (** Once a tactic has succeeded, do not backtrack anymore *)
        Proofview.tclONCE general

(* Interprets the Match expressions *)
and interp_match ist lz constr lmr =
  let (>>=) = Ftactic.bind in
  begin Proofview.tclORELSE
    (interp_ltac_constr ist constr)
    begin function
      | (e, info) ->
          Proofview.tclLIFT (debugging_exception_step ist true e
          (fun () -> str "evaluation of the matched expression")) <*>
          Proofview.tclZERO ~info e
    end
  end >>= fun constr ->
  Ftactic.enter { enter = begin fun gl ->
    let sigma = project gl in
    let env = Proofview.Goal.env gl in
    let ilr = read_match_rule (extract_ltac_constr_values ist env) ist env sigma lmr in
    interp_match_successes lz ist (Tactic_matching.match_term env sigma constr ilr)
  end }

(* Interprets the Match Context expressions *)
and interp_match_goal ist lz lr lmr =
    Ftactic.nf_enter { enter = begin fun gl ->
      let sigma = project gl in
      let env = Proofview.Goal.env gl in
      let hyps = Proofview.Goal.hyps gl in
      let hyps = if lr then List.rev hyps else hyps in
      let concl = Proofview.Goal.concl gl in
      let ilr = read_match_rule (extract_ltac_constr_values ist env) ist env sigma lmr in
      interp_match_successes lz ist (Tactic_matching.match_goal env sigma hyps concl ilr)
    end }

(* Interprets extended tactic generic arguments *)
and interp_genarg ist x : Val.t Ftactic.t =
    let open Ftactic.Notations in
    (** Ad-hoc handling of some types. *)
    let tag = genarg_tag x in
    if argument_type_eq tag (unquote (topwit (wit_list wit_var))) then
      interp_genarg_var_list ist x
    else if argument_type_eq tag (unquote (topwit (wit_list wit_constr))) then
      interp_genarg_constr_list ist x
    else
    let GenArg (Glbwit wit, x) = x in
    match wit with
    | ListArg wit ->
      let map x = interp_genarg ist (Genarg.in_gen (glbwit wit) x) in
      Ftactic.List.map map x >>= fun l ->
      Ftactic.return (Val.Dyn (Val.typ_list, l))
    | OptArg wit ->
      begin match x with
      | None -> Ftactic.return (Val.Dyn (Val.typ_opt, None))
      | Some x ->
        interp_genarg ist (Genarg.in_gen (glbwit wit) x) >>= fun x ->
        Ftactic.return (Val.Dyn (Val.typ_opt, Some x))
      end
    | PairArg (wit1, wit2) ->
      let (p, q) = x in
      interp_genarg ist (Genarg.in_gen (glbwit wit1) p) >>= fun p ->
      interp_genarg ist (Genarg.in_gen (glbwit wit2) q) >>= fun q ->
      Ftactic.return (Val.Dyn (Val.typ_pair, (p, q)))
    | ExtraArg s ->
      Geninterp.interp wit ist x

(** returns [true] for genargs which have the same meaning
    independently of goals. *)

and interp_genarg_constr_list ist x =
  Ftactic.nf_s_enter { s_enter = begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Sigma.to_evar_map (Proofview.Goal.sigma gl) in
  let lc = Genarg.out_gen (glbwit (wit_list wit_constr)) x in
  let (sigma,lc) = interp_constr_list ist env sigma lc in
  let lc = in_list (val_tag wit_constr) lc in
  Sigma.Unsafe.of_pair (Ftactic.return lc, sigma)
  end }

and interp_genarg_var_list ist x =
  Ftactic.enter { enter = begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Sigma.to_evar_map (Proofview.Goal.sigma gl) in
  let lc = Genarg.out_gen (glbwit (wit_list wit_var)) x in
  let lc = interp_hyp_list ist env sigma lc in
  let lc = in_list (val_tag wit_var) lc in
  Ftactic.return lc
  end }

(* Interprets tactic expressions : returns a "constr" *)
and interp_ltac_constr ist e : constr Ftactic.t =
  let (>>=) = Ftactic.bind in
  begin Proofview.tclORELSE
      (val_interp ist e)
      begin function (err, info) -> match err with
        | Not_found ->
            Ftactic.enter { enter = begin fun gl ->
              let env = Proofview.Goal.env gl in
              Proofview.tclLIFT begin
                debugging_step ist (fun () ->
                  str "evaluation failed for" ++ fnl() ++
                    Pptactic.pr_glob_tactic env e)
              end
            <*> Proofview.tclZERO Not_found
            end }
        | err -> Proofview.tclZERO ~info err
      end
  end >>= fun result ->
  Ftactic.enter { enter = begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = project gl in
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
    Tacticals.New.tclZEROMSG (str "Must evaluate to a closed term" ++ fnl() ++
      str "offending expression: " ++ fnl() ++ pr_inspect env e result)
  end }


(* Interprets tactic expressions : returns a "tactic" *)
and interp_tactic ist tac : unit Proofview.tactic =
  Ftactic.run (val_interp ist tac) (fun v -> tactic_of_value ist v)

(* Provides a "name" for the trace to atomic tactics *)
and name_atomic ?env tacexpr tac : unit Proofview.tactic =
  begin match env with
  | Some e -> Proofview.tclUNIT e
  | None -> Proofview.tclENV
  end >>= fun env ->
  let name () = Pptactic.pr_atomic_tactic env tacexpr in
  Proofview.Trace.name_tactic name tac

(* Interprets a primitive tactic *)
and interp_atomic ist tac : unit Proofview.tactic =
  match tac with
  (* Basic tactics *)
  | TacIntroPattern (ev,l) ->
      Proofview.Goal.enter { enter = begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = project gl in
        let sigma,l' = interp_intro_pattern_list_as_list ist env sigma l in
        Tacticals.New.tclWITHHOLES ev
        (name_atomic ~env
          (TacIntroPattern (ev,l))
          (* spiwack: print uninterpreted, not sure if it is the
             expected behaviour. *)
          (Tactics.intro_patterns ev l')) sigma
      end }
  | TacApply (a,ev,cb,cl) ->
      (* spiwack: until the tactic is in the monad *)
      Proofview.Trace.name_tactic (fun () -> Pp.str"<apply>") begin
      Proofview.Goal.enter { enter = begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = project gl in
	let l = List.map (fun (k,c) ->
          let loc, f = interp_open_constr_with_bindings_loc ist c in
	    (k,(loc,f))) cb 
	in
        let sigma,tac = match cl with
          | None -> sigma, Tactics.apply_with_delayed_bindings_gen a ev l
          | Some cl ->
              let sigma,(id,cl) = interp_in_hyp_as ist env sigma cl in
              sigma, Tactics.apply_delayed_in a ev id l cl in
        Tacticals.New.tclWITHHOLES ev tac sigma
      end }
      end
  | TacElim (ev,(keep,cb),cbo) ->
      Proofview.Goal.enter { enter = begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = project gl in 
        let sigma, cb = interp_constr_with_bindings ist env sigma cb in
        let sigma, cbo = Option.fold_map (interp_constr_with_bindings ist env) sigma cbo in
        let named_tac =
          let tac = Tactics.elim ev keep cb cbo in
          name_atomic ~env (TacElim (ev,(keep,cb),cbo)) tac
        in
        Tacticals.New.tclWITHHOLES ev named_tac sigma
      end }
  | TacCase (ev,(keep,cb)) ->
      Proofview.Goal.enter { enter = begin fun gl ->
        let sigma = project gl in
        let env = Proofview.Goal.env gl in
        let sigma, cb = interp_constr_with_bindings ist env sigma cb in
        let named_tac =
          let tac = Tactics.general_case_analysis ev keep cb in
          name_atomic ~env (TacCase(ev,(keep,cb))) tac
        in
        Tacticals.New.tclWITHHOLES ev named_tac sigma
      end }
  | TacMutualFix (id,n,l) ->
      (* spiwack: until the tactic is in the monad *)
      Proofview.Trace.name_tactic (fun () -> Pp.str"<mutual fix>") begin
      Proofview.Goal.nf_s_enter { s_enter = begin fun gl ->
        let env = pf_env gl in
        let f sigma (id,n,c) =
          let (sigma,c_interp) = interp_type ist env sigma c in
	  sigma , (interp_ident ist env sigma id,n,c_interp) in
        let (sigma,l_interp) =
          Evd.MonadR.List.map_right (fun c sigma -> f sigma c) l (project gl)
        in
        let tac = Tactics.mutual_fix (interp_ident ist env sigma id) n l_interp 0 in
        Sigma.Unsafe.of_pair (tac, sigma)
      end }
      end
  | TacMutualCofix (id,l) ->
      (* spiwack: until the tactic is in the monad *)
      Proofview.Trace.name_tactic (fun () -> Pp.str"<mutual cofix>") begin
      Proofview.Goal.nf_s_enter { s_enter = begin fun gl ->
        let env = pf_env gl in
        let f sigma (id,c) =
	  let (sigma,c_interp) = interp_type ist env sigma c in
	  sigma , (interp_ident ist env sigma id,c_interp) in
        let (sigma,l_interp) =
          Evd.MonadR.List.map_right (fun c sigma -> f sigma c) l (project gl)
        in
        let tac = Tactics.mutual_cofix (interp_ident ist env sigma id) l_interp 0 in
        Sigma.Unsafe.of_pair (tac, sigma)
      end }
      end
  | TacAssert (b,t,ipat,c) ->
      Proofview.Goal.enter { enter = begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = project gl in
        let (sigma,c) = 
          (if Option.is_empty t then interp_constr else interp_type) ist env sigma c
        in
        let sigma, ipat' = interp_intro_pattern_option ist env sigma ipat in
        let tac = Option.map (Option.map (interp_tactic ist)) t in
        Tacticals.New.tclWITHHOLES false
        (name_atomic ~env
          (TacAssert(b,Option.map (Option.map ignore) t,ipat,c))
          (Tactics.forward b tac ipat' c)) sigma
      end }
  | TacGeneralize cl ->
      Proofview.Goal.enter { enter = begin fun gl ->
        let sigma = project gl in
        let env = Proofview.Goal.env gl in
        let sigma, cl = interp_constr_with_occurrences_and_name_as_list ist env sigma cl in
        Tacticals.New.tclWITHHOLES false
        (name_atomic ~env
          (TacGeneralize cl)
          (Tactics.generalize_gen cl)) sigma
      end }
  | TacLetTac (na,c,clp,b,eqpat) ->
      Proofview.V82.nf_evar_goals <*>
      Proofview.Goal.nf_enter { enter = begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = project gl in
        let clp = interp_clause ist env sigma clp in
        let eqpat = interp_intro_pattern_naming_option ist env sigma eqpat in
        if Locusops.is_nowhere clp then
        (* We try to fully-typecheck the term *)
          let (sigma,c_interp) = interp_constr ist env sigma c in
          let let_tac b na c cl eqpat =
            let id = Option.default (Loc.ghost,IntroAnonymous) eqpat in
            let with_eq = if b then None else Some (true,id) in
            Tactics.letin_tac with_eq na c None cl
          in
          let na = interp_name ist env sigma na in
          Tacticals.New.tclWITHHOLES false
          (name_atomic ~env
            (TacLetTac(na,c_interp,clp,b,eqpat))
            (let_tac b na c_interp clp eqpat)) sigma
        else
        (* We try to keep the pattern structure as much as possible *)
          let let_pat_tac b na c cl eqpat =
            let id = Option.default (Loc.ghost,IntroAnonymous) eqpat in
            let with_eq = if b then None else Some (true,id) in
            Tactics.letin_pat_tac with_eq na c cl
          in
          let (sigma',c) = interp_pure_open_constr ist env sigma c in
          name_atomic ~env
            (TacLetTac(na,c,clp,b,eqpat))
	    (Tacticals.New.tclWITHHOLES false (*in hope of a future "eset/epose"*)
               (let_pat_tac b (interp_name ist env sigma na)
                  ((sigma,sigma'),c) clp eqpat) sigma')
      end }

  (* Derived basic tactics *)
  | TacInductionDestruct (isrec,ev,(l,el)) ->
      (* spiwack: some unknown part of destruct needs the goal to be
         prenormalised. *)
      Proofview.V82.nf_evar_goals <*>
      Proofview.Goal.nf_s_enter { s_enter = begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = project gl in
        let sigma,l =
          List.fold_map begin fun sigma (c,(ipato,ipats),cls) ->
            (* TODO: move sigma as a side-effect *)
             (* spiwack: the [*p] variants are for printing *)
            let cp = c in
            let c = interp_destruction_arg ist gl c in
            let ipato = interp_intro_pattern_naming_option ist env sigma ipato in
            let ipatsp = ipats in
            let sigma,ipats = interp_or_and_intro_pattern_option ist env sigma ipats in
            let cls = Option.map (interp_clause ist env sigma) cls in
            sigma,((c,(ipato,ipats),cls),(cp,(ipato,ipatsp),cls))
          end sigma l
        in
        let l,lp = List.split l in
        let sigma,el =
          Option.fold_map (interp_constr_with_bindings ist env) sigma el in
        let tac = name_atomic ~env
          (TacInductionDestruct(isrec,ev,(lp,el)))
            (Tactics.induction_destruct isrec ev (l,el))
        in
        Sigma.Unsafe.of_pair (tac, sigma)
      end }

  (* Conversion *)
  | TacReduce (r,cl) ->
      Proofview.Goal.nf_s_enter { s_enter = begin fun gl ->
        let (sigma,r_interp) = interp_red_expr ist (pf_env gl) (project gl) r in
        Sigma.Unsafe.of_pair (Tactics.reduce r_interp (interp_clause ist (pf_env gl) (project gl) cl), sigma)
      end }
  | TacChange (None,c,cl) ->
      (* spiwack: until the tactic is in the monad *)
      Proofview.Trace.name_tactic (fun () -> Pp.str"<change>") begin
      Proofview.V82.nf_evar_goals <*>
      Proofview.Goal.nf_enter { enter = begin fun gl ->
        let is_onhyps = match cl.onhyps with
          | None | Some [] -> true
          | _ -> false
        in
        let is_onconcl = match cl.concl_occs with
          | AllOccurrences | NoOccurrences -> true
          | _ -> false
        in
        let c_interp patvars = { Sigma.run = begin fun sigma ->
	  let lfun' = Id.Map.fold (fun id c lfun ->
	    Id.Map.add id (Value.of_constr c) lfun) 
	    patvars ist.lfun
	  in
	  let sigma = Sigma.to_evar_map sigma in
	  let ist = { ist with lfun = lfun' } in
	  let (sigma, c) =
            if is_onhyps && is_onconcl
            then interp_type ist (pf_env gl) sigma c
            else interp_constr ist (pf_env gl) sigma c
          in
          Sigma.Unsafe.of_pair (c, sigma)
        end } in
        Tactics.change None c_interp (interp_clause ist (pf_env gl) (project gl) cl)
      end }
      end
  | TacChange (Some op,c,cl) ->
      (* spiwack: until the tactic is in the monad *)
      Proofview.Trace.name_tactic (fun () -> Pp.str"<change>") begin
      Proofview.V82.nf_evar_goals <*>
      Proofview.Goal.enter { enter = begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = project gl in
        let op = interp_typed_pattern ist env sigma op in
        let to_catch = function Not_found -> true | e -> CErrors.is_anomaly e in
        let c_interp patvars = { Sigma.run = begin fun sigma ->
          let lfun' = Id.Map.fold (fun id c lfun ->
            Id.Map.add id (Value.of_constr c) lfun) 
            patvars ist.lfun
          in
          let ist = { ist with lfun = lfun' } in
            try
              let sigma = Sigma.to_evar_map sigma in
              let (sigma, c) = interp_constr ist env sigma c in
              Sigma.Unsafe.of_pair (c, sigma)
            with e when to_catch e (* Hack *) ->
              user_err  (strbrk "Failed to get enough information from the left-hand side to type the right-hand side.")
        end } in
        Tactics.change (Some op) c_interp (interp_clause ist env sigma cl)
      end }
      end


  (* Equality and inversion *)
  | TacRewrite (ev,l,cl,by) ->
      Proofview.Goal.enter { enter = begin fun gl ->
        let l' = List.map (fun (b,m,(keep,c)) ->
          let f = { delayed = fun env sigma ->
            let sigma = Sigma.to_evar_map sigma in
            let (sigma, c) = interp_open_constr_with_bindings ist env sigma c in
            Sigma.Unsafe.of_pair (c, sigma)
          } in
	  (b,m,keep,f)) l in
        let env = Proofview.Goal.env gl in
        let sigma = project gl in
        let cl = interp_clause ist env sigma cl in
        name_atomic ~env
          (TacRewrite (ev,l,cl,Option.map ignore by))
          (Equality.general_multi_rewrite ev l' cl
             (Option.map (fun by -> Tacticals.New.tclCOMPLETE (interp_tactic ist by),
               Equality.Naive)
                by))
      end }
  | TacInversion (DepInversion (k,c,ids),hyp) ->
      Proofview.Goal.nf_enter { enter = begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = project gl in
        let (sigma,c_interp) =
          match c with
          | None -> sigma , None
          | Some c ->
              let (sigma,c_interp) = interp_constr ist env sigma c in
              sigma , Some c_interp
        in
        let dqhyps = interp_declared_or_quantified_hypothesis ist env sigma hyp in
        let sigma,ids_interp = interp_or_and_intro_pattern_option ist env sigma ids in
        Tacticals.New.tclWITHHOLES false
        (name_atomic ~env
          (TacInversion(DepInversion(k,c_interp,ids),dqhyps))
          (Inv.dinv k c_interp ids_interp dqhyps)) sigma
      end }
  | TacInversion (NonDepInversion (k,idl,ids),hyp) ->
      Proofview.Goal.enter { enter = begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = project gl in
        let hyps = interp_hyp_list ist env sigma idl in
        let dqhyps = interp_declared_or_quantified_hypothesis ist env sigma hyp in
        let sigma, ids_interp = interp_or_and_intro_pattern_option ist env sigma ids in
        Tacticals.New.tclWITHHOLES false
        (name_atomic ~env
          (TacInversion (NonDepInversion (k,hyps,ids),dqhyps))
          (Inv.inv_clause k ids_interp hyps dqhyps)) sigma
      end }
  | TacInversion (InversionUsing (c,idl),hyp) ->
      Proofview.Goal.s_enter { s_enter = begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = project gl in
        let (sigma,c_interp) = interp_constr ist env sigma c in
        let dqhyps = interp_declared_or_quantified_hypothesis ist env sigma hyp in
        let hyps = interp_hyp_list ist env sigma idl in
        let tac = name_atomic ~env
          (TacInversion (InversionUsing (c_interp,hyps),dqhyps))
          (Leminv.lemInv_clause dqhyps c_interp hyps)
        in
        Sigma.Unsafe.of_pair (tac, sigma)
      end }

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
  Proofview.Goal.enter { enter = begin fun gl ->
  let env = Proofview.Goal.env gl in
  let extra = TacStore.set TacStore.empty f_debug debug in
  let extra = TacStore.set extra f_avoid_ids avoid_ids in
  let ist = { lfun = lfun; extra = extra } in
  let ltacvars = Id.Map.domain lfun in
  interp_tactic ist
    (intern_pure_tactic {
      ltacvars; genv = env } t)
  end }

let interp t = interp_tac_gen Id.Map.empty [] (get_debug()) t

(* Used to hide interpretation for pretty-print, now just launch tactics *)
(* [global] means that [t] should be internalized outside of goals. *)
let hide_interp global t ot =
  let hide_interp env =
    let ist = { ltacvars = Id.Set.empty; genv = env } in
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
    Proofview.Goal.enter { enter = begin fun gl ->
      hide_interp (Proofview.Goal.env gl)
    end }

(***************************************************************************)
(** Register standard arguments *)

let register_interp0 wit f =
  let open Ftactic.Notations in
  let interp ist v =
    f ist v >>= fun v -> Ftactic.return (Val.inject (val_tag wit) v)
  in
  Geninterp.register_interp0 wit interp

let def_intern ist x = (ist, x)
let def_subst _ x = x
let def_interp ist x = Ftactic.return x

let declare_uniform t =
  Genintern.register_intern0 t def_intern;
  Genintern.register_subst0 t def_subst;
  register_interp0 t def_interp

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

let lift f = (); fun ist x -> Ftactic.enter { enter = begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Sigma.to_evar_map (Proofview.Goal.sigma gl) in
  Ftactic.return (f ist env sigma x)
end }

let lifts f = (); fun ist x -> Ftactic.nf_s_enter { s_enter = begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Sigma.to_evar_map (Proofview.Goal.sigma gl) in
  let (sigma, v) = f ist env sigma x in
  Sigma.Unsafe.of_pair (Ftactic.return v, sigma)
end }

let interp_bindings' ist bl = Ftactic.return { delayed = fun env sigma ->
  let (sigma, bl) = interp_bindings ist env (Sigma.to_evar_map sigma) bl in
  Sigma.Unsafe.of_pair (bl, sigma)
  }

let interp_constr_with_bindings' ist c = Ftactic.return { delayed = fun env sigma ->
  let (sigma, c) = interp_constr_with_bindings ist env (Sigma.to_evar_map sigma) c in
  Sigma.Unsafe.of_pair (c, sigma)
  }

let interp_destruction_arg' ist c = Ftactic.nf_enter { enter = begin fun gl ->
  Ftactic.return (interp_destruction_arg ist gl c)
end }

let () =
  register_interp0 wit_int_or_var (fun ist n -> Ftactic.return (interp_int_or_var ist n));
  register_interp0 wit_ref (lift interp_reference);
  register_interp0 wit_ident (lift interp_ident);
  register_interp0 wit_var (lift interp_hyp);
  register_interp0 wit_intro_pattern (lifts interp_intro_pattern);
  register_interp0 wit_clause_dft_concl (lift interp_clause);
  register_interp0 wit_constr (lifts interp_constr);
  register_interp0 wit_tacvalue (fun ist v -> Ftactic.return v);
  register_interp0 wit_red_expr (lifts interp_red_expr);
  register_interp0 wit_quant_hyp (lift interp_declared_or_quantified_hypothesis);
  register_interp0 wit_open_constr (lifts interp_open_constr);
  register_interp0 wit_bindings interp_bindings';
  register_interp0 wit_constr_with_bindings interp_constr_with_bindings';
  register_interp0 wit_destruction_arg interp_destruction_arg';
  ()

let () =
  let interp ist tac = Ftactic.return (Value.of_closure ist tac) in
  register_interp0 wit_tactic interp

let () =
  let interp ist tac = interp_tactic ist tac >>= fun () -> Ftactic.return () in
  register_interp0 wit_ltac interp

let () =
  register_interp0 wit_uconstr (fun ist c -> Ftactic.nf_enter { enter = begin fun gl ->
    Ftactic.return (interp_uconstr ist (Proofview.Goal.env gl) c)
  end })

(***************************************************************************)
(* Other entry points *)

let val_interp ist tac k = Ftactic.run (val_interp ist tac) k

let interp_ltac_constr ist c k = Ftactic.run (interp_ltac_constr ist c) k

let interp_redexp env sigma r =
  let ist = default_ist () in
  let gist = { fully_empty_glob_sign with genv = env; } in
  interp_red_expr ist env sigma (intern_red_expr gist r)

(***************************************************************************)
(* Backwarding recursive needs of tactic glob/interp/eval functions *)

let _ =
  let eval ty env sigma lfun arg =
    let ist = { lfun = lfun; extra = TacStore.empty; } in
    if Genarg.has_type arg (glbwit wit_tactic) then
      let tac = Genarg.out_gen (glbwit wit_tactic) arg in
      let tac = interp_tactic ist tac in
      Pfedit.refine_by_tactic env sigma ty tac
    else
      failwith "not a tactic"
  in
  Hook.set Pretyping.genarg_interp_hook eval

(** Used in tactic extension **)

let dummy_id = Id.of_string "_"

let lift_constr_tac_to_ml_tac vars tac =
  let tac _ ist = Proofview.Goal.enter { enter = begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = project gl in
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
  end } in
  tac

let vernac_debug b =
  set_debug (if b then Tactic_debug.DebugOn 0 else Tactic_debug.DebugOff)

let _ =
  let open Goptions in
  declare_bool_option
    { optsync  = false;
      optdepr  = false;
      optname  = "Ltac debug";
      optkey   = ["Ltac";"Debug"];
      optread  = (fun () -> get_debug () != Tactic_debug.DebugOff);
      optwrite = vernac_debug }

let _ =
  let open Goptions in
  declare_bool_option
    { optsync  = false;
      optdepr  = false;
      optname  = "Ltac debug";
      optkey   = ["Debug";"Ltac"];
      optread  = (fun () -> get_debug () != Tactic_debug.DebugOff);
      optwrite = vernac_debug }

let () = Hook.set Vernacentries.interp_redexp_hook interp_redexp
