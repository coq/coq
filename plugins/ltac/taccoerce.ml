(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Constr
open EConstr
open Namegen
open Tactypes
open Genarg
open Stdarg
open Tacarg
open Geninterp
open Pp

exception CannotCoerceTo of string

let base_val_typ wit =
  match val_tag (topwit wit) with Val.Base t -> t | _ -> CErrors.anomaly (Pp.str "Not a base val.")

let (wit_constr_context : (Empty.t, Empty.t, EConstr.constr) Genarg.genarg_type) =
  let wit = Genarg.create_arg "constr_context" in
  let () = register_val0 wit None in
  let () = Genprint.register_val_print0 (base_val_typ wit)
    (Pptactic.make_constr_printer Printer.pr_econstr_n_env) in
  wit

(* includes idents known to be bound and references *)
let (wit_constr_under_binders : (Empty.t, Empty.t, Ltac_pretype.constr_under_binders) Genarg.genarg_type) =
  let wit = Genarg.create_arg "constr_under_binders" in
  let () = register_val0 wit None in
  let () = Genprint.register_val_print0 (base_val_typ wit)
             (fun c ->
               Genprint.TopPrinterNeedsContext (fun env sigma -> Printer.pr_constr_under_binders_env env sigma c)) in
  wit

(** All the types considered here are base types *)
let val_tag wit = match val_tag wit with
| Val.Base t -> t
| _ -> assert false

let has_type : type a. Val.t -> a typed_abstract_argument_type -> bool = fun v wit ->
  let Val.Dyn (t, _) = v in
  match Val.eq t (val_tag wit) with
  | None -> false
  | Some Refl -> true

let prj : type a. a Val.typ -> Val.t -> a option = fun t v ->
  let Val.Dyn (t', x) = v in
  match Val.eq t t' with
  | None -> None
  | Some Refl -> Some x

let in_gen wit v = Val.Dyn (val_tag wit, v)
let out_gen wit v = match prj (val_tag wit) v with None -> assert false | Some x -> x

module Value =
struct

type t = Val.t

let of_constr c = in_gen (topwit wit_constr) c

let to_constr v =
  if has_type v (topwit wit_constr) then
    let c = out_gen (topwit wit_constr) v in
    Some c
  else if has_type v (topwit wit_constr_under_binders) then
    let vars, c = out_gen (topwit wit_constr_under_binders) v in
    match vars with [] -> Some c | _ -> None
  else None

let of_uconstr c = in_gen (topwit wit_uconstr) c

let to_uconstr v =
  if has_type v (topwit wit_uconstr) then
    Some (out_gen (topwit wit_uconstr) v)
  else None

let of_int i = in_gen (topwit wit_int) i

let to_int v =
  if has_type v (topwit wit_int) then
    Some (out_gen (topwit wit_int) v)
  else None

let to_list v = prj Val.typ_list v

let to_option v = prj Val.typ_opt v

let to_pair v = prj Val.typ_pair v

let cast_error wit v =
  let pr_v = Pptactic.pr_value Pptactic.ltop v in
  let Val.Dyn (tag, _) = v in
  let tag = Val.pr tag in
  CErrors.user_err (str "Type error: value " ++ pr_v ++ str " is a " ++ tag
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
| ExtraArg _ -> Geninterp.val_tag (topwit wit)
| ListArg t -> Val.List (tag_of_arg t)
| OptArg t -> Val.Opt (tag_of_arg t)
| PairArg (t1, t2) -> Val.Pair (tag_of_arg t1, tag_of_arg t2)

let val_cast arg v = prj (tag_of_arg arg) v

let cast (Topwit wit) v = val_cast wit v

end

let is_variable env id =
  Id.List.mem id (Termops.ids_of_named_context (Environ.named_context env))

(* Transforms an id into a constr if possible, or fails with Not_found *)
let constr_of_id env id =
  EConstr.mkVar (let _ = Environ.lookup_named id env in id)

(* Gives the constr corresponding to a Constr_context tactic_arg *)
let coerce_to_constr_context v =
  if has_type v (topwit wit_constr_context) then
    out_gen (topwit wit_constr_context) v
  else raise (CannotCoerceTo "a term context")

(* Interprets an identifier which must be fresh *)
let coerce_var_to_ident fresh env sigma v =
  let fail () = raise (CannotCoerceTo "a fresh identifier") in
  if has_type v (topwit wit_intro_pattern) then
    match out_gen (topwit wit_intro_pattern) v with
    | { CAst.v=IntroNaming (IntroIdentifier id)} -> id
    | _ -> fail ()
  else if has_type v (topwit wit_var) then
    out_gen (topwit wit_var) v
  else match Value.to_constr v with
  | None -> fail ()
  | Some c ->
    (* We need it fresh for intro e.g. in "Tac H = clear H; intro H" *)
    if isVar sigma c && not (fresh && is_variable env (destVar sigma c)) then
      destVar sigma c
    else fail ()


(* Interprets, if possible, a constr to an identifier which may not
   be fresh but suitable to be given to the fresh tactic. Works for
   vars, constants, inductive, constructors and sorts. *)
let coerce_to_ident_not_fresh sigma v =
let id_of_name = function
  | Name.Anonymous -> Id.of_string "x"
  | Name.Name x -> x in
  let fail () = raise (CannotCoerceTo "an identifier") in
  if has_type v (topwit wit_intro_pattern) then
    match out_gen (topwit wit_intro_pattern) v with
    | {CAst.v=IntroNaming (IntroIdentifier id)} -> id
    | _ -> fail ()
  else if has_type v (topwit wit_var) then
    out_gen (topwit wit_var) v
  else
    match Value.to_constr v with
    | None -> fail ()
    | Some c ->
       match EConstr.kind sigma c with
       | Var id -> id 
       | Meta m -> id_of_name (Evd.meta_name sigma m)
       | Evar (kn,_) ->
        begin match Evd.evar_ident kn sigma with
        | None -> fail ()
        | Some id -> id
        end
       | Const (cst,_) -> Label.to_id (Constant.label cst)
       | Construct (cstr,_) ->
	  let ref = Globnames.ConstructRef cstr in
	  let basename = Nametab.basename_of_global ref in
	  basename
       | Ind (ind,_) ->
	  let ref = Globnames.IndRef ind in
	  let basename = Nametab.basename_of_global ref in
	  basename
       | Sort s ->
          begin
	    match ESorts.kind sigma s with
            | Sorts.Prop -> Label.to_id (Label.make "Prop")
            | Sorts.Set -> Label.to_id (Label.make "Set")
            | Sorts.Type _ -> Label.to_id (Label.make "Type")
          end
       | _ -> fail()


let coerce_to_intro_pattern sigma v =
  if has_type v (topwit wit_intro_pattern) then
    (out_gen (topwit wit_intro_pattern) v).CAst.v
  else if has_type v (topwit wit_var) then
    let id = out_gen (topwit wit_var) v in
    IntroNaming (IntroIdentifier id)
  else match Value.to_constr v with
  | Some c when isVar sigma c ->
      (* This happens e.g. in definitions like "Tac H = clear H; intro H" *)
      (* but also in "destruct H as (H,H')" *)
      IntroNaming (IntroIdentifier (destVar sigma c))
  | _ -> raise (CannotCoerceTo "an introduction pattern")

let coerce_to_intro_pattern_naming sigma v =
  match coerce_to_intro_pattern sigma v with
  | IntroNaming pat -> pat
  | _ -> raise (CannotCoerceTo "a naming introduction pattern")

let coerce_to_hint_base v =
  if has_type v (topwit wit_intro_pattern) then
    match out_gen (topwit wit_intro_pattern) v with
    | {CAst.v=IntroNaming (IntroIdentifier id)} -> Id.to_string id
    | _ -> raise (CannotCoerceTo "a hint base name")
  else raise (CannotCoerceTo "a hint base name")

let coerce_to_int v =
  if has_type v (topwit wit_int) then
    out_gen (topwit wit_int) v
  else raise (CannotCoerceTo "an integer")

let coerce_to_constr env v =
  let fail () = raise (CannotCoerceTo "a term") in
  if has_type v (topwit wit_intro_pattern) then
    match out_gen (topwit wit_intro_pattern) v with
    | {CAst.v=IntroNaming (IntroIdentifier id)} ->
      (try ([], constr_of_id env id) with Not_found -> fail ())
    | _ -> fail ()
  else if has_type v (topwit wit_constr) then
    let c = out_gen (topwit wit_constr) v in
    ([], c)
  else if has_type v (topwit wit_constr_under_binders) then
    out_gen (topwit wit_constr_under_binders) v
  else if has_type v (topwit wit_var) then
    let id = out_gen (topwit wit_var) v in
    (try [], constr_of_id env id with Not_found -> fail ())
  else fail ()

let coerce_to_uconstr v =
  if has_type v (topwit wit_uconstr) then
    out_gen (topwit wit_uconstr) v
  else
    raise (CannotCoerceTo "an untyped term")

let coerce_to_closed_constr env v =
  let ids,c = coerce_to_constr env v in
  let () = if not (List.is_empty ids) then raise (CannotCoerceTo "a term") in
  c

let coerce_to_evaluable_ref env sigma v =
  let fail () = raise (CannotCoerceTo "an evaluable reference") in
  let ev =
  if has_type v (topwit wit_intro_pattern) then
    match out_gen (topwit wit_intro_pattern) v with
    | {CAst.v=IntroNaming (IntroIdentifier id)} when is_variable env id -> EvalVarRef id
    | _ -> fail ()
  else if has_type v (topwit wit_var) then
    let id = out_gen (topwit wit_var) v in
    if Id.List.mem id (Termops.ids_of_context env) then EvalVarRef id
    else fail ()
  else if has_type v (topwit wit_ref) then
    let open Globnames in
    let r = out_gen (topwit wit_ref) v in
    match r with
    | VarRef var -> EvalVarRef var
    | ConstRef c -> EvalConstRef c
    | IndRef _ | ConstructRef _ -> fail ()
  else
    match Value.to_constr v with
    | Some c when isConst sigma c -> EvalConstRef (fst (destConst sigma c))
    | Some c when isVar sigma c -> EvalVarRef (destVar sigma c)
    | _ -> fail ()
  in if Tacred.is_evaluable env ev then ev else fail ()

let coerce_to_constr_list env v =
  let v = Value.to_list v in
  match v with
  | Some l ->
    let map v = coerce_to_closed_constr env v in
    List.map map l
  | None -> raise (CannotCoerceTo "a term list")

let coerce_to_intro_pattern_list ?loc sigma v =
  match Value.to_list v with
  | None -> raise (CannotCoerceTo "an intro pattern list")
  | Some l ->
    let map v = CAst.make ?loc @@ coerce_to_intro_pattern sigma v in
    List.map map l

let coerce_to_hyp env sigma v =
  let fail () = raise (CannotCoerceTo "a variable") in
  if has_type v (topwit wit_intro_pattern) then
    match out_gen (topwit wit_intro_pattern) v with
    | {CAst.v=IntroNaming (IntroIdentifier id)} when is_variable env id -> id
    | _ -> fail ()
  else if has_type v (topwit wit_var) then
    let id = out_gen (topwit wit_var) v in
    if is_variable env id then id else fail ()
  else match Value.to_constr v with
  | Some c when isVar sigma c -> destVar sigma c
  | _ -> fail ()

let coerce_to_hyp_list env sigma v =
  let v = Value.to_list v in
  match v with
  | Some l ->
    let map n = coerce_to_hyp env sigma n in
    List.map map l
  | None -> raise (CannotCoerceTo "a variable list")

(* Interprets a qualified name *)
let coerce_to_reference sigma v =
  match Value.to_constr v with
  | Some c ->
    begin
      try fst (Termops.global_of_constr sigma c)
      with Not_found -> raise (CannotCoerceTo "a reference")
    end
  | None -> raise (CannotCoerceTo "a reference")

(* Quantified named or numbered hypothesis or hypothesis in context *)
(* (as in Inversion) *)
let coerce_to_quantified_hypothesis sigma v =
  if has_type v (topwit wit_intro_pattern) then
    let v = out_gen (topwit wit_intro_pattern) v in
    match v with
    | {CAst.v=IntroNaming (IntroIdentifier id)} -> NamedHyp id
    | _ -> raise (CannotCoerceTo "a quantified hypothesis")
  else if has_type v (topwit wit_var) then
    let id = out_gen (topwit wit_var) v in
    NamedHyp id
  else if has_type v (topwit wit_int) then
    AnonHyp (out_gen (topwit wit_int) v)
  else match Value.to_constr v with
  | Some c when isVar sigma c -> NamedHyp (destVar sigma c)
  | _ -> raise (CannotCoerceTo "a quantified hypothesis")

(* Quantified named or numbered hypothesis or hypothesis in context *)
(* (as in Inversion) *)
let coerce_to_decl_or_quant_hyp sigma v =
  if has_type v (topwit wit_int) then
    AnonHyp (out_gen (topwit wit_int) v)
  else
    try coerce_to_quantified_hypothesis sigma v
    with CannotCoerceTo _ ->
      raise (CannotCoerceTo "a declared or quantified hypothesis")

let coerce_to_int_or_var_list v =
  match Value.to_list v with
  | None -> raise (CannotCoerceTo "an int list")
  | Some l ->
    let map n = Locus.ArgArg (coerce_to_int n) in
    List.map map l

(** Abstract application, to print ltac functions *)
type appl =
  | UnnamedAppl (** For generic applications: nothing is printed *)
  | GlbAppl of (Names.KerName.t * Val.t list) list
       (** For calls to global constants, some may alias other. *)

(* Values for interpretation *)
type tacvalue =
  | VFun of appl*Tacexpr.ltac_trace * Val.t Id.Map.t *
      Name.t list * Tacexpr.glob_tactic_expr
  | VRec of Val.t Id.Map.t ref * Tacexpr.glob_tactic_expr

let (wit_tacvalue : (Empty.t, tacvalue, tacvalue) Genarg.genarg_type) =
  let wit = Genarg.create_arg "tacvalue" in
  let () = register_val0 wit None in
  let () = Genprint.register_val_print0 (base_val_typ wit)
             (fun _ -> Genprint.TopPrinterBasic (fun () -> str "<tactic closure>")) in
  wit

let pr_argument_type arg =
  let Val.Dyn (tag, _) = arg in
  Val.pr tag

(** TODO: unify printing of generic Ltac values in case of coercion failure. *)

(* Displays a value *)
let pr_value env v =
  let pr_with_env pr =
    match env with
    | Some (env,sigma) -> pr env sigma
    | None -> str "a value of type" ++ spc () ++ pr_argument_type v in
  let open Genprint in
  match generic_val_print v with
  | TopPrinterBasic pr -> pr ()
  | TopPrinterNeedsContext pr -> pr_with_env pr
  | TopPrinterNeedsContextAndLevel { default_already_surrounded; printer } ->
     pr_with_env (fun env sigma -> printer env sigma default_already_surrounded)

let error_ltac_variable ?loc id env v s =
   CErrors.user_err ?loc  (str "Ltac variable " ++ Id.print id ++
   strbrk " is bound to" ++ spc () ++ pr_value env v ++ spc () ++
   strbrk "which cannot be coerced to " ++ str s ++ str".")
