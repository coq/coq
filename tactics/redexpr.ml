(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Constr
open EConstr
open Genredexpr
open Pattern
open Reductionops
open Tacred
open RedFlags
open Libobject

let warn_vm_disabled =
  CWarnings.create ~name:"vm-compute-disabled" ~category:CWarnings.CoreCategories.bytecode_compiler
  (fun () ->
   strbrk "vm_compute disabled at configure time; falling back to cbv.")

(* call by value normalisation function using the virtual machine *)
let cbv_vm env sigma c =
  if (Environ.typing_flags env).enable_VM then
    let ctyp = Retyping.get_type_of env sigma c in
    Vnorm.cbv_vm env sigma c ctyp
  else begin
    warn_vm_disabled ();
    compute env sigma c
  end

let warn_native_compute_disabled =
  CWarnings.create_in Nativeconv.w_native_disabled
  (fun () ->
   strbrk "native_compute disabled at configure time; falling back to vm_compute.")

let cbv_native env sigma c =
  if (Environ.typing_flags env).enable_native_compiler then
    let ctyp = Retyping.get_type_of env sigma c in
    Nativenorm.native_norm env sigma c ctyp
  else
    (warn_native_compute_disabled ();
     cbv_vm env sigma c)

let { Goptions.get = simplIsCbn } =
  Goptions.declare_bool_option_and_ref
    ~key:["SimplIsCbn"]
    ~value:false
    ()

let set_strategy_one ref l =
  Global.set_strategy ref l;
  match ref, l with
  | Evaluable.EvalConstRef sp, Conv_oracle.Opaque -> ()
  | Evaluable.EvalConstRef sp, _ ->
    if Declareops.is_opaque (Global.lookup_constant sp) then
      user_err
        (str "Cannot make" ++ spc () ++
            Nametab.pr_global_env Id.Set.empty (GlobRef.ConstRef sp) ++
            spc () ++ str "transparent because it was declared opaque.")
  | _ -> ()

let cache_strategy (_,str) =
  List.iter
    (fun (lev,ql) -> List.iter (fun q -> set_strategy_one q lev) ql)
    str

let subst_strategy (subs,(local,obj)) =
  local,
  List.Smart.map
    (fun (k,ql as entry) ->
      let ql' = List.Smart.map (Tacred.subst_evaluable_reference subs) ql in
      if ql==ql' then entry else (k,ql'))
    obj


let map_strategy f l =
  let l'  = List.fold_right
    (fun (lev,ql) str ->
      let ql' = List.fold_right
        (fun q ql ->
          match f q with
              Some q' -> q' :: ql
            | None -> ql) ql [] in
      if List.is_empty ql' then str else (lev,ql')::str) l [] in
  if List.is_empty l' then None else Some (false,l')

let classify_strategy (local,_) =
  if local then Dispose else Substitute

let disch_ref ref =
  match ref with
  | Evaluable.EvalConstRef c -> Some ref
  | Evaluable.EvalProjectionRef p -> Some ref
  | Evaluable.EvalVarRef id -> if Lib.is_in_section (GlobRef.VarRef id) then None else Some ref

let discharge_strategy (local,obj) =
  if local then None else
  map_strategy disch_ref obj

type strategy_obj = bool * (Conv_oracle.level * Evaluable.t list) list

let inStrategy : strategy_obj -> obj =
  declare_object
    {(default_object "STRATEGY") with
     cache_function = cache_strategy;
     load_function = (fun _ obj -> cache_strategy obj);
     subst_function = subst_strategy;
     discharge_function = discharge_strategy;
     classify_function = classify_strategy;
    }


let set_strategy local str =
  Lib.add_leaf (inStrategy (local,str))

(* Generic reduction: reduction functions used in reduction tactics *)

type red_expr = (constr, Evaluable.t, constr_pattern) red_expr_gen

type red_expr_val =
  (constr, Evaluable.t, constr_pattern, strength * RedFlags.reds) red_expr_gen0

let make_flag_constant = function
  | Evaluable.EvalVarRef id -> fVAR id
  | Evaluable.EvalConstRef sp -> fCONST sp
  | Evaluable.EvalProjectionRef p -> fPROJ p

let make_flag env f =
  let red = no_red in
  let red = if f.rBeta then red_add red fBETA else red in
  let red = if f.rMatch then red_add red fMATCH else red in
  let red = if f.rFix then red_add red fFIX else red in
  let red = if f.rCofix then red_add red fCOFIX else red in
  let red = if f.rZeta then red_add red fZETA else red in
  let red =
    if f.rDelta then (* All but rConst *)
        let red = red_add red fDELTA in
        let red = red_add_transparent red
                    (Conv_oracle.get_transp_state (Environ.oracle env)) in
        List.fold_right
          (fun v red -> red_sub red (make_flag_constant v))
          f.rConst red
    else (* Only rConst *)
        let red = red_add red fDELTA in
        List.fold_right
          (fun v red -> red_add red (make_flag_constant v))
          f.rConst red
  in
  f.rStrength, red

(* table of custom reductino fonctions, not synchronized,
   filled via ML calls to [declare_reduction] *)
let reduction_tab = ref String.Map.empty

(* table of custom reduction expressions, synchronized,
   filled by command Declare Reduction *)
let red_expr_tab = Summary.ref String.Map.empty ~name:"Declare Reduction"

let declare_reduction s f =
  if String.Map.mem s !reduction_tab || String.Map.mem s !red_expr_tab
  then user_err
    (str "There is already a reduction expression of name " ++ str s ++ str ".")
  else reduction_tab := String.Map.add s f !reduction_tab

let check_custom = function
  | ExtraRedExpr s ->
      if not (String.Map.mem s !reduction_tab || String.Map.mem s !red_expr_tab)
      then user_err (str "Reference to undefined reduction expression " ++ str s ++ str ".")
  |_ -> ()

let decl_red_expr s e =
  if String.Map.mem s !reduction_tab || String.Map.mem s !red_expr_tab
  then user_err
    (str "There is already a reduction expression of name " ++ str s ++ str ".")
  else begin
    check_custom e;
    red_expr_tab := String.Map.add s e !red_expr_tab
  end

let out_arg = function
  | Locus.ArgVar _ -> anomaly (Pp.str "Unevaluated or_var variable.")
  | Locus.ArgArg x -> x

let out_occurrences occs =
  let occs = Locusops.occurrences_map (List.map out_arg) occs in
  match occs with
  | Locus.OnlyOccurrences (n::_ as nl) when n < 0 ->
     Locus.AllOccurrencesBut (List.map abs nl)
  | Locus.OnlyOccurrences nl when List.exists (fun n -> n < 0) nl ->
     CErrors.user_err Pp.(str "Illegal negative occurrence number.")
  | Locus.OnlyOccurrences _ | Locus.AllOccurrencesBut _ | Locus.NoOccurrences
  | Locus.AllOccurrences | Locus.AtLeastOneOccurrence -> occs

let out_with_occurrences (occs,c) =
  (out_occurrences occs, c)

let e_red f env evm c = evm, f env evm c

let contextualize f = function
  | Some (occs,c) ->
      let l = out_occurrences occs in
      let b,c = match c with
        | Inl r -> true,PRef (global_of_evaluable_reference r)
        | Inr c -> false,c in
      e_red (contextually b (l,c) (fun _ -> f))
  | None -> e_red f

let warn_simpl_unfolding_modifiers =
  CWarnings.create ~name:"simpl-unfolding-modifiers" ~category:CWarnings.CoreCategories.tactics
         (fun () ->
          Pp.strbrk "The legacy simpl ignores constant unfolding modifiers.")

let rec eval_red_expr env = function
| Simpl (f, o) ->
  let () =
    if not (simplIsCbn () || List.is_empty f.rConst) then
      warn_simpl_unfolding_modifiers () in
  let f = if simplIsCbn () then make_flag env f else f.rStrength, RedFlags.all (* dummy *) in
  Simpl (f, o)
| Cbv f -> Cbv (make_flag env f)
| Cbn f -> Cbn (make_flag env f)
| Lazy f -> Lazy (make_flag env f)
| ExtraRedExpr s ->
  begin match String.Map.find s !red_expr_tab with
  | e -> eval_red_expr env e
  | exception Not_found -> ExtraRedExpr s (* delay to runtime interpretation *)
  end
| (Red | Hnf | Unfold _ | Fold _ | Pattern _ | CbvVm _ | CbvNative _) as e -> e

let red_product_exn env sigma c = match red_product env sigma c with
  | None -> user_err Pp.(str "No head constant to reduce.")
  | Some c -> c

let reduction_of_red_expr_val = function
  | Red -> (e_red red_product_exn, DEFAULTcast)
  | Hnf -> (e_red hnf_constr,DEFAULTcast)
  | Simpl ((w,f),o) ->
    let am = match w, simplIsCbn () with
      | Norm, true -> Cbn.norm_cbn f
      | Norm, false -> simpl
      | Head, true -> Cbn.whd_cbn f
      | Head, false -> whd_simpl
    in
     (contextualize am o,DEFAULTcast)
  | Cbv (Norm, f) -> (e_red (cbv_norm_flags ~strong:true f),DEFAULTcast)
  | Cbv (Head, f) -> (e_red (cbv_norm_flags ~strong:false f),DEFAULTcast)
  | Cbn (w,f) ->
    let cbn = match w with Norm -> Cbn.norm_cbn | Head -> Cbn.whd_cbn in
     (e_red (cbn f), DEFAULTcast)
  | Lazy (w,f) ->
    let redf = match w with Norm -> clos_norm_flags | Head -> clos_whd_flags in
    (e_red (redf f),DEFAULTcast)
  | Unfold ubinds -> (e_red (unfoldn (List.map out_with_occurrences ubinds)),DEFAULTcast)
  | Fold cl -> (e_red (fold_commands cl),DEFAULTcast)
  | Pattern lp -> (pattern_occs (List.map out_with_occurrences lp),DEFAULTcast)
  | ExtraRedExpr s ->
      (try (e_red (String.Map.find s !reduction_tab),DEFAULTcast)
      with Not_found ->
           user_err
             (str "Unknown user-defined reduction \"" ++ str s ++ str "\"."))
  | CbvVm o -> (contextualize cbv_vm o, VMcast)
  | CbvNative o -> (contextualize cbv_native o, NATIVEcast)

let reduction_of_red_expr env r =
  reduction_of_red_expr_val (eval_red_expr env r)

(* Possibly equip a reduction with the occurrences mentioned in an
   occurrence clause *)

let error_illegal_clause () =
  CErrors.user_err Pp.(str "\"at\" clause not supported in presence of an occurrence clause.")

let error_multiple_patterns () =
  CErrors.user_err Pp.(str "\"at\" clause in occurences not supported with multiple patterns or references.")

let error_illegal_non_atomic_clause () =
  CErrors.user_err Pp.(str "\"at\" clause not supported in presence of a non atomic \"in\" clause.")

let error_at_in_occurrences_not_supported () =
  CErrors.user_err Pp.(str "\"at\" clause not supported for this reduction tactic.")

let bind_red_expr_occurrences occs nbcl redexp =
  let open Locus in
  let has_at_clause = function
    | Unfold l -> List.exists (fun (occl,_) -> occl != AllOccurrences) l
    | Pattern l -> List.exists (fun (occl,_) -> occl != AllOccurrences) l
    | Simpl (_,Some (occl,_)) -> occl != AllOccurrences
    | _ -> false in
  if occs == AllOccurrences then
    if nbcl > 1 && has_at_clause redexp then
      error_illegal_non_atomic_clause ()
    else
      redexp
  else
    match redexp with
    | Unfold (_::_::_) ->
        error_multiple_patterns ()
    | Unfold [(occl,c)] ->
        if occl != AllOccurrences then
          error_illegal_clause ()
        else
          Unfold [(occs,c)]
    | Pattern (_::_::_) ->
        error_multiple_patterns ()
    | Pattern [(occl,c)] ->
        if occl != AllOccurrences then
          error_illegal_clause ()
        else
          Pattern [(occs,c)]
    | Simpl (f,Some (occl,c)) ->
        if occl != AllOccurrences then
          error_illegal_clause ()
        else
          Simpl (f,Some (occs,c))
    | CbvVm (Some (occl,c)) ->
        if occl != AllOccurrences then
          error_illegal_clause ()
        else
          CbvVm (Some (occs,c))
    | CbvNative (Some (occl,c)) ->
        if occl != AllOccurrences then
          error_illegal_clause ()
        else
          CbvNative (Some (occs,c))
    | Red | Hnf | Cbv _ | Lazy _ | Cbn _
    | ExtraRedExpr _ | Fold _ | Simpl (_,None) | CbvVm None | CbvNative None ->
        error_at_in_occurrences_not_supported ()
    | Unfold [] | Pattern [] ->
        assert false

let reduction_of_red_expr_val ?occs r =
  let r = match occs with
  | None -> r
  | Some (occs, nbcl) -> bind_red_expr_occurrences occs nbcl r
  in
  reduction_of_red_expr_val r

let subst_mps subst c =
  EConstr.of_constr (Mod_subst.subst_mps subst (EConstr.Unsafe.to_constr c))

let subst_red_expr subs =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Redops.map_red_expr_gen
    (subst_mps subs)
    (Tacred.subst_evaluable_reference subs)
    (Patternops.subst_pattern env sigma subs)

let inReduction : bool * string * red_expr -> obj =
  declare_object
    {(default_object "REDUCTION") with
     cache_function = (fun (_,s,e) -> decl_red_expr s e);
     load_function = (fun _ (_,s,e) -> decl_red_expr s e);
     subst_function =
       (fun (subs,(b,s,e)) -> b,s,subst_red_expr subs e);
     classify_function =
       (fun ((b,_,_)) -> if b then Dispose else Substitute) }

let declare_red_expr locality s expr =
    Lib.add_leaf (inReduction (locality,s,expr))

let make0 ?dyn name =
  let wit = Genarg.make0 name in
  let () = Geninterp.register_val0 wit dyn in
  wit

let wit_red_expr = make0 "redexpr"
