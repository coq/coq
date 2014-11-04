(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Term
open Declarations
open Globnames
open Genredexpr
open Pattern
open Reductionops
open Tacred
open Closure
open RedFlags
open Libobject
open Misctypes

(* call by value normalisation function using the virtual machine *)
let cbv_vm env sigma c =
  let ctyp = Retyping.get_type_of env sigma c in
  if Termops.occur_meta_or_existential c then
    error "vm_compute does not support existential variables.";
  Vnorm.cbv_vm env c ctyp

let cbv_native env sigma c =
  let ctyp = Retyping.get_type_of env sigma c in
  let evars = Nativenorm.evars_of_evar_map sigma in
  Nativenorm.native_norm env evars c ctyp

let set_strategy_one ref l  =
  let k =
    match ref with
      | EvalConstRef sp -> ConstKey sp
      | EvalVarRef id -> VarKey id in
  Global.set_strategy k l;
  match k,l with
      ConstKey sp, Conv_oracle.Opaque ->
        Csymtable.set_opaque_const sp
    | ConstKey sp, _ ->
        let cb = Global.lookup_constant sp in
	(match cb.const_body with
	  | OpaqueDef _ ->
            errorlabstrm "set_transparent_const"
              (str "Cannot make" ++ spc () ++
		 Nametab.pr_global_env Id.Set.empty (ConstRef sp) ++
		 spc () ++ str "transparent because it was declared opaque.");
	  | _ -> Csymtable.set_transparent_const sp)
    | _ -> ()

let cache_strategy (_,str) =
  List.iter
    (fun (lev,ql) -> List.iter (fun q -> set_strategy_one q lev) ql)
    str

let subst_strategy (subs,(local,obj)) =
  local,
  List.smartmap
    (fun (k,ql as entry) ->
      let ql' = List.smartmap (Mod_subst.subst_evaluable_reference subs) ql in
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

let classify_strategy (local,_ as obj) =
  if local then Dispose else Substitute obj

let disch_ref ref =
  match ref with
      EvalConstRef c ->
        let c' = Lib.discharge_con c in
        if c==c' then Some ref else Some (EvalConstRef c')
    | EvalVarRef id -> if Lib.is_in_section (VarRef id) then None else Some ref

let discharge_strategy (_,(local,obj)) =
  if local then None else
  map_strategy disch_ref obj

type strategy_obj =
    bool * (Conv_oracle.level * evaluable_global_reference list) list

let inStrategy : strategy_obj -> obj =
  declare_object {(default_object "STRATEGY") with
                    cache_function = (fun (_,obj) -> cache_strategy obj);
		    load_function = (fun _ (_,obj) -> cache_strategy obj);
		    subst_function = subst_strategy;
                    discharge_function = discharge_strategy;
		    classify_function = classify_strategy }


let set_strategy local str =
  Lib.add_anonymous_leaf (inStrategy (local,str))

(* Generic reduction: reduction functions used in reduction tactics *)

type red_expr =
    (constr, evaluable_global_reference, constr_pattern) red_expr_gen

let make_flag_constant = function
  | EvalVarRef id -> fVAR id
  | EvalConstRef sp -> fCONST sp

let make_flag env f =
  let red = no_red in
  let red = if f.rBeta then red_add red fBETA else red in
  let red = if f.rIota then red_add red fIOTA else red in
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
        let red = red_add_transparent (red_add red fDELTA) all_opaque in
	List.fold_right
	  (fun v red -> red_add red (make_flag_constant v))
	  f.rConst red
  in red

let is_reference = function PRef _ | PVar _ -> true | _ -> false

(* table of custom reductino fonctions, not synchronized,
   filled via ML calls to [declare_reduction] *)
let reduction_tab = ref String.Map.empty

(* table of custom reduction expressions, synchronized,
   filled by command Declare Reduction *)
let red_expr_tab = Summary.ref String.Map.empty ~name:"Declare Reduction"

let declare_reduction s f =
  if String.Map.mem s !reduction_tab || String.Map.mem s !red_expr_tab
  then error ("There is already a reduction expression of name "^s)
  else reduction_tab := String.Map.add s f !reduction_tab

let check_custom = function
  | ExtraRedExpr s ->
      if not (String.Map.mem s !reduction_tab || String.Map.mem s !red_expr_tab)
      then error ("Reference to undefined reduction expression "^s)
  |_ -> ()

let decl_red_expr s e =
  if String.Map.mem s !reduction_tab || String.Map.mem s !red_expr_tab
  then error ("There is already a reduction expression of name "^s)
  else begin
    check_custom e;
    red_expr_tab := String.Map.add s e !red_expr_tab
  end

let out_arg = function
  | ArgVar _ -> anomaly (Pp.str "Unevaluated or_var variable")
  | ArgArg x -> x

let out_with_occurrences (occs,c) =
  (Locusops.occurrences_map (List.map out_arg) occs, c)

let reduction_of_red_expr env =
  let make_flag = make_flag env in
  let e_red f env evm c = evm, f env evm c in
  let rec reduction_of_red_expr = function
  | Red internal ->
      if internal then (e_red try_red_product,DEFAULTcast)
      else (e_red red_product,DEFAULTcast)
  | Hnf -> (e_red hnf_constr,DEFAULTcast)
  | Simpl (Some (_,c as lp)) ->
    let f = contextually (is_reference c) (out_with_occurrences lp)
      (fun _ -> simpl)
    in (e_red f,DEFAULTcast)
  | Simpl None -> (e_red simpl,DEFAULTcast)
  | Cbv f -> (e_red (cbv_norm_flags (make_flag f)),DEFAULTcast)
  | Cbn f ->
    let f = strong (fun env evd x -> Stack.zip ~refold:true
      (fst (whd_state_gen true (make_flag f) env evd (x, Stack.empty)))) in
      (e_red f, DEFAULTcast)
  | Lazy f -> (e_red (clos_norm_flags (make_flag f)),DEFAULTcast)
  | Unfold ubinds -> (e_red (unfoldn (List.map out_with_occurrences ubinds)),DEFAULTcast)
  | Fold cl -> (e_red (fold_commands cl),DEFAULTcast)
  | Pattern lp -> (pattern_occs (List.map out_with_occurrences lp),DEFAULTcast)
  | ExtraRedExpr s ->
      (try (e_red (String.Map.find s !reduction_tab),DEFAULTcast)
      with Not_found ->
	(try reduction_of_red_expr (String.Map.find s !red_expr_tab)
	 with Not_found ->
	   error("unknown user-defined reduction \""^s^"\"")))
  | CbvVm (Some lp) ->
    let b = is_reference (snd lp) in
    let lp = out_with_occurrences lp in
    let vmfun _ env map c =
      let tpe = Retyping.get_type_of env map c in
      Vnorm.cbv_vm env c tpe
    in
    let redfun = contextually b lp vmfun in
    (e_red redfun, VMcast)
  | CbvVm None -> (e_red cbv_vm, VMcast)
  | CbvNative (Some lp) ->
    let b = is_reference (snd lp) in
    let lp = out_with_occurrences lp in
    let nativefun _ env map c =
      let tpe = Retyping.get_type_of env map c in
      let evars = Nativenorm.evars_of_evar_map map in
      Nativenorm.native_norm env evars c tpe
    in
    let redfun = contextually b lp nativefun in
    (e_red redfun, NATIVEcast)
  | CbvNative None -> (e_red cbv_native, NATIVEcast)
  in
    reduction_of_red_expr

let subst_flags subs flags =
  { flags with rConst = List.map subs flags.rConst }

let subst_occs subs (occ,e) = (occ,subs e)

let subst_gen_red_expr subs_a subs_b subs_c = function
  | Fold l -> Fold (List.map subs_a l)
  | Pattern occs_l -> Pattern (List.map (subst_occs subs_a) occs_l)
  | Simpl occs_o -> Simpl (Option.map (subst_occs subs_c) occs_o)
  | Unfold occs_l -> Unfold (List.map (subst_occs subs_b) occs_l)
  | Cbv flags -> Cbv (subst_flags subs_b flags)
  | Lazy flags -> Lazy (subst_flags subs_b flags)
  | e -> e

let subst_red_expr subs e =
  subst_gen_red_expr
    (Mod_subst.subst_mps subs)
    (Mod_subst.subst_evaluable_reference subs)
    (Patternops.subst_pattern subs)
    e

let inReduction : bool * string * red_expr -> obj =
  declare_object
    {(default_object "REDUCTION") with
       cache_function = (fun (_,(_,s,e)) -> decl_red_expr s e);
       load_function = (fun _ (_,(_,s,e)) -> decl_red_expr s e);
       subst_function =
	(fun (subs,(b,s,e)) -> b,s,subst_red_expr subs e);
       classify_function =
	(fun ((b,_,_) as obj) -> if b then Dispose else Substitute obj) }

let declare_red_expr locality s expr =
    Lib.add_anonymous_leaf (inReduction (locality,s,expr))
