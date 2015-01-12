(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

let whd_cbn flags env sigma t =
  let (state,_) =
    (whd_state_gen true flags env sigma (t,Reductionops.Stack.empty))
  in Reductionops.Stack.zip ~refold:true state

let strong_cbn flags =
  strong (whd_cbn flags)

let simplIsCbn = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optsync = true; Goptions.optdepr = false;
  Goptions.optname =
    "Plug the simpl tactic to the new cbn mechanism";
  Goptions.optkey = ["SimplIsCbn"];
  Goptions.optread = (fun () -> !simplIsCbn);
  Goptions.optwrite = (fun a -> simplIsCbn:=a);
}

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

let e_red f env evm c = evm, f env evm c

let head_style = false (* Turn to true to have a semantics where simpl
   only reduce at the head when an evaluable reference is given, e.g.
   2+n would just reduce to S(1+n) instead of S(S(n)) *)

let contextualize f g = function
  | Some (occs,c) ->
      let l = Locusops.occurrences_map (List.map out_arg) occs in
      let b,c,h = match c with
        | Inl r -> true,PRef (global_of_evaluable_reference r),f
        | Inr c -> false,c,f in
      e_red (contextually b (l,c) (fun _ -> h))
  | None -> e_red g

let reduction_of_red_expr env =
  let make_flag = make_flag env in
  let rec reduction_of_red_expr = function
  | Red internal ->
      if internal then (e_red try_red_product,DEFAULTcast)
      else (e_red red_product,DEFAULTcast)
  | Hnf -> (e_red hnf_constr,DEFAULTcast)
  | Simpl (f,o) ->
     let whd_am = if !simplIsCbn then whd_cbn (make_flag f) else whd_simpl in
     let am = if !simplIsCbn then strong_cbn (make_flag f) else simpl in
     let () =
       if not (!simplIsCbn || List.is_empty f.rConst) then
	 Pp.msg_warning (Pp.strbrk "The legacy simpl does not deal with delta flags.") in
     (contextualize (if head_style then whd_am else am) am o,DEFAULTcast)
  | Cbv f -> (e_red (cbv_norm_flags (make_flag f)),DEFAULTcast)
  | Cbn f ->
     (e_red (strong_cbn (make_flag f)), DEFAULTcast)
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
  | CbvVm o -> (contextualize cbv_vm cbv_vm o, VMcast)
  | CbvNative o -> (contextualize cbv_native cbv_native o, VMcast)
  in
    reduction_of_red_expr

let subst_red_expr subs =
  Miscops.map_red_expr_gen
    (Mod_subst.subst_mps subs)
    (Mod_subst.subst_evaluable_reference subs)
    (Patternops.subst_pattern subs)

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
