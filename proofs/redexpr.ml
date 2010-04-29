(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Term
open Declarations
open Libnames
open Rawterm
open Pattern
open Reductionops
open Tacred
open Closure
open RedFlags
open Libobject
open Summary

(* call by value normalisation function using the virtual machine *)
let cbv_vm env _ c =
  let ctyp = (fst (Typeops.infer env c)).Environ.uj_type in
  Vnorm.cbv_vm env c ctyp


let set_strategy_one ref l  =
  let k =
    match ref with
      | EvalConstRef sp -> ConstKey sp
      | EvalVarRef id -> VarKey id in
  Conv_oracle.set_strategy k l;
  match k,l with
      ConstKey sp, Conv_oracle.Opaque ->
        Csymtable.set_opaque_const sp
    | ConstKey sp, _ ->
        let cb = Global.lookup_constant sp in
        if cb.const_body <> None & cb.const_opaque then
          errorlabstrm "set_transparent_const"
            (str "Cannot make" ++ spc () ++
            Nametab.pr_global_env Idset.empty (ConstRef sp) ++
            spc () ++ str "transparent because it was declared opaque.");
        Csymtable.set_transparent_const sp
    | _ -> ()

let cache_strategy (_,str) =
  List.iter
    (fun (lev,ql) -> List.iter (fun q -> set_strategy_one q lev) ql)
    str

let subst_strategy (subs,(local,obj)) =
  local,
  list_smartmap
    (fun (k,ql as entry) ->
      let ql' = list_smartmap (Mod_subst.subst_evaluable_reference subs) ql in
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
      if ql'=[] then str else (lev,ql')::str) l [] in
  if l'=[] then None else Some (false,l')

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

let (inStrategy,outStrategy) =
  declare_object {(default_object "STRATEGY") with
                    cache_function = (fun (_,obj) -> cache_strategy obj);
		    load_function = (fun _ (_,obj) -> cache_strategy obj);
		    subst_function = subst_strategy;
                    discharge_function = discharge_strategy;
		    classify_function = classify_strategy }


let set_strategy local str =
  Lib.add_anonymous_leaf (inStrategy (local,str))

let _ = declare_summary "Transparent constants and variables"
    { freeze_function = Conv_oracle.freeze;
      unfreeze_function = Conv_oracle.unfreeze;
      init_function = Conv_oracle.init }


(* Generic reduction: reduction functions used in reduction tactics *)

type red_expr =
    (constr, evaluable_global_reference, constr_pattern) red_expr_gen

let make_flag_constant = function
  | EvalVarRef id -> fVAR id
  | EvalConstRef sp -> fCONST sp

let make_flag f =
  let red = no_red in
  let red = if f.rBeta then red_add red fBETA else red in
  let red = if f.rIota then red_add red fIOTA else red in
  let red = if f.rZeta then red_add red fZETA else red in
  let red =
    if f.rDelta then (* All but rConst *)
        let red = red_add red fDELTA in
        let red = red_add_transparent red (Conv_oracle.get_transp_state()) in
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
let reduction_tab = ref Stringmap.empty

(* table of custom reduction expressions, synchronized,
   filled by command Declare Reduction *)
let red_expr_tab = ref Stringmap.empty

let declare_reduction s f =
  if Stringmap.mem s !reduction_tab || Stringmap.mem s !red_expr_tab
  then error ("There is already a reduction expression of name "^s)
  else reduction_tab := Stringmap.add s f !reduction_tab

let check_custom = function
  | ExtraRedExpr s ->
      if not (Stringmap.mem s !reduction_tab || Stringmap.mem s !red_expr_tab)
      then error ("Reference to undefined reduction expression "^s)
  |_ -> ()

let decl_red_expr s e =
  if Stringmap.mem s !reduction_tab || Stringmap.mem s !red_expr_tab
  then error ("There is already a reduction expression of name "^s)
  else begin
    check_custom e;
    red_expr_tab := Stringmap.add s e !red_expr_tab
  end

let out_arg = function
  | ArgVar _ -> anomaly "Unevaluated or_var variable"
  | ArgArg x -> x

let out_with_occurrences ((b,l),c) =
  ((b,List.map out_arg l), c)

let rec reduction_of_red_expr = function
  | Red internal ->
      if internal then (try_red_product,DEFAULTcast)
      else (red_product,DEFAULTcast)
  | Hnf -> (hnf_constr,DEFAULTcast)
  | Simpl (Some (_,c as lp)) ->
    (contextually (is_reference c) (out_with_occurrences lp)
      (fun _ -> simpl),DEFAULTcast)
  | Simpl None -> (simpl,DEFAULTcast)
  | Cbv f -> (cbv_norm_flags (make_flag f),DEFAULTcast)
  | Lazy f -> (clos_norm_flags (make_flag f),DEFAULTcast)
  | Unfold ubinds -> (unfoldn (List.map out_with_occurrences ubinds),DEFAULTcast)
  | Fold cl -> (fold_commands cl,DEFAULTcast)
  | Pattern lp -> (pattern_occs (List.map out_with_occurrences lp),DEFAULTcast)
  | ExtraRedExpr s ->
      (try (Stringmap.find s !reduction_tab,DEFAULTcast)
      with Not_found ->
	(try reduction_of_red_expr (Stringmap.find s !red_expr_tab)
	 with Not_found ->
	   error("unknown user-defined reduction \""^s^"\"")))
  | CbvVm -> (cbv_vm ,VMcast)


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
    (Pattern.subst_pattern subs)
    e

let (inReduction,_) =
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

let _ = declare_summary "Declare Reduction"
  { freeze_function = (fun () -> !red_expr_tab);
    unfreeze_function = ((:=) red_expr_tab);
    init_function = (fun () -> red_expr_tab := Stringmap.empty) }
