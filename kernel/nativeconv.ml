(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Errors
open Names
open Univ
open Nativelib
open Reduction
open Util
open Nativevalues
open Nativecode 

(** This module implements the conversion test by compiling to OCaml code *)

let rec conv_val env pb lvl v1 v2 cu = 
  if v1 == v2 then cu
  else
    match kind_of_value v1, kind_of_value v2 with
    | Vaccu k1, Vaccu k2 ->
	conv_accu env pb lvl k1 k2 cu
    | Vfun f1, Vfun f2 ->
	let v = mk_rel_accu lvl in
	conv_val env CONV (lvl+1) (f1 v) (f2 v) cu
    | Vconst i1, Vconst i2 -> 
	if Int.equal i1 i2 then cu else raise NotConvertible
    | Vblock b1, Vblock b2 ->
	let n1 = block_size b1 in
        let n2 = block_size b2 in
	if not (Int.equal (block_tag b1) (block_tag b2)) || not (Int.equal n1 n2) then
	  raise NotConvertible;
	let rec aux lvl max b1 b2 i cu =
	  if Int.equal i max then 
	    conv_val env CONV lvl (block_field b1 i) (block_field b2 i) cu
	  else
	    let cu = 
	      conv_val env CONV lvl (block_field b1 i) (block_field b2 i) cu in
	    aux lvl max b1 b2 (i+1) cu in
	aux lvl (n1-1) b1 b2 0 cu
    | Vfun f1, _ -> 
	conv_val env CONV lvl v1 (fun x -> v2 x) cu
    | _, Vfun f2 ->
	conv_val env CONV lvl (fun x -> v1 x) v2 cu
    | _, _ -> raise NotConvertible

and conv_accu env pb lvl k1 k2 cu = 
  let n1 = accu_nargs k1 in
  let n2 = accu_nargs k2 in
  if not (Int.equal n1 n2) then raise NotConvertible;
  if Int.equal n1 0 then 
    conv_atom env pb lvl (atom_of_accu k1) (atom_of_accu k2) cu
  else
    let cu = conv_atom env pb lvl (atom_of_accu k1) (atom_of_accu k2) cu in
    List.fold_right2 (conv_val env CONV lvl) (args_of_accu k1) (args_of_accu k2) cu

and conv_atom env pb lvl a1 a2 cu =
  if a1 == a2 then cu
  else
    match a1, a2 with
    | Arel i1, Arel i2 -> 
	if not (Int.equal i1 i2) then raise NotConvertible;
	cu
    | Aind ind1, Aind ind2 ->
	if not (eq_ind ind1 ind2) then raise NotConvertible;
	cu
    | Aconstant c1, Aconstant c2 ->
	if not (eq_constant c1 c2) then raise NotConvertible;
	cu
    | Asort s1, Asort s2 -> 
        check_sort_cmp_universes env pb s1 s2 cu; cu
    | Avar id1, Avar id2 ->
	if not (Id.equal id1 id2) then raise NotConvertible;
	cu
    | Acase(a1,ac1,p1,bs1), Acase(a2,ac2,p2,bs2) ->
	if not (eq_ind a1.asw_ind a2.asw_ind) then raise NotConvertible;
	let cu = conv_accu env CONV lvl ac1 ac2 cu in
	let tbl = a1.asw_reloc in
	let len = Array.length tbl in
	if Int.equal len 0 then conv_val env CONV lvl p1 p2 cu 
	else
	  let cu = conv_val env CONV lvl p1 p2 cu in
	  let max = len - 1 in
	  let rec aux i cu =
	    let tag,arity = tbl.(i) in
	    let ci = 
	      if Int.equal arity 0 then mk_const tag
	      else mk_block tag (mk_rels_accu lvl arity) in
	    let bi1 = bs1 ci and bi2 = bs2 ci in
	    if Int.equal i max then conv_val env CONV (lvl + arity) bi1 bi2 cu
	    else aux (i+1) (conv_val env CONV (lvl + arity) bi1 bi2 cu) in
	  aux 0 cu
    | Afix(t1,f1,rp1,s1), Afix(t2,f2,rp2,s2) ->
	if not (Int.equal s1 s2) || not (Array.equal Int.equal rp1 rp2) then raise NotConvertible;
	if f1 == f2 then cu
	else conv_fix env lvl t1 f1 t2 f2 cu
    | (Acofix(t1,f1,s1,_) | Acofixe(t1,f1,s1,_)),
      (Acofix(t2,f2,s2,_) | Acofixe(t2,f2,s2,_)) ->
	if not (Int.equal s1 s2) then raise NotConvertible;
	if f1 == f2 then cu
	else
	  if not (Int.equal (Array.length f1) (Array.length f2)) then raise NotConvertible
	  else conv_fix env lvl t1 f1 t2 f2 cu 
    | Aprod(_,d1,c1), Aprod(_,d2,c2) ->
	let cu = conv_val env CONV lvl d1 d2 cu in
	let v = mk_rel_accu lvl in
	conv_val env pb (lvl + 1) (d1 v) (d2 v) cu 
    | _, _ -> raise NotConvertible

(* Precondition length t1 = length f1 = length f2 = length t2 *)
and conv_fix env lvl t1 f1 t2 f2 cu =
  let len = Array.length f1 in
  let max = len - 1 in
  let fargs = mk_rels_accu lvl len in
  let flvl = lvl + len in
  let rec aux i cu =
    let cu = conv_val env CONV lvl t1.(i) t2.(i) cu in
    let fi1 = napply f1.(i) fargs in
    let fi2 = napply f2.(i) fargs in
    if Int.equal i max then conv_val env CONV flvl fi1 fi2 cu 
    else aux (i+1) (conv_val env CONV flvl fi1 fi2 cu) in
  aux 0 cu

let native_conv pb sigma env t1 t2 =
  if !Flags.no_native_compiler then begin
    let msg = "Native compiler is disabled, "^
    "falling back to VM conversion test." in
    Pp.msg_warning (Pp.str msg);
    vm_conv pb env t1 t2
  end
  else
  let penv = Environ.pre_env env in 
  let ml_filename, prefix = get_ml_filename () in
  let code, upds = mk_conv_code penv sigma prefix t1 t2 in
  match compile ml_filename code with
  | (0,fn) ->
      begin
        if !Flags.debug then Pp.msg_debug (Pp.str "Running test...");
        let t0 = Sys.time () in
        call_linker ~fatal:true prefix fn (Some upds);
        let t1 = Sys.time () in
        let time_info = Format.sprintf "Evaluation done in %.5f@." (t1 -. t0) in
        if !Flags.debug then Pp.msg_debug (Pp.str time_info);
        (* TODO change 0 when we can have deBruijn *)
        ignore(conv_val env pb 0 !rt1 !rt2 (Environ.universes env))
      end
  | _ -> anomaly (Pp.str "Compilation failure") 

let _ = set_nat_conv native_conv
