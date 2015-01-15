(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Bruno Barras for Benjamin Grégoire as part of the
   bytecode-based reduction machine, Oct 2004 *)
(* Bug fix #1419 by Jean-Marc Notin, Mar 2007 *)

(* This file manages the table of global symbols for the bytecode machine *)

open Util
open Names
open Term
open Context
open Vm
open Cemitcodes
open Cbytecodes
open Declarations
open Pre_env
open Cbytegen


external tcode_of_code : emitcodes -> int -> tcode = "coq_tcode_of_code"
external eval_tcode : tcode -> values array -> values = "coq_eval_tcode"

(*******************)
(* Linkage du code *)
(*******************)

(* Table des globaux *)

(* [global_data] contient les valeurs des constantes globales
   (axiomes,definitions), les annotations des switch et les structured
   constant *)
external global_data : unit -> values array = "get_coq_global_data"

(* [realloc_global_data n] augmente de n la taille de [global_data] *)
external realloc_global_data : int -> unit = "realloc_coq_global_data"

let check_global_data n =
  if n >= Array.length (global_data()) then realloc_global_data n

let num_global = ref 0

let set_global v =
  let n = !num_global in
  check_global_data n;
  (global_data()).(n) <- v;
  incr num_global;
  n

(* table pour les structured_constant et les annotations des switchs *)

let rec eq_structured_constant c1 c2 = match c1, c2 with
| Const_sorts s1, Const_sorts s2 -> Sorts.equal s1 s2
| Const_ind i1, Const_ind i2 -> Univ.eq_puniverses eq_ind i1 i2
| Const_b0 t1, Const_b0 t2 -> Int.equal t1 t2
| Const_bn (t1, a1), Const_bn (t2, a2) ->
  Int.equal t1 t2 && Array.equal eq_structured_constant a1 a2
| _ -> false

let rec hash_structured_constant c =
  let open Hashset.Combine in
  match c with
  | Const_sorts s -> combinesmall 1 (Sorts.hash s)
  | Const_ind (i,u) -> combinesmall 2 (combine (ind_hash i) (Univ.Instance.hash u))
  | Const_b0 t -> combinesmall 3 (Int.hash t)
  | Const_bn (t, a) ->
    let fold h c = combine h (hash_structured_constant c) in
    let h = Array.fold_left fold 0 a in
    combinesmall 4 (combine (Int.hash t) h)

module SConstTable = Hashtbl.Make (struct
  type t = structured_constant
  let equal = eq_structured_constant
  let hash = hash_structured_constant
end)

let eq_annot_switch asw1 asw2 =
  let eq_ci ci1 ci2 =
    eq_ind ci1.ci_ind ci2.ci_ind &&
    Int.equal ci1.ci_npar ci2.ci_npar &&
    Array.equal Int.equal ci1.ci_cstr_ndecls ci2.ci_cstr_ndecls
  in
  let eq_rlc (i1, j1) (i2, j2) = Int.equal i1 i2 && Int.equal j1 j2 in
  eq_ci asw1.ci asw2.ci &&
  Array.equal eq_rlc asw1.rtbl asw2.rtbl &&
  (asw1.tailcall : bool) == asw2.tailcall

let hash_annot_switch asw =
  let open Hashset.Combine in
  let h1 = Constr.case_info_hash asw.ci in
  let h2 = Array.fold_left (fun h (t, i) -> combine3 h t i) 0 asw.rtbl in
  let h3 = if asw.tailcall then 1 else 0 in
  combine3 h1 h2 h3

module AnnotTable = Hashtbl.Make (struct
  type t = annot_switch
  let equal = eq_annot_switch
  let hash = hash_annot_switch
end)

let str_cst_tbl : int SConstTable.t = SConstTable.create 31

let annot_tbl : int AnnotTable.t = AnnotTable.create 31
    (* (annot_switch * int) Hashtbl.t  *)

(*************************************************************)
(*** Mise a jour des valeurs des variables et des constantes *)
(*************************************************************)

exception NotEvaluated

let key rk =
  match !rk with
  | None -> raise NotEvaluated
  | Some k -> (*Pp.msgnl (str"found at: "++int k);*)
      try Ephemeron.get k
      with Ephemeron.InvalidKey -> raise NotEvaluated

(************************)
(* traduction des patch *)

(* slot_for_*, calcul la valeur de l'objet, la place
   dans la table global, rend sa position dans la table *)

let slot_for_str_cst key =
  try SConstTable.find str_cst_tbl key
  with Not_found ->
    let n = set_global (val_of_str_const key) in
    SConstTable.add str_cst_tbl key n;
    n

let slot_for_annot key =
  try AnnotTable.find annot_tbl key
  with Not_found ->
    let n =  set_global (val_of_annot_switch key) in
    AnnotTable.add annot_tbl key n;
    n

let rec slot_for_getglobal env (kn,u) =
  let (cb,(_,rk)) = lookup_constant_key kn env in
  try key rk
  with NotEvaluated ->
(*    Pp.msgnl(str"not yet evaluated");*)
    let pos =
      match Cemitcodes.force cb.const_body_code with
      | BCdefined(code,pl,fv) ->
	if Univ.Instance.is_empty u then
	  let v = eval_to_patch env (code,pl,fv) in
	    set_global v
	else set_global (val_of_constant (kn,u))
    | BCallias kn' -> slot_for_getglobal env kn'
    | BCconstant -> set_global (val_of_constant (kn,u)) in
(*Pp.msgnl(str"value stored at: "++int pos);*)
    rk := Some (Ephemeron.create pos);
    pos

and slot_for_fv env fv =
  let fill_fv_cache cache id v_of_id env_of_id b =
    let v,d =
      match b with
      | None -> v_of_id id, Id.Set.empty
      | Some c ->
          val_of_constr (env_of_id id env) c,
          Environ.global_vars_set (Environ.env_of_pre_env env) c in
    build_lazy_val cache (v, d); v in
  let val_of_rel i = val_of_rel (nb_rel env - i) in
  let idfun _ x = x in
  match fv with
  | FVnamed id ->
      let nv = Pre_env.lookup_named_val id env in
      begin match force_lazy_val nv with
      | None ->
          let _, b, _ = Context.lookup_named id env.env_named_context in
          fill_fv_cache nv id val_of_named idfun b
      | Some (v, _) -> v
      end
  | FVrel i ->
      let rv = Pre_env.lookup_rel_val i env in
      begin match force_lazy_val rv with
      | None ->
          let _, b, _ = lookup_rel i env.env_rel_context in
          fill_fv_cache rv i val_of_rel env_of_rel b
      | Some (v, _) -> v
      end

and eval_to_patch env (buff,pl,fv) =
  (* copy code *before* patching because of nested evaluations:
     the code we are patching might be called (and thus "concurrently" patched)
     and results in wrong results. Side-effects... *)
  let buff = Cemitcodes.copy buff in
  let patch = function
    | Reloc_annot a, pos -> patch_int buff pos (slot_for_annot a)
    | Reloc_const sc, pos -> patch_int buff pos (slot_for_str_cst sc)
    | Reloc_getglobal kn, pos ->
(*      Pp.msgnl (str"patching global: "++str(debug_string_of_con kn));*)
	patch_int buff pos (slot_for_getglobal env kn);
(*      Pp.msgnl (str"patch done: "++str(debug_string_of_con kn))*)
  in
  List.iter patch pl;
  let vm_env = Array.map (slot_for_fv env) fv in
  let tc = tcode_of_code buff (length buff) in
(*Pp.msgnl (str"execute code");*)
  eval_tcode tc vm_env

and val_of_constr env c =
  let (_,fun_code,_ as ccfv) =
    try compile env c
    with reraise ->
      let reraise = Errors.push reraise in
      let () = print_string "can not compile \n" in
      let () = Format.print_flush () in
      iraise reraise
  in
  eval_to_patch env (to_memory ccfv)

let set_transparent_const kn = () (* !?! *)
let set_opaque_const kn = () (* !?! *)


