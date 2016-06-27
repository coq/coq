(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
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
| Const_sorts _, _ -> false
| Const_ind i1, Const_ind i2 -> eq_ind i1 i2
| Const_ind _, _ -> false
| Const_proj p1, Const_proj p2 -> Constant.equal p1 p2
| Const_proj _, _ -> false
| Const_b0 t1, Const_b0 t2 -> Int.equal t1 t2
| Const_b0 _, _ -> false
| Const_bn (t1, a1), Const_bn (t2, a2) ->
  Int.equal t1 t2 && Array.equal eq_structured_constant a1 a2
| Const_bn _, _ -> false
| Const_univ_level l1 , Const_univ_level l2 -> Univ.eq_levels l1 l2
| Const_univ_level _ , _ -> false
| Const_type u1 , Const_type u2 -> Univ.Universe.equal u1 u2
| Const_type _ , _ -> false

let rec hash_structured_constant c =
  let open Hashset.Combine in
  match c with
  | Const_sorts s -> combinesmall 1 (Sorts.hash s)
  | Const_ind i -> combinesmall 2 (ind_hash i)
  | Const_proj p -> combinesmall 3 (Constant.hash p)
  | Const_b0 t -> combinesmall 4 (Int.hash t)
  | Const_bn (t, a) ->
    let fold h c = combine h (hash_structured_constant c) in
    let h = Array.fold_left fold 0 a in
    combinesmall 5 (combine (Int.hash t) h)
  | Const_univ_level l -> combinesmall 6 (Univ.Level.hash l)
  | Const_type u -> combinesmall 7 (Univ.Universe.hash u)

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
  | Some k ->
      try CEphemeron.get k
      with CEphemeron.InvalidKey -> raise NotEvaluated

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

let rec slot_for_getglobal env kn =
  let (cb,(_,rk)) = lookup_constant_key kn env in
  try key rk
  with NotEvaluated ->
(*    Pp.msgnl(str"not yet evaluated");*)
    let pos =
      match cb.const_body_code with
      | None -> set_global (val_of_constant kn)
      | Some code ->
	 match Cemitcodes.force code with
	 | BCdefined(code,pl,fv) ->
           let v = eval_to_patch env (code,pl,fv) in
           set_global v
	 | BCalias kn' -> slot_for_getglobal env kn'
	 | BCconstant -> set_global (val_of_constant kn)
    in
(*Pp.msgnl(str"value stored at: "++int pos);*)
    rk := Some (CEphemeron.create pos);
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
         let open Context.Named in
         let open Declaration in
	 env.env_named_context |> lookup id |> get_value |> fill_fv_cache nv id val_of_named idfun
      | Some (v, _) -> v
      end
  | FVrel i ->
      let rv = Pre_env.lookup_rel_val i env in
      begin match force_lazy_val rv with
      | None ->
         let open Context.Rel in
         let open Declaration in
	 env.env_rel_context |> lookup i |> get_value |> fill_fv_cache rv i val_of_rel env_of_rel
      | Some (v, _) -> v
      end
  | FVuniv_var idu ->
    assert false

and eval_to_patch env (buff,pl,fv) =
  let patch = function
    | Reloc_annot a, pos -> (pos, slot_for_annot a)
    | Reloc_const sc, pos -> (pos, slot_for_str_cst sc)
    | Reloc_getglobal kn, pos -> (pos, slot_for_getglobal env kn)
  in
  let patches = List.map_left patch pl in
  let buff = patch_int buff patches in
  let vm_env = Array.map (slot_for_fv env) fv in
  let tc = tcode_of_code buff (length buff) in
  eval_tcode tc vm_env

and val_of_constr env c =
  let (_,fun_code,_ as ccfv) =
    try match compile true env c with
	| Some v -> v
	| None -> assert false
    with reraise ->
      let reraise = CErrors.push reraise in
      let () = print_string "can not compile \n" in
      let () = Format.print_flush () in
      iraise reraise
  in
  eval_to_patch env (to_memory ccfv)

let set_transparent_const kn = () (* !?! *)
let set_opaque_const kn = () (* !?! *)
