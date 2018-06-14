(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Bruno Barras for Benjamin Grégoire as part of the
   bytecode-based reduction machine, Oct 2004 *)
(* Bug fix #1419 by Jean-Marc Notin, Mar 2007 *)

(* This file manages the table of global symbols for the bytecode machine *)

open Util
open Names
open Vmvalues
open Vmemitcodes
open Vmbytecodes
open Declarations
open Environ
open Vmbytegen

module NamedDecl = Context.Named.Declaration
module RelDecl = Context.Rel.Declaration

external eval_tcode : tcode -> atom array -> vm_global -> values array -> values = "coq_eval_tcode"

type global_data = { mutable glob_len : int; mutable glob_val : values array }

(*******************)
(* Linkage du code *)
(*******************)

(* Table des globaux *)

(* [global_data] contient les valeurs des constantes globales
   (axiomes,definitions), les annotations des switch et les structured
   constant *)
let global_data = {
  glob_len = 0;
  glob_val = Array.make 4096 crazy_val;
}

let get_global_data () = Vmvalues.vm_global global_data.glob_val

let realloc_global_data n =
  let n = min (2 * n + 0x100) Sys.max_array_length in
  let ans = Array.make n crazy_val in
  let src = global_data.glob_val in
  let () = Array.blit src 0 ans 0 (Array.length src) in
  global_data.glob_val <- ans

let check_global_data n =
  if n >= Array.length global_data.glob_val then realloc_global_data n

let set_global v =
  let n = global_data.glob_len in
  check_global_data n;
  global_data.glob_val.(n) <- v;
  global_data.glob_len <- global_data.glob_len + 1;
  n

(* Initialization of OCaml primitives *)
let parray_make = set_global Vmvalues.parray_make
let parray_get = set_global Vmvalues.parray_get
let parray_get_default = set_global Vmvalues.parray_get_default
let parray_set = set_global Vmvalues.parray_set
let parray_copy = set_global Vmvalues.parray_copy
let parray_length = set_global Vmvalues.parray_length

(* table pour les structured_constant et les annotations des switchs *)

module HashMap (M : Hashtbl.HashedType) :
sig
  type +'a t
  val empty : 'a t
  val add : M.t -> 'a -> 'a t -> 'a t
  val find : M.t -> 'a t -> 'a
end =
struct
  type 'a t = (M.t * 'a) list Int.Map.t
  let empty = Int.Map.empty
  let add k v m =
    let hash = M.hash k in
    try Int.Map.modify hash (fun _ l -> (k, v) :: l) m
    with Not_found -> Int.Map.add hash [k, v] m
  let find k m =
    let hash = M.hash k in
    let l = Int.Map.find hash m in
    List.assoc_f M.equal k l
end

module SConstTable = HashMap (struct
  type t = structured_constant
  let equal = eq_structured_constant
  let hash = hash_structured_constant
end)

module AnnotTable = HashMap (struct
  type t = annot_switch
  let equal = eq_annot_switch
  let hash = hash_annot_switch
end)

type global_table = {
  glob_sconst : int SConstTable.t;
  glob_annot : int AnnotTable.t;
}

let global_table = ref {
  glob_sconst = SConstTable.empty;
  glob_annot = AnnotTable.empty;
}

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
  try SConstTable.find key global_table.contents.glob_sconst
  with Not_found ->
    let n = set_global (val_of_str_const key) in
    let glob_sconst = SConstTable.add key n global_table.contents.glob_sconst in
    global_table := { !global_table with glob_sconst };
    n

let slot_for_annot key =
  try AnnotTable.find key global_table.contents.glob_annot
  with Not_found ->
    let n = set_global (val_of_annot_switch key) in
    let glob_annot = AnnotTable.add key n global_table.contents.glob_annot in
    global_table := { !global_table with glob_annot };
    n

let slot_for_caml_prim = function
  | CAML_Arraymake -> parray_make
  | CAML_Arrayget -> parray_get
  | CAML_Arraydefault -> parray_get_default
  | CAML_Arrayset -> parray_set
  | CAML_Arraycopy -> parray_copy
  | CAML_Arraylength -> parray_length

let rec slot_for_getglobal env sigma kn =
  let (cb,(_,rk)) = lookup_constant_key kn env in
  try key rk
  with NotEvaluated ->
(*    Pp.msgnl(str"not yet evaluated");*)
    let pos =
      match cb.const_body_code with
      | None -> set_global (val_of_constant kn)
      | Some code ->
         match code with
         | BCdefined(code,pl,fv) ->
           let v = eval_to_patch env sigma (code,pl,fv) in
           set_global v
         | BCalias kn' -> slot_for_getglobal env sigma kn'
         | BCconstant -> set_global (val_of_constant kn)
    in
(*Pp.msgnl(str"value stored at: "++int pos);*)
    rk := Some (CEphemeron.create pos);
    pos

and slot_for_fv env sigma fv =
  let fill_fv_cache cache id v_of_id env_of_id b =
    let v,d =
      match b with
      | None -> v_of_id id, Id.Set.empty
      | Some c ->
          val_of_constr (env_of_id id env) sigma c,
          Environ.global_vars_set env c in
    build_lazy_val cache (v, d); v in
  let val_of_rel i = val_of_rel (nb_rel env - i) in
  let idfun _ x = x in
  match fv with
  | FVnamed id ->
      let nv = lookup_named_val id env in
      begin match force_lazy_val nv with
      | None ->
         env |> lookup_named id |> NamedDecl.get_value |> fill_fv_cache nv id val_of_named idfun
      | Some (v, _) -> v
      end
  | FVrel i ->
      let rv = lookup_rel_val i env in
      begin match force_lazy_val rv with
      | None ->
        env |> lookup_rel i |> RelDecl.get_value |> fill_fv_cache rv i val_of_rel env_of_rel
      | Some (v, _) -> v
      end
  | FVevar evk -> val_of_evar evk
  | FVuniv_var _idu ->
    assert false

and eval_to_patch env sigma (buff,pl,fv) =
  let slots = function
    | Reloc_annot a -> slot_for_annot a
    | Reloc_const sc -> slot_for_str_cst sc
    | Reloc_getglobal kn -> slot_for_getglobal env sigma kn
    | Reloc_caml_prim op -> slot_for_caml_prim op
  in
  let tc = patch buff pl slots in
  let vm_env =
    (* Environment should look like a closure, so free variables start at slot 2. *)
    let a = Array.make (Array.length fv + 2) crazy_val in
    a.(1) <- Obj.magic 2;
    Array.iteri (fun i v -> a.(i + 2) <- slot_for_fv env sigma v) fv;
    a in
  eval_tcode tc (get_atom_rel ()) (vm_global global_data.glob_val) vm_env

and val_of_constr env sigma c =
  match compile ~fail_on_error:true env sigma c with
  | Some v -> eval_to_patch env sigma (to_memory v)
  | None -> assert false

let set_transparent_const _kn = () (* !?! *)
let set_opaque_const _kn = () (* !?! *)
