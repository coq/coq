(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Names
open Values

(********************************************)
(* Initialization of the abstract machine ***)
(* Necessary for [relaccu_tbl]              *)
(********************************************)

external init_vm : unit -> unit = "init_rocq_vm"

let _ = init_vm ()

(******************************************************)
(* Abstract data types and utility functions **********)
(******************************************************)

(* The representation of values relies on this assertion *)
let _ = assert (Int.equal Obj.first_non_constant_constructor_tag 0)

(* Values of the abstract machine *)
type values
type structured_values = values
let val_of_obj v = ((Obj.obj v):values)
let crazy_val = (val_of_obj (Obj.repr 0))

type tag = int

let type_atom_tag = 2
let max_atom_tag = 2
let proj_tag = 3
let fix_app_tag = 4
let switch_tag = 5
let cofix_tag = 6
let cofix_evaluated_tag = 7

(** Structured constants are constants whose construction is done once. Their
occurrences share the same value modulo kernel name substitutions (for functor
application). Structured values have the additional property that no
substitution will need to be performed, so their runtime value can directly be
shared without reallocating a more structured representation. *)
type structured_constant =
  | Const_sort of Sorts.t
  | Const_ind of inductive
  | Const_evar of Evar.t
  | Const_b0 of tag
  | Const_univ_instance of UVars.Instance.t
  | Const_val of structured_values
  | Const_uint of Uint63.t
  | Const_float of Float64.t
  | Const_string of Pstring.t

type reloc_table = (tag * int) array

(** When changing this, adapt Is_tailrec_switch in rocq_values.h accordingly *)
type annot_switch =
   { rtbl : reloc_table; tailcall : bool; max_stack_size : int }

let rec eq_structured_values v1 v2 =
  v1 == v2 ||
  let o1 = Obj.repr v1 in
  let o2 = Obj.repr v2 in
  if Obj.is_int o1 && Obj.is_int o2 then o1 == o2
  else
    let t1 = Obj.tag o1 in
    let t2 = Obj.tag o2 in
    if Int.equal t1 t2 &&
       Int.equal (Obj.size o1) (Obj.size o2)
    then if Int.equal t1 Obj.custom_tag
      then Int64.equal (Obj.magic v1 : int64) (Obj.magic v2 : int64)
    else if Int.equal t1 Obj.double_tag
      then Float64.(equal (of_float (Obj.magic v1)) (of_float (Obj.magic v2)))
    else if Int.equal t1 Obj.string_tag
      then String.equal (Obj.magic v1) (Obj.magic v2)
    else begin
      assert (t1 <= Obj.last_non_constant_constructor_tag &&
              t2 <= Obj.last_non_constant_constructor_tag);
      let i = ref 0 in
      while (!i < Obj.size o1 && eq_structured_values
               (Obj.magic (Obj.field o1 !i) : structured_values)
               (Obj.magic (Obj.field o2 !i) : structured_values)) do
        incr i
      done;
      !i >= Obj.size o1
    end
    else false

let hash_structured_values (v : structured_values) =
  (* We may want a better hash function here *)
  Hashtbl.hash v

let eq_structured_constant c1 c2 = match c1, c2 with
| Const_sort s1, Const_sort s2 -> Sorts.equal s1 s2
| Const_sort _, _ -> false
| Const_ind i1, Const_ind i2 -> Ind.CanOrd.equal i1 i2
| Const_ind _, _ -> false
| Const_evar e1, Const_evar e2 -> Evar.equal e1 e2
| Const_evar _, _ -> false
| Const_b0 t1, Const_b0 t2 -> Int.equal t1 t2
| Const_b0 _, _ -> false
| Const_univ_instance u1 , Const_univ_instance u2 -> UVars.Instance.equal u1 u2
| Const_univ_instance _ , _ -> false
| Const_val v1, Const_val v2 -> eq_structured_values v1 v2
| Const_val _, _ -> false
| Const_uint i1, Const_uint i2 -> Uint63.equal i1 i2
| Const_uint _, _ -> false
| Const_float f1, Const_float f2 -> Float64.equal f1 f2
| Const_float _, _ -> false
| Const_string s1, Const_string s2 -> Pstring.equal s1 s2
| Const_string _, _ -> false

let hash_structured_constant c =
  let open Hashset.Combine in
  match c with
  | Const_sort s -> combinesmall 1 (Sorts.hash s)
  | Const_ind i -> combinesmall 2 (Ind.CanOrd.hash i)
  | Const_evar e -> combinesmall 3 (Evar.hash e)
  | Const_b0 t -> combinesmall 4 (Int.hash t)
  | Const_univ_instance u -> combinesmall 5 (UVars.Instance.hash u)
  | Const_val v -> combinesmall 6 (hash_structured_values v)
  | Const_uint i -> combinesmall 7 (Uint63.hash i)
  | Const_float f -> combinesmall 8 (Float64.hash f)
  | Const_string s -> combinesmall 9 (Pstring.hash s)

let eq_annot_switch asw1 asw2 =
  let eq_rlc (i1, j1) (i2, j2) = Int.equal i1 i2 && Int.equal j1 j2 in
  CArray.equal eq_rlc asw1.rtbl asw2.rtbl &&
  (asw1.tailcall : bool) == asw2.tailcall &&
  Int.equal asw1.max_stack_size asw2.max_stack_size

let hash_annot_switch asw =
  let open Hashset.Combine in
  let h1 = Array.fold_left (fun h (t, i) -> combine3 h t i) 0 asw.rtbl in
  let h2 = if asw.tailcall then 1 else 0 in
  combine3 h1 h2 asw.max_stack_size

let pp_sort s =
  let open Sorts in
  match s with
  | SProp -> Pp.str "SProp"
  | Prop -> Pp.str "Prop"
  | Set -> Pp.str "Set"
  | Type u -> Pp.(str "Type@{" ++ Univ.Universe.raw_pr u ++ str "}")
  | QSort (q, u) ->
    Pp.(str "QSort@{" ++ (Sorts.QVar.raw_pr q) ++ strbrk ", " ++ Univ.Universe.raw_pr u ++ str "}")

let pp_struct_const = function
  | Const_sort s -> pp_sort s
  | Const_ind (mind, i) -> Pp.(MutInd.print mind ++ str"#" ++ int i)
  | Const_evar e -> Pp.( str "Evar(" ++ int (Evar.repr e) ++ str ")")
  | Const_b0 i -> Pp.int i
  | Const_univ_instance u -> UVars.Instance.pr Sorts.QVar.raw_pr Univ.Level.raw_pr u
  | Const_val _ -> Pp.str "(value)"
  | Const_uint i -> Pp.str (Uint63.to_string i)
  | Const_float f -> Pp.str (Float64.to_string f)
  | Const_string s -> Pp.str (Printf.sprintf "%S" (Pstring.to_string s))

(* Abstract data *)
type vprod
type vfun
type vfix
type vcofix
type vblock
type arguments

let fun_val v = (Obj.magic v : values)
let fix_val v = (Obj.magic v : values)
let cofix_upd_val v = (Obj.magic v : values)

type vm_env
let inj_env v = (Obj.magic v : vm_env)
let fun_env v = (Obj.magic v : vm_env)
let cofix_env v = (Obj.magic v : vm_env)
let cofix_upd_env v = (Obj.magic v : vm_env)
type vstack = values array

let fun_of_val v = (Obj.magic v : vfun)

(*******************************************)
(* Machine code *** ************************)
(*******************************************)

type tcode
(** A block whose first field is a C-allocated VM bytecode, encoded as char*.
    This is compatible with the representation of OCaml closures. *)

type tcode_array

external mkAccuCode : int -> tcode = "rocq_makeaccu"
external offset_tcode : tcode -> int -> tcode = "rocq_offset_tcode"

let fun_code v = (Obj.magic v : tcode)
let fix_code = fun_code
let cofix_upd_code = fun_code


type vswitch = {
    sw_type_code : tcode;
    sw_code : tcode;
    sw_annot : annot_switch;
    sw_stk : vstack;
    sw_env : vm_env
  }

(* Representation of values *)
(* + Products : *)
(*   -   vprod = 0_[ dom | codom]                                         *)
(*             dom : values, codom : vfun                                 *)
(*                                                                        *)
(* + Functions have two representations :                                 *)
(*   - unapplied fun :  vf = Ct_[ C | envofs=2 | fv1 | ... | fvn]         *)
(*                                       C:tcode, fvi : values            *)
(*     Remark : a function and its environment is the same value.         *)
(*   - partially applied fun : Ct_[ Restart::C | envofs=2 | vf | arg1 | ... | argn] *)
(*                                                                        *)
(* + Fixpoints :                                                          *)
(*   - Ct_[C1|envofs1=3*n-1 | Infix_t|C2|envofs2 | ... | Infix_t|Cn|envofsn=2 | fv1|...|fvn] *)
(*     One single block to represent all of the fixpoints, each fixpoint  *)
(*     is the pointer to the field holding the pointer to its code, and   *)
(*     the infix tag is used to know where the block starts.              *)
(*   - Partial application follows the scheme of partially applied        *)
(*     functions. Note: only fixpoints not having been applied to its     *)
(*     recursive argument are coded this way. When the rec. arg. is       *)
(*     applied, either it's a constructor and the fix reduces, or it's    *)
(*     and the fix is coded as an accumulator.                            *)
(*                                                                        *)
(* + Cofixpoints : see cbytegen.ml                                        *)
(*                                                                        *)
(* + vblock's encode (non constant) constructors as in Ocaml, but         *)
(*   starting from 0 up.                                                  *)
(*                                                                        *)
(* + vm_env is the type of the machine environments (i.e. a function or   *)
(*   a fixpoint)                                                          *)
(*                                                                        *)
(* + Accumulators : At_[accumulate | envofs=2 | accu | arg1 | ... | argn ] *)
(*   - representation of [accu] : tag_[....]                              *)
(*     -- tag <= 3 : encoding atom type (sorts, free vars, etc.)          *)
(*     -- 10_[accu|proj name] : a projection blocked by an accu           *)
(*     -- 11_[accu|fix_app] : a fixpoint blocked by an accu               *)
(*     -- 12_[accu|vswitch] : a match blocked by an accu                  *)
(*     -- 13_[fcofix]       : a cofix function                            *)
(*     -- 14_[fcofix|val]   : a cofix function, val represent the value   *)
(*        of the function applied to arg1 ... argn                        *)
(* The [arguments] type, which is abstracted as an array, represents :    *)
(*          tag[ _ | _ |v1|... | vn]                                      *)
(* Generally the first field is a code pointer.                           *)

(* Do not edit this type without editing C code, especially "rocq_values.h" *)

type id_key =
| ConstKey of Constant.t
| VarKey of Id.t
| RelKey of Int.t
| EvarKey of Evar.t

let eq_id_key (k1 : id_key) (k2 : id_key) = match k1, k2 with
| ConstKey c1, ConstKey c2 -> Constant.CanOrd.equal c1 c2
| VarKey id1, VarKey id2 -> Id.equal id1 id2
| RelKey n1, RelKey n2 -> Int.equal n1 n2
| EvarKey evk1, EvarKey evk2 -> Evar.equal evk1 evk2
| _ -> false

type atom =
  | Aid of id_key
  | Aind of inductive
  | Asort of Sorts.t

(* Zippers *)

type zipper =
  | Zapp of arguments
  | Zfix of vfix*arguments  (* Possibly empty *)
  | Zswitch of vswitch
  | Zproj of int (* index of the projection as in Projection.Repr *)

type stack = zipper list

type to_update = values
type accumulator = atom * stack

type kind = (values, accumulator, vfun, vprod, vfix * arguments option, vcofix * to_update * arguments option, vblock) Values.kind

(* Functions over arguments *)
let nargs : arguments -> int = fun args -> Obj.size (Obj.repr args) - 3
let arg args i =
  if  0 <= i && i < (nargs args) then
    val_of_obj (Obj.field (Obj.repr args) (i + 3))
  else invalid_arg
                ("Vm.arg size = "^(string_of_int (nargs args))^
                 " acces "^(string_of_int i))

(*************************************************)
(* Destructors ***********************************)
(*************************************************)

let uni_instance (v : values) : UVars.Instance.t = Obj.magic v

let rec whd_accu a stk =
  let stk =
    if Int.equal (Obj.size a) 3 then stk
    else Zapp (Obj.obj a) :: stk in
  let at = Obj.field a 2 in
  match Obj.tag at with
  | i when Int.equal i type_atom_tag ->
     begin match stk with
     | [] -> Vaccu (Obj.magic at, stk)
     | [Zapp args] ->
        let () = assert (Int.equal (nargs args) 1) in
        let inst = uni_instance (arg args 0) in
        let s = Obj.obj (Obj.field at 0) in
        let s = UVars.subst_instance_sort inst s in
        Vaccu (Asort s, [])
     | _ -> assert false
     end
  | i when i <= max_atom_tag ->
      Vaccu (Obj.magic at, stk)
  | i when Int.equal i proj_tag ->
     let zproj = Zproj (Obj.obj (Obj.field at 0)) in
     whd_accu (Obj.field at 1) (zproj :: stk)
  | i when Int.equal i fix_app_tag ->
      let fa = Obj.field at 1 in
      let zfix  =
        Zfix (Obj.obj (Obj.field fa 2), Obj.obj fa) in
      whd_accu (Obj.field at 0) (zfix :: stk)
  | i when Int.equal i switch_tag ->
      let zswitch = Zswitch (Obj.obj (Obj.field at 1)) in
      whd_accu (Obj.field at 0) (zswitch :: stk)
  | i when Int.equal i cofix_tag ->
      let vcfx = Obj.obj (Obj.field at 0) in
      let to_up = Obj.obj a in
      begin match stk with
      | []          -> Vcofix(vcfx, to_up, None)
      | [Zapp args] -> Vcofix(vcfx, to_up, Some args)
      | _           -> assert false
      end
  | i when Int.equal i cofix_evaluated_tag ->
      let vcofix = Obj.obj (Obj.field at 0) in
      let res = Obj.obj a in
      begin match stk with
      | []          -> Vcofix(vcofix, res, None)
      | [Zapp args] -> Vcofix(vcofix, res, Some args)
      | _           -> assert false
      end
  | tg ->
    CErrors.anomaly
      Pp.(strbrk "Failed to parse VM value. Tag = " ++ int tg ++ str ".")

[@@@warning "-37"]
type vm_closure_kind =
  | VCfun (** closure, or fixpoint applied past the recursive argument *)
  | VCfix (** unapplied fixpoint *)
  | VCfix_partial (** partially applied fixpoint, but not sufficiently for recursion *)
  | VCaccu (** accumulator *)
[@@@warning "+37"]

external kind_of_closure : Obj.t -> vm_closure_kind = "rocq_kind_of_closure"
external is_accumulate : tcode -> bool = "rocq_is_accumulate_code"
external int_tcode : tcode -> int -> int = "rocq_int_tcode"
external accumulate : unit -> tcode = "rocq_accumulate"
external set_bytecode_field : Obj.t -> int -> tcode -> unit = "rocq_set_bytecode_field"
let accumulate = accumulate ()

let whd_val (v: values) =
  let o = Obj.repr v in
  if Obj.is_int o then Vconst (Obj.obj o)
  else
    let tag = Obj.tag o in
    if Int.equal tag 0 then
      if Int.equal (Obj.size o) 1 then
        Varray (Obj.obj o)
      else Vprod (Obj.obj o)
    else if Int.equal tag Obj.closure_tag && is_accumulate (fun_code o) then
      whd_accu o []
    else if Int.equal tag Obj.closure_tag || Int.equal tag Obj.infix_tag then
      match kind_of_closure o with
      | VCfun -> Vfun (Obj.obj o)
      | VCfix -> Vfix (Obj.obj o, None)
      | VCfix_partial -> Vfix (Obj.obj (Obj.field o 2), Some (Obj.obj o))
      | VCaccu -> Vaccu (Aid (RelKey (int_tcode (fun_code o) 1)), [])
    else if Int.equal tag Obj.custom_tag then Vint64 (Obj.magic v)
    else if Int.equal tag Obj.double_tag then Vfloat64 (Obj.magic v)
    else if Int.equal tag Obj.string_tag then Vstring (Obj.magic v)
    else
      Vblock (Obj.obj o)

(**********************************************)
(* Constructors *******************************)
(**********************************************)

let obj_of_atom : atom -> Obj.t =
  fun a ->
    let res = Obj.new_block Obj.closure_tag 3 in
    set_bytecode_field res 0 accumulate;
    Obj.set_field res 1 (Obj.repr 2);
    Obj.set_field res 2 (Obj.repr a);
    res

(* obj_of_str_const : structured_constant -> Obj.t *)
let obj_of_str_const str =
  match str with
  | Const_sort s -> obj_of_atom (Asort s)
  | Const_ind ind -> obj_of_atom (Aind ind)
  | Const_evar e -> obj_of_atom (Aid (EvarKey e))
  | Const_b0 tag -> Obj.repr tag
  | Const_univ_instance u -> Obj.repr u
  | Const_val v -> Obj.repr v
  | Const_uint i -> Obj.repr i
  | Const_float f -> Obj.repr f
  | Const_string s -> Obj.repr s

let val_of_block tag (args : structured_values array) =
  let nargs = Array.length args in
  let r = Obj.new_block tag nargs in
  for i = 0 to nargs - 1 do
    Obj.set_field r i (Obj.repr args.(i))
  done;
  (Obj.magic r : structured_values)

let val_of_obj o = ((Obj.obj o) : values)

let val_of_str_const str = val_of_obj (obj_of_str_const str)

let val_of_atom a = val_of_obj (obj_of_atom a)

let val_of_int i = (Obj.magic i : values)

let val_of_uint i = (Obj.magic i : structured_values)

let val_of_float f = (Obj.magic f : structured_values)

let val_of_string s = (Obj.magic s : structured_values)

let atom_of_proj kn v =
  let r = Obj.new_block proj_tag 2 in
  Obj.set_field r 0 (Obj.repr kn);
  Obj.set_field r 1 (Obj.repr v);
  ((Obj.obj r) : atom)

let val_of_proj kn v =
  val_of_atom (atom_of_proj kn v)

module IdKeyHash =
struct
  type t = id_key
  let equal = eq_id_key
  open Hashset.Combine
  let hash : t -> tag = function
  | ConstKey c -> combinesmall 1 (Constant.CanOrd.hash c)
  | VarKey id -> combinesmall 2 (Id.hash id)
  | RelKey i -> combinesmall 3 (Int.hash i)
  | EvarKey evk -> combinesmall 4 (Evar.hash evk)
end

module KeyTable = Hashtbl.Make(IdKeyHash)

let idkey_tbl = KeyTable.create 31

let val_of_idkey key =
  try KeyTable.find idkey_tbl key
  with Not_found ->
    let v = val_of_atom (Aid key) in
    KeyTable.add idkey_tbl key v;
    v

let val_of_rel k = val_of_idkey (RelKey k)

let val_of_named id = val_of_idkey (VarKey id)

let val_of_constant c = val_of_idkey (ConstKey c)

let val_of_evar evk = val_of_idkey (EvarKey evk)

external val_of_annot_switch : annot_switch -> values = "%identity"

(*************************************************)
(** Operations manipulating data types ***********)
(*************************************************)

(* Functions over products *)

let dom : vprod -> values = fun p -> val_of_obj (Obj.field (Obj.repr p) 0)
let codom : vprod -> vfun = fun p -> (Obj.obj (Obj.field (Obj.repr p) 1))

(* Functions over vfun *)

external closure_arity : vfun -> int = "rocq_closure_arity"

(* Functions over fixpoint *)

external current_fix : vfix -> int = "rocq_current_fix"
external shift_fix : vfix -> int -> vfix = "rocq_shift_fix"
external last_fix : vfix -> vfix = "rocq_last_fix"
external tcode_array : tcode_array -> tcode array = "rocq_tcode_array"

let first_fix o = shift_fix o (- current_fix o)
let fix_env v = (Obj.magic (last_fix v) : vm_env)

let last o = (Obj.field o (Obj.size o - 1))
let fix_types (v:vfix) = tcode_array (Obj.magic (last (Obj.repr v)) : tcode_array)
let cofix_types (v:vcofix) = tcode_array (Obj.magic (last (Obj.repr v)) : tcode_array)

let unsafe_rec_arg fb i = int_tcode (Obj.magic (shift_fix fb i)) 1

let rec_args vf =
  let fb = first_fix vf in
  let size = Obj.size (last (Obj.repr fb)) in
  Array.init size (unsafe_rec_arg fb)

exception FALSE

let check_fix f1 f2 =
  let i1, i2 = current_fix f1, current_fix f2 in
  (* Checking starting point *)
  if i1 = i2 then
    let fb1,fb2 = first_fix f1, first_fix f2 in
    let n = Obj.size (last (Obj.repr fb1)) in
    (* Checking number of definitions *)
    if n = Obj.size (last (Obj.repr fb2)) then
      (* Checking recursive arguments *)
      try
        for i = 0 to n - 1 do
          if unsafe_rec_arg fb1 i <> unsafe_rec_arg fb2 i
          then raise FALSE
        done;
        true
      with FALSE -> false
    else false
  else false

let atom_rel : atom array ref =
  let init i = Aid (RelKey i) in
  ref (Array.init 40 init)

let get_atom_rel () = !atom_rel

let realloc_atom_rel n =
  let n = min (2 * n + 0x100) Sys.max_array_length in
  let init i = Aid (RelKey i) in
  let ans = Array.init n init in
  atom_rel := ans

let relaccu_tbl =
  let len = Array.length !atom_rel in
  ref (Array.init len mkAccuCode)

let relaccu_code i =
  let len = Array.length !relaccu_tbl in
  if i < len then !relaccu_tbl.(i)
  else
    begin
      realloc_atom_rel i;
      let nl = Array.length !atom_rel in
      relaccu_tbl :=
        Array.init nl
          (fun j -> if j < len then !relaccu_tbl.(j) else mkAccuCode j);
      !relaccu_tbl.(i)
    end

let mk_fix_body k ndef fb =
  let e = Obj.dup (Obj.repr fb) in
  let env = Obj.repr (fix_env (Obj.obj e)) in
  for i = 0 to ndef - 1 do
    set_bytecode_field e (3 * i) (relaccu_code (k + i))
  done;
  let fix_body i =
    let c = offset_tcode (Obj.magic (shift_fix fb i)) 2 in
    let res = Obj.new_block Obj.closure_tag 3 in
    set_bytecode_field res 0 c;
    Obj.set_field res 1 (Obj.repr 2);
    Obj.set_field res 2 env;
    ((Obj.obj res) : vfun)  in
  Array.init ndef fix_body

(* Functions over vcofix *)

let get_fcofix vcf i =
  match whd_val (Obj.obj (Obj.field (Obj.repr vcf) (i+2))) with
  | Vcofix(vcfi, _, _) -> vcfi
  | _ -> assert false

let current_cofix vcf =
  let ndef = Obj.size (last (Obj.repr vcf)) in
  let rec find_cofix pos =
    if pos < ndef then
      if get_fcofix vcf pos == vcf then pos
      else find_cofix (pos+1)
    else raise Not_found in
  try find_cofix 0
  with Not_found -> assert false

let check_cofix vcf1 vcf2 =
  (current_cofix vcf1 = current_cofix vcf2) &&
  (Obj.size (last (Obj.repr vcf1)) = Obj.size (last (Obj.repr vcf2)))

let mk_cofix_body apply_varray k ndef vcf =
  let e = Obj.dup (Obj.repr vcf) in
  for i = 0 to ndef - 1 do
    Obj.set_field e (i+2) (Obj.repr (val_of_rel (k+i)))
  done;

  let cofix_body i =
    let vcfi = get_fcofix vcf i in
    let c = Obj.field (Obj.repr vcfi) 0 in
    Obj.set_field e 0 c;
    let atom = Obj.new_block cofix_tag 1 in
    let self = obj_of_atom (Obj.obj atom) in
    apply_varray (Obj.obj e) [|Obj.obj self|] in
  Array.init ndef cofix_body

(* Functions over vblock *)

let btag : vblock -> int = fun b -> Obj.tag (Obj.repr b)
let bsize : vblock -> int = fun b -> Obj.size (Obj.repr b)
let bfield b i =
  if 0 <= i && i < (bsize b) then val_of_obj (Obj.field (Obj.repr b) i)
  else invalid_arg "Vm.bfield"


(* Functions over vswitch *)

let check_switch sw1 sw2 = sw1.sw_annot.rtbl = sw2.sw_annot.rtbl

let branch_arg k (tag,arity) =
  if Int.equal arity 0 then  ((Obj.magic tag):values)
  else
    let b, ofs =
      if tag < Obj.last_non_constant_constructor_tag then Obj.new_block tag arity, 0
      else
        let b = Obj.new_block Obj.last_non_constant_constructor_tag (arity+1) in
        Obj.set_field b 0 (Obj.repr (tag-Obj.last_non_constant_constructor_tag));
        b,1 in
    for i = ofs to ofs + arity - 1 do
      Obj.set_field b i (Obj.repr (val_of_rel (k+i)))
    done;
    val_of_obj b

(* Printing *)

let rec pr_atom a =
  Pp.(match a with
  | Aid c -> str "Aid(" ++ (match c with
                            | ConstKey c -> Constant.print c
                            | RelKey i -> str "#" ++ int i
                            | _ -> str "...") ++ str ")"
  | Aind (mi,i) -> str "Aind(" ++ MutInd.print mi ++ str "#" ++ int i ++ str ")"
  | Asort _ -> str "Asort(")
and pr_kind w =
  let open Pp in
  match w with
  | Vprod _ -> str "Vprod"
  | Vfun _ -> str "Vfun"
  | Vfix _ -> str "Vfix"
  | Vcofix _ -> str "Vcofix"
  | Vconst i -> str "Vconst(" ++ int i ++ str ")"
  | Vblock _b -> str "Vblock"
  | Vint64 i -> i |> Format.sprintf "Vint64(%LiL)" |> str
  | Vfloat64 f -> str "Vfloat64(" ++ str (Float64.(to_string (of_float f))) ++ str ")"
  | Vstring s -> Pstring.to_string s |> Format.sprintf "Vstring(%S)" |> str
  | Varray _ -> str "Varray"
  | Vaccu (a, stk) -> str "Vaccu(" ++ pr_atom a ++ str ", " ++ pr_stack stk ++ str ")"
and pr_stack stk =
  Pp.(match stk with
      | [] -> str "[]"
      | s :: stk -> pr_zipper s ++ str " :: " ++ pr_stack stk)
and pr_zipper z =
  Pp.(match z with
  | Zapp args -> str "Zapp(len = " ++ int (nargs args) ++ str ")"
  | Zfix (_f,args) -> str "Zfix(..., len=" ++ int (nargs args) ++ str ")"
  | Zswitch _s -> str "Zswitch(...)"
  | Zproj n -> str "Zproj(" ++ int n ++ str ")")

(** Primitives implemented in OCaml *)

let parray_make = Obj.magic Parray.make
let parray_get = Obj.magic Parray.get
let parray_get_default = Obj.magic Parray.default
let parray_set = Obj.magic Parray.set
let parray_copy = Obj.magic Parray.copy
let parray_length = Obj.magic Parray.length

let pstring_make = Obj.magic Pstring.make
let pstring_length = Obj.magic Pstring.length
let pstring_get = Obj.magic Pstring.get
let pstring_sub = Obj.magic Pstring.sub
let pstring_cat = Obj.magic Pstring.cat
let pstring_compare = Obj.magic @@ fun x y ->
  match Pstring.compare x y with 0 -> 0 | i when i < 0 -> 1 | _ -> 2
