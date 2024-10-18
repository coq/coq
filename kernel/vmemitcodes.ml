(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Author: Benjamin Grégoire as part of the bytecode-based virtual reduction
   machine, Oct 2004 *)
(* Extension: Arnaud Spiwack (support for native arithmetic), May 2005 *)

open Names
open Vmvalues
open Vmbytecodes
open Vmopcodes
open Mod_subst
open CPrimitives

type emitcodes = String.t

external tcode_of_code : Bytes.t -> Vmvalues.tcode = "rocq_tcode_of_code"

(* Relocation information *)
type reloc_info =
  | Reloc_annot of annot_switch
  | Reloc_const of structured_constant
  | Reloc_getglobal of Names.Constant.t
  | Reloc_caml_prim of caml_prim

let eq_reloc_info r1 r2 = match r1, r2 with
| Reloc_annot sw1, Reloc_annot sw2 -> eq_annot_switch sw1 sw2
| Reloc_annot _, _ -> false
| Reloc_const c1, Reloc_const c2 -> eq_structured_constant c1 c2
| Reloc_const _, _ -> false
| Reloc_getglobal c1, Reloc_getglobal c2 -> Constant.CanOrd.equal c1 c2
| Reloc_getglobal _, _ -> false
| Reloc_caml_prim p1, Reloc_caml_prim p2 -> CPrimitives.equal (caml_prim_to_prim p1) (caml_prim_to_prim p2)
| Reloc_caml_prim _, _ -> false

let hash_reloc_info r =
  let open Hashset.Combine in
  match r with
  | Reloc_annot sw -> combinesmall 1 (hash_annot_switch sw)
  | Reloc_const c -> combinesmall 2 (hash_structured_constant c)
  | Reloc_getglobal c -> combinesmall 3 (Constant.CanOrd.hash c)
  | Reloc_caml_prim p -> combinesmall 4 (CPrimitives.hash (caml_prim_to_prim p))

module RelocTable = Hashtbl.Make(struct
  type t = reloc_info
  let equal = eq_reloc_info
  let hash = hash_reloc_info
end)

module Positions :
sig
  type t
  val of_list : int list -> t
  val iter : (int -> unit) -> t -> unit
end =
struct

type t = string
(* Represent an ordered set of 32-bit integers as an array of successive diffs.
   We use furthermore an approach where smaller integers use less bytes. Numbers
   smaller than 255 are stored into one byte. Otherwise we use the byte 0x00 to
   signal that we store the integer in the next 4 bytes. This is a cheap way to
   compact this data. *)

let output buf n =
  if n <= 0xFF then Buffer.add_uint8 buf n
  else
    let () = Buffer.add_uint8 buf 0x00 in
    Buffer.add_int32_be buf (Int32.of_int n)

let input s pos =
  let c = Char.code s.[!pos] in
  if Int.equal c 0x00 then
    (* TODO: use String.get_int32_be when available in OCaml 4.13.0 *)
    let c1 = Char.code s.[!pos + 1] in
    let c2 = Char.code s.[!pos + 2] in
    let c3 = Char.code s.[!pos + 3] in
    let c4 = Char.code s.[!pos + 4] in
    let () = pos := !pos + 5 in
    (c1 lsl 24) lor (c2 lsl 16) lor (c3 lsl 8) lor c4
  else
    let () = pos := !pos + 1 in
    c

let of_list l = match l with
| [] -> ""
| n :: l ->
  let buf = Buffer.create 16 in
  let () = assert (0 < n) in
  let () = output buf n in
  let rec aux cur l = match l with
  | [] -> ()
  | n :: l ->
    let () = assert (cur < n) in
    let () = output buf (n - cur) in
    aux n l
  in
  let () = aux n l in
  Buffer.contents buf

let iter f s =
  let pos = ref 0 in
  let len = String.length s in
  let cur = ref 0 in
  while !pos < len do
    let n = input s pos in
    let () = cur := n + !cur in
    f !cur
  done

end

module NonSubstReloc =
struct

(** Relocations that are left untouched by module substitution. To reduce the
    memory footprint, this data is kept on the VM segment. *)
type t =
| SReloc_Const_sort of Sorts.t
| SReloc_Const_evar of Evar.t
| SReloc_Const_b0 of tag
| SReloc_Const_univ_instance of UVars.Instance.t
| SReloc_Const_val of structured_values
| SReloc_Const_uint of Uint63.t
| SReloc_Const_float of Float64.t
| SReloc_Const_string of Pstring.t
| SReloc_annot of annot_switch
| SReloc_caml_prim of caml_prim

let to_reloc = function
| SReloc_Const_sort s -> Reloc_const (Const_sort s)
| SReloc_Const_evar e -> Reloc_const (Const_evar e)
| SReloc_Const_b0 tag -> Reloc_const (Const_b0 tag)
| SReloc_Const_univ_instance u -> Reloc_const (Const_univ_instance u)
| SReloc_Const_val v -> Reloc_const (Const_val v)
| SReloc_Const_uint i -> Reloc_const (Const_uint i)
| SReloc_Const_float f -> Reloc_const (Const_float f)
| SReloc_Const_string s -> Reloc_const (Const_string s)
| SReloc_annot annot -> Reloc_annot annot
| SReloc_caml_prim prm -> Reloc_caml_prim prm

end

module Reloc =
struct

type t =
| SReloc_Const_ind of inductive
| SReloc_getglobal of Names.Constant.t
| SReloc_indirect of int (* index in the non-subst table *)

let to_reloc table = function
| SReloc_Const_ind ind -> Reloc_const (Const_ind ind)
| SReloc_getglobal cst -> Reloc_getglobal cst
| SReloc_indirect i -> NonSubstReloc.to_reloc table.(i)

let subst s reloc = match reloc with
| SReloc_Const_ind ind ->
  let ind' = Mod_subst.subst_ind s ind in
  if ind' == ind then reloc else SReloc_Const_ind ind'
| SReloc_getglobal cst ->
  let cst' = Mod_subst.subst_constant s cst in
  if cst' == cst then reloc else SReloc_getglobal cst'
| SReloc_indirect _ -> reloc

end

(* Most of the words of the bytecode are comprised of a byte followed by three
   nul bytes. It is compressed as follows. In the common case, only the byte is
   output. In the other cases (or when the byte is too large), 255 is output
   followed by the four original bytes, or 254 is output followed by the first
   three original bytes (assuming the fourth is nul), or 253 or 252. *)

let compress_code src sz =
  let buf = Buffer.create (sz * 3 / 8) in
  for i = 0 to sz / 4 - 1 do
    let c01 = Bytes.get_uint16_le src (i * 4) in
    let c23 = Bytes.get_uint16_le src (i * 4 + 2) in
    if c23 = 0 then
      if c01 < 252 then
        Buffer.add_uint8 buf c01
      else
        begin
          Buffer.add_uint8 buf 253;
          Buffer.add_uint16_le buf c01;
        end
    else if c23 = 0xffff && c01 >= 0xff00 then
      begin
        Buffer.add_uint8 buf 252;
        Buffer.add_uint8 buf c01;
      end
    else if c23 <= 0xff then
      begin
        Buffer.add_uint8 buf 254;
        Buffer.add_uint16_le buf c01;
        Buffer.add_uint8 buf c23;
      end
    else
      begin
        Buffer.add_uint8 buf 255;
        Buffer.add_uint16_le buf c01;
        Buffer.add_uint16_le buf c23;
      end
  done;
  Buffer.contents buf

let decompress_code src =
  let sz = String.length src in
  let buf = Buffer.create (sz * 4) in
  (* TODO: remove the following two lines once the minimal version of OCaml is 4.13 *)
  let module String = Bytes in
  let src = String.unsafe_of_string src in
  let i = ref 0 in
  while !i < sz do
    let c01, c23 =
      match String.get src !i with
      | '\000' .. '\251' as c ->
          i := !i + 1;
          (Char.code c, 0)
      | '\252' ->
          i := !i + 2;
          (String.get_uint8 src (!i - 1) + 0xff00, 0xffff)
      | '\253' ->
          i := !i + 3;
          (String.get_uint16_le src (!i - 2), 0)
      | '\254' ->
          i := !i + 4;
          (String.get_uint16_le src (!i - 3), String.get_uint8 src (!i - 1))
      | '\255' ->
          i := !i + 5;
          (String.get_uint16_le src (!i - 4), String.get_int16_le src (!i - 2))
    in
    Buffer.add_uint16_le buf c01;
    Buffer.add_uint16_le buf c23;
  done;
  Buffer.to_bytes buf

(** This data type is stored in vo files. *)

type patches = {
  reloc_infos : Reloc.t array;
}

type to_patch = {
  tp_code : emitcodes;
  tp_fv : fv;
  tp_pos : Positions.t;
  tp_reloc : NonSubstReloc.t array;
}

let patch_int tp reloc =
  let buff = decompress_code tp.tp_code in
  let iter pos =
    let id = Bytes.get_int32_le buff pos in
    let reloc = reloc.(Int32.to_int id) in
    Bytes.set_int32_le buff pos (Int32.of_int reloc)
  in
  let () = Positions.iter iter tp.tp_pos in
  buff

let patch (tp, pl) f =
  let f r = f (Reloc.to_reloc tp.tp_reloc r) in
  let reloc = CArray.map_left f pl.reloc_infos in
  let buff = patch_int tp reloc in
  tcode_of_code buff, tp.tp_fv

(* Buffering of bytecode *)

type label_definition =
    Label_defined of int
  | Label_undefined of (int * int) list

type env = {
  mutable out_buffer : Bytes.t;
  mutable out_position : int;
  mutable reloc_pos : int list;
  mutable reloc_id : int;
  mutable label_table : label_definition array;
  (* i-th table element = Label_defined n means that label i was already
     encountered and lives at offset n
     i-th table element = Label_undefined l means that the label was not
     encountered yet, first integer is the location of the value to be patched
     in the string, seconed one is its origin *)
  reloc_info : int RelocTable.t;
}

let out_word env b1 b2 b3 b4 =
  let p = env.out_position in
  let buf =
    let len = Bytes.length env.out_buffer in
    if p + 3 < len then env.out_buffer
    else
      let new_len = min (Sys.max_string_length) (2 * len) in
      (* Not the right exception... *)
      let () = if not (p + 3 < new_len) then Vmerrors.too_large_code() in
      let new_buffer = Bytes.create new_len in
      let () = Bytes.blit env.out_buffer 0 new_buffer 0 len in
      let () = env.out_buffer <- new_buffer in
      new_buffer
  in
  let () = Bytes.set_uint8 buf p b1 in
  let () = Bytes.set_uint8 buf (p + 1) b2 in
  let () = Bytes.set_uint8 buf (p + 2) b3 in
  let () = Bytes.set_uint8 buf (p + 3) b4 in
  env.out_position <- p + 4

let out env opcode =
  out_word env opcode 0 0 0

let is_immed i = Uint63.le (Uint63.of_int i) Uint63.maxuint31

(* Detect whether the current value of the accu register is no longer
   needed (i.e., the register is written before being read). If so, the
   register can be used freely; no need to save and restore it. *)
let is_accu_dead = function
  | [] -> false
  | c :: _ ->
      match c with
      | Kacc _ | Kenvacc _ | Kconst _ | Koffsetclosure _ | Kgetglobal _ -> true
      | _ -> false

let out_int env n =
  out_word env n (n asr 8) (n asr 16) (n asr 24)

(* Handling of local labels and backpatching *)

let extend_label_table env needed =
  let new_size = ref(Array.length env.label_table) in
  while needed >= !new_size do new_size := 2 * !new_size done;
  let new_table = Array.make !new_size (Label_undefined []) in
  Array.blit env.label_table 0 new_table 0 (Array.length env.label_table);
  env.label_table <- new_table

let backpatch env (pos, orig) =
  let displ = (env.out_position - orig) asr 2 in
  Bytes.set_int32_le env.out_buffer pos (Int32.of_int displ)

let define_label env lbl =
  if lbl >= Array.length env.label_table then extend_label_table env lbl;
  match (env.label_table).(lbl) with
    Label_defined _ ->
      raise(Failure "CEmitcode.define_label")
  | Label_undefined patchlist ->
      List.iter (fun p -> backpatch env p) patchlist;
      (env.label_table).(lbl) <- Label_defined env.out_position

let out_label_with_orig env orig lbl =
  if lbl >= Array.length env.label_table then extend_label_table env lbl;
  match (env.label_table).(lbl) with
    Label_defined def ->
      out_int env ((def - orig) asr 2)
  | Label_undefined patchlist ->
        (env.label_table).(lbl) <-
          Label_undefined((env.out_position, orig) :: patchlist);
      out_int env 0

let out_label env l = out_label_with_orig env env.out_position l

(* Relocation information *)

let enter env info =
  let pos = env.out_position in
  let () = env.reloc_pos <- pos :: env.reloc_pos in
  try RelocTable.find env.reloc_info info
  with Not_found ->
    let id = env.reloc_id in
    let () = env.reloc_id <- id + 1 in
    let () = RelocTable.add env.reloc_info info id in
    id

let slot_for env r = out_int env (enter env r)

let slot_for_const env c = slot_for env (Reloc_const c)
let slot_for_annot env a = slot_for env (Reloc_annot a)
let slot_for_getglobal env p = slot_for env (Reloc_getglobal p)
let slot_for_caml_prim env op = slot_for env (Reloc_caml_prim op)

(* Emission of one instruction *)

let check_prim_op = function
  | Int63head0     -> opCHECKHEAD0INT63
  | Int63tail0     -> opCHECKTAIL0INT63
  | Int63add       -> opCHECKADDINT63
  | Int63sub       -> opCHECKSUBINT63
  | Int63mul       -> opCHECKMULINT63
  | Int63div       -> opCHECKDIVINT63
  | Int63mod       -> opCHECKMODINT63
  | Int63divs      -> opCHECKDIVSINT63
  | Int63mods      -> opCHECKMODSINT63
  | Int63lsr       -> opCHECKLSRINT63
  | Int63lsl       -> opCHECKLSLINT63
  | Int63asr       -> opCHECKASRINT63
  | Int63land      -> opCHECKLANDINT63
  | Int63lor       -> opCHECKLORINT63
  | Int63lxor      -> opCHECKLXORINT63
  | Int63addc      -> opCHECKADDCINT63
  | Int63subc      -> opCHECKSUBCINT63
  | Int63addCarryC -> opCHECKADDCARRYCINT63
  | Int63subCarryC -> opCHECKSUBCARRYCINT63
  | Int63mulc      -> opCHECKMULCINT63
  | Int63diveucl   -> opCHECKDIVEUCLINT63
  | Int63div21     -> opCHECKDIV21INT63
  | Int63addMulDiv -> opCHECKADDMULDIVINT63
  | Int63eq        -> opCHECKEQINT63
  | Int63lt        -> opCHECKLTINT63
  | Int63le        -> opCHECKLEINT63
  | Int63lts       -> opCHECKLTSINT63
  | Int63les       -> opCHECKLESINT63
  | Int63compare   -> opCHECKCOMPAREINT63
  | Int63compares  -> opCHECKCOMPARESINT63
  | Float64opp     -> opCHECKOPPFLOAT
  | Float64abs     -> opCHECKABSFLOAT
  | Float64eq      -> opCHECKEQFLOAT
  | Float64lt      -> opCHECKLTFLOAT
  | Float64le      -> opCHECKLEFLOAT
  | Float64compare -> opCHECKCOMPAREFLOAT
  | Float64equal   -> opCHECKEQUALFLOAT
  | Float64classify -> opCHECKCLASSIFYFLOAT
  | Float64add     -> opCHECKADDFLOAT
  | Float64sub     -> opCHECKSUBFLOAT
  | Float64mul     -> opCHECKMULFLOAT
  | Float64div     -> opCHECKDIVFLOAT
  | Float64sqrt    -> opCHECKSQRTFLOAT
  | Float64ofUint63 -> opCHECKFLOATOFINT63
  | Float64normfr_mantissa -> opCHECKFLOATNORMFRMANTISSA
  | Float64frshiftexp -> opCHECKFRSHIFTEXP
  | Float64ldshiftexp -> opCHECKLDSHIFTEXP
  | Float64next_up    -> opCHECKNEXTUPFLOAT
  | Float64next_down  -> opCHECKNEXTDOWNFLOAT
  | Arraymake | Arrayget | Arrayset | Arraydefault | Arraycopy | Arraylength
  | Stringmake | Stringlength | Stringget | Stringsub | Stringcat | Stringcompare
    -> assert false

let check_caml_prim_op = function
| CAML_Arraymake -> opCHECKCAMLCALL2_1
| CAML_Arrayget -> opCHECKCAMLCALL2
| CAML_Arrayset -> opCHECKCAMLCALL3_1
| CAML_Arraydefault | CAML_Arraycopy | CAML_Arraylength -> opCHECKCAMLCALL1
| CAML_Stringmake -> opCHECKCAMLCALL2
| CAML_Stringlength -> opCHECKCAMLCALL1
| CAML_Stringget -> opCHECKCAMLCALL2
| CAML_Stringsub -> opCHECKCAMLCALL3
| CAML_Stringcat | CAML_Stringcompare -> opCHECKCAMLCALL2

let inplace_prim_op = function
  | Float64next_up | Float64next_down -> true
  | _ -> false

let check_prim_op_inplace = function
  | Float64next_up   -> opCHECKNEXTUPFLOATINPLACE
  | Float64next_down -> opCHECKNEXTDOWNFLOATINPLACE
  | _ -> assert false

let emit_instr env = function
  | Klabel lbl -> define_label env lbl
  | Kacc n ->
      if n < 8 then out env(opACC0 + n) else (out env opACC; out_int env n)
  | Kenvacc n ->
      if n >= 0 && n <= 3
      then out env(opENVACC0 + n)
      else (out env opENVACC; out_int env n)
  | Koffsetclosure ofs ->
      if Int.equal ofs 0 || Int.equal ofs 1
      then out env (opOFFSETCLOSURE0 + ofs)
      else (out env opOFFSETCLOSURE; out_int env ofs)
  | Kpush ->
      out env opPUSH
  | Kpop n ->
      out env opPOP; out_int env n
  | Kpush_retaddr lbl ->
      out env opPUSH_RETADDR; out_label env lbl
  | Kshort_apply n ->
      assert (1 <= n && n <= 4);
      out env(opAPPLY1 + n - 1)
  | Kapply n ->
      out env opAPPLY; out_int env n
  | Kappterm(n, sz) ->
      if n < 4 then (out env(opAPPTERM1 + n - 1); out_int env sz)
               else (out env opAPPTERM; out_int env n; out_int env sz)
  | Kreturn n ->
      out env opRETURN; out_int env n
  | Kjump ->
      out env opRETURN; out_int env 0
  | Krestart ->
      out env opRESTART
  | Kgrab n ->
      out env opGRAB; out_int env n
  | Kgrabrec(rec_arg) ->
      out env opGRABREC; out_int env rec_arg
  | Kclosure(lbl, n) ->
      out env opCLOSURE; out_int env n; out_label env lbl
  | Kclosurerec(nfv,init,lbl_types,lbl_bodies) ->
      out env opCLOSUREREC;out_int env (Array.length lbl_bodies);
      out_int env nfv; out_int env init;
      let org = env.out_position in
      Array.iter (out_label_with_orig env org) lbl_types;
      let org = env.out_position in
      Array.iter (out_label_with_orig env org) lbl_bodies
  | Kclosurecofix(nfv,init,lbl_types,lbl_bodies) ->
      out env opCLOSURECOFIX;out_int env (Array.length lbl_bodies);
      out_int env nfv; out_int env init;
      let org = env.out_position in
      Array.iter (out_label_with_orig env org) lbl_types;
      let org = env.out_position in
      Array.iter (out_label_with_orig env org) lbl_bodies
  | Kgetglobal q ->
      out env opGETGLOBAL; slot_for_getglobal env q
  | Ksubstinstance u ->
      out env opSUBSTINSTANCE; slot_for_const env (Const_univ_instance u)
  | Kconst (Const_b0 i) when is_immed i ->
      if i >= 0 && i <= 3
          then out env (opCONST0 + i)
          else (out env opCONSTINT; out_int env i)
  | Kconst c ->
      out env opGETGLOBAL; slot_for_const env c
  | Kmakeblock(n, t) ->
      if 0 < n && n < 4 then (out env(opMAKEBLOCK1 + n - 1); out_int env t)
      else (out env opMAKEBLOCK; out_int env n; out_int env t)
  | Kmakeswitchblock(typlbl,swlbl,annot,sz) ->
      out env opMAKESWITCHBLOCK;
      out_label env typlbl; out_label env swlbl;
      slot_for_annot env annot;out_int env sz
  | Kswitch (tbl_const, tbl_block) ->
      let lenb = Array.length tbl_block in
      let lenc = Array.length tbl_const in
      assert (lenb < 0x100 && lenc < 0x1000000);
      out env opSWITCH;
      out_word env lenb lenc (lenc asr 8) (lenc asr 16);
(*      out_int env (Array.length tbl_const + (Array.length tbl_block lsl 23)); *)
      let org = env.out_position in
      Array.iter (out_label_with_orig env org) tbl_const;
      Array.iter (out_label_with_orig env org) tbl_block
  | Kpushfields n ->
      out env opPUSHFIELDS;out_int env n
  | Kfield n ->
      if n <= 1 then out env (opGETFIELD0+n)
      else (out env opGETFIELD;out_int env n)
  | Ksetfield n ->
      out env opSETFIELD; out_int env n
  | Ksequence _ -> invalid_arg "Vmemitcodes.emit_instr"
  | Kproj p -> out env opPROJ; out_int env p
  | Kensurestackcapacity size -> out env opENSURESTACKCAPACITY; out_int env size
  | Kbranch lbl -> out env opBRANCH; out_label env lbl
  | Kprim (op, (q,_u)) ->
      out env (check_prim_op op);
      slot_for_getglobal env q

  | Kcamlprim (op,lbl) ->
    out env (check_caml_prim_op op);
    out_label env lbl;
    slot_for_caml_prim env op

  | Kstop -> out env opSTOP

(* Emission of a current list and remaining lists of instructions. Include some peephole optimization. *)

let rec emit env insns remaining = match insns with
  | [] ->
     (match remaining with
       [] -> ()
     | (first::rest) -> emit env first rest)
  (* Peephole optimizations *)
  | Kpush :: Kacc n :: c ->
      let rec aux n c nb =
        match c with
        | Kpush :: Kacc j :: c when j = n -> aux n c (nb + 1)
        | _ -> (nb, c) in
      let (nb, c') = aux n c 1 in
      if nb >= 3 || (nb >= 2 && n > 7)
      then (
        out env opPUSHACCMANY; out_int env n; out_int env nb;
        emit env c' remaining)
      else (
        if n = 0 then out env opPUSH
        else if n < 8 then out env (opPUSHACC1 + n - 1)
        else (out env opPUSHACC; out_int env n);
        emit env c remaining)
  | Kpush :: Kenvacc n :: c ->
      let rec aux n c nb =
        match c with
        | Kpush :: Kenvacc j :: c when j = n - nb -> aux n c (nb + 1)
        | _ -> (nb, c) in
      let (nb, c') = aux n c 1 in
      if nb >= 3 || (nb >= 2 && n > 3)
      then (
        out env opPUSHENVACCMANY; out_int env (n - nb + 1); out_int env nb;
        emit env c' remaining)
      else (
        if n >= 0 && n <= 3
        then out env (opPUSHENVACC0 + n)
        else (out env opPUSHENVACC; out_int env n);
        emit env c remaining)
  | Kpush :: Koffsetclosure ofs :: c ->
      if Int.equal ofs 0 || Int.equal ofs 1
      then out env(opPUSHOFFSETCLOSURE0 + ofs)
      else (out env opPUSHOFFSETCLOSURE; out_int env ofs);
      emit env c remaining
  | Kpush :: Kgetglobal id :: c ->
      out env opPUSHGETGLOBAL; slot_for_getglobal env id; emit env c remaining
  | Kpush :: Kconst (Const_b0 i) :: c when is_immed i ->
      if i >= 0 && i <= 3
      then out env (opPUSHCONST0 + i)
      else (out env opPUSHCONSTINT; out_int env i);
      emit env c remaining
  | Kpush :: Kconst const :: c ->
      out env opPUSHGETGLOBAL; slot_for_const env const;
      emit env c remaining
  | Kpushfields 1 :: c when is_accu_dead c ->
      out env opGETFIELD0;
      emit env (Kpush :: c) remaining
  | Kpop n :: Kjump :: c ->
      out env opRETURN; out_int env n; emit env c remaining
  | Ksequence c1 :: c ->
      emit env c1 (c :: remaining)
  | Kprim (op1, (q1, _)) :: Kprim (op2, (q2, _)) :: c when inplace_prim_op op2 ->
      out env (check_prim_op op1);
      slot_for_getglobal env q1;
      out env (check_prim_op_inplace op2);
      slot_for_getglobal env q2;
      emit env c remaining
  (* Default case *)
  | instr :: c ->
      emit_instr env instr; emit env c remaining

(* Substitution *)

let subst_patches subst p =
  let infos = CArray.Smart.map (fun r -> Reloc.subst subst r) p.reloc_infos in
  { reloc_infos = infos }

type 'a pbody_code =
  | BCdefined of bool array * 'a * patches
  | BCalias of Names.Constant.t
  | BCconstant

type body_code = to_patch pbody_code

let subst_body_code s = function
| BCdefined (m, x, tp) -> BCdefined (m, x, subst_patches s tp)
| BCalias cu -> BCalias (subst_constant s cu)
| BCconstant -> BCconstant

let to_memory fv code =
  let env = {
    out_buffer = Bytes.create 1024;
    out_position = 0;
    reloc_id = 0;
    reloc_pos = [];
    label_table = Array.make 16 (Label_undefined []);
    reloc_info = RelocTable.create 91;
  } in
  emit env code [];
  let code = compress_code env.out_buffer env.out_position in
  let code = CString.hcons code in
  let fold reloc id accu = (id, reloc) :: accu in
  let reloc = RelocTable.fold fold env.reloc_info [] in
  let reloc = List.sort (fun (id1, _) (id2, _) -> Int.compare id1 id2) reloc in
  let uid = ref 0 in
  let table = ref [] in
  let push r =
    let id = !uid in
    let () = table := r :: !table in
    let () = incr uid in
    Reloc.SReloc_indirect id
  in
  let map (_, r) =
    let open NonSubstReloc in
    match r with
    | Reloc_getglobal cst -> Reloc.SReloc_getglobal cst
    | Reloc_const (Const_ind ind) -> Reloc.SReloc_Const_ind ind
    | Reloc_annot annot -> push (SReloc_annot annot)
    | Reloc_caml_prim prm -> push (SReloc_caml_prim prm)
    | Reloc_const (Const_sort s) -> push (SReloc_Const_sort s)
    | Reloc_const (Const_evar e) -> push (SReloc_Const_evar e)
    | Reloc_const (Const_b0 tag) -> push (SReloc_Const_b0 tag)
    | Reloc_const (Const_univ_instance u) -> push (SReloc_Const_univ_instance u)
    | Reloc_const (Const_val v) -> push (SReloc_Const_val v)
    | Reloc_const (Const_uint i) -> push (SReloc_Const_uint i)
    | Reloc_const (Const_float f) -> push (SReloc_Const_float f)
    | Reloc_const (Const_string s) -> push (SReloc_Const_string s)
  in
  let reloc_infos = CArray.map_of_list map reloc in
  let positions = Positions.of_list (List.rev env.reloc_pos) in
  let reloc = { reloc_infos } in
  let to_patch = {
    tp_code = code;
    tp_fv = fv;
    tp_pos = positions;
    tp_reloc = CArray.rev_of_list !table;
  } in
  Array.iter (fun lbl ->
    (match lbl with
      Label_defined _ -> assert true
    | Label_undefined patchlist ->
        assert (patchlist = []))) env.label_table;
  (to_patch, reloc)
