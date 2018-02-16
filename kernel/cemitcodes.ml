(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Author: Benjamin Grégoire as part of the bytecode-based virtual reduction
   machine, Oct 2004 *)
(* Extension: Arnaud Spiwack (support for native arithmetic), May 2005 *)

open Names
open Constr
open Vmvalues
open Cbytecodes
open Copcodes
open Mod_subst
open CPrimitives

type emitcodes = String.t

external tcode_of_code : Bytes.t -> Vmvalues.tcode = "coq_tcode_of_code"

(* Relocation information *)
type reloc_info =
  | Reloc_annot of annot_switch
  | Reloc_const of structured_constant
  | Reloc_getglobal of Names.Constant.t
  | Reloc_proj_name of Projection.Repr.t

let eq_reloc_info r1 r2 = match r1, r2 with
| Reloc_annot sw1, Reloc_annot sw2 -> eq_annot_switch sw1 sw2
| Reloc_annot _, _ -> false
| Reloc_const c1, Reloc_const c2 -> eq_structured_constant c1 c2
| Reloc_const _, _ -> false
| Reloc_getglobal c1, Reloc_getglobal c2 -> Constant.equal c1 c2
| Reloc_getglobal _, _ -> false
| Reloc_proj_name p1, Reloc_proj_name p2 -> Projection.Repr.equal p1 p2
| Reloc_proj_name _, _ -> false

let hash_reloc_info r =
  let open Hashset.Combine in
  match r with
  | Reloc_annot sw -> combinesmall 1 (hash_annot_switch sw)
  | Reloc_const c -> combinesmall 2 (hash_structured_constant c)
  | Reloc_getglobal c -> combinesmall 3 (Constant.hash c)
  | Reloc_proj_name p -> combinesmall 4 (Projection.Repr.hash p)

module RelocTable = Hashtbl.Make(struct
  type t = reloc_info
  let equal = eq_reloc_info
  let hash = hash_reloc_info
end)

(** We use arrays for on-disk representation. On 32-bit machines, this means we
    can only have a maximum amount of about 4.10^6 relocations, which seems
    quite a lot, but potentially reachable if e.g. compiling big proofs. This
    would prevent VM computing with these terms on 32-bit architectures. Maybe
    we should use a more robust data structure? *)
type patches = {
  reloc_infos : (reloc_info * int array) array;
}

let patch_char4 buff pos c1 c2 c3 c4 = 
  Bytes.unsafe_set buff pos       c1;
  Bytes.unsafe_set buff (pos + 1) c2;
  Bytes.unsafe_set buff (pos + 2) c3;
  Bytes.unsafe_set buff (pos + 3) c4 
  
let patch1 buff pos n =
  patch_char4 buff pos 
    (Char.unsafe_chr n) (Char.unsafe_chr (n asr 8))  (Char.unsafe_chr (n asr 16))
    (Char.unsafe_chr (n asr 24))

let patch_int buff reloc =
  (* copy code *before* patching because of nested evaluations:
     the code we are patching might be called (and thus "concurrently" patched)
     and results in wrong results. Side-effects... *)
  let buff = Bytes.of_string buff in
  let iter (reloc, npos) = Array.iter (fun pos -> patch1 buff pos reloc) npos in
  let () = CArray.iter iter reloc in
  buff

let patch buff pl f =
  (** Order seems important here? *)
  let reloc = CArray.map (fun (r, pos) -> (f r, pos)) pl.reloc_infos in
  let buff = patch_int buff reloc in
  tcode_of_code buff

(* Buffering of bytecode *)

type label_definition =
    Label_defined of int
  | Label_undefined of (int * int) list

type env = {
  mutable out_buffer : Bytes.t;
  mutable out_position : int;
  mutable label_table : label_definition array;
  (* le ieme element de la table = Label_defined n signifie que l'on a
    deja rencontrer le label i et qu'il est a l'offset n.
                                = Label_undefined l signifie que l'on a
    pas encore rencontrer ce label, le premier entier indique ou est l'entier
    a patcher dans la string, le deuxieme son origine  *)
  reloc_info : int list RelocTable.t;
}

let out_word env b1 b2 b3 b4 =
  let p = env.out_position in
  if p >= Bytes.length env.out_buffer then begin
    let len = Bytes.length env.out_buffer in
    let new_len =
      if len <= Sys.max_string_length / 2
      then 2 * len
      else
	if len = Sys.max_string_length
	then invalid_arg "String.create"  (* Pas la bonne exception .... *)
	else Sys.max_string_length in
    let new_buffer = Bytes.create new_len in
    Bytes.blit env.out_buffer 0 new_buffer 0 len;
    env.out_buffer <- new_buffer
  end;
  patch_char4 env.out_buffer p (Char.unsafe_chr b1)
   (Char.unsafe_chr b2) (Char.unsafe_chr b3) (Char.unsafe_chr b4);
  env.out_position <- p + 4

let out env opcode =
  out_word env opcode 0 0 0

let is_immed i = Uint63.le (Uint63.of_int i) Uint63.maxuint31

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
  Bytes.set env.out_buffer  pos    @@ Char.unsafe_chr displ;
  Bytes.set env.out_buffer (pos+1) @@ Char.unsafe_chr (displ asr 8);
  Bytes.set env.out_buffer (pos+2) @@ Char.unsafe_chr (displ asr 16);
  Bytes.set env.out_buffer (pos+3) @@ Char.unsafe_chr (displ asr 24)

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
      (* spiwack: patchlist is supposed to be non-empty all the time
         thus I commented that out. If there is no problem I suggest
         removing it for next release (cur: 8.1) *)
      (*if patchlist = [] then *)
        (env.label_table).(lbl) <-
          Label_undefined((env.out_position, orig) :: patchlist);
      out_int env 0

let out_label env l = out_label_with_orig env env.out_position l

(* Relocation information *)

let enter env info =
  let pos = env.out_position in
  let old = try RelocTable.find env.reloc_info info with Not_found -> [] in
  RelocTable.replace env.reloc_info info (pos :: old)

let slot_for_const env c =
  enter env (Reloc_const c);
  out_int env 0

let slot_for_annot env a =
  enter env (Reloc_annot a);
  out_int env 0

let slot_for_getglobal env p =
  enter env (Reloc_getglobal p);
  out_int env 0

let slot_for_proj_name env p =
  enter env (Reloc_proj_name p);
  out_int env 0

(* Emission of one instruction *)

let nocheck_prim_op = function
  | Int63add -> opADDINT63
  | Int63sub -> opSUBINT63
  | Int63lt  -> opLTINT63
  | Int63le  -> opLEINT63
  | _ -> assert false


let check_prim_op = function
  | Int63head0     -> opCHECKHEAD0INT63
  | Int63tail0     -> opCHECKTAIL0INT63
  | Int63add       -> opCHECKADDINT63
  | Int63sub       -> opCHECKSUBINT63
  | Int63mul       -> opCHECKMULINT63
  | Int63div       -> opCHECKDIVINT63
  | Int63mod       -> opCHECKMODINT63
  | Int63lsr       -> opCHECKLSRINT63
  | Int63lsl       -> opCHECKLSLINT63
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
  | Int63compare   -> opCHECKCOMPAREINT63

let emit_instr env = function
  | Klabel lbl -> define_label env lbl
  | Kacc n ->
      if n < 8 then out env(opACC0 + n) else (out env opACC; out_int env n)
  | Kenvacc n ->
      if n >= 1 && n <= 4
      then out env(opENVACC1 + n - 1)
      else (out env opENVACC; out_int env n)
  | Koffsetclosure ofs ->
      if Int.equal ofs (-2) || Int.equal ofs 0 || Int.equal ofs 2
      then out env (opOFFSETCLOSURE0 + ofs / 2)
      else (out env opOFFSETCLOSURE; out_int env ofs)
  | Kpush ->
      out env opPUSH
  | Kpop n ->
      out env opPOP; out_int env n
  | Kpush_retaddr lbl ->
      out env opPUSH_RETADDR; out_label env lbl
  | Kapply n ->
      if n <= 4 then out env(opAPPLY1 + n - 1) else (out env opAPPLY; out_int env n)
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
  | Kconst (Const_b0 i) when is_immed i ->
      if i >= 0 && i <= 3
          then out env (opCONST0 + i)
          else (out env opCONSTINT; out_int env i)
  | Kconst c ->
      out env opGETGLOBAL; slot_for_const env c
  | Kmakeblock(n, t) ->
      if Int.equal n 0 then invalid_arg "emit_instr : block size = 0"
      else if n < 4 then (out env(opMAKEBLOCK1 + n - 1); out_int env t)
      else (out env opMAKEBLOCK; out_int env n; out_int env t)
  | Kmakeprod ->
      out env opMAKEPROD
  | Kmakeswitchblock(typlbl,swlbl,annot,sz) ->
      out env opMAKESWITCHBLOCK;
      out_label env typlbl; out_label env swlbl;
      slot_for_annot env annot;out_int env sz
  | Kswitch (tbl_const, tbl_block) ->
      let lenb = Array.length tbl_block in
      let lenc = Array.length tbl_const in
      assert (lenb < 0x100 && lenc < 0x1000000);
      out env opSWITCH;
      out_word env lenc (lenc asr 8) (lenc asr 16) (lenb);
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
      if n <= 1 then out env (opSETFIELD0+n)
      else (out env opSETFIELD;out_int env n)
  | Ksequence _ -> invalid_arg "Cemitcodes.emit_instr"
  | Kproj p -> out env opPROJ; out_int env (Projection.Repr.arg p); slot_for_proj_name env p
  | Kensurestackcapacity size -> out env opENSURESTACKCAPACITY; out_int env size
  | Kbranch lbl -> out env opBRANCH; out_label env lbl
  | Kprim (op,None) ->
      out env (nocheck_prim_op op)

  | Kprim(op,Some (q,_u)) ->
      out env (check_prim_op op);
      slot_for_getglobal env q

  | Kareint 1 -> out env opISINT
  | Kareint 2 -> out env opAREINT2;

  | Kstop -> out env opSTOP

  | Kareint _ -> assert false

(* Emission of a current list and remaining lists of instructions. Include some peephole optimization. *)

let rec emit env insns remaining = match insns with
  | [] -> 
     (match remaining with 
       [] -> () 
     | (first::rest) -> emit env first rest)
  (* Peephole optimizations *)
  | Kpush :: Kacc n :: c ->
      if n < 8 then out env(opPUSHACC0 + n) else (out env opPUSHACC; out_int env n);
      emit env c remaining
  | Kpush :: Kenvacc n :: c ->
      if n >= 1 && n <= 4
      then out env(opPUSHENVACC1 + n - 1)
      else (out env opPUSHENVACC; out_int env n);
      emit env c remaining
  | Kpush :: Koffsetclosure ofs :: c ->
      if Int.equal ofs (-2) || Int.equal ofs 0 || Int.equal ofs 2
      then out env(opPUSHOFFSETCLOSURE0 + ofs / 2)
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
  | Kpop n :: Kjump :: c ->
      out env opRETURN; out_int env n; emit env c remaining
  | Ksequence(c1,c2)::c ->
      emit env c1 (c2::c::remaining)
  (* Default case *)
  | instr :: c ->
      emit_instr env instr; emit env c remaining

(* Initialization *)

type to_patch = emitcodes * patches * fv

(* Substitution *)
let subst_strcst s sc =
  match sc with
  | Const_sort _ | Const_b0 _ | Const_univ_level _ | Const_val _ | Const_uint _ -> sc
  | Const_ind ind -> let kn,i = ind in Const_ind (subst_mind s kn, i)

let subst_reloc s ri =
  match ri with
  | Reloc_annot a ->
      let (kn,i) = a.ci.ci_ind in
      let ci = {a.ci with ci_ind = (subst_mind s kn,i)} in
      Reloc_annot {a with ci = ci}
  | Reloc_const sc -> Reloc_const (subst_strcst s sc)
  | Reloc_getglobal kn -> Reloc_getglobal (subst_constant s kn)
  | Reloc_proj_name p -> Reloc_proj_name (subst_proj_repr s p)

let subst_patches subst p =
  let infos = CArray.map (fun (r, pos) -> (subst_reloc subst r, pos)) p.reloc_infos in
  { reloc_infos = infos; }

let subst_to_patch s (code,pl,fv) =
  code, subst_patches s pl, fv

type body_code =
  | BCdefined of to_patch
  | BCalias of Names.Constant.t
  | BCconstant

type to_patch_substituted =
| PBCdefined of to_patch substituted
| PBCalias of Names.Constant.t substituted
| PBCconstant

let from_val = function
| BCdefined tp -> PBCdefined (from_val tp)
| BCalias cu -> PBCalias (from_val cu)
| BCconstant -> PBCconstant

let force = function
| PBCdefined tp -> BCdefined (force subst_to_patch tp)
| PBCalias cu -> BCalias (force subst_constant cu)
| PBCconstant -> BCconstant

let subst_to_patch_subst s = function
| PBCdefined tp -> PBCdefined (subst_substituted s tp)
| PBCalias cu -> PBCalias (subst_substituted s cu)
| PBCconstant -> PBCconstant

let repr_body_code = function
| PBCdefined tp ->
  let (s, tp) = repr_substituted tp in
  (s, BCdefined tp)
| PBCalias cu ->
  let (s, cu) = repr_substituted cu in
  (s, BCalias cu)
| PBCconstant -> (None, BCconstant)

let to_memory (init_code, fun_code, fv) =
  let env = {
    out_buffer = Bytes.create 1024;
    out_position = 0;
    label_table = Array.make 16 (Label_undefined []);
    reloc_info = RelocTable.create 91;
  } in
  emit env init_code [];
  emit env fun_code [];
  (** Later uses of this string are all purely functional *)
  let code = Bytes.sub_string env.out_buffer 0 env.out_position in
  let code = CString.hcons code in
  let fold reloc npos accu = (reloc, Array.of_list npos) :: accu in
  let reloc = RelocTable.fold fold env.reloc_info [] in
  let reloc = { reloc_infos = CArray.of_list reloc } in
  Array.iter (fun lbl ->
    (match lbl with
      Label_defined _ -> assert true
    | Label_undefined patchlist ->
        assert (patchlist = []))) env.label_table;
  (code, reloc, fv)
