(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Author: Benjamin Grégoire as part of the bytecode-based virtual reduction
   machine, Oct 2004 *)
(* Extension: Arnaud Spiwack (support for native arithmetic), May 2005 *)

open Term
open Cbytecodes
open Copcodes
open Mod_subst

(* Relocation information *)
type reloc_info =
  | Reloc_annot of annot_switch
  | Reloc_const of structured_constant
  | Reloc_getglobal of Names.constant

type patch = reloc_info * int

let patch_char4 buff pos c1 c2 c3 c4 = 
  String.unsafe_set buff pos       c1;
  String.unsafe_set buff (pos + 1) c2;
  String.unsafe_set buff (pos + 2) c3;
  String.unsafe_set buff (pos + 3) c4 
  
let patch_int buff pos n =
  patch_char4 buff pos 
    (Char.unsafe_chr n) (Char.unsafe_chr (n asr 8))  (Char.unsafe_chr (n asr 16))
    (Char.unsafe_chr (n asr 24))

(* Buffering of bytecode *)

let out_buffer = ref(String.create 1024)
and out_position = ref 0

let out_word b1 b2 b3 b4 =
  let p = !out_position in
  if p >= String.length !out_buffer then begin
    let len = String.length !out_buffer in
    let new_len =
      if len <= Sys.max_string_length / 2
      then 2 * len
      else
	if len = Sys.max_string_length
	then invalid_arg "String.create"  (* Pas la bonne exception .... *)
	else Sys.max_string_length in
    let new_buffer = String.create new_len in
    String.blit !out_buffer 0 new_buffer 0 len;
    out_buffer := new_buffer
  end;
  patch_char4 !out_buffer p (Char.unsafe_chr b1)
   (Char.unsafe_chr b2) (Char.unsafe_chr b3) (Char.unsafe_chr b4);
  out_position := p + 4

let out opcode =
  out_word opcode 0 0 0

let out_int n =
  out_word n (n asr 8) (n asr 16) (n asr 24)

(* Handling of local labels and backpatching *)

type label_definition =
    Label_defined of int
  | Label_undefined of (int * int) list

let label_table  = ref ([| |] : label_definition array)
(* le ieme element de la table = Label_defined n signifie que l'on a
   deja rencontrer le label i et qu'il est a l'offset n.
                               = Label_undefined l signifie que l'on a
   pas encore rencontrer ce label, le premier entier indique ou est l'entier
   a patcher dans la string, le deuxieme son origine  *)

let extend_label_table needed =
  let new_size = ref(Array.length !label_table) in
  while needed >= !new_size do new_size := 2 * !new_size done;
  let new_table = Array.make !new_size (Label_undefined []) in
  Array.blit !label_table 0 new_table 0 (Array.length !label_table);
  label_table := new_table

let backpatch (pos, orig) =
  let displ = (!out_position - orig) asr 2 in
  !out_buffer.[pos]   <- Char.unsafe_chr displ;
  !out_buffer.[pos+1] <- Char.unsafe_chr (displ asr 8);
  !out_buffer.[pos+2] <- Char.unsafe_chr (displ asr 16);
  !out_buffer.[pos+3] <- Char.unsafe_chr (displ asr 24)

let define_label lbl =
  if lbl >= Array.length !label_table then extend_label_table lbl;
  match (!label_table).(lbl) with
    Label_defined _ ->
      raise(Failure "CEmitcode.define_label")
  | Label_undefined patchlist ->
      List.iter backpatch patchlist;
      (!label_table).(lbl) <- Label_defined !out_position

let out_label_with_orig orig lbl =
  if lbl >= Array.length !label_table then extend_label_table lbl;
  match (!label_table).(lbl) with
    Label_defined def ->
      out_int((def - orig) asr 2)
  | Label_undefined patchlist ->
      (* spiwack: patchlist is supposed to be non-empty all the time
         thus I commented that out. If there is no problem I suggest
         removing it for next release (cur: 8.1) *)
      (*if patchlist = [] then *)
	(!label_table).(lbl) <-
          Label_undefined((!out_position, orig) :: patchlist);
      out_int 0

let out_label l = out_label_with_orig !out_position l

(* Relocation information *)

let reloc_info = ref ([] : (reloc_info * int) list)

let enter info =
  reloc_info := (info, !out_position) :: !reloc_info

let slot_for_const c =
  enter (Reloc_const c);
  out_int 0

let slot_for_annot a =
  enter (Reloc_annot a);
  out_int 0

let slot_for_getglobal p =
  enter (Reloc_getglobal p);
  out_int 0


(* Emission of one instruction *)


let emit_instr = function
  | Klabel lbl -> define_label lbl
  | Kacc n ->
      if n < 8 then out(opACC0 + n) else (out opACC; out_int n)
  | Kenvacc n ->
      if n >= 1 && n <= 4
      then out(opENVACC1 + n - 1)
      else (out opENVACC; out_int n)
  | Koffsetclosure ofs ->
      if Int.equal ofs (-2) || Int.equal ofs 0 || Int.equal ofs 2
      then out (opOFFSETCLOSURE0 + ofs / 2)
      else (out opOFFSETCLOSURE; out_int ofs)
  | Kpush ->
      out opPUSH
  | Kpop n ->
      out opPOP; out_int n
  | Kpush_retaddr lbl ->
      out opPUSH_RETADDR; out_label lbl
  | Kapply n ->
      if n < 4 then out(opAPPLY1 + n - 1) else (out opAPPLY; out_int n)
  | Kappterm(n, sz) ->
      if n < 4 then (out(opAPPTERM1 + n - 1); out_int sz)
               else (out opAPPTERM; out_int n; out_int sz)
  | Kreturn n ->
      out opRETURN; out_int n
  | Kjump ->
      out opRETURN; out_int 0
  | Krestart ->
      out opRESTART
  | Kgrab n ->
      out opGRAB; out_int n
  | Kgrabrec(rec_arg) ->
      out opGRABREC; out_int rec_arg
  | Kclosure(lbl, n) ->
      out opCLOSURE; out_int n; out_label lbl
  | Kclosurerec(nfv,init,lbl_types,lbl_bodies) ->
      out opCLOSUREREC;out_int (Array.length lbl_bodies);
      out_int nfv; out_int init;
      let org = !out_position in
      Array.iter (out_label_with_orig org) lbl_types;
      let org = !out_position in
      Array.iter (out_label_with_orig org) lbl_bodies
  | Kclosurecofix(nfv,init,lbl_types,lbl_bodies) ->
      out opCLOSURECOFIX;out_int (Array.length lbl_bodies);
      out_int nfv; out_int init;
      let org = !out_position in
      Array.iter (out_label_with_orig org) lbl_types;
      let org = !out_position in
      Array.iter (out_label_with_orig org) lbl_bodies
  | Kgetglobal q ->
      out opGETGLOBAL; slot_for_getglobal q
  | Kconst (Const_b0 i) ->
      if i >= 0 && i <= 3
          then out (opCONST0 + i)
          else (out opCONSTINT; out_int i)
  | Kconst c ->
      out opGETGLOBAL; slot_for_const c
  | Kmakeblock(n, t) ->
      if Int.equal n 0 then invalid_arg "emit_instr : block size = 0"
      else if n < 4 then (out(opMAKEBLOCK1 + n - 1); out_int t)
      else (out opMAKEBLOCK; out_int n; out_int t)
  | Kmakeprod ->
      out opMAKEPROD
  | Kmakeswitchblock(typlbl,swlbl,annot,sz) ->
      out opMAKESWITCHBLOCK;
      out_label typlbl; out_label swlbl;
      slot_for_annot annot;out_int sz
  | Kswitch (tbl_const, tbl_block) ->
      let lenb = Array.length tbl_block in
      let lenc = Array.length tbl_const in
      assert (lenb < 0x100 && lenc < 0x1000000);
      out opSWITCH;
      out_word lenc (lenc asr 8) (lenc asr 16) (lenb);
(*      out_int (Array.length tbl_const + (Array.length tbl_block lsl 23)); *)
      let org = !out_position in
      Array.iter (out_label_with_orig org) tbl_const;
      Array.iter (out_label_with_orig org) tbl_block
  | Kpushfields n ->
      out opPUSHFIELDS;out_int n
  | Kfield n ->
      if n <= 1 then out (opGETFIELD0+n)
      else (out opGETFIELD;out_int n)
  | Ksetfield n ->
      if n <= 1 then out (opSETFIELD0+n)
      else (out opSETFIELD;out_int n)
  | Ksequence _ -> invalid_arg "Cemitcodes.emit_instr"
  | Kproj (n,p) -> out opPROJ; out_int n; slot_for_const (Const_proj p)
  (* spiwack *)
  | Kbranch lbl -> out opBRANCH; out_label lbl
  | Kaddint31 -> out opADDINT31
  | Kaddcint31 -> out opADDCINT31
  | Kaddcarrycint31 -> out opADDCARRYCINT31
  | Ksubint31 -> out opSUBINT31
  | Ksubcint31 -> out opSUBCINT31
  | Ksubcarrycint31 -> out opSUBCARRYCINT31
  | Kmulint31 -> out opMULINT31
  | Kmulcint31 -> out opMULCINT31
  | Kdiv21int31 -> out opDIV21INT31
  | Kdivint31 -> out opDIVINT31
  | Kaddmuldivint31 -> out opADDMULDIVINT31
  | Kcompareint31 -> out opCOMPAREINT31
  | Khead0int31 -> out opHEAD0INT31
  | Ktail0int31 -> out opTAIL0INT31
  | Kisconst lbl -> out opISCONST; out_label lbl
  | Kareconst(n,lbl) -> out opARECONST; out_int n; out_label lbl
  | Kcompint31 -> out opCOMPINT31
  | Kdecompint31 -> out opDECOMPINT31
  | Klorint31 -> out opORINT31
  | Klandint31 -> out opANDINT31
  | Klxorint31 -> out opXORINT31
  (*/spiwack *)
  | Kstop ->
      out opSTOP

(* Emission of a list of instructions. Include some peephole optimization. *)

let rec emit = function
  | [] -> ()
  (* Peephole optimizations *)
  | Kpush :: Kacc n :: c ->
      if n < 8 then out(opPUSHACC0 + n) else (out opPUSHACC; out_int n);
      emit c
  | Kpush :: Kenvacc n :: c ->
      if n >= 1 && n <= 4
      then out(opPUSHENVACC1 + n - 1)
      else (out opPUSHENVACC; out_int n);
      emit c
  | Kpush :: Koffsetclosure ofs :: c ->
      if Int.equal ofs (-2) || Int.equal ofs 0 || Int.equal ofs 2
      then out(opPUSHOFFSETCLOSURE0 + ofs / 2)
      else (out opPUSHOFFSETCLOSURE; out_int ofs);
      emit c
  | Kpush :: Kgetglobal id :: c ->
      out opPUSHGETGLOBAL; slot_for_getglobal id; emit c
  | Kpush :: Kconst (Const_b0 i) :: c ->
      if i >= 0 && i <= 3
      then out (opPUSHCONST0 + i)
      else (out opPUSHCONSTINT; out_int i);
      emit c
  | Kpush :: Kconst const :: c ->
      out opPUSHGETGLOBAL; slot_for_const const;
      emit c
  | Kpop n :: Kjump :: c ->
      out opRETURN; out_int n; emit c
  | Ksequence(c1,c2)::c ->
      emit c1; emit c2;emit c
  (* Default case *)
  | instr :: c ->
      emit_instr instr; emit c

(* Initialization *)

let init () =
  out_position := 0;
  label_table := Array.make 16 (Label_undefined []);
  reloc_info := []

type emitcodes = string

let copy = String.copy

let length = String.length

type to_patch = emitcodes * (patch list) * fv

(* Substitution *)
let rec subst_strcst s sc =
  match sc with
  | Const_sorts _ | Const_b0 _ -> sc
  | Const_proj p -> Const_proj (subst_constant s p)
  | Const_bn(tag,args) -> Const_bn(tag,Array.map (subst_strcst s) args)
  | Const_ind ind -> let kn,i = ind in Const_ind (subst_mind s kn, i)

let subst_patch s (ri,pos) =
  match ri with
  | Reloc_annot a ->
      let (kn,i) = a.ci.ci_ind in
      let ci = {a.ci with ci_ind = (subst_mind s kn,i)} in
      (Reloc_annot {a with ci = ci},pos)
  | Reloc_const sc -> (Reloc_const (subst_strcst s sc), pos)
  | Reloc_getglobal kn -> (Reloc_getglobal (subst_constant s kn), pos)

let subst_to_patch s (code,pl,fv) =
  code,List.rev_map (subst_patch s) pl,fv

let subst_pconstant s (kn, u) = (fst (subst_con_kn s kn), u)

type body_code =
  | BCdefined of to_patch
  | BCalias of Names.constant
  | BCconstant

type to_patch_substituted =
| PBCdefined of to_patch substituted
| PBCalias of Names.constant substituted
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
  init();
  emit init_code;
  emit fun_code;
  let code = String.create !out_position in
  String.unsafe_blit !out_buffer 0 code 0 !out_position;
  let reloc = List.rev !reloc_info in
  Array.iter (fun lbl ->
    (match lbl with
      Label_defined _ -> assert true
    | Label_undefined patchlist ->
	assert (patchlist = []))) !label_table;
  (code, reloc, fv)
