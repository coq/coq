(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** List of opcodes.

    It is used to generate the files [coq_instruct.h], [coq_jumptbl.h],
    [coq_arity.h], and [vmopcodes.ml].

    [STOP] needs to be the last opcode.

    Arity -1 designates opcodes that need special handling in [coq_fix_code.c].
*)
let opcodes =
  [|
    "ACC0", 0;
    "ACC1", 0;
    "ACC2", 0;
    "ACC3", 0;
    "ACC4", 0;
    "ACC5", 0;
    "ACC6", 0;
    "ACC7", 0;
    "ACC", 1;
    "PUSH", 0;
    "PUSHACC1", 0;
    "PUSHACC2", 0;
    "PUSHACC3", 0;
    "PUSHACC4", 0;
    "PUSHACC5", 0;
    "PUSHACC6", 0;
    "PUSHACC7", 0;
    "PUSHACC", 1;
    "POP", 1;
    "ENVACC0", 0;
    "ENVACC1", 0;
    "ENVACC2", 0;
    "ENVACC3", 0;
    "ENVACC", 1;
    "PUSHENVACC0", 0;
    "PUSHENVACC1", 0;
    "PUSHENVACC2", 0;
    "PUSHENVACC3", 0;
    "PUSHENVACC", 1;
    "PUSH_RETADDR", 1;
    "APPLY", 1;
    "APPLY1", 0;
    "APPLY2", 0;
    "APPLY3", 0;
    "APPLY4", 0;
    "APPTERM", 2;
    "APPTERM1", 1;
    "APPTERM2", 1;
    "APPTERM3", 1;
    "RETURN", 1;
    "RESTART", 0;
    "GRAB", 1;
    "GRABREC", 1;
    "CLOSURE", 2;
    "CLOSUREREC", -1;
    "CLOSURECOFIX", -1;
    "OFFSETCLOSURE0", 0;
    "OFFSETCLOSURE1", 0;
    "OFFSETCLOSURE", 1;
    "PUSHOFFSETCLOSURE0", 0;
    "PUSHOFFSETCLOSURE1", 0;
    "PUSHOFFSETCLOSURE", 1;
    "GETGLOBAL", 1;
    "PUSHGETGLOBAL", 1;
    "MAKEBLOCK", 2;
    "MAKEBLOCK1", 1;
    "MAKEBLOCK2", 1;
    "MAKEBLOCK3", 1;
    "MAKEBLOCK4", 1;
    "SWITCH", -1;
    "PUSHFIELDS", 1;
    "GETFIELD0", 0;
    "GETFIELD1", 0;
    "GETFIELD", 1;
    "SETFIELD", 1;
    "PROJ", 1;
    "ENSURESTACKCAPACITY", 1;
    "CONST0", 0;
    "CONST1", 0;
    "CONST2", 0;
    "CONST3", 0;
    "CONSTINT", 1;
    "PUSHCONST0", 0;
    "PUSHCONST1", 0;
    "PUSHCONST2", 0;
    "PUSHCONST3", 0;
    "PUSHCONSTINT", 1;
    "ACCUMULATE", 0;
    "MAKESWITCHBLOCK", 4;
    "MAKEACCU", 1;
    "BRANCH", 1;
    "CHECKADDINT63", 1;
    "CHECKADDCINT63", 1;
    "CHECKADDCARRYCINT63", 1;
    "CHECKSUBINT63", 1;
    "CHECKSUBCINT63", 1;
    "CHECKSUBCARRYCINT63", 1;
    "CHECKMULINT63", 1;
    "CHECKMULCINT63", 1;
    "CHECKDIVINT63", 1;
    "CHECKMODINT63", 1;
    "CHECKDIVSINT63", 1;
    "CHECKMODSINT63", 1;
    "CHECKDIVEUCLINT63", 1;
    "CHECKDIV21INT63", 1;
    "CHECKLXORINT63", 1;
    "CHECKLORINT63", 1;
    "CHECKLANDINT63", 1;
    "CHECKLSLINT63", 1;
    "CHECKLSRINT63", 1;
    "CHECKASRINT63", 1;
    "CHECKADDMULDIVINT63", 1;
    "CHECKEQINT63", 1;
    "CHECKLTINT63", 1;
    "CHECKLEINT63", 1;
    "CHECKLTSINT63", 1;
    "CHECKLESINT63", 1;
    "CHECKCOMPAREINT63", 1;
    "CHECKCOMPARESINT63", 1;
    "CHECKHEAD0INT63", 1;
    "CHECKTAIL0INT63", 1;
    "CHECKOPPFLOAT", 1;
    "CHECKABSFLOAT", 1;
    "CHECKEQFLOAT", 1;
    "CHECKLTFLOAT", 1;
    "CHECKLEFLOAT", 1;
    "CHECKCOMPAREFLOAT", 1;
    "CHECKEQUALFLOAT", 1;
    "CHECKCLASSIFYFLOAT", 1;
    "CHECKADDFLOAT", 1;
    "CHECKSUBFLOAT", 1;
    "CHECKMULFLOAT", 1;
    "CHECKDIVFLOAT", 1;
    "CHECKSQRTFLOAT", 1;
    "CHECKFMAFLOAT", 1;
    "CHECKFLOATOFINT63", 1;
    "CHECKFLOATNORMFRMANTISSA", 1;
    "CHECKFRSHIFTEXP", 1;
    "CHECKLDSHIFTEXP", 1;
    "CHECKNEXTUPFLOAT", 1;
    "CHECKNEXTDOWNFLOAT", 1;
    "CHECKNEXTUPFLOATINPLACE", 1;
    "CHECKNEXTDOWNFLOATINPLACE", 1;
    "CHECKCAMLCALL2_1", 2;
    "CHECKCAMLCALL1", 2;
    "CHECKCAMLCALL2", 2;
    "CHECKCAMLCALL3_1", 2;
    "STOP", 0
  |]

let pp_c_comment fmt =
  Format.fprintf fmt "/* %s */\n"

let pp_ocaml_comment fmt =
  Format.fprintf fmt "(* %s *)\n"

let pp_header isOcaml fmt =
  Format.fprintf fmt "%a"
    (if isOcaml then pp_ocaml_comment else pp_c_comment)
    "DO NOT EDIT: automatically generated by kernel/genOpcodeFiles.ml"

let pp_coq_instruct_h fmt =
  pp_header false fmt;
  Format.fprintf fmt "#pragma once@.enum instructions {@.";
  Array.iter (fun (name, _) ->
      Format.fprintf fmt "  %s,@." name
    ) opcodes;
  Format.fprintf fmt "};@."

let pp_coq_jumptbl_h fmt =
  pp_header false fmt;
  Array.iter (fun (name, _) ->
      Format.fprintf fmt "  &&coq_lbl_%s,@." name
    ) opcodes

let pp_coq_arity_h fmt =
  pp_header false fmt;
  Format.fprintf fmt "static signed char arity[] = {@.";
  Array.iter (fun (_, arity) ->
      Format.fprintf fmt "  %d,@." arity
    ) opcodes;
  Format.fprintf fmt "};@."

let pp_vmopcodes_ml fmt =
  pp_header true fmt;
  Array.iteri (fun n s ->
      Format.fprintf fmt "let op%s = %d@.@." s n
    ) (Array.map fst opcodes)

let pp_vmopcodes_mli fmt =
  pp_header true fmt;
  Array.iteri (fun _ s ->
      Format.fprintf fmt "val op%s : int@.@." s
    ) (Array.map fst opcodes)

let usage () =
  Format.eprintf "usage: %s [enum|jump|arity|copml]@." Sys.argv.(0);
  exit 1

let main () =
  match Sys.argv.(1) with
  | "enum" -> pp_coq_instruct_h Format.std_formatter
  | "jump" -> pp_coq_jumptbl_h Format.std_formatter
  | "arity" -> pp_coq_arity_h Format.std_formatter
  | "copml" -> pp_vmopcodes_ml Format.std_formatter
  | "copmli" -> pp_vmopcodes_mli Format.std_formatter
  | _ -> usage ()
  | exception Invalid_argument _ -> usage ()

let () = main ()
