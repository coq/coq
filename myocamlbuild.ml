(** * Plugin for building Coq via Ocamlbuild *)

open Ocamlbuild_plugin
open Ocamlbuild_pack
open Printf
open Scanf

(** WARNING !! this is preliminary stuff, able only to build
    coqtop.opt and coqtop.byte, and only in a precise environment
    (ocaml 3.11 with natdynlink)

    Support for other rules and other configurations will be
    added later...

    Usage: ./build   (which launches ocamlbuild coq.itarget)

    Then you can (hopefully) launch coq (with no input state) via:
    
    bin/coqtop.opt -nois -coqlib .

    or

    export CAML_LD_LIBRARY_PATH=_build/kernel/byterun 
    bin/coqtop.byte -nois -coqlib .

    Apart from binaries in bin/, every created files are in _build.
    A "./build clean" should give you back a clean source tree
 
    TODO: understand how to create the right symlinks towards _build ...

*)

(** Generic file reader, which produces a list of strings, one per line *)

let read_file f =
  let ic = open_in f in
  let lines = ref [] in
  begin try
    while true do lines := (input_line ic)::!lines done
  with End_of_file -> () end;
  close_in ic;
  List.rev !lines

(** Parse a config file such as config/Makefile. Valid lines are VAR=def.
    If def is double-quoted we remove the "..." (first sscanf attempt with %S).
    Otherwise, def is as long as possible (%s@\n prevents stopping at ' ').
*)

let read_env f =
  let lines = read_file f in
  let add, get = let l = ref [] in (fun x -> l:= x::!l), (fun () -> !l) in
  let get_var_def s =
    try sscanf s "%[A-Z0-9_]=%S" (fun v d -> add (v,d))
    with _ ->
      try sscanf s "%[A-Z0-9_]=%s@\n" (fun v d -> add (v,d))
      with _ -> ()
  in
  List.iter get_var_def lines; get ()

let env_vars =
  let f = "config/Makefile" in
  try read_env f with _ -> (eprintf "Error while reading %s\n" f; exit 1)

let get_env s =
  try List.assoc s env_vars
  with Not_found -> (eprintf "Unknown environment variable %s\n" s; exit 1)



(** Configuration *)

let _ = Options.ocamlc := A(get_env "OCAMLC")

let camlp4o = A(get_env "CAMLP4O")
let camlp4lib = S[A"-I"; A(get_env "MYCAMLP4LIB")]
let camlp4compat = Sh(get_env "CAMLP4COMPAT")
let opt = (get_env "BEST" = "opt")
let best_oext = if opt then ".native" else ".byte"
let best_ext = if opt then ".opt" else ".byte"
let hasdynlink = (get_env "HASNATDYNLINK" = "true")
let flag_dynlink = if hasdynlink then A"-DHasDynLink" else N

(** Do we want to inspect .ml generated from .ml4 ? *)
let readable_genml = false
let readable_flag = if readable_genml then A"pr_o.cmo" else N



(** Abbreviations about files *)

let core_libs =
  ["lib/lib"; "kernel/kernel"; "library/library";
   "pretyping/pretyping"; "interp/interp";  "proofs/proofs";
   "parsing/parsing"; "tactics/tactics"; "toplevel/toplevel";
   "parsing/highparsing"; "tactics/hightactics"]
let core_cma = List.map (fun s -> s^".cma") core_libs
let core_cmxa = List.map (fun s -> s^".cmxa") core_libs
let core_mllib = List.map (fun s -> s^".mllib") core_libs

let ide_mllib = "ide/ide.mllib"

let tolink = "scripts/tolink.ml"
let coqconfig = "config/coq_config"

let c_headers_base =
  ["coq_fix_code.h";"coq_instruct.h"; "coq_memory.h"; "int64_emul.h";
   "coq_gc.h"; "coq_interp.h"; "coq_values.h"; "int64_native.h";
   "coq_jumptbl.h"]
let c_headers = List.map ((^) "kernel/byterun/") c_headers_base

let coqinstrs = "kernel/byterun/coq_instruct.h"
let coqjumps = "kernel/byterun/coq_jumptbl.h"
let copcodes = "kernel/copcodes.ml"

let libcoqrun = "kernel/byterun/libcoqrun.a"

let grammar = "parsing/grammar.cma"
let qconstr = "parsing/q_constr.cmo"

let coqtop = "bin/coqtop"
let coqmktop = "bin/coqmktop"
let coqdep_boot = "bin/coqdep_boot"
let coqdep = "bin/coqdep"
let coqdoc = "bin/coqdoc"
let coqwc = "bin/coqwc"
let coqtex = "bin/coq-tex"
let coqmakefile = "bin/coq_makefile"
let gallina = "bin/gallina"



(** A few common rules *)

let copy_rule src dst =
  rule (src^"_"^dst) ~dep:src ~prod:dst (fun _ _ -> cp src dst)

let copy_bin srcd radix =
  let src = srcd^radix and dst = "bin/"^radix in
  copy_rule (src^".byte") (dst^".byte");
  if opt then copy_rule (src^".native") (dst^".opt")

let copy_bin_alias srcd radix =
  let f = "bin/"^radix in
  let fo = f^".opt" and fb = f^".byte" in
  let deps = if opt then [fb;fo] else [fb] in
  copy_bin srcd radix;
  rule f ~deps:deps ~prod:f (fun _ _ -> ln_s (radix^best_ext) f)



(** The real game ... *)

let _ = dispatch begin function
 | After_rules ->  (* Add our rules after the standard ones. *)

(** The _build/bin directory isn't done by default *)

     if not (Sys.file_exists "_build/bin") then
       Command.execute ~quiet:true (ln_s "../bin" "_build");

(** Camlp4 extensions *)

     rule "ml4ml" ~dep:"%.ml4" ~prod:"%.ml"
       (fun env _ ->
	  let ml4 = env "%.ml4" and ml = env "%.ml" in
	  Cmd (S[camlp4o;T(tags_of_pathname ml4 ++ "p4mod");readable_flag;
		 T(tags_of_pathname ml4 ++ "p4option"); camlp4compat;
		 A"-o"; P ml; A"-impl"; P ml4]));

     flag ["is_ml4"; "p4mod"; "use_macro"] (A"pa_macro.cmo");
     flag ["is_ml4"; "p4mod"; "use_extend"] (A"pa_extend.cmo");
     flag ["is_ml4"; "p4mod"; "use_MLast"] (A"q_MLast.cmo");

     flag_and_dep ["is_ml4"; "p4mod"; "use_grammar"] (P grammar);
     flag_and_dep ["is_ml4"; "p4mod"; "use_constr"] (P qconstr);

(** Special case of toplevel/mltop.ml4: 
    - mltop.ml will be the old mltop.optml and be used to obtain mltop.cmx
    - we add a special mltop.ml4 --> mltop.cmo rule, before all the others
*)
     flag ["is_mltop"; "p4option"] flag_dynlink;

(*TODO: this is rather ugly for a simple file, we should try to
        benefit more from predefined rules *)
     let mltop = "toplevel/mltop" in
     let ml4 = mltop^".ml4" and mlo = mltop^".cmo" and
	 ml = mltop^".ml" and mld = mltop^".ml.depends"
     in
     rule "mltop_byte" ~deps:[ml4;mld]  ~prod:mlo ~insert:`top
       (fun env build ->
	  Ocaml_compiler.prepare_compile build ml;
	  Cmd (S [!Options.ocamlc; A"-c"; A"-pp";
		  Quote (S [camlp4o; T(tags_of_pathname ml4 ++ "p4mod");
			    A"-DByte"; A"-DHasDynLink"; camlp4compat;
			    A"-impl"]);
		  A"-rectypes"; camlp4lib; Ocaml_utils.ocaml_include_flags ml4;
		  A"-impl"; P ml4]));

(** All caml files are compiled with -rectypes and +camlp4/5 *)

     flag ["compile"; "ocaml"] (S [A"-rectypes"; camlp4lib]);
     flag ["link"; "ocaml"] (S [A"-rectypes"; camlp4lib]);

(** Extra libraries *)

     ocaml_lib ~extern:true "gramlib";

(** C code for the VM *)

     dep ["compile"; "c"] c_headers;
     flag ["compile"; "c"] (S[A"-ccopt";A"-fno-defer-pop -Wall -Wno-unused"]);
     dep ["link"; "ocaml"; "use_libcoqrun"] [libcoqrun];

(** VM: Generation of coq_jumbtbl.h and copcodes.ml from coq_instruct.h *)

     rule "coqinstrs" ~dep:coqinstrs ~prods:[coqjumps;copcodes]
       (fun _ _ ->
	  let jmps = ref [] and ops = ref [] and i = ref 0 in
	  let add_instr instr comma =
	    if instr = "" then failwith "Empty" else begin
	      jmps:=sprintf "&&coq_lbl_%s%s \n" instr comma :: !jmps;
	      ops:=sprintf "let op%s = %d\n" instr !i :: !ops;
	      incr i
	    end
	  in
	  (** we recognize comma-separated uppercase instruction names *)
	  let parse_line s =
	    let b = Scanning.from_string s in
	    try while true do bscanf b " %[A-Z0-9_]%[,]" add_instr done
	    with _ -> ()
	  in
	  List.iter parse_line (read_file coqinstrs);
	  Seq [Echo (List.rev !jmps, coqjumps);
	       Echo (List.rev !ops, copcodes)]);

(** Generation of tolink.ml *)

     rule "tolink.ml" ~deps:(ide_mllib::core_mllib) ~prod:tolink
       (fun _ _ ->
	  let cat s = String.concat " " (read_file s) in
	  let core_mods = String.concat " " (List.map cat core_mllib) in
	  let ide_mods = cat ide_mllib in
	  let core_cmas = String.concat " " core_cma in
	  Echo (["let copts = \"-cclib -lcoqrun\"\n";
		 "let core_libs = \""^coqconfig^".cmo "^core_cmas^"\"\n";
		 "let core_objs = \"Coq_config "^core_mods^"\"\n";
		 "let ide = \""^ide_mods^"\"\n"],
		tolink));

(** Coqtop *)

     let coqtopo = coqtop^".opt" and coqtopb = coqtop^".byte" in
     let depso = [coqmktop;libcoqrun;coqconfig^".cmx"] @ core_cmxa
     and depsb = [coqmktop;libcoqrun;coqconfig^".cmo"] @ core_cma
     in
     if opt then rule coqtopo ~prod:coqtopo ~deps:depso
       (fun _ _ ->
	  Cmd (S [P coqmktop;A"-boot";A"-opt";
		  Ocaml_utils.ocaml_include_flags coqtopo; A"-o";P coqtopo]));
     rule coqtopb ~prod:coqtopb ~deps:depsb
       (fun _ _ ->
	  Cmd (S [P coqmktop;A"-boot";A"-top";
		  Ocaml_utils.ocaml_include_flags coqtopb; A"-o";P coqtopb]));
     rule coqtop ~prod:coqtop ~deps:(coqtopb :: if opt then [coqtopo] else [])
       (fun _ _ -> ln_s ("coqtop"^best_ext) coqtop);

(** Coqmktop *)

     copy_bin_alias "scripts/" "coqmktop";

(** Coqc *)

     copy_bin_alias "scripts/" "coqc";

(** Coqdep *)

     copy_rule ("tools/coqdep_boot"^best_oext) coqdep_boot;
     copy_rule ("tools/coqdep"^best_oext) coqdep;

(** Misc binaries *)

     copy_rule ("tools/coqdoc/main"^best_oext) coqdoc;
     copy_rule ("tools/coqwc"^best_oext) coqwc;
     copy_rule ("tools/coq_makefile"^best_oext) coqmakefile;
     copy_rule ("tools/coq_tex"^best_oext) coqtex;
     copy_rule ("tools/gallina"^best_oext) gallina;

(* TODO: coqide, coqchk *)

 | _ -> ()

end
