(** * Plugin for building Coq via Ocamlbuild *)

open Ocamlbuild_plugin
open Ocamlbuild_pack
open Printf

(** WARNING !! this is preliminary stuff, able only to build
    coqtop.opt and coqtop.byte, and only in a precise environment
    (ocaml 3.11 with natdynlink)

    Support for other rules and other configurations will be
    added later...

    Usage: 

    ocamlbuild coq.otarget

    Then you can (hopefully) launch coq (with no input state) via:
    
    _build/bin/coqtop.opt -nois -coqlib .

    or

    CAML_LD_LIBRARY_PATH=_build/kernel/byterun _build/bin/coqtop.byte -nois -coqlib .
 
    TODO: understand how to create the right symlinks towards _build ...

*)



(** Parse a config file such as config/Makefile: 
    valid lines are NAME=value, comments start by # *)

let read_env f =
  let ic = open_in f in
  let vars = ref [] in
  begin try while true do
    let l = input_line ic in
    if l <> "" && l.[0] <> '#' && l.[0] <> ' ' then
      try
	let i = String.index l '=' in
	let var = String.sub l 0 i
	and def = if i+1 >= String.length l then "" else
	  String.sub l (i+1) (String.length l - i - 1)
	in
	let def = if String.length def >= 2 &&
	  def.[0]='\"' && def.[String.length def - 1] = '\"'
	then String.sub def 1 (String.length def - 2) else def
	in
	vars:=(var,def)::!vars
      with Not_found -> ()
  done with End_of_file -> () end;
  close_in ic;
  !vars

let env_vars =
  let f = "config/Makefile" in
  try read_env f with _ -> (eprintf "Error while reading %s\n" f; exit 1)

let get_env s =
  try List.assoc s env_vars
  with Not_found -> (eprintf "Unknown environment variable %s\n" s; exit 1)


(** Configuration *)

let _ = Options.ocamlc := A(get_env "OCAMLC")

let camlp4o = get_env "CAMLP4O"
let camlp4lib = get_env "MYCAMLP4LIB"
let camlp4compat = get_env "CAMLP4COMPAT"
let hasdynlink = (get_env "HASNATDYNLINK" = "true")
let flag_dynlink = if hasdynlink then "-DHasDynLink" else ""

(** Do we want to inspect .ml generated from .ml4 ? *)
let readable_genml = false
let readable_flag = if readable_genml then A"pr_o.cmo" else N

let core_libs =
  ["lib/lib"; "kernel/kernel"; "library/library";
   "pretyping/pretyping"; "interp/interp";  "proofs/proofs";
   "parsing/parsing"; "tactics/tactics"; "toplevel/toplevel";
   "parsing/highparsing"; "tactics/hightactics"]
let core_cma = List.map (fun s -> s^".cma") core_libs
let core_cmxa = List.map (fun s -> s^".cmxa") core_libs
let core_mllib = List.map (fun s -> s^".mllib") core_libs


let _ = dispatch begin function
 | After_rules ->  (* Add our rules after the standard ones. *)

(** Camlp4 extensions *)

     rule "ml4ml" ~dep:"%.ml4" ~prod:"%.ml"
       (fun env _ ->
	  let ml4 = env "%.ml4" and ml = env "%.ml" in
	  Cmd (S[A camlp4o;T(tags_of_pathname ml4 ++ "p4mod");readable_flag;
		 T(tags_of_pathname ml4 ++ "p4option");
		 Sh camlp4compat; A"-o"; P ml; A"-impl"; P ml4]));

     flag ["is_ml4"; "p4mod"; "use_macro"] (A"pa_macro.cmo");
     flag ["is_ml4"; "p4mod"; "use_extend"] (A"pa_extend.cmo");
     flag ["is_ml4"; "p4mod"; "use_MLast"] (A"q_MLast.cmo");

     flag_and_dep ["is_ml4"; "p4mod"; "use_grammar"] (P"parsing/grammar.cma");
     flag_and_dep ["is_ml4"; "p4mod"; "use_constr"] (P"parsing/q_constr.cmo");

(** Special case of toplevel/mltop.ml4: 
    - mltop.ml will be the old mltop.optml and be used to obtain mltop.cmx
    - we add a special mltop.ml4 --> mltop.cmo rule, before all the others
*)
     flag ["is_mltop"; "p4option"] (A flag_dynlink);

(*TODO: this is rather ugly for a simple file, we should try to
        benefit more from predefined rules *)
     let mltop = "toplevel/mltop" in
     let ml4 = mltop^".ml4" and mlo = mltop^".cmo" and
	 ml = mltop^".ml" and mld = mltop^".ml.depends"
     in
     rule "mltop_byte" ~deps:[ml4;mld]  ~prod:mlo ~insert:`top
       (fun env build ->
	  Ocaml_compiler.prepare_compile build ml;
	  Cmd (S [!Options.ocamlc; A"-c";A"-rectypes"; A"-I"; A camlp4lib;
		  A"-pp";
		  Quote (S [A camlp4o; T(tags_of_pathname ml4 ++ "p4mod");
			    A"-DByte"; A"-DHasDynLink"; Sh camlp4compat;
			    A"-impl"]);
		  A"-rectypes"; A"-I"; A camlp4lib;
		  Ocaml_utils.ocaml_include_flags ml4;
		  A"-impl"; P ml4]));

(** All caml files are compiled with -rectypes and +camlp5 *)

     flag ["compile"; "ocaml"] (S [A"-rectypes"; A"-I"; A camlp4lib]);
     flag ["link"; "ocaml"] (S [A"-rectypes"; A"-I"; A camlp4lib]);

(** Extra libraries *)

     ocaml_lib ~extern:true "gramlib";

(** C code for the VM *)

     let headers = List.map (fun s -> "kernel/byterun/"^s)
       ["coq_fix_code.h";"coq_instruct.h"; "coq_memory.h"; "int64_emul.h";
	"coq_gc.h"; "coq_interp.h"; "coq_values.h"; "int64_native.h";
	"coq_jumptbl.h"]
     in
     dep ["compile"; "c"] headers;
     flag ["compile"; "c"] (S[A"-ccopt";A"-fno-defer-pop -Wall -Wno-unused"]);
     dep ["link"; "ocaml"; "use_libcoqrun"] ["kernel/byterun/libcoqrun.a"];

(** Generation of coq_jumbtbl.h for the VM *)

     let coqjump = "kernel/byterun/coq_jumptbl.h"
     and coqinstr = "kernel/byterun/coq_instruct.h" in
     let cmd = Printf.sprintf
       "sed -n -e '/^  /s/ \\([A-Z]\\)/ \\&\\&coq_lbl_\\1/gp' -e '/^}/q' %s > %s"
       coqinstr coqjump
     in
     rule "coqjump" ~deps:[coqinstr] ~prod:coqjump
       (fun _ _ -> Cmd (Sh cmd));

(** Generation of opcodes for the VM *)

     let copcodes = "kernel/copcodes.ml"
     and coqinstr = "kernel/byterun/coq_instruct.h"
     and script = "kernel/make-opcodes" in
     let cmd = Printf.sprintf
       "sed -n -e '/^enum/p' -e 's/,//g' -e '/^  /p' %s | awk -f %s > %s"
       coqinstr script copcodes
     in
     rule "copcodes" ~deps:[coqinstr;script] ~prod:copcodes
       (fun _ _ -> Cmd (Sh cmd));

(** Generation of tolink.ml *)

     let tolink = "scripts/tolink.ml" in
     let core_cma_s = String.concat " " core_cma in
     let core_mllib_s = String.concat " " core_mllib in
     let cmd =
       "(echo \'let copts = \"-cclib -lcoqrun\"\'; "^
       "echo \'let core_libs = \"config/coq_config.cmo "^core_cma_s^"\"\'; "^
       "echo \'let core_objs = \"Coq_config `cat "^core_mllib_s^"`\"\'; "^
       "echo \'let ide = \"`cat ide/ide.mllib`\"\' " ^
       ") > " ^ tolink
     in
     rule "tolink.ml" ~deps:core_mllib ~prod:tolink
       (fun _ _ -> Cmd (Sh cmd));

(** Coqtop *)

     let coqtopopt = "bin/coqtop.opt"
     and coqtopbyte = "bin/coqtop.byte" in
     let deps = ["scripts/coqmktop.native";"kernel/byterun/libcoqrun.a"] in
     let depsopt = [ "config/coq_config.cmx"] @ deps @ core_cmxa
     and depsbyte = [ "config/coq_config.cmo"] @ deps @ core_cma
     in begin
     rule "coqtop.opt" ~deps:depsopt ~prod:coqtopopt
       (fun _ _ ->
	  Cmd (S [P "scripts/coqmktop.native";A"-boot";A"-opt";
		  Ocaml_utils.ocaml_include_flags coqtopopt;
		  A"-o";P coqtopopt]));
     rule "coqtop.byte" ~deps:depsbyte ~prod:coqtopbyte
       (fun _ _ ->
	  Cmd (S [P "scripts/coqmktop.native";A"-boot";A"-top";
		  Ocaml_utils.ocaml_include_flags coqtopbyte;
		  A"-o";P coqtopbyte]));
     end;

(** bin : directory bin doesn't get made by default ??!! *)

     rule "bin dir" ~prod:"bin/.foo" (fun _ _ -> Cmd (Sh "mkdir -p bin && touch bin/.foo"));

 | _ -> ()

end
