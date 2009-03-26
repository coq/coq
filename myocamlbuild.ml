(** * Plugin for building Coq via Ocamlbuild *)

open Ocamlbuild_plugin
open Ocamlbuild_pack
open Printf
open Scanf

(** WARNING !! this is preliminary stuff. It should allows you to
    build coq and its libraries if everything goes right.
    Support for all the build rules and configuration options
    is progressively added. Tested only on linux + ocaml 3.11 +
    natdynlink for now.

    Usage: 
     ./configure -local -opt
     manual addition of /_build to coqlib and coqsrc in config/coq_config.ml
     ./build   (which launches ocamlbuild coq.otarget)

    Then you can (hopefully) launch coq via:
    
    _build/bin/coqtop.opt

    or

    export CAML_LD_LIBRARY_PATH=_build/kernel/byterun 
    _build/bin/coqtop.byte -nois

    Every created files are in _build.
    A "./build clean" should give you back a clean source tree

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
let _ = Options.ocamlopt := A(get_env "OCAMLOPT")
let _ = Options.ocamlmklib := A(get_env "OCAMLMKLIB")
let _ = Options.ocamldep := A(get_env "OCAMLDEP")
let _ = Options.ocamldoc := A(get_env "OCAMLDOC")
let _ = Options.ocamlopt := A(get_env "OCAMLOPT")
let _ = Options.ocamlyacc := A(get_env "OCAMLYACC")
let _ = Options.ocamllex := A(get_env "OCAMLLEX")

let ocaml = A(get_env "OCAML")
let camlp4o = A(get_env "CAMLP4O")
let camlp4incl = S[A"-I"; A(get_env "MYCAMLP4LIB")]
let camlp4compat = Sh(get_env "CAMLP4COMPAT")
let opt = (get_env "BEST" = "opt")
let best_oext = if opt then ".native" else ".byte"
let best_ext = if opt then ".opt" else ".byte"
let hasdynlink = (get_env "HASNATDYNLINK" = "true")
let flag_dynlink = if hasdynlink then A"-DHasDynlink" else N
let dep_dynlink = if hasdynlink then N else Sh"-natdynlink no"
let lablgtkincl = Sh(get_env "COQIDEINCLUDES")

(** Do we want to inspect .ml generated from .ml4 ? *)
let readable_genml = false
let readable_flag = if readable_genml then A"pr_o.cmo" else N

let _build = Options.build_dir


(** Abbreviations about files *)

let core_libs =
  ["lib/lib"; "kernel/kernel"; "library/library";
   "pretyping/pretyping"; "interp/interp";  "proofs/proofs";
   "parsing/parsing"; "tactics/tactics"; "toplevel/toplevel";
   "parsing/highparsing"; "tactics/hightactics"]
let core_cma = List.map (fun s -> s^".cma") core_libs
let core_cmxa = List.map (fun s -> s^".cmxa") core_libs
let core_mllib = List.map (fun s -> s^".mllib") core_libs

let ide_cma = "ide/ide.cma"
let ide_cmxa = "ide/ide.cmxa"
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
let coqide = "bin/coqide"
let coqmktop = "bin/coqmktop"
let coqc = "bin/coqc"
let coqchk = "bin/coqchk"
let coqdep_boot = "bin/coqdep_boot"
let coqdep = "bin/coqdep"
let coqdoc = "bin/coqdoc"
let coqwc = "bin/coqwc"
let coqtex = "bin/coq-tex"
let coqmakefile = "bin/coq_makefile"
let gallina = "bin/gallina"

let initialcoq = "states/initial.coq"
let init_vo = ["theories/Init/Prelude.vo";"theories/Init/Logic_Type.vo"]
let makeinitial = "states/MakeInitial.v"

let nmake = "theories/Numbers/Natural/BigN/NMake.v"
let nmakegen = "theories/Numbers/Natural/BigN/NMake_gen.ml"

let genvfiles = [nmake]

(** A few common functions *)

let copy_rule src dst =
  rule (src^"_"^dst) ~dep:src ~prod:dst (fun _ _ -> cp src dst)

let copy_bin_alias src dst =
  let dsto = dst^".opt" and dstb = dst^".byte" in
  copy_rule (src^".byte") (dst^".byte");
  if opt then copy_rule (src^".native") (dst^".opt");
  rule dst ~prod:dst ~deps:(if opt then [dsto;dstb] else [dstb])
    (fun _ _ -> ln_s ((Filename.basename dst)^best_ext) dst)

let copy_bin_best src dst = copy_rule (src^best_oext) dst

let incl f = Ocaml_utils.ocaml_include_flags f

(** The real game ... *)

let _ = dispatch begin function
 | After_rules ->  (* Add our rules after the standard ones. *)

(** We "pre-create" a few subdirs in _build to please coqtop *)

     Shell.mkdir_p (!_build^"/bin");
     Shell.mkdir_p (!_build^"/dev");

(** Moreover, we "pre-import" in _build the sources file that will be needed
    by coqdep_boot *)

     (*TODO: do something nicer than this call to find (maybe with Slurp) *)

     let exclude = "-name _\\$* -or -name .\\* -prune -or" in
     Command.execute ~quiet:true (Cmd (Sh
       ("for i in `find theories plugins "^exclude^" -print`; do "^
	"[ -f $i -a ! -f _build/$i ] && mkdir -p _build/`dirname $i` && cp $i _build/$i; "^
	"done; true")));

(** Camlp4 extensions *)

     rule ".ml4.ml" ~dep:"%.ml4" ~prod:"%.ml"
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
			    A"-DByte";A"-DHasDynlink";camlp4compat;A"-impl"]);
		  A"-rectypes"; camlp4incl; incl ml4; A"-impl"; P ml4]));

(** All caml files are compiled with -rectypes and +camlp4/5 
    and ide files need +lablgtk2 *)

     flag ["compile"; "ocaml"] (S [A"-rectypes"; camlp4incl]);
     flag ["link"; "ocaml"] (S [A"-rectypes"; camlp4incl]);
     flag ["compile"; "ocaml"; "ide"] lablgtkincl;
     flag ["link"; "ocaml"; "ide"] lablgtkincl;

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
	  let cat s = String.concat " " (string_list_of_file s) in
	  let core_mods = String.concat " " (List.map cat core_mllib) in
	  let ide_mods = cat ide_mllib in
	  let core_cmas = String.concat " " core_cma in
	  Echo (["let copts = \"-cclib -lcoqrun\"\n";
		 "let core_libs = \""^coqconfig^".cmo "^core_cmas^"\"\n";
		 "let core_objs = \"Coq_config "^core_mods^"\"\n";
		 "let ide = \""^ide_mods^"\"\n"],
		tolink));

(** Coqtop and coqide *)

     let rules f is_ide =
       let fo = f^".opt" and fb = f^".byte" in
       let ideflag = if is_ide then A"-ide" else N in
       let depsall = [coqmktop;libcoqrun] in
       let depso = (coqconfig^".cmx") :: core_cmxa in
       let depsb = (coqconfig^".cmo") :: core_cma in
       let depideo = if is_ide then [ide_cmxa] else [] in
       let depideb = if is_ide then [ide_cma] else [] in
       if opt then rule fo ~prod:fo ~deps:(depsall@depso@depideo)
	 (fun _ _ -> Cmd (S [P coqmktop;A"-boot";A"-opt";ideflag;
			     incl fo;A"-o";P fo]));
       rule fb ~prod:fb ~deps:(depsall@depsb@depideb)
	 (fun _ _ -> Cmd (S [P coqmktop;A"-boot";A"-top";ideflag;
			     incl fb;A"-o";P fb]));
       rule f ~prod:f ~deps:(if opt then [fb;fo] else [fb])
	 (fun _ _ -> ln_s ((Filename.basename f)^best_ext) f)
     in
     rules coqtop false;
     rules coqide true;

(** Other binaries *)

     copy_bin_alias "scripts/coqmktop" coqmktop;
     copy_bin_alias "scripts/coqc" coqc;
     copy_bin_alias "checker/main" coqchk;
     copy_bin_best "tools/coqdep_boot" coqdep_boot;
     copy_bin_best "tools/coqdep" coqdep;
     copy_bin_best "tools/coqdoc/main" coqdoc;
     copy_bin_best "tools/coqwc" coqwc;
     copy_bin_best "tools/coq_makefile" coqmakefile;
     copy_bin_best "tools/coq_tex" coqtex;
     copy_bin_best "tools/gallina" gallina;

(** Coq files dependencies *)

     rule ".v.d" ~prod:"%.v.depends" ~deps:(["%.v";coqdep_boot]@genvfiles)
       (fun env _ ->
	  let v = env "%.v" and vd = env "%.v.depends" in
	  (** NB: this relies on all .v files being already in _build. *)
	  Cmd (S [P coqdep_boot;dep_dynlink;A"-slash";P v;Sh">";P vd]));

(** Coq files compilation *)

     let coq_build_dep f build =
       (** NB: this relies on coqdep producing a single Makefile line
	   for one .v file, with some specific shape : *)
       match string_list_of_file (f^".v.depends") with
	 | vo::vg::v::deps when vo=f^".vo" && vg=f^".glob:" && v=f^".v" ->
	     let d = List.map (fun x -> [x]) deps in
	     List.iter Outcome.ignore_good (build d)
	 | _ -> failwith ("Something wrong with dependencies of "^f^".v")
     in

     let coq_v_rule d init =
       let bootflag = if init then A"-nois" else N in
       let gendeps = if init then [coqtop] else [coqtop;initialcoq] in
       rule (d^".v.vo")
	 ~prods:[d^"%.vo";d^"%.glob"] ~deps:([d^"%.v";d^"%.v.depends"]@gendeps)
	 (fun env build ->
	    let f = env (d^"%") in
	    coq_build_dep f build;
	    Cmd (S [P coqtop;A"-boot";bootflag;A"-compile";P f]))
     in
     coq_v_rule "theories/Init/" true;
     coq_v_rule "" false;

     rule "initial.coq" ~prod:initialcoq ~deps:(makeinitial :: init_vo)
       (fun _ _ ->
	  Cmd (S [P coqtop;A"-boot";A"-batch";A"-nois";A"-notop";A"-silent";
		  A"-l";P makeinitial; A"-outputstate";P initialcoq]));

(** Generation of _plugin_mod.ml files *)

     rule "_mod.ml" ~prod:"%_plugin_mod.ml" ~dep:"%_plugin.mllib"
       (fun env _ ->
	  let mods = string_list_of_file (env "%_plugin.mllib") in
	  let line s = "let _ = Mltop.add_known_module \""^s^"\"\n" in
	  Echo (List.map line mods, env "%_plugin_mod.ml"));

(** Rule for native dynlinkable plugins *)

     rule ".cmxa.cmxs" ~prod:"%.cmxs" ~dep:"%.cmxa"
       (fun env _ ->
	  (* TODO: reuse the fix for MacOS *)
	  Cmd (S [!Options.ocamlopt;A"-linkall";A"-shared";
		  A"-o";P (env "%.cmxs"); P (env "%.cmxa")]));

(** Generation of NMake.v from NMake_gen.ml *)

     rule "NMake" ~prod:nmake ~dep:nmakegen
       (fun _ _ -> Cmd (S [ocaml;P nmakegen;Sh ">";P nmake]));

 | _ -> ()

end

(** TODO / Remarques:

    * L'idée initiale de partager bin/ et _build/bin/ a coup de symlink
      etait une anerie : ocamlbuild prenait bin/foo comme _source_
      et le copiait dans _build/bin/ (par dessus foo), ce qui donnait un
      foo vide.

    ==> Pour l'instant, les binaires sont dans _build/bin uniquement.
    Une solution serait d'avoir deux repertoires de noms differents:
    bin/ et _build/binaries/ par exemple.

    * On repasse tout en revue sans arret, et c'est long, meme cached:
      1 min 25 pour les 2662 targets en cache. 
      Peut-on mieux faire ?

    * coqdep a besoin dans _build des fichiers dont on depend,
      mais ils n'y sont pas forcement, d'ou un gros cp au debut.
      Y-a-t'il mieux à faire ?

*)
