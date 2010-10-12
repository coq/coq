(** * Plugin for building Coq via Ocamlbuild *)

open Ocamlbuild_plugin
open Ocamlbuild_pack
open Printf
open Scanf

(** WARNING !! this is preliminary stuff. It should allows you to
    build coq and its libraries if everything goes right.
    Support for all the build rules and configuration options
    is progressively added. Tested only on linux + ocaml 3.11 +
    local + natdynlink for now.

    Usage:
     ./configure -local -opt
     ./build   (which launches ocamlbuild coq.otarget)

    Then you can (hopefully) launch bin/coqtop, bin/coqide and so on.
    Apart from the links in bin, every created files are in _build.
    A "./build clean" should give you back a clean source tree

*)

(** F.A.Q about ocamlbuild:

* P / Px ?

 Same, except that the second can be use to signal the main target
 of a rule, in order to get a nicer log (otherwise the full command
 is used as target name)

*)



(** Generic file reader, which produces a list of strings, one per line *)

let read_file f =
  let ic = open_in f and l = ref [] in
  (try while true do l := (input_line ic)::!l done with End_of_file -> ());
  close_in ic; List.rev !l


(** Configuration *)

(** First, we access coq_config.ml indirectly : we symlink it to
    myocamlbuild_config.ml, which is linked with this myocamlbuild.ml *)

module Coq_config = struct include Myocamlbuild_config end

let _ = begin
  Options.ocamlc := A Coq_config.ocamlc;
  Options.ocamlopt := A Coq_config.ocamlopt;
  Options.ocamlmklib := A Coq_config.ocamlmklib;
  Options.ocamldep := A Coq_config.ocamldep;
  Options.ocamldoc := A Coq_config.ocamldoc;
  Options.ocamlyacc := A Coq_config.ocamlyacc;
  Options.ocamllex := A Coq_config.ocamllex;
end

let w32 = (Coq_config.arch = "win32")

let w32pref = "i586-mingw32msvc"
let w32ocamlc = w32pref^"-ocamlc"
let w32ocamlopt = w32pref^"-ocamlopt"
let w32ocamlmklib = w32pref^"-ocamlmklib"
let w32lib = "/usr/"^w32pref^"/lib/"
let w32bin = "/usr/"^w32pref^"/bin/"

let _ = if w32 then begin
  Options.ocamlopt := A w32ocamlopt;
  Options.ocamlmklib := A w32ocamlmklib;
end

let _ =
  if Coq_config.camlp4 = "camlp5" then begin
    printf "Camlp5 is not supported by this ocamlbuild plugin\n";
    printf "Use camlp4, or make, or both\n";
    exit 1
  end

let ocaml = A Coq_config.ocaml
let camlp4o = A Coq_config.camlp4o
let camlp4incl = S[A"-I"; A Coq_config.camlp4lib]
let camlp4compat = Sh Coq_config.camlp4compat
let opt = (Coq_config.best = "opt")
let ide = Coq_config.has_coqide
let hasdynlink = Coq_config.has_natdynlink
let os5fix = (Coq_config.natdynlinkflag = "os5fixme")
let flag_dynlink = if hasdynlink then A"-DHasDynlink" else N
let dep_dynlink = if hasdynlink then N else Sh"-natdynlink no"
let lablgtkincl = Sh Coq_config.coqideincl
let local = Coq_config.local
let coqsrc = Coq_config.coqsrc
let cflags = S[A"-ccopt";A Coq_config.cflags]

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

let c_headers_base =
  ["coq_fix_code.h";"coq_instruct.h"; "coq_memory.h"; "int64_emul.h";
   "coq_gc.h"; "coq_interp.h"; "coq_values.h"; "int64_native.h";
   "coq_jumptbl.h"]
let c_headers = List.map ((^) "kernel/byterun/") c_headers_base

let coqinstrs = "kernel/byterun/coq_instruct.h"
let coqjumps = "kernel/byterun/coq_jumptbl.h"
let copcodes = "kernel/copcodes.ml"

let libcoqrun = "kernel/byterun/libcoqrun.a"

let initialcoq = "states/initial.coq"
let init_vo = ["theories/Init/Prelude.vo";"theories/Init/Logic_Type.vo"]
let makeinitial = "states/MakeInitial.v"

let nmake = "theories/Numbers/Natural/BigN/NMake_gen.v"
let nmakegen = "theories/Numbers/Natural/BigN/NMake_gen.ml"

let adapt_name (pref,oldsuf,newsuf) f =
 pref ^ (Filename.chop_suffix f oldsuf) ^ newsuf

let get_names (oldsuf,newsuf) s =
  let pref = Filename.dirname s ^ "/" in
  List.map (adapt_name (pref,oldsuf,newsuf)) (string_list_of_file s)

let get_vo_itargets f =
  let vo_itargets = get_names (".otarget",".itarget") f in
  List.flatten (List.map (get_names (".vo",".v")) vo_itargets)

let theoriesv = get_vo_itargets "theories/theories.itarget"

let pluginsv = get_vo_itargets "plugins/pluginsvo.itarget"

let pluginsmllib = get_names (".cma",".mllib") "plugins/pluginsbyte.itarget"

(** for correct execution of coqdep_boot, source files should have
    been imported in _build (and NMake_gen.v should have been created). *)

let coqdepdeps = theoriesv @ pluginsv @ pluginsmllib

let coqtop = "toplevel/coqtop"
let coqide = "ide/coqide"
let coqdepboot = "tools/coqdep_boot"
let coqmktop = "scripts/coqmktop"

(** The list of binaries to build:
    (name of link in bin/, name in _build, install both or only best) *)

type links = Both | Best | BestInPlace | Ide

let all_binaries =
 [ "coqtop", coqtop, Both;
   "coqide", coqide, Ide;
   "coqmktop", coqmktop, Both;
   "coqc", "scripts/coqc", Both;
   "coqchk", "checker/main", Both;
   "coqdep_boot", coqdepboot, Best;
   "coqdep", "tools/coqdep", Best;
   "coqdoc", "tools/coqdoc/main", Best;
   "coqwc", "tools/coqwc", Best;
   "coq_makefile", "tools/coq_makefile", Best;
   "coq-tex", "tools/coq_tex", Best;
   "gallina", "tools/gallina", Best;
   "csdpcert", "plugins/micromega/csdpcert", BestInPlace;
 ]


let best_oext = if opt then ".native" else ".byte"
let best_ext = if opt then ".opt" else ".byte"
let best_iext = if ide = "opt" then ".opt" else ".byte"

let coqtopbest = coqtop^best_oext
(* For inner needs, we rather use the bytecode versions of coqdep
   and coqmktop: slightly slower but compile quickly, and ok with
   w32 cross-compilation *)
let coqdep_boot = coqdepboot^".byte"
let coqmktop_boot = coqmktop^".byte"

let binariesopt_deps =
  let addext b = b ^ ".native" in
  let rec deps = function
    | [] -> []
    | (_,b,Ide)::l -> if ide="opt" then addext b :: deps l else deps l
    | (_,b,_)::l -> if opt then addext b :: deps l else deps l
  in deps all_binaries

let binariesbyte_deps =
  let addext b = b ^ ".byte" in
  let rec deps = function
    | [] -> []
    | (_,b,Ide)::l -> if ide<>"no" then addext b :: deps l else deps l
    | (_,b,Both)::l -> addext b :: deps l
    | (_,b,_)::l -> if not opt then addext b :: deps l else deps l
  in deps all_binaries

let ln_sf toward f =
  Command.execute ~quiet:true (Cmd (S [A"ln";A"-sf";P toward;P f]))

let rec make_bin_links = function
  | [] -> ()
  | (b,ob,kind)::l ->
      make_bin_links l;
      let obd = "../"^ !_build^"/"^ob and bd = "bin/"^b in
      match kind with
	| Ide when ide <> "no" ->
	    ln_sf (obd^".byte") (bd^".byte");
	    if ide = "opt" then ln_sf (obd^".native") (bd^".opt");
	    ln_sf (b^best_iext) bd
	| Ide (* when ide = "no" *) -> ()
	| Both ->
	    ln_sf (obd^".byte") (bd^".byte");
	    if opt then ln_sf (obd^".native") (bd^".opt");
	    ln_sf (b^best_ext) bd
	| Best -> ln_sf (obd^best_oext) bd
	| BestInPlace -> ln_sf (b^best_oext) (!_build^"/"^ob)

let incl f = Ocaml_utils.ocaml_include_flags f

let cmd cl = (fun _ _ -> (Cmd (S cl)))

let initial_actions () = begin
  (** We "pre-create" a few subdirs in _build *)
  Shell.mkdir_p (!_build^"/dev");
  Shell.mkdir_p (!_build^"/bin");
  Shell.mkdir_p (!_build^"/plugins/micromega");
  make_bin_links all_binaries;
end

let extra_rules () = begin

(** Virtual target for building all binaries *)

  rule "binariesopt" ~stamp:"binariesopt" ~deps:binariesopt_deps (fun _ _ -> Nop);
  rule "binariesbyte" ~stamp:"binariesbyte" ~deps:binariesbyte_deps (fun _ _ -> Nop);
  rule "binaries" ~stamp:"binaries" ~deps:["binariesbyte";"binariesopt"] (fun _ _ -> Nop);

(** We create a special coq_config which mentions _build *)

  rule "coq_config.ml" ~prod:"coq_config.ml" ~dep:"config/coq_config.ml"
    (fun _ _ ->
       if w32 then cp "config/coq_config.ml" "coq_config.ml" else
       let lines = read_file "config/coq_config.ml" in
       let lines = List.map (fun s -> s^"\n") lines in
       let srcbuild = Filename.concat coqsrc !_build in
       let line0 = "\n(* Adapted variables for ocamlbuild *)\n" in
       let line1 = "let coqsrc = \""^srcbuild^"\"\n" in
       let line2 = "let coqlib = \""^srcbuild^"\"\n" in
       (* TODO : line3 isn't completely accurate with respect to ./configure:
	  the case of -local -coqrunbyteflags foo isn't supported *)
       let line3 =
	 "let coqrunbyteflags = \"-dllib -lcoqrun -dllpath '"
	 ^srcbuild^"/kernel/byterun'\"\n"
       in
       Echo (lines @ [line0;line1] @ (if local then [line2;line3] else []),
	     "coq_config.ml"));

(** Camlp4 extensions *)

  rule ".ml4.ml" ~dep:"%.ml4" ~prod:"%.ml"
    (fun env _ ->
       let ml4 = env "%.ml4" and ml = env "%.ml" in
       Cmd (S[camlp4o;T(tags_of_pathname ml4 ++ "p4mod");readable_flag;
	      T(tags_of_pathname ml4 ++ "p4option"); camlp4compat;
	      A"-o"; Px ml; A"-impl"; P ml4]));

  flag_and_dep ["p4mod"; "use_grammar"] (P "parsing/grammar.cma");
  flag_and_dep ["p4mod"; "use_constr"] (P "parsing/q_constr.cmo");

  flag_and_dep ["p4mod"; "use_compat5"] (P "tools/compat5.cmo");
  flag_and_dep ["p4mod"; "use_compat5b"] (P "tools/compat5b.cmo");

  let mlp_cmo s =
    let src=s^".mlp" and dst=s^".cmo" in
    rule (src^".cmo") ~dep:src ~prod:dst ~insert:`top
      (fun env _ ->
	 Cmd (S [!Options.ocamlc; A"-c"; A"-pp";
		 Quote (S [camlp4o;A"-impl"]); camlp4incl; A"-impl"; P src]))
  in
  mlp_cmo "tools/compat5";
  mlp_cmo "tools/compat5b";

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

(** C code for the VM *)

  dep ["compile"; "c"] c_headers;
  flag ["compile"; "c"] cflags;
  dep ["link"; "ocaml"; "use_libcoqrun"] [libcoqrun];

  (* we need to use a different ocamlc. For now we copy the rule *)
  if w32 then
  rule ".c.o"  ~deps:("%.c"::c_headers) ~prod:"%.o" ~insert:`top
    (fun env _ ->
       let c = env "%.c" in
       let o = env "%.o" in
       Seq [Cmd (S [P w32ocamlc;cflags;A"-c";Px c]);
	    mv  (Filename.basename o) o]);

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

  rule tolink ~deps:(ide_mllib::core_mllib) ~prod:tolink
    (fun _ _ ->
       let cat s = String.concat " " (string_list_of_file s) in
       let core_mods = String.concat " " (List.map cat core_mllib) in
       let ide_mods = cat ide_mllib in
       let core_cmas = String.concat " " core_cma in
       Echo (["let copts = \"-cclib -lcoqrun\"\n";
	      "let core_libs = \"coq_config.cmo "^core_cmas^"\"\n";
	      "let core_objs = \"Coq_config "^core_mods^"\"\n";
	      "let ide = \""^ide_mods^"\"\n"],
	     tolink));

(** Coqtop and coqide *)

  let mktop_rule f is_ide =
    let fo = f^".native" and fb = f^".byte" in
    let ideflag = if is_ide then A"-ide" else N in
    let depsall = [coqmktop_boot;libcoqrun] in
    let depso = "coq_config.cmx" :: core_cmxa in
    let depsb = "coq_config.cmo" :: core_cma in
    let depideo = if is_ide then [ide_cmxa] else [] in
    let depideb = if is_ide then [ide_cma] else [] in
    let w32ideflag = (*if is_ide then [A"-ccopt";A"\"-link -mwindows\""] else*) [] in
    let w32flag = if not w32 then N else S ([A"-camlbin";A w32bin]@w32ideflag) in
    if opt then rule fo ~prod:fo ~deps:(depsall@depso@depideo) ~insert:`top
      (cmd [P coqmktop_boot;w32flag;A"-boot";A"-opt";ideflag;incl fo;A"-o";Px fo]);
    rule fb ~prod:fb ~deps:(depsall@depsb@depideb) ~insert:`top
      (cmd [P coqmktop_boot;w32flag;A"-boot";A"-top";ideflag;incl fb;A"-o";Px fb]);
  in
  mktop_rule coqtop false;
  mktop_rule coqide true;

(** Coq files dependencies *)

  rule "coqdepready" ~stamp:"coqdepready" ~deps:coqdepdeps (fun _ _ -> Nop);

  rule ".v.d" ~prod:"%.v.depends" ~deps:["%.v";coqdep_boot;"coqdepready"]
    (fun env _ ->
       let v = env "%.v" and vd = env "%.v.depends" in
       (** NB: this relies on all .v files being already in _build. *)
       Cmd (S [P coqdep_boot;dep_dynlink;A"-slash";P v;Sh">";Px vd]));

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
    let gendep = if init then coqtopbest else initialcoq in
    rule (d^".v.vo")
      ~prods:[d^"%.vo";d^"%.glob"] ~deps:[gendep;d^"%.v";d^"%.v.depends"]
      (fun env build ->
	 let f = env (d^"%") in
	 coq_build_dep f build;
	 Cmd (S [P coqtopbest;A"-boot";bootflag;A"-compile";Px f]))
  in
  coq_v_rule "theories/Init/" true;
  coq_v_rule "" false;

(** Initial state *)

  rule "initial.coq" ~prod:initialcoq ~deps:(makeinitial::init_vo)
    (cmd [P coqtopbest;A"-boot";A"-batch";A"-nois";A"-notop";A"-silent";
	  A"-l";P makeinitial; A"-outputstate";Px initialcoq]);

(** Generation of _plugin_mod.ml files *)

  rule "_mod.ml" ~prod:"%_plugin_mod.ml" ~dep:"%_plugin.mllib"
    (fun env _ ->
       let line s = "let _ = Mltop.add_known_module \""^s^"\"\n" in
       let mods =
	 string_list_of_file (env "%_plugin.mllib") @
	   [Filename.basename (env "%_plugin")]
       in
       Echo (List.map line mods, env "%_plugin_mod.ml"));

(** Rule for native dynlinkable plugins *)

  rule ".cmxa.cmxs" ~prod:"%.cmxs" ~dep:"%.cmxa"
    (fun env _ ->
       let cmxs = Px (env "%.cmxs") and cmxa = P (env "%.cmxa") in
       if os5fix then
	 Cmd (S [A"../dev/ocamlopt_shared_os5fix.sh"; !Options.ocamlopt; cmxs])
       else
	 Cmd (S [!Options.ocamlopt;A"-linkall";A"-shared";A"-o";cmxs;cmxa]));

(** Generation of NMake.v from NMake_gen.ml *)

  rule "NMake" ~prod:nmake ~dep:nmakegen
    (cmd [ocaml;P nmakegen;Sh ">";Px nmake]);

end

(** Registration of our rules (after the standard ones) *)

let _ = dispatch begin function
  | After_rules -> initial_actions (); extra_rules ()
  | _ -> ()
end

(** TODO / Remarques:

    * Apres un premier build, le second prend du temps, meme cached:
      1 min 25 pour les 2662 targets en cache. Etonnement, refaire
      coqtop.byte ne prend que ~4s, au lieu des ~40s pour coqtop.opt.
      A comprendre ...

    * Parallelisation: vraiment pas top

*)
