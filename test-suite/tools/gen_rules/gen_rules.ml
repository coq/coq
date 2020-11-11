(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* gen_rules: generate dune build rules for Coq's test-suite            *)
(* It is desirable that this file can be bootstrapped alone             *)

let worker_deps deps lvl =
  [ "%{bin:coqtacticworker.opt}"
  ; "%{bin:coqproofworker.opt}"
  ; "%{bin:coqqueryworker.opt}"
  ] @ deps lvl

(* scan *)
let plugins_dir = ["btauto"; "cc"; "derive"; "extraction"; "firstorder"; "funind"; "ltac"; "ltac2"; "micromega"; "nsatz"; "ring"; "rtauto"; "ssr"; "ssrmatching"; "syntax"]

(* TODO: This is already in coq_rules for stdlib *)
let plugins_cctx lvl =
  List.concat_map (fun pdir -> ["-I"; Filename.(concat (concat lvl "../plugins") pdir)]) plugins_dir

let in_subdir_foreach_ext ~out ?(ext=".v") ?(ignore=[]) f dir =
  Dune.Rules.in_subdir out dir ~f:(fun _ () ->
    let files = Dir.scan_files_by_ext ~ext ~ignore dir in
    List.iter f files)

let test_in_subdir ~out ?ext ?out_file_ext ?(log_file_ext=".log") ?(targets=[]) ?(deps=[]) ~run ~dir () =
  (* log file extension is appended, out file extension is replaced *)
  in_subdir_foreach_ext ~out ?ext (fun file ->
    let log_file = file ^ log_file_ext in
    Dune.Rules.run ~run:(run file) ~out ~log_file ~targets ~deps:(file :: deps) ();
    match out_file_ext with
    | Some out_file_ext ->
      let out_file = Filename.chop_extension file ^ out_file_ext in
      Dune.Rules.diff ~out out_file log_file
    | None -> ()) dir

let test_ide ~out ~deps : unit =
  let dir = "ide" in
  let lvl = ".." in
  let args file = [
    "-q" ;
    "-async-proofs" ; "on" ;
    "-async-proofs-tactic-error-resilience" ; "off";
    "-async-proofs-command-error-resilience" ; "off";
    "-boot";
    "-R"; Filename.concat lvl "../theories" ; "Coq";
    "-R"; Filename.concat lvl "prerequisite"; "TestSuite";
    "-Q"; Filename.concat lvl "../user-contrib/Ltac2"; "Ltac2";
    ] @ (plugins_cctx lvl) @ Coq_rules.vfile_header ~dir file
    |> String.concat " "
  in
  (* NOTE: it is very important for the arguments to be quoted, so args will have to be flattened *)
  let run = fun file -> ["fake_ide"; "%{bin:coqidetop.opt}"; file; "\"" ^ args file ^ "\""] in
  test_in_subdir ~dir ~out ~run ~ext:".fake" ~deps ()

let coqdoc_html_with_diff_rule ~dir ~out file  =
  let filename = Filename.chop_extension file in
  let doc_file = filename ^ ".html" in
  let log_file = filename ^ ".html.log" in
  let out_file = filename ^ ".html.out" in
  let vofile = filename ^ ".vo" in
  let globfile = filename ^ ".glob" in
  let args = [
    "-utf8";
    "-coqlib_url"; "http://coq.inria.fr/stdlib";
    "--html";
    ]
    (* Get extra args under "coqdoc-prog-args" in file *)
    @ Coq_rules.vfile_header ~dir ~name:"coqdoc-prog-args" file
  in
  let run = "%{bin:coqdoc}" :: args @ [file] in
  Dune.Rules.run ~run ~out ~log_file ~targets:[doc_file]
    ~deps:[file; vofile; globfile; "(package coq-core)"] ();
  Dune.Rules.diff ~out out_file doc_file

let coqdoc_latex_with_diff_rule ~dir ~out file  =
  let filename = Filename.chop_extension file in
  let doc_file = filename ^ ".tex" in
  let doc_file_scrub = filename ^ ".tex.scrub" in
  let log_file = filename ^ ".tex.log" in
  let out_file = filename ^ ".tex.out" in
  let vofile = filename ^ ".vo" in
  let globfile = filename ^ ".glob" in
  let args = [
    "-utf8";
    "-coqlib_url"; "http://coq.inria.fr/stdlib";
    "--latex";
    ]
    (* Get extra args under "coqdoc-prog-args" in file *)
    @ Coq_rules.vfile_header ~dir ~name:"coqdoc-prog-args" file
  in
  Dune.Rules.run ~out ~run:("%{bin:coqdoc}" :: args @ [file])
    ~log_file ~targets:[doc_file]
    ~deps:[file; vofile; globfile; "(package coq-core)"] ();
  (* We need to scrub the .tex file of comments begining %% *)
  Dune.Rules.run ~out ~run:["grep"; "-v"; "\"^%%\""; doc_file]
    ~log_file:doc_file_scrub ~deps:[doc_file] ();
  Dune.Rules.diff ~out out_file doc_file_scrub

let test_coqdoc ~out dir =
  in_subdir_foreach_ext ~out (fun file ->
    coqdoc_html_with_diff_rule ~dir ~out file;
    coqdoc_latex_with_diff_rule ~dir ~out file;
    ()) dir

let test_tool ?(envs=[]) ?(deps=[]) ~out ?(ignore=[]) dir =
  Dune.Rules.in_subdir out dir ~f:(fun out () ->
    let dirs = Dir.scan_dirs dir ~ignore in
    let per_dir subdir =
      Dune.Rules.in_subdir out subdir ~f:(fun out () ->
        Dune.Rules.run ~run:["./run.sh"] ~out ~log_file:(subdir ^ ".log")
          ~deps:(["run.sh"; "(source_tree .)"] @ deps)
          ~envs
        ())
    in
    List.iter per_dir dirs)

let test_misc ~out ?(ignore=[]) dir =
  in_subdir_foreach_ext ~out ~ext:".sh" ~ignore (fun file ->
    let log_file = file ^ ".log" in
    Dune.Rules.run ~out ~run:["./" ^ file] ~log_file
      ~deps:[
        file;
        (* We need all files in misc as deps *)
        (* These could be finer, but at this point its better to just rereun
        them all. In the future we could make a lot of tests in misc into cram
        tests which would allow for finer deps than we currently have. *)
        "(source_tree .)";
        "../../config/coq_config.py";
        "../prerequisite/ssr_mini_mathcomp.vo";
        "(package coq-core)";
        "(source_tree deps)";
        (* This is needed because of universe.v *)
        (* We could probably do a lot better (stdlib tests?) *)
        "(package coq-stdlib)";
        "%{lib:coq-core.vm:../../stublibs/dllcoqrun_stubs.so}";
        (* coq_environment.sh (already pulled by coq-core tho) *)
        "../../tools/CoqMakefile.in";
        (* printers.sh deps *)
        "../../dev/incdir_dune";
        "../../dev/base_include";
        "../../dev/inc_ltac_dune";
        "../../dev/include_printers";
        "../../dev/include";
        "../../dev/top_printers.ml";
        "../../dev/vm_printers.ml";
        (* coqtop_print-mod-uid.sh deps *)
        "../prerequisite/admit.vo";
      ] ();
    ()) dir

  let test_complexity ~out ~cctx ?(envs=[]) ?(deps=(fun _ -> [])) ?(ignore=[]) ~dir () =
    (* Is this really a useful metric? *)
    (* Fetch bogomips value *)
    let run cmd =
      let inp = Unix.open_process_in cmd in
      let r = input_line inp in
      close_in inp; r
    in
    (* TODO: what if this doesn't work? Windows? *)
    let bogomips = run "./tools/bogomips.sh" in
    (* Run tests *)
    Coq_rules.check_dir ~out ~cctx ~envs ~dir
      (* ~output:Coq_rules.Compilation.Output.MainJob *)
      ~deps:(worker_deps deps)
      ~args:["-test-mode"; "-async-proofs-cache"; "force"] ();
    (* Run complexity.sh on test *)
    in_subdir_foreach_ext ~out ~ext:".v" ~ignore
      (fun file ->
        let vofile = file ^ "o" in
        let log_file = file ^ ".log" in
        Dune.Rules.run ~out
          ~deps:[
            vofile;
            "../tools/complexity.sh";
            ]
          ~envs:["BOGOMIPS", bogomips]
          ~run:["../tools/complexity.sh"; file; log_file] ()
      ) dir;
    ()

let output_rules out =

  (* Common context - This will be passed to coqdep and coqc *)
  let cctx lvl =
    [ "-boot"
    ; "-R"; Filename.concat lvl "prerequisite"; "TestSuite"
    ; "-R"; Filename.concat lvl "../theories" ; "Coq"
    ; "-Q"; Filename.concat lvl "../user-contrib/Ltac2"; "Ltac2"
    (* TODO perhaps this instead of above? *)
    (* ; "-Q"; Filename.concat lvl "../user-contrib"; "" *)
    ] @ plugins_cctx lvl
  in

  (* Including this argument will allow .csdp.cache to be copied into that test
  directory in a writable state. *)
  let copy_csdp_cache = ".csdp.cache.test-suite" in

  (* Some standard deps to pass to test rules, for now we inject
     prelude to everyone *)
  let deps lvl = [ Filename.concat lvl "../theories/Init/Prelude.vo" ] in

  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"prerequisite" ();

  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"bugs" ~copy_csdp_cache
    ~ignore:[ "bug_2923.v"     (* coqchk will fail on bug_2923.v see coq/coq#15930  *)
            ; "bug_12138.v"    (* coqdep cannot parse bug_12138.v *)
            ; "bug_16278.v"    (* doesn't work :( *)
            ] ();

  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"coqchk" ~copy_csdp_cache ();
  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"failure" ();
  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"interactive" ~kind:Coqtop ();
  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"ltac2" ();
  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"micromega" ~copy_csdp_cache ();

  (* We override cctx here in order to pass these arguments to coqdep uniformly *)
  begin
  let cctx lvl = ["-R"; lvl; "Mods"] in
  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"modules" ()
  end;

  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"output" ~output:MainJob ~copy_csdp_cache
    ~args:["-test-mode"; "-async-proofs-cache"; "force"]
    (* TODO: Load.v is broken because we call coqdep in one directory and run coqc in another. *)
    ~ignore:["Load.v"]
    ();

  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"output-coqchk" ~output:CheckJob ();
  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"output-coqtop" ~output:MainJob ~kind:Coqtop ();

  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"output-failure" ~output:MainJob
    ~args:["-test-mode"; "-async-proofs-cache"; "force"] ~exit_codes:[1] ();

  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"output-modulo-time" ~output:MainJobModTime ();
  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"primitive/arrays" ();
  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"primitive/float" ();
  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"primitive/sint63" ();
  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"primitive/uint63" ();
  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"ssr" ();

  Coq_rules.check_dir ~out ~cctx ~deps:(worker_deps deps) ~dir:"stm" ~args:["-async-proofs"; "on"] ();
  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"success" ();
  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"vio" ~kind:Vio ();
  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"vio" ~kind:Vio2vo ();

  (* Other tests *)

  test_complexity ~out ~cctx ~deps ~dir:"complexity"
    (* This fails sporadically *)
    ~ignore:["pretyping.v"] ();

  test_in_subdir ~out ~dir:"coqwc" ~run:(fun file -> ["coqwc"; file]) ();

  test_ide ~out ~deps:[
    "(source_tree %{project_root}/test-suite/output/load)";
    "%{project_root}/theories/Init/Prelude.vo";
    "%{project_root}/theories/Lists/List.vo";
    "%{project_root}/theories/extraction/Extraction.vo";
    "%{project_root}/user-contrib/Ltac2/Ltac2.vo";
    "(package coq-core)";
    ];

  Coq_rules.check_dir ~out ~cctx ~deps ~dir:"coqdoc" ~args:["-Q"; "coqdoc"; "Coqdoc"] ();

  test_coqdoc ~out "coqdoc";

  test_tool ~out "coq-makefile" ~ignore:["template"]
    ~deps:[
      "%{bin:coq_makefile}";
      "%{project_root}/tools/CoqMakefile.in";
      "(source_tree ../template)";
      "(package coq-core)";
      (* TODO: refine this *)
      "(package coq-stdlib)";
      ]
    ~envs:[
      "CoqMakefile_in", "%{project_root}/tools/CoqMakefile.in";
      "TTOOLSDIR", "%{project_root}/tools";
      ];

  test_tool ~out "tools" ~ignore:["gen_rules"]
    ~deps:[
      "(source_tree %{project_root}/theories/Compat)";
      "%{project_root}/test-suite/success/CompatOldOldFlag.v";
      "%{project_root}/sysinit/coqargs.ml";
      "%{project_root}/tools/configure/configure.ml";
      "%{project_root}/dev/tools/update-compat.py";
      "%{project_root}/dev/header.ml";
      "%{project_root}/doc/stdlib/index-list.html.template";
      ];

  test_misc ~out "misc";
  ()

let main () =
  let out = open_out "test_suite_rules.sexp" in
  let fmt = Format.formatter_of_out_channel out in
  output_rules fmt;
  Format.pp_print_flush fmt ();
  close_out out

let () =
  Printexc.record_backtrace true;
  try main ()
  with exn ->
    let bt = Printexc.get_backtrace () in
    let exn = Printexc.to_string exn in
    Format.eprintf "%s@\n%s@\n%!" exn bt;
    let exception Gen_rules_Anomaly in
    raise Gen_rules_Anomaly
