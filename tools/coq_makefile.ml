(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Coq_makefile: automatically create a Makefile for a Coq development *)

let output_channel = ref stdout
let makefile_name = ref "Makefile"
let make_name = ref ""

let some_vfile = ref false
let some_mlfile = ref false
let some_mlifile = ref false
let some_ml4file = ref false
let some_mllibfile = ref false
let some_mlpackfile = ref false

let print x = output_string !output_channel x
let printf x = Printf.fprintf !output_channel x

let rec print_list sep = function
  | [ x ] -> print x
  | x :: l -> print x; print sep; print_list sep l
  | [] -> ()

let rec print_prefix_list sep = function
  | x :: l -> print sep; print x; print_prefix_list sep l
  | [] -> ()

let section s =
  let l = String.length s in
  let print_com s =
    print "#";
    print s;
    print "#\n" in
  print_com (String.make (l+2) '#');
  print_com (String.make (l+2) ' ');
  print "# "; print s; print " #\n";
  print_com (String.make (l+2) ' ');
  print_com (String.make (l+2) '#');
  print "\n"

(* These are the Coq library directories that are used for
 * plugin development
 *)
let lib_dirs =
  ["kernel"; "lib"; "library"; "parsing";
   "pretyping"; "interp"; "printing"; "intf";
   "proofs"; "tactics"; "tools";
   "vernac"; "stm"; "toplevel"; "grammar"; "config";
   "engine"]


let usage () =
  output_string stderr "Usage summary:\
\n\
\ncoq_makefile .... [file.v] ... [file.ml[i4]?] ... [file.ml{lib,pack}]\
\n  ... [any] ... [-extra[-phony] result dependencies command]\
\n  ... [-I dir] ... [-R physicalpath logicalpath]\
\n  ... [-Q physicalpath logicalpath] ... [VARIABLE = value]\
\n  ...  [-arg opt] ... [-opt|-byte] [-no-install] [-f file] [-o file]\
\n  [-h] [--help]\
\n\
\n[file.v]: Coq file to be compiled\
\n[file.ml[i4]?]: Objective Caml file to be compiled\
\n[file.ml{lib,pack}]: ocamlbuild file that describes a Objective Caml\
\n  library/module\
\n[any] : subdirectory that should be \"made\" and has a Makefile itself\
\n  to do so. Very fragile and discouraged.\
\n[-extra result dependencies command]: add target \"result\" with command\
\n  \"command\" and dependencies \"dependencies\". If \"result\" is not\
\n  generic (do not contains a %), \"result\" is built by _make all_ and\
\n  deleted by _make clean_.\
\n[-extra-phony result dependencies command]: add a PHONY target \"result\"\
\n with command \"command\" and dependencies \"dependencies\". Note that\
\n _-extra-phony foo bar \"\"_ is a regular way to add the target \"bar\" as\
\n as a dependencies of an already defined target \"foo\".\
\n[-I dir]: look for Objective Caml dependencies in \"dir\"\
\n[-R physicalpath logicalpath]: look for Coq dependencies resursively\
\n  starting from \"physicalpath\". The logical path associated to the\
\n  physical path is \"logicalpath\".\
\n[-Q physicalpath logicalpath]: look for Coq dependencies starting from\
\n  \"physicalpath\". The logical path associated to the physical path\
\n  is \"logicalpath\".\
\n[VARIABLE = value]: Add the variable definition \"VARIABLE=value\"\
\n[-byte]: compile with byte-code version of coq\
\n[-opt]: compile with native-code version of coq\
\n[-arg opt]: send option \"opt\" to coqc\
\n[-install opt]: where opt is \"user\" to force install into user directory,\
\n  \"none\" to build a makefile with no install target or\
\n  \"global\" to force install in $COQLIB directory\
\n[-f file]: take the contents of file as arguments\
\n[-o file]: output should go in file file\
\n	Output file outside the current directory is forbidden.\
\n[-h]: print this usage summary\
\n[--help]: equivalent to [-h]\n";
  exit 1

let is_genrule r = (* generic rule (like bar%foo: ...) *)
    let genrule = Str.regexp("%") in
      Str.string_match genrule r 0

let string_prefix a b =
  let rec aux i =
    try if a.[i] = b.[i] then aux (i+1) else i with Invalid_argument _ -> i
  in
  String.sub a 0 (aux 0)

let is_prefix dir1 dir2 =
  let l1 = String.length dir1 in
  let l2 = String.length dir2 in
  let sep = Filename.dir_sep in
  if dir1 = dir2 then true
  else if l1 + String.length sep <= l2 then
    let dir1' = String.sub dir2 0 l1 in
    let sep' = String.sub dir2 l1 (String.length sep) in
    dir1' = dir1 && sep' = sep
  else false

let physical_dir_of_logical_dir ldir =
  let le = String.length ldir - 1 in
  let pdir =
    if le >= 0 && ldir.[le] = '.' then String.sub ldir 0 (le - 1)
    else ldir
  in
  String.map (fun c -> if c = '.' then '/' else c) pdir

let standard opt =
  print "byte:\n";
  print "\t$(MAKE) all \"OPT:=-byte\"\n\n";
  print "opt:\n";
  if not opt then print "\t@echo \"WARNING: opt is disabled\"\n";
  print "\t$(MAKE) all \"OPT:="; print (if opt then "-opt" else "-byte");
  print "\"\n\n"

let classify_files_by_root var files (inc_ml,inc_i,inc_r) =
  if List.exists (fun (pdir,_,_) -> pdir = ".") inc_r ||
     List.exists (fun (pdir,_,_) -> pdir = ".") inc_i
  then ()
  else
    let absdir_of_files =List.rev_map
	(fun x -> CUnix.canonical_path_name (Filename.dirname x))
	files
    in
    (* files in scope of a -I option (assuming they are no overlapping) *)
    if List.exists (fun (_,a) -> List.mem a absdir_of_files) inc_ml then
      begin
	printf "%sINC=" var;
	List.iter (fun (pdir,absdir) ->
		   if List.mem absdir absdir_of_files
		   then printf "$(filter $(wildcard %s/*),$(%s)) " pdir var)
		  inc_ml;
	printf "\n";
      end;
    (* Files in the scope of a -R option (assuming they are disjoint) *)
    List.iteri (fun i (pdir,_,abspdir) ->
		if List.exists (is_prefix abspdir) absdir_of_files then
		  printf "%s%d=$(patsubst %s/%%,%%,$(filter %s/%%,$(%s)))\n"
			 var i pdir pdir var)
	       (inc_i@inc_r)

let vars_to_put_by_root var_x_files_l (inc_ml,inc_i,inc_r) =
  let var_x_absdirs_l =
    List.rev_map
      (fun (v,l) ->
       (v,List.rev_map
            (fun x -> CUnix.canonical_path_name (Filename.dirname x)) l))
      var_x_files_l
  in
  let var_filter f g =
    List.fold_left
      (fun acc (var,dirs) -> if f dirs then (g var)::acc else acc)
      [] var_x_absdirs_l
  in
  (* All files caught by a -R . option (assuming it is the only one) *)
  match inc_i@inc_r with
  |[(".",t,_)] ->
    (None,[".",physical_dir_of_logical_dir t,List.rev_map fst var_x_files_l])
  |l ->
    try
      let out = List.assoc "." (List.rev_map (fun (p,l,_) -> (p,l)) l) in
      let () = prerr_string "Warning: install rule assumes that -R/-Q . _ is the only -R/-Q option\n"
      in
      (None,[".",physical_dir_of_logical_dir out,List.rev_map fst var_x_files_l])
    with Not_found ->
      (* vars for -Q options *)
      let varq = var_filter
                   (fun l -> List.exists (fun (_,a) -> List.mem a l) inc_ml)
                   (fun x -> x)
      in
      (* (physical dir, physical dir of logical path,vars) for -R options
	 (assuming physical dirs are disjoint) *)
      let other =
        if l = [] then
	  [".","$(INSTALLDEFAULTROOT)",[]]
        else
	  Util.List.fold_left_i (fun i out (pdir,ldir,abspdir) ->
	    let vars_r = var_filter
                           (List.exists (is_prefix abspdir))
                           (fun x -> x^string_of_int i)
            in
	    let pdir' = physical_dir_of_logical_dir ldir in
	    (pdir,pdir',vars_r)::out) 0 [] l
      in (Some varq, other)

let install_include_by_root perms =
  let install_dir for_i (pdir,pdir',vars) =
    let b = vars <> [] in
    if b then begin
      printf "\tcd \"%s\" && for i in " pdir;
      print_list " " (List.rev_map (Format.sprintf "$(%s)") vars);
      print "; do \\\n";
      printf "\t install -d \"`dirname \"$(DSTROOT)\"$(COQLIBINSTALL)/%s/$$i`\"; \\\n" pdir';
      printf "\t install -m %s $$i \"$(DSTROOT)\"$(COQLIBINSTALL)/%s/$$i; \\\n" perms pdir';
      printf "\tdone\n";
    end;
    for_i b pdir' in
  let install_i = function
    |[] -> fun _ _ -> ()
    |l -> fun b d ->
      if not b then printf "\tinstall -d \"$(DSTROOT)\"$(COQLIBINSTALL)/%s; \\\n" d;
      print "\tfor i in ";
      print_list " " (List.rev_map (Format.sprintf "$(%sINC)") l);
      print "; do \\\n";
      printf "\t install -m %s $$i \"$(DSTROOT)\"$(COQLIBINSTALL)/%s/`basename $$i`; \\\n" perms d;
      printf "\tdone\n"
  in function
  |None,l -> List.iter (install_dir (fun _ _ -> ())) l
  |Some v_i,l -> List.iter (install_dir (install_i v_i)) l

let uninstall_by_root =
  let uninstall_dir for_i (pdir,pdir',vars) =
    printf "\tprintf 'cd \"$${DSTROOT}\"$(COQLIBINSTALL)/%s" pdir';
    if vars <> [] then begin
      print " && rm -f ";
      print_list " " (List.rev_map (Format.sprintf "$(%s)") vars);
    end;
    for_i ();
    print " && find . -type d -and -empty -delete\\n";
    print "cd \"$${DSTROOT}\"$(COQLIBINSTALL) && ";
    printf "find \"%s\" -maxdepth 0 -and -empty -exec rmdir -p \\{\\} \\;\\n' >> \"$@\"\n" pdir'
in
  let uninstall_i = function
    |[] -> ()
    |l ->
      print " && \\\\\\nfor i in ";
      print_list " " (List.rev_map (Format.sprintf "$(%sINC)") l);
      print "; do rm -f \"`basename \"$$i\"`\"; done"
  in function
  |None,l -> List.iter (uninstall_dir (fun _ -> ())) l
  |Some v_i,l -> List.iter (uninstall_dir (fun () -> uninstall_i v_i)) l

let where_put_doc = function
    |_,[],[] -> "$(INSTALLDEFAULTROOT)";
    |_,((_,lp,_)::q as inc_i),[] ->
      let pr = List.fold_left (fun a (_,b,_) -> string_prefix a b) lp q in
      if (pr <> "") &&
	((List.exists (fun(_,b,_) -> b = pr) inc_i)
	 || pr.[String.length pr - 1] = '.')
      then
	physical_dir_of_logical_dir pr
      else
	let () = prerr_string ("Warning: -Q options don't have a correct common prefix,"
                        ^ " install-doc will put anything in $INSTALLDEFAULTROOT\n") in
	"$(INSTALLDEFAULTROOT)"
    |_,inc_i,((_,lp,_)::q as inc_r) ->
      let pr = List.fold_left (fun a (_,b,_) -> string_prefix a b) lp q in
      let pr = List.fold_left (fun a (_,b,_) -> string_prefix a b) pr inc_i in
      if (pr <> "") &&
	((List.exists (fun(_,b,_) -> b = pr) inc_r)
	 || (List.exists (fun(_,b,_) -> b = pr) inc_i)
	 || pr.[String.length pr - 1] = '.')
      then
	physical_dir_of_logical_dir pr
      else
	let () = prerr_string ("Warning: -R/-Q options don't have a correct common prefix,"
                        ^ " install-doc will put anything in $INSTALLDEFAULTROOT\n") in
	"$(INSTALLDEFAULTROOT)"

let install (vfiles,(mlis,ml4s,mls,mllibs,mlpacks),_,sds) inc = function
  |Project_file.NoInstall -> ()
  |is_install ->
    let not_empty = function |[] -> false |_::_ -> true in
    let cmos = List.rev_append mlpacks (List.rev_append mls ml4s) in
    let cmis = List.rev_append mlis cmos in
    let cmxss = List.rev_append cmos mllibs in
    let where_what_cmxs = vars_to_put_by_root [("CMXSFILES",cmxss)] inc in
    let where_what_oth = vars_to_put_by_root
      [("VOFILES",vfiles);("VFILES",vfiles);
       ("GLOBFILES",vfiles);("NATIVEFILES",vfiles);
       ("CMOFILES",cmos);("CMIFILES",cmis);("CMAFILES",mllibs)]
      inc in
    let doc_dir = where_put_doc inc in
    if is_install = Project_file.UnspecInstall then begin
	print "userinstall:\n\t+$(MAKE) USERINSTALL=true install\n\n"
    end;
    if not_empty cmxss then begin
      print "install-natdynlink:\n";
      install_include_by_root "0755" where_what_cmxs;
      print "\n";
    end;
    if not_empty cmxss then begin
      print "install-toploop: $(MLLIBFILES:.mllib=.cmxs)\n";
      printf "\t install -d \"$(DSTROOT)\"$(COQTOPINSTALL)/\n";
      printf "\t install -m 0755 $?  \"$(DSTROOT)\"$(COQTOPINSTALL)/\n";
      print "\n";
    end;
    print "install:";
    if not_empty cmxss then begin
      print "$(if $(HASNATDYNLINK_OR_EMPTY),install-natdynlink)";
    end;
    print "\n";
    install_include_by_root "0644" where_what_oth;
    List.iter
      (fun x ->
	printf "\t+cd %s && $(MAKE) DSTROOT=\"$(DSTROOT)\" INSTALLDEFAULTROOT=\"$(INSTALLDEFAULTROOT)/%s\" install\n" x x)
      sds;
    print "\n";
    let install_one_kind kind dir =
      printf "\tinstall -d \"$(DSTROOT)\"$(COQDOCINSTALL)/%s/%s\n" dir kind;
      printf "\tfor i in %s/*; do \\\n" kind;
      printf "\t install -m 0644 $$i \"$(DSTROOT)\"$(COQDOCINSTALL)/%s/$$i;\\\n" dir;
      print "\tdone\n" in
    print "install-doc:\n";
    if not_empty vfiles then install_one_kind "html" doc_dir;
    if not_empty mlis then install_one_kind "mlihtml" doc_dir;
    print "\n";
    let uninstall_one_kind kind dir =
      printf "\tprintf 'cd \"$${DSTROOT}\"$(COQDOCINSTALL)/%s \\\\\\n' >> \"$@\"\n" dir;
      printf "\tprintf '&& rm -f $(shell find \"%s\" -maxdepth 1 -and -type f -print)\\n' >> \"$@\"\n" kind;
      print "\tprintf 'cd \"$${DSTROOT}\"$(COQDOCINSTALL) && ";
      printf "find %s/%s -maxdepth 0 -and -empty -exec rmdir -p \\{\\} \\;\\n' >> \"$@\"\n" dir kind
    in
    printf "uninstall_me.sh: %s\n" !makefile_name;
    print "\techo '#!/bin/sh' > $@\n";
    if not_empty cmxss then uninstall_by_root where_what_cmxs;
    uninstall_by_root where_what_oth;
    if not_empty vfiles then uninstall_one_kind "html" doc_dir;
    if not_empty mlis then uninstall_one_kind "mlihtml" doc_dir;
    print "\tchmod +x $@\n";
    print "\n";
    print "uninstall: uninstall_me.sh\n";
    print "\tsh $<\n\n"

let make_makefile sds =
  if !make_name <> "" then begin
    printf "%s: %s\n" !makefile_name !make_name;
    print "\tmv -f $@ $@.bak\n";
    print "\t\"$(COQBIN)coq_makefile\" -f $< -o $@\n\n";
    List.iter
      (fun x -> print "\t+cd "; print x; print " && $(MAKE) Makefile\n")
      sds;
    print "\n";
  end

let clean sds sps =
  print "clean::\n";
  if !some_mlfile || !some_mlifile || !some_ml4file
     || !some_mllibfile || !some_mlpackfile
  then
    begin
      print "\trm -f $(ALLCMOFILES) $(CMIFILES) $(CMAFILES)\n";
      print "\trm -f $(ALLCMOFILES:.cmo=.cmx) $(CMXAFILES) $(CMXSFILES) $(ALLCMOFILES:.cmo=.o) $(CMXAFILES:.cmxa=.a)\n";
      print "\trm -f $(addsuffix .d,$(MLFILES) $(MLIFILES) $(ML4FILES) $(MLLIBFILES) $(MLPACKFILES))\n";
    end;
  if !some_vfile then
    begin
      print "\trm -f $(OBJFILES) $(OBJFILES:.o=.native) $(NATIVEFILES)\n";
      print "\tfind . -name .coq-native -type d -empty -delete\n";
      print "\trm -f $(VOFILES) $(VOFILES:.vo=.vio) $(GFILES) $(VFILES:.v=.v.d) $(VFILES:=.beautified) $(VFILES:=.old)\n"
    end;
  print "\trm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) all-mli.tex\n";
  print "\t- rm -rf html mlihtml uninstall_me.sh\n";
  List.iter
    (fun (file,_,is_phony,_) ->
       if not (is_phony || is_genrule file) then
	 (print "\t- rm -rf "; print file; print "\n"))
    sps;
  List.iter
    (fun x -> print "\t+cd "; print x; print " && $(MAKE) clean\n")
    sds;
  print "\n";
  let () =
    if !some_vfile then
      let () = print "cleanall:: clean\n" in
      print "\trm -f $(foreach f,$(VFILES:.v=),$(dir $(f)).$(notdir $(f)).aux)\n\n" in
  print "archclean::\n";
  print "\trm -f *.cmx *.o\n";
  List.iter
    (fun x -> print "\t+cd "; print x; print " && $(MAKE) archclean\n")
    sds;
  print "\n";
  print "printenv:\n\t@\"$(COQBIN)coqtop\" -config\n";
  print "\t@echo 'OCAMLFIND =\t$(OCAMLFIND)'\n\t@echo 'PP =\t$(PP)'\n\t@echo 'COQFLAGS =\t$(COQFLAGS)'\n";
  print "\t@echo 'COQLIBINSTALL =\t$(COQLIBINSTALL)'\n\t@echo 'COQDOCINSTALL =\t$(COQDOCINSTALL)'\n\n"

let header_includes () = ()

let implicit () =
    section "Implicit rules.";
  let mli_rules () =
    print "$(MLIFILES:.mli=.cmi): %.cmi: %.mli\n";
    print "\t$(SHOW)'CAMLC -c $<'\n";
    print "\t$(HIDE)$(CAMLC) $(ZDEBUG) $(ZFLAGS) $<\n\n";
    print "$(addsuffix .d,$(MLIFILES)): %.mli.d: %.mli\n";
    print "\t$(SHOW)'CAMLDEP $<'\n";
    print "\t$(HIDE)$(CAMLDEP) $(OCAMLLIBS) \"$<\" > \"$@\" || ( RV=$$?; rm -f \"$@\"; exit $${RV} )\n\n"
  in
  let ml4_rules () =
    print "$(ML4FILES:.ml4=.cmo): %.cmo: %.ml4\n";
    print "\t$(SHOW)'CAMLC -pp -c $<'\n";
    print "\t$(HIDE)$(CAMLC) $(ZDEBUG) $(ZFLAGS) $(PP) -impl $<\n\n";
    print "$(filter-out $(addsuffix .cmx,$(foreach lib,$(MLPACKFILES:.mlpack=_MLPACK_DEPENDENCIES),$($(lib)))),$(ML4FILES:.ml4=.cmx)): %.cmx: %.ml4\n";
    print "\t$(SHOW)'CAMLOPT -pp -c $<'\n";
    print "\t$(HIDE)$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) $(PP) -impl $<\n\n";
    print "$(addsuffix .d,$(ML4FILES)): %.ml4.d: %.ml4\n";
    print "\t$(SHOW)'CAMLDEP -pp $<'\n";
    print "\t$(HIDE)$(CAMLDEP) $(OCAMLLIBS) $(PP) -impl \"$<\" > \"$@\" || ( RV=$$?; rm -f \"$@\"; exit $${RV} )\n\n" in
  let ml_rules () =
    print "$(MLFILES:.ml=.cmo): %.cmo: %.ml\n";
    print "\t$(SHOW)'CAMLC -c $<'\n";
    print "\t$(HIDE)$(CAMLC) $(ZDEBUG) $(ZFLAGS) $<\n\n";
    print "$(filter-out $(addsuffix .cmx,$(foreach lib,$(MLPACKFILES:.mlpack=_MLPACK_DEPENDENCIES),$($(lib)))),$(MLFILES:.ml=.cmx)): %.cmx: %.ml\n";
    print "\t$(SHOW)'CAMLOPT -c $<'\n";
    print "\t$(HIDE)$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) $<\n\n";
    print "$(addsuffix .d,$(MLFILES)): %.ml.d: %.ml\n";
    print "\t$(SHOW)'CAMLDEP $<'\n";
    print "\t$(HIDE)$(CAMLDEP) $(OCAMLLIBS) \"$<\" > \"$@\" || ( RV=$$?; rm -f \"$@\"; exit $${RV} )\n\n" in
  let cmxs_rules () = (* order is important here when there is foo.ml and foo.mllib *)
    print "$(filter-out $(MLLIBFILES:.mllib=.cmxs),$(MLFILES:.ml=.cmxs) $(ML4FILES:.ml4=.cmxs) $(MLPACKFILES:.mlpack=.cmxs)): %.cmxs: %.cmx\n";
    print "\t$(SHOW)'CAMLOPT -shared -o $@'\n";
    print "\t$(HIDE)$(CAMLOPTLINK) $(ZDEBUG) $(ZFLAGS) -shared -o $@ $<\n\n";
    print "$(MLLIBFILES:.mllib=.cmxs): %.cmxs: %.cmxa\n";
    print "\t$(SHOW)'CAMLOPT -shared -o $@'\n";
    print "\t$(HIDE)$(CAMLOPTLINK) $(ZDEBUG) $(ZFLAGS) -linkall -shared -o $@ $<\n\n"
  in
  let mllib_rules () =
    print "$(MLLIBFILES:.mllib=.cma): %.cma: | %.mllib\n";
    print "\t$(SHOW)'CAMLC -a -o $@'\n";
    print "\t$(HIDE)$(CAMLLINK) $(ZDEBUG) $(ZFLAGS) -a -o $@ $^\n\n";
    print "$(MLLIBFILES:.mllib=.cmxa): %.cmxa: | %.mllib\n";
    print "\t$(SHOW)'CAMLOPT -a -o $@'\n";
    print "\t$(HIDE)$(CAMLOPTLINK) $(ZDEBUG) $(ZFLAGS) -a -o $@ $^\n\n";
    print "$(addsuffix .d,$(MLLIBFILES)): %.mllib.d: %.mllib\n";
    print "\t$(SHOW)'COQDEP $<'\n";
    print "\t$(HIDE)$(COQDEP) $(OCAMLLIBS) -c \"$<\" > \"$@\" || ( RV=$$?; rm -f \"$@\"; exit $${RV} )\n\n"
  in
  let mlpack_rules () =
    print "$(MLPACKFILES:.mlpack=.cmo): %.cmo: | %.mlpack\n";
    print "\t$(SHOW)'CAMLC -pack -o $@'\n";
    print "\t$(HIDE)$(CAMLLINK) $(ZDEBUG) $(ZFLAGS) -pack -o $@ $^\n\n";
    print "$(MLPACKFILES:.mlpack=.cmx): %.cmx: | %.mlpack\n";
    print "\t$(SHOW)'CAMLOPT -pack -o $@'\n";
    print "\t$(HIDE)$(CAMLOPTLINK) $(ZDEBUG) $(ZFLAGS) -pack -o $@ $^\n\n";
    print "$(addsuffix .d,$(MLPACKFILES)): %.mlpack.d: %.mlpack\n";
    print "\t$(SHOW)'COQDEP $<'\n";
    print "\t$(HIDE)$(COQDEP) $(OCAMLLIBS) -c \"$<\" > \"$@\" || ( RV=$$?; rm -f \"$@\"; exit $${RV} )\n\n"
  in
  let v_rules () =
    print "$(VOFILES): %.vo: %.v\n";
    print "\t$(SHOW)COQC $<\n";
    print "\t$(HIDE)$(COQC) $(COQDEBUG) $(COQFLAGS) $<\n\n";
    print "$(GLOBFILES): %.glob: %.v\n\t$(COQC) $(COQDEBUG) $(COQFLAGS) $<\n\n";
    print "$(VFILES:.v=.vio): %.vio: %.v\n\t$(COQC) -quick $(COQDEBUG) $(COQFLAGS) $<\n\n";
    print "$(GFILES): %.g: %.v\n\t$(GALLINA) $<\n\n";
    print "$(VFILES:.v=.tex): %.tex: %.v\n\t$(COQDOC) $(COQDOCFLAGS) -latex $< -o $@\n\n";
    print "$(HTMLFILES): %.html: %.v %.glob\n\t$(COQDOC) $(COQDOCFLAGS) -html $< -o $@\n\n";
    print "$(VFILES:.v=.g.tex): %.g.tex: %.v\n\t$(COQDOC) $(COQDOCFLAGS) -latex -g $< -o $@\n\n";
    print "$(GHTMLFILES): %.g.html: %.v %.glob\n\t$(COQDOC) $(COQDOCFLAGS)  -html -g $< -o $@\n\n";
    print "$(addsuffix .d,$(VFILES)): %.v.d: %.v\n";
    print "\t$(SHOW)'COQDEP $<'\n";
    print "\t$(HIDE)$(COQDEP) $(COQLIBS) \"$<\" > \"$@\" || ( RV=$$?; rm -f \"$@\"; exit $${RV} )\n\n";
    print "$(addsuffix .beautified,$(VFILES)): %.v.beautified:\n\t$(COQC) $(COQDEBUG) $(COQFLAGS) -beautify $*.v\n\n"
  in
    if !some_mlifile then mli_rules ();
    if !some_ml4file then ml4_rules ();
    if !some_mlfile then ml_rules ();
    if !some_mlfile || !some_ml4file then cmxs_rules ();
    if !some_mllibfile then mllib_rules ();
    if !some_mlpackfile then mlpack_rules ();
    if !some_vfile then v_rules ()

let variables is_install opt (args,defs) =
  let var_aux (v,def) = print v; print "="; print def; print "\n" in
    section "Variables definitions.";
    List.iter var_aux defs;
    print "\n";
    if not opt then
      print "override OPT:=-byte\n"
    else
      print "OPT?=\n";
    begin
      match args with
	|[] -> ()
	|h::t -> print "OTHERFLAGS=";
	  print h;
	  List.iter (fun s -> print " ";print s) t;
	  print "\n";
    end;
    (* Coq executables and relative variables *)
    if !some_vfile || !some_mlpackfile || !some_mllibfile then
      print "COQDEP?=\"$(COQBIN)coqdep\" -c\n";
    if !some_vfile then begin
    print "COQFLAGS?=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)\n";
    print "COQCHKFLAGS?=-silent -o\n";
    print "COQDOCFLAGS?=-interpolate -utf8\n";
    print "COQC?=$(TIMER) \"$(COQBIN)coqc\"\n";
    print "GALLINA?=\"$(COQBIN)gallina\"\n";
    print "COQDOC?=\"$(COQBIN)coqdoc\"\n";
    print "COQCHK?=\"$(COQBIN)coqchk\"\n";
    print "COQMKTOP?=\"$(COQBIN)coqmktop\"\n\n";
    end;
    (* Caml executables and relative variables *)
    if !some_ml4file || !some_mlfile || !some_mlifile then begin
    print "COQSRCLIBS?=" ;
    List.iter (fun c -> print "-I \"$(COQLIB)"; print c ; print "\" \\\n") lib_dirs ;
    List.iter (fun c -> print " \\\
\n  -I \"$(COQLIB)/"; print c; print "\"") Coq_config.plugins_dirs; print "\n";
    print "ZFLAGS=$(OCAMLLIBS) $(COQSRCLIBS) -I $(CAMLP4LIB)\n\n";
    print "CAMLC?=$(OCAMLFIND) ocamlc -c -rectypes -thread -safe-string\n";
    print "CAMLOPTC?=$(OCAMLFIND) opt -c -rectypes -thread -safe-string\n";
    print "CAMLLINK?=$(OCAMLFIND) ocamlc -rectypes -thread -safe-string\n";
    print "CAMLOPTLINK?=$(OCAMLFIND) opt -rectypes -thread -safe-string\n";
    print "CAMLDEP?=$(OCAMLFIND) ocamldep -slash -ml-synonym .ml4 -ml-synonym .mlpack\n";
    print "CAMLLIB?=$(shell $(OCAMLFIND) printconf stdlib)\n";
    print "GRAMMARS?=grammar.cma\n";
    print "CAMLP4EXTEND=pa_extend.cmo q_MLast.cmo pa_macro.cmo\n";
    print "PP?=-pp '$(CAMLP4O) -I $(CAMLLIB) -I $(COQLIB)/grammar compat5.cmo \\\
\n  $(CAMLP4EXTEND) $(GRAMMARS) $(CAMLP4OPTIONS) -impl'\n\n";
    end;
    match is_install with
      | Project_file.NoInstall -> ()
      | Project_file.UnspecInstall ->
        section "Install Paths.";
	print "ifdef USERINSTALL\n";
        print "XDG_DATA_HOME?=\"$(HOME)/.local/share\"\n";
        print "COQLIBINSTALL=$(XDG_DATA_HOME)/coq\n";
        print "COQDOCINSTALL=$(XDG_DATA_HOME)/doc/coq\n";
	print "else\n";
        print "COQLIBINSTALL=\"${COQLIB}user-contrib\"\n";
        print "COQDOCINSTALL=\"${DOCDIR}user-contrib\"\n";
        print "COQTOPINSTALL=\"${COQLIB}toploop\"\n";
	print "endif\n\n"
      | Project_file.TraditionalInstall ->
          section "Install Paths.";
          print "COQLIBINSTALL=\"${COQLIB}user-contrib\"\n";
          print "COQDOCINSTALL=\"${DOCDIR}user-contrib\"\n";
          print "COQTOPINSTALL=\"${COQLIB}toploop\"\n";
          print "\n"
      | Project_file.UserInstall ->
          section "Install Paths.";
          print "XDG_DATA_HOME?=\"$(HOME)/.local/share\"\n";
          print "COQLIBINSTALL=$(XDG_DATA_HOME)/coq\n";
          print "COQDOCINSTALL=$(XDG_DATA_HOME)/doc/coq\n";
          print "COQTOPINSTALL=$(XDG_DATA_HOME)/coq/toploop\n";
          print "\n"

let parameters () =
  print ".DEFAULT_GOAL := all\n\n";
  print "# This Makefile may take arguments passed as environment variables:\n";
  print "# COQBIN to specify the directory where Coq binaries resides;\n";
  print "# TIMECMD set a command to log .v compilation time;\n";
  print "# TIMED if non empty, use the default time command as TIMECMD;\n";
  print "# ZDEBUG/COQDEBUG to specify debug flags for ocamlc&ocamlopt/coqc;\n";
  print "# DSTROOT to specify a prefix to install path.\n";
  print "# VERBOSE to disable the short display of compilation rules.\n\n";
  print "VERBOSE?=\n";
  print "SHOW := $(if $(VERBOSE),@true \"\",@echo \"\")\n";
  print "HIDE := $(if $(VERBOSE),,@)\n\n";
  print "# Here is a hack to make $(eval $(shell works:\n";
  print "define donewline\n\n\nendef\n";
  print "includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\\r' | tr '\\n' '@'; })))\n";
  print "$(call includecmdwithout@,$(COQBIN)coqtop -config)\n\n";
  print "TIMED?=\nTIMECMD?=\nSTDTIME?=/usr/bin/time -f \"$* (user: %U mem: %M ko)\"\n";
  print "TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))\n\n";
  print "vo_to_obj = $(addsuffix .o,\\\n";
  print "  $(filter-out Warning: Error:,\\\n";
  print "  $(shell $(COQBIN)coqtop -q -noinit -batch -quiet -print-mod-uid $(1))))\n\n"

let include_dirs (inc_ml,inc_q,inc_r) =
  let parse_ml_includes l = List.map (fun (x,_) -> "-I \"" ^ x ^ "\"") l in
  let includes =
    List.map (fun (p,l,_) ->
              let l' = if l = "" then "\"\"" else l in
              " \"" ^ p ^ "\" " ^ l' ^"") in
  let str_ml = parse_ml_includes inc_ml in
  section "Libraries definitions.";
  if !some_ml4file || !some_mlfile || !some_mlifile then begin
    print "OCAMLLIBS?="; print_list "\\\n  " str_ml; print "\n";
  end;
  if !some_vfile || !some_mllibfile || !some_mlpackfile then begin
    print "COQLIBS?=";
    print_prefix_list "\\\n  -Q" (includes inc_q);
    print_prefix_list "\\\n  -R" (includes inc_r);
    print_prefix_list "\\\n  " str_ml;
    print "\n";
  end;
  if !some_vfile then begin
    print "COQCHKLIBS?=";
    print_prefix_list "\\\n  -R" (includes inc_q);
    print_prefix_list "\\\n  -R" (includes inc_r);
    print "\n";
    print "COQDOCLIBS?=";
    print_prefix_list "\\\n  -R" (includes inc_q);
    print_prefix_list "\\\n  -R" (includes inc_r);
    print "\n";
  end;
  print "\n"

let double_colon = ["clean"; "cleanall"; "archclean"]

let custom sps =
  let pr_path (file,dependencies,is_phony,com) =
    print file;
    print (if List.mem file double_colon then ":: " else ": ");
    print dependencies; print "\n";
    if com <> "" then (print "\t"; print com; print "\n");
    print "\n"
  in
    if sps <> [] then section "Custom targets.";
    List.iter pr_path sps

let subdirs sds =
  let pr_subdir s =
    print s; print ":\n\t+cd \""; print s; print "\" && $(MAKE) all\n\n"
  in
  if sds <> [] then
    let () =
      Format.eprintf "@[Warning: Targets for subdirectories are very fragile.@ " in
    let () =
      Format.eprintf "For example,@ nothing is done to handle dependencies@ with them.@]@." in
      section "Subdirectories.";
    List.iter pr_subdir sds

let forpacks l =
  let () = if l <> [] then section "Ad-hoc implicit rules for mlpack." in
  List.iter (fun it ->
    let h = Filename.chop_extension it in
    let pk = String.capitalize (Filename.basename h) in
    printf "$(addsuffix .cmx,$(filter $(basename $(MLFILES)),$(%s_MLPACK_DEPENDENCIES))): %%.cmx: %%.ml\n" h;
    printf "\t$(SHOW)'CAMLOPT -c -for-pack %s $<'\n" pk;
    printf "\t$(HIDE)$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) -for-pack %s $<\n\n" pk;
    printf "$(addsuffix .cmx,$(filter $(basename $(ML4FILES)),$(%s_MLPACK_DEPENDENCIES))): %%.cmx: %%.ml4\n" h;
    printf "\t$(SHOW)'CAMLOPT -c -pp -for-pack %s $<'\n" pk;
    printf "\t$(HIDE)$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) -for-pack %s $(PP) -impl $<\n\n" pk
  ) l

let main_targets vfiles (mlifiles,ml4files,mlfiles,mllibfiles,mlpackfiles) other_targets inc =
  let decl_var var = function
    |[] -> ()
    |l ->
      printf "%s:=" var; print_list "\\\n  " l; print "\n\n";
      print "ifneq ($(filter-out archclean clean cleanall printenv,$(MAKECMDGOALS)),)\n";
      printf "-include $(addsuffix .d,$(%s))\n" var;
      print "else\nifeq ($(MAKECMDGOALS),)\n";
      printf "-include $(addsuffix .d,$(%s))\n" var;
      print "endif\nendif\n\n";
      printf ".SECONDARY: $(addsuffix .d,$(%s))\n\n" var
  in
  section "Files dispatching.";
  decl_var "VFILES" vfiles;
  begin match vfiles with
    |[] -> ()
    |l ->
      print "VO=vo\n";
      print "VOFILES:=$(VFILES:.v=.$(VO))\n";
      classify_files_by_root "VOFILES" l inc;
      classify_files_by_root "VFILES" l inc;
      print "GLOBFILES:=$(VFILES:.v=.glob)\n";
      print "GFILES:=$(VFILES:.v=.g)\n";
      print "HTMLFILES:=$(VFILES:.v=.html)\n";
      print "GHTMLFILES:=$(VFILES:.v=.g.html)\n";
      print "OBJFILES=$(call vo_to_obj,$(VOFILES))\n";
      print "ALLNATIVEFILES=$(OBJFILES:.o=.cmi) $(OBJFILES:.o=.cmo) $(OBJFILES:.o=.cmx) $(OBJFILES:.o=.cmxs)\n";
      print "NATIVEFILES=$(foreach f, $(ALLNATIVEFILES), $(wildcard $f))\n";
      classify_files_by_root "NATIVEFILES" l inc
  end;
  decl_var "ML4FILES" ml4files;
  decl_var "MLFILES" mlfiles;
  decl_var "MLPACKFILES" mlpackfiles;
  decl_var "MLLIBFILES" mllibfiles;
  decl_var "MLIFILES" mlifiles;
  let mlsfiles = match ml4files,mlfiles,mlpackfiles with
    |[],[],[] -> []
    |[],[],_ -> Printf.eprintf "Mlpack cannot work without ml[4]?"; []
    |[],ml,[] ->
      print "ALLCMOFILES:=$(MLFILES:.ml=.cmo)\n";
      ml
    |ml4,[],[] ->
      print "ALLCMOFILES:=$(ML4FILES:.ml4=.cmo)\n";
      ml4
    |ml4,ml,[] ->
      print "ALLCMOFILES:=$(ML4FILES:.ml4=.cmo) $(MLFILES:.ml=.cmo)\n";
      List.rev_append ml ml4
    |[],ml,mlpack ->
      print "ALLCMOFILES:=$(MLFILES:.ml=.cmo) $(MLPACKFILES:.mlpack=.cmo)\n";
      List.rev_append mlpack ml
    |ml4,[],mlpack ->
      print "ALLCMOFILES:=$(ML4FILES:.ml4=.cmo) $(MLPACKFILES:.mlpack=.cmo)\n";
      List.rev_append mlpack ml4
    |ml4,ml,mlpack ->
      print "ALLCMOFILES:=$(ML4FILES:.ml4=.cmo) $(MLFILES:.ml=.cmo) $(MLPACKFILES:.mlpack=.cmo)\n";
      List.rev_append mlpack (List.rev_append ml ml4) in
  begin match mlsfiles with
    |[] -> ()
    |l ->
  print "CMOFILES=$(filter-out $(addsuffix .cmo,$(foreach lib,$(MLLIBFILES:.mllib=_MLLIB_DEPENDENCIES) $(MLPACKFILES:.mlpack=_MLPACK_DEPENDENCIES),$($(lib)))),$(ALLCMOFILES))\n";
      classify_files_by_root "CMOFILES" l inc;
      print "CMXFILES=$(CMOFILES:.cmo=.cmx)\n";
      print "OFILES=$(CMXFILES:.cmx=.o)\n";
  end;
  begin match mllibfiles with
    |[] -> ()
    |l ->
      print "CMAFILES:=$(MLLIBFILES:.mllib=.cma)\n";
	classify_files_by_root "CMAFILES" l inc;
      print "CMXAFILES:=$(CMAFILES:.cma=.cmxa)\n";
  end;
  begin match mlifiles,mlsfiles with
    |[],[] -> ()
    |l,[] ->
       print "CMIFILES:=$(MLIFILES:.mli=.cmi)\n";
	classify_files_by_root "CMIFILES" l inc;
    |[],l ->
      print "CMIFILES=$(ALLCMOFILES:.cmo=.cmi)\n";
      classify_files_by_root "CMIFILES" l inc;
    |l1,l2 ->
      print "CMIFILES=$(sort $(ALLCMOFILES:.cmo=.cmi) $(MLIFILES:.mli=.cmi))\n";
      classify_files_by_root "CMIFILES" (l1@l2) inc;
  end;
  begin match mllibfiles,mlsfiles with
    |[],[] -> ()
    |l,[] ->
      print "CMXSFILES:=$(CMXAFILES:.cmxa=.cmxs)\n";
      classify_files_by_root "CMXSFILES" l inc;
    |[],l ->
      print "CMXSFILES=$(CMXFILES:.cmx=.cmxs)\n";
      classify_files_by_root "CMXSFILES" l inc;
    |l1,l2 ->
      print "CMXSFILES=$(CMXFILES:.cmx=.cmxs) $(CMXAFILES:.cmxa=.cmxs)\n";
      classify_files_by_root "CMXSFILES" (l1@l2) inc;
  end;
  print "ifeq '$(HASNATDYNLINK)' 'true'\n";
  print "HASNATDYNLINK_OR_EMPTY := yes\n";
  print "else\n";
  print "HASNATDYNLINK_OR_EMPTY :=\n";
  print "endif\n\n";
  section "Definition of the toplevel targets.";
  print "all: ";
  if !some_vfile then print "$(VOFILES) ";
  if !some_mlfile || !some_ml4file || !some_mlpackfile then print "$(CMOFILES) ";
  if !some_mllibfile then print "$(CMAFILES) ";
  if !some_mlfile || !some_ml4file || !some_mllibfile || !some_mlpackfile
  then print "$(if $(HASNATDYNLINK_OR_EMPTY),$(CMXSFILES)) ";
  print_list "\\\n  " other_targets; print "\n\n";
  if !some_mlifile then
    begin
      print "mlihtml: $(MLIFILES:.mli=.cmi)\n";
      print "\t mkdir $@ || rm -rf $@/*\n";
      print "\t$(OCAMLFIND) ocamldoc -html -safe-string -rectypes -d $@ -m A $(ZDEBUG) $(ZFLAGS) $(^:.cmi=.mli)\n\n";
      print "all-mli.tex: $(MLIFILES:.mli=.cmi)\n";
      print "\t$(OCAMLFIND) ocamldoc -latex -safe-string -rectypes -o $@ -m A $(ZDEBUG) $(ZFLAGS) $(^:.cmi=.mli)\n\n";
    end;
  if !some_vfile then
    begin
      print "quick: $(VOFILES:.vo=.vio)\n\n";
      print "vio2vo:\n\t$(COQC) $(COQDEBUG) $(COQFLAGS) -schedule-vio2vo $(J) $(VOFILES:%.vo=%.vio)\n";
      print "checkproofs:\n\t$(COQC) $(COQDEBUG) $(COQFLAGS) -schedule-vio-checking $(J) $(VOFILES:%.vo=%.vio)\n";
      print "gallina: $(GFILES)\n\n";
      print "html: $(GLOBFILES) $(VFILES)\n";
      print "\t- mkdir -p html\n";
      print "\t$(COQDOC) -toc $(COQDOCFLAGS) -html $(COQDOCLIBS) -d html $(VFILES)\n\n";
      print "gallinahtml: $(GLOBFILES) $(VFILES)\n";
      print "\t- mkdir -p html\n";
      print "\t$(COQDOC) -toc $(COQDOCFLAGS) -html -g $(COQDOCLIBS) -d html $(VFILES)\n\n";
      print "all.ps: $(VFILES)\n";
      print "\t$(COQDOC) -toc $(COQDOCFLAGS) -ps $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`\n\n";
      print "all-gal.ps: $(VFILES)\n";
      print "\t$(COQDOC) -toc $(COQDOCFLAGS) -ps -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`\n\n";
      print "all.pdf: $(VFILES)\n";
      print "\t$(COQDOC) -toc $(COQDOCFLAGS) -pdf $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`\n\n";
      print "all-gal.pdf: $(VFILES)\n";
      print "\t$(COQDOC) -toc $(COQDOCFLAGS) -pdf -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`\n\n";
      print "validate: $(VOFILES)\n";
      print "\t$(COQCHK) $(COQCHKFLAGS) $(COQCHKLIBS) $(notdir $(^:.vo=))\n\n";
      print "beautify: $(VFILES:=.beautified)\n";
      print "\tfor file in $^; do mv $${file%.beautified} $${file%beautified}old && mv $${file} $${file%.beautified}; done\n";
      print "\t@echo \'Do not do \"make clean\" until you are sure that everything went well!\'\n";
      print "\t@echo \'If there were a problem, execute \"for file in $$(find . -name \\*.v.old -print); do mv $${file} $${file%.old}; done\" in your shell/'\n\n"
    end

let all_target (vfiles, (_,_,_,_,mlpackfiles as mlfiles), sps, sds) inc =
  let other_targets =
    CList.map_filter
      (fun (n,_,is_phony,_) -> if not (is_phony || is_genrule n) then Some n else None)
      sps @ sds in
  main_targets vfiles mlfiles other_targets inc;
  print ".PHONY: ";
  print_list
    " "
    ("all" :: "archclean" :: "beautify" :: "byte" :: "clean" :: "cleanall"
     :: "gallina" :: "gallinahtml" :: "html" :: "install" :: "install-doc"
     :: "install-natdynlink" :: "install-toploop" :: "opt" :: "printenv"
     :: "quick" :: "uninstall" :: "userinstall" :: "validate" :: "vio2vo"
     :: (sds@(CList.map_filter
		(fun (n,_,is_phony,_) ->
		 if is_phony then Some n else None) sps)));
  print "\n\n";
  custom sps;
  subdirs sds;
  forpacks mlpackfiles

let banner () =
  print (Printf.sprintf
"#############################################################################\
\n##  v      #                   The Coq Proof Assistant                     ##\
\n## <O___,, #                INRIA - CNRS - LIX - LRI - PPS                 ##\
\n##   \\VV/  #                                                               ##\
\n##    //   #  Makefile automagically generated by coq_makefile V%s ##\
\n#############################################################################\
\n\n"
(Coq_config.version ^ String.make (10 - String.length Coq_config.version) ' '))

let warning () =
  print "# WARNING\n#\n";
  print "# This Makefile has been automagically generated\n";
  print "# Edit at your own risks !\n";
  print "#\n# END OF WARNING\n\n"

let print_list l = List.iter (fun x -> print x; print " ") l

let command_line args =
  print "#\n# This Makefile was generated by the command line :\n";
  print "# coq_makefile ";
  print_list args;
  print "\n#\n\n"

let ensure_root_dir (vfiles,(mlis,ml4s,mls,mllibs,mlpacks),_,_) inc =
  let (ml_inc,i_inc,r_inc) = inc in
  let here = Sys.getcwd () in
  let not_tops =  List.for_all (fun s -> s <> Filename.basename s) in
  if List.exists (fun (_,_,x) -> x = here) i_inc
    || List.exists (fun (_,_,x) -> is_prefix x here) r_inc
    || (not_tops vfiles && not_tops mlis && not_tops ml4s && not_tops mls
	&& not_tops mllibs && not_tops mlpacks)
  then
    inc
  else
    ((".",here)::ml_inc,i_inc,(".","Top",here)::r_inc)

let warn_install_at_root_directory (vfiles,(mlis,ml4s,mls,mllibs,mlpacks),_,_) inc =
  let (inc_ml,inc_i,inc_r) = inc in
  let inc_top = List.filter (fun (_,ldir,_) -> ldir = "") (inc_r@inc_i) in
  let inc_top_p = List.map (fun (p,_,_) -> p) inc_top in
  let files = vfiles @ mlis @ ml4s @ mls @ mllibs @ mlpacks in
  if List.exists (fun f -> List.mem (Filename.dirname f) inc_top_p) files
  then
    Printf.eprintf "Warning: install target will copy files at the first level of the coq contributions installation directory; option -R or -Q %sis recommended\n"
      (if inc_top = [] then "" else "with non trivial logical root ")

let check_overlapping_include (_,inc_i,inc_r) =
  let pwd = Sys.getcwd () in
  let aux = function
    | [] -> ()
    | (pdir,_,abspdir)::l ->
	if not (is_prefix pwd abspdir) then
	  Printf.eprintf "Warning: in option -R/-Q, %s is not a subdirectory of the current directory\n" pdir;
	List.iter (fun (pdir',_,abspdir') ->
	  if is_prefix abspdir abspdir' || is_prefix abspdir' abspdir then
	    Printf.eprintf "Warning: in options -R/-Q, %s and %s overlap\n" pdir pdir') l;
  in aux (inc_i@inc_r)

(* Generate a .merlin file that references the standard library and
 * any -I included paths.
 *)
let merlin targets (ml_inc,_,_) =
  print ".merlin:\n";
  print "\t@echo 'FLG -rectypes -safe-string' > .merlin\n" ;
  List.iter (fun c ->
      printf "\t@echo \"B $(COQLIB)%s\" >> .merlin\n" c)
    lib_dirs ;
  List.iter (fun (_,c) ->
      printf "\t@echo \"B %s\" >> .merlin\n" c;
      printf "\t@echo \"S %s\" >> .merlin\n" c)
    ml_inc;
  print "\n"

let do_makefile args =
  let has_file var = function
    |[] -> var := false
    |_::_ -> var := true in
  let (project_file,makefile,is_install,opt),l =
    try
      Project_file.process_cmd_line Filename.current_dir_name
       (None,None,Project_file.UnspecInstall,true) [] args
    with Project_file.Parsing_error -> usage () in
  let (v_f,(mli_f,ml4_f,ml_f,mllib_f,mlpack_f),sps,sds as targets), inc, defs =
    Project_file.split_arguments l in

  let () = match project_file with |None -> () |Some f -> make_name := f in
  let () = match makefile with
    |None -> ()
    |Some f -> makefile_name := f; output_channel := open_out f in
  has_file some_vfile v_f; has_file some_mlifile mli_f;
  has_file some_mlfile ml_f; has_file some_ml4file ml4_f;
  has_file some_mllibfile mllib_f; has_file some_mlpackfile mlpack_f;
  let check_dep f =
    if Filename.check_suffix f ".v" then some_vfile := true
    else if (Filename.check_suffix f ".mli") then some_mlifile := true
    else if (Filename.check_suffix f ".ml4") then some_ml4file := true
    else if (Filename.check_suffix f ".ml") then some_mlfile := true
    else if (Filename.check_suffix f ".mllib") then some_mllibfile := true
    else if (Filename.check_suffix f ".mlpack") then some_mlpackfile := true
  in
  List.iter (fun (_,dependencies,_,_) ->
    List.iter check_dep (Str.split (Str.regexp "[ \t]+") dependencies)) sps;

  let inc = ensure_root_dir targets inc in
  if is_install <> Project_file.NoInstall then begin
    warn_install_at_root_directory targets inc;
  end;
  check_overlapping_include inc;
  banner ();
  header_includes ();
  warning ();
  command_line args;
  parameters ();
  include_dirs inc;
  variables is_install opt defs;
  all_target targets inc;
  section "Special targets.";
  standard opt;
  install targets inc is_install;
  merlin targets inc;
  clean sds sps;
  make_makefile sds;
  implicit ();
  warning ();
  if not (makefile = None) then close_out !output_channel;
  exit 0

let _ =
  let args =
    if Array.length Sys.argv = 1 then usage ();
    List.tl (Array.to_list Sys.argv)
  in
    do_makefile args
