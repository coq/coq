(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* créer un Makefile pour un développement Coq automatiquement *)

type target =
  | ML of string (* ML file : foo.ml -> (ML "foo") *)
  | V of string  (* V file : foo.v -> (V "foo") *)
  | Special of string * string * string (* file, dependencies, command *)
  | Subdir of string
  | Def of string * string (* X=foo -> Def ("X","foo") *)
  | Include of string
  | RInclude of string * string (* -R physicalpath logicalpath *)

let output_channel = ref stdout
let makefile_name = ref "Makefile"
let make_name = ref ""

let some_file = ref false
let some_vfile = ref false
let some_mlfile = ref false

let opt = ref "-opt"
let impredicative_set = ref false

let print x = output_string !output_channel x
let printf x = Printf.fprintf !output_channel x

let rec print_list sep = function
  | [ x ] -> print x
  | x :: l -> print x; print sep; print_list sep l
  | [] -> ()

let best_ocamlc = 
  if Coq_config.best = "opt" then "ocamlc.opt" else "ocamlc"
let best_ocamlopt =
  if Coq_config.best = "opt" then "ocamlopt.opt" else "ocamlopt"

let section s =
  let l = String.length s in
  let sep = String.make (l+5) '#'
  and sep2 = String.make (l+5) ' ' in
  String.set sep (l+4) '\n';
  String.set sep2 0 '#';
  String.set sep2 (l+3) '#';
  String.set sep2 (l+4) '\n';
  print sep;
  print sep2;
  print "# "; print s; print " #\n";
  print sep2;
  print sep;
  print "\n"

let usage () =
  output_string stderr "Usage summary:

coq_makefile [subdirectory] .... [file.v] ... [file.ml] ... [-custom
  command dependencies file] ... [-I dir] ... [-R physicalpath logicalpath]
  ... [VARIABLE = value] ...  [-opt|-byte] [-f file] [-o file] [-h] [--help]

[file.v]: Coq file to be compiled
[file.ml]: ML file to be compiled
[subdirectory] : subdirectory that should be \"made\"
[-custom command dependencies file]: add target \"file\" with command
  \"command\" and dependencies \"dependencies\"
[-I dir]: look for dependencies in \"dir\"
[-R physicalpath logicalpath]: look for dependencies resursively starting from
 \"physicalpath\". The logical path associated to the physical path is
 \"logicalpath\".
[VARIABLE = value]: Add the variable definition \"VARIABLE=value\"
[-byte]: compile with byte-code version of coq
[-opt]: compile with native-code version of coq
[-impredicative-set]: compile with option -impredicative-set of coq
[-f file]: take the contents of file as arguments
[-o file]: output should go in file file 
[-h]: print this usage summary
[--help]: equivalent to [-h]\n";
  exit 1

let is_genrule r =
  let genrule = Str.regexp("%") in
    Str.string_match genrule r 0

let standard sds sps =
  print "byte:\n";
  print "\t$(MAKE) all \"OPT=\"\n\n";
  print "opt:\n";
  if !opt = "" then print "\t@echo \"WARNING: opt is disabled\"\n";
  print "\t$(MAKE) all \"OPT="; print !opt; print "\"\n\n";
  if !some_file then print "include .depend\n\n";
  print ".depend depend:\n";
  if !some_file then begin
    print "\trm -f .depend\n";
    print "\t$(COQDEP) -slash -i $(COQLIBS) $(VFILES) *.ml *.mli >.depend\n";
    print "\t$(COQDEP) -slash $(COQLIBS) -suffix .html $(VFILES) >>.depend\n";
  end;
  List.iter
    (fun x -> print "\t(cd "; print x; print " ; $(MAKE) depend)\n")
    sds;
  print "\n";
  print "install:\n";
  print "\tmkdir -p `$(COQC) -where`/user-contrib\n";
  if !some_vfile then print "\tcp -f $(VOFILES) `$(COQC) -where`/user-contrib\n";
  if !some_mlfile then print "\tcp -f *.cmo `$(COQC) -where`/user-contrib\n";
  List.iter
    (fun x -> print "\t(cd "; print x; print " ; $(MAKE) install)\n")
    sds;
  print "\n";
  if !make_name <> "" then begin
    printf "%s: %s\n" !makefile_name !make_name;
    printf "\tmv -f %s %s.bak\n" !makefile_name !makefile_name;
    printf "\t$(COQBIN)coq_makefile -f %s -o %s\n" !make_name !makefile_name;
    print "\n";
    List.iter
      (fun x -> print "\t(cd "; print x; print " ; $(MAKE) Makefile)\n")
      sds;
    print "\n";
  end;
  print "clean:\n";
  print "\trm -f *.cmo *.cmi *.cmx *.o $(VOFILES) $(VIFILES) $(GFILES) *~\n";
  print "\trm -f all.ps all-gal.ps all.pdf all-gal.pdf $(HTMLFILES) $(GHTMLFILES)\n";
List.iter
    (fun (file,_,_) -> 
      if not (is_genrule file) then
	(print "\t- rm -f "; print file; print "\n"))
    sps;
  List.iter
    (fun x -> print "\t(cd "; print x; print " ; $(MAKE) clean)\n")
    sds;
  print "\n";
  print "archclean:\n";
  print "\trm -f *.cmx *.o\n";
  List.iter
    (fun x -> print "\t(cd "; print x; print " ; $(MAKE) archclean)\n")
    sds;
  print "\n";
  print "html:\n";
  List.iter
    (fun x -> print "\t(cd "; print x; print " ; $(MAKE) html)\n")
    sds;
  print "\n"

let implicit () =
  let ml_rules () =
    print ".mli.cmi:\n\t$(CAMLC) $(ZDEBUG) $(ZFLAGS) $<\n\n";
    print ".ml.cmo:\n\t$(CAMLC) $(ZDEBUG) $(ZFLAGS) $(PP) $<\n\n";
    print ".ml.cmx:\n\t$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) $(PP) $<\n\n";
  and v_rule () =
    print ".v.vo:\n\t$(COQC) $(COQDEBUG) $(COQFLAGS) $*\n\n";
    print ".v.vi:\n\t$(COQC) -i $(COQDEBUG) $(COQFLAGS) $*\n\n";
    print ".v.g:\n\t$(GALLINA) $<\n\n";
    print ".v.tex:\n\t$(COQDOC) -latex $< -o $@\n\n";
    print ".v.html:\n\t$(COQDOC) -html $< -o $@\n\n";
    print ".v.g.tex:\n\t$(COQDOC) -latex -g $< -o $@\n\n";
    print ".v.g.html:\n\t$(COQDOC) -html -g $< -o $@\n\n"
  and ml_suffixes =
    if !some_mlfile then 
      [ ".mli"; ".ml"; ".cmo"; ".cmi"; ".cmx" ]
    else 
      []
  and v_suffixes =
    if !some_vfile then 
      [ ".v"; ".vo"; ".vi"; ".g"; ".html"; ".tex"; ".g.tex"; ".g.html" ] 
    else 
      []
  in
  let suffixes = ml_suffixes @ v_suffixes in
  if suffixes <> [] then begin
    print ".SUFFIXES: "; print_list " " suffixes;
    print "\n\n"
  end;
  if !some_mlfile then ml_rules ();
  if !some_vfile then v_rule ()

let variables l =
  let rec var_aux = function
    | [] -> ()
    | Def(v,def) :: r -> print v; print "="; print def; print "\n"; var_aux r
    | _ :: r -> var_aux r
  in
  section "Variables definitions.";
  printf "CAMLP4=%s\n" Coq_config.camlp4;
  print "ifdef CAMLP4BIN\n";
  print "  CAMLP4LIB=$(shell $(CAMLP4BIN)/$(CAMLP4) -where 2> /dev/null)\n";
  print "else\n";
  print "  CAMLP4LIB=$(shell $(CAMLP4) -where 2> /dev/null)\n";
  print "endif\n";
  print "ifdef COQTOP # set COQTOP for compiling from Coq sources\n";
  print "ifndef COQBIN\n";
  print "  COQBIN=$(COQTOP)/bin/\n";
  print "endif\n";
  print "ifndef COQLIB\n";
  print "  COQLIB=$(COQTOP)\n";
  print "endif\n";
  print "  COQSRC=-I $(COQTOP)/kernel -I $(COQTOP)/lib \\
   -I $(COQTOP)/library -I $(COQTOP)/parsing \\
   -I $(COQTOP)/pretyping -I $(COQTOP)/interp \\
   -I $(COQTOP)/proofs -I $(COQTOP)/syntax -I $(COQTOP)/tactics \\
   -I $(COQTOP)/toplevel -I $(COQTOP)/contrib/cc -I $(COQTOP)/contrib/dp \\
   -I $(COQTOP)/contrib/extraction -I $(COQTOP)/contrib/field \\
   -I $(COQTOP)/contrib/firstorder -I $(COQTOP)/contrib/fourier \\
   -I $(COQTOP)/contrib/funind -I $(COQTOP)/contrib/interface \\
   -I $(COQTOP)/contrib/micromega -I $(COQTOP)/contrib/omega \\
   -I $(COQTOP)/contrib/ring -I $(COQTOP)/contrib/romega \\
   -I $(COQTOP)/contrib/rtauto -I $(COQTOP)/contrib/setoid_ring \\
   -I $(COQTOP)/contrib/subtac -I $(COQTOP)/contrib/xml\n";
  print "else\n";
  print "ifndef COQLIB\n";
  print "  COQLIB=$(shell $(COQBIN)coqtop -where 2> /dev/null)\n";
  print "endif\n";
  print "ifneq ($(strip $(COQLIB)),)\n";
  print "  COQSRC=-I $(COQLIB)\n";
  print "else\n";
  print "  $(error Cannot find coqtop in path; set variable COQBIN to the directory where coqtop is located)\n";
  print "endif\n";
  print "endif\n";
  if List.exists (function ML _ -> true | _ -> false) l then
    begin
      print "ifeq ($(strip $(CAMLP4LIB)),)\n";
      print "  $(error Cannot find $(CAMLP4) in path; set variable CAMLP4BIN to the directory where $(CAMLP4) is located)\n";
      print "endif\n";
    end;
  print "ZFLAGS=$(OCAMLLIBS) $(COQSRC) -I $(CAMLP4LIB)\n";
  if !opt = "-byte" then 
    print "override OPT=-byte\n"
  else
    print "OPT=\n";
  if !impredicative_set = true then print "OTHERFLAGS=-impredicative-set\n";
  print "COQFLAGS=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)\n";
  print "COQC=$(COQBIN)coqc\n";
  print "GALLINA=gallina\n";
  print "COQDOC=$(COQBIN)coqdoc\n";
  printf "CAMLC=%s -rectypes -c\n" best_ocamlc;
  printf "CAMLOPTC=%s -rectypes -c\n" best_ocamlopt;
  printf "CAMLLINK=%s -rectypes\n" best_ocamlc;
  printf "CAMLOPTLINK=%s -rectypes\n" best_ocamlopt;
  print "COQDEP=$(COQBIN)coqdep -c -coqlib $(COQLIB)\n";
  print "CAMLP4EXTEND=pa_extend.cmo pa_macro.cmo q_MLast.cmo\n";
  print "GRAMMARS=grammar.cma\n";
  print "CAMLP4OPTIONS=\n";
  print "PP=-pp \"$(CAMLP4)o -I . $(COQSRC) $(CAMLP4EXTEND) $(GRAMMARS) $(CAMLP4OPTIONS) -impl\"\n";
  var_aux l;
  print "\n"

let include_dirs l =
  let include_aux' includeR =
   let rec include_aux = function
     | [] -> []
     | Include x :: r -> ("-I " ^ x) :: (include_aux r)
     | RInclude (p,l) :: r when includeR ->
        let l' = if l = "" then "\"\"" else l in
        ("-R " ^ p ^ " " ^ l') :: (include_aux r)
     | _ :: r -> include_aux r
   in
    include_aux
  in
  let i_ocaml = "-I ." :: (include_aux' false l) in
  let i_coq   = "-I ." :: (include_aux' true  l) in
  section "Libraries definition.";
  print "OCAMLLIBS="; print_list "\\\n  " i_ocaml; print "\n";
  print "COQLIBS=";   print_list "\\\n  " i_coq; print "\n\n"

let rec special = function
  | [] -> []
  | Special (file,deps,com) :: r -> (file,deps,com) :: (special r)
  | _ :: r -> special r

let custom sps =
  let pr_sp (file,dependencies,com) =
    print file; print ": "; print dependencies; print "\n";
    print "\t"; print com; print "\n\n"
  in
  if sps <> [] then section "Custom targets.";
  List.iter pr_sp sps

let subdirs l =
  let rec subdirs_aux = function
    | [] -> []
    | Subdir x :: r -> x :: (subdirs_aux r)
    | _ :: r -> subdirs_aux r
  and pr_subdir s =
    print s; print ":\n\tcd "; print s; print " ; $(MAKE) all\n\n"
  in
  let sds = subdirs_aux l in
  if sds <> [] then section "Subdirectories.";
  List.iter pr_subdir sds;
  section "Special targets.";
  print ".PHONY: ";
  print_list " "
    ("all" ::  "opt" :: "byte" :: "archclean" :: "clean" :: "install" 
     :: "depend" :: "html" :: sds);
  print "\n\n";
  sds

(* Extract gallina/html filenames (foo.v) from the list of all targets *)

let rec other_files suff = function
  | V n :: r -> 
      let f = (Filename.chop_suffix n ".vo") ^ suff in
      f :: (other_files suff r)
  | _   :: r -> 
      other_files suff r
  | [] -> 
      []

let vfiles = other_files ".v"
let gfiles = other_files ".g"
let hfiles = other_files ".html"
let tfiles = other_files ".tex"
let vifiles = other_files ".vi"
let gtfiles l = List.map (fun f -> f ^ ".tex") (gfiles l)
let ghfiles l = List.map (fun f -> f ^ ".html") (gfiles l)
let vofiles = other_files ".vo"

let all_target l =
  let rec fnames = function
    | ML n :: r -> n :: (fnames r)
    | Subdir n :: r -> n :: (fnames r)
    | V n :: r -> n :: (fnames r)
    | Special (n,_,_) :: r -> 
	if is_genrule n then fnames r else n :: (fnames r)
    | Include _ :: r -> fnames r
    | RInclude _ :: r -> fnames r
    | Def _ :: r -> fnames r
    | [] -> []
  in
  section "Definition of the \"all\" target.";
  print "VFILES="; print_list "\\\n  " (vfiles l); print "\n";
  print "VOFILES=$(VFILES:.v=.vo)\n";
  print "VIFILES=$(VFILES:.v=.vi)\n";
  print "GFILES=$(VFILES:.v=.g)\n";
  print "HTMLFILES=$(VFILES:.v=.html)\n";
  print "GHTMLFILES=$(VFILES:.v=.g.html)\n";
  print "\n";
  print "all: "; print_list "\\\n  " (fnames l);
  print "\n\n";
  if !some_vfile then begin
    print "spec: $(VIFILES)\n\n";
    print "gallina: $(GFILES)\n\n";
    print "html: $(HTMLFILES)\n\n";
    print "gallinahtml: $(GHTMLFILES)\n\n";
    print "all.ps: $(VFILES)\n";
    print "\t$(COQDOC) -ps -o $@ `$(COQDEP) -slash -sort -suffix .v $(VFILES)`\n\n";
    print "all-gal.ps: $(VFILES)\n";
    print "\t$(COQDOC) -ps -g -o $@ `$(COQDEP) -slash -sort -suffix .v $(VFILES)`\n\n";
    print "all.pdf: $(VFILES)\n";
    print "\t$(COQDOC) -toc -pdf $(COQDOCLIBS) -o $@ `$(COQDEP) -slash -sort -suffix .v $(VFILES)`\n\n";
    print "all-gal.pdf: $(VFILES)\n";
    print "\t$(COQDOC) -toc -pdf -g $(COQDOCLIBS) -o $@ `$(COQDEP) -slash -sort -suffix .v $(VFILES)`\n\n";
     print "\n\n"
  end

let parse f =
  let rec string = parser 
    | [< '' ' | '\n' | '\t' >] -> ""
    | [< 'c; s >] -> (String.make 1 c)^(string s)
    | [< >] -> ""
  and string2 = parser 
    | [< ''"' >] -> ""
    | [< 'c; s >] -> (String.make 1 c)^(string2 s)
  and skip_comment = parser 
    | [< ''\n'; s >] -> s
    | [< 'c; s >] -> skip_comment s
    | [< >] -> [< >]
  and args = parser 
    | [< '' ' | '\n' | '\t'; s >] -> args s
    | [< ''#'; s >] -> args (skip_comment s)
    | [< ''"'; str = string2; s >] -> ("" ^ str) :: args s
    | [< 'c; str = string; s >] -> ((String.make 1 c) ^ str) :: (args s)
    | [< >] -> []
  in
  let c = open_in f in
  let res = args (Stream.of_channel c) in
  close_in c;
  res

let rec process_cmd_line = function
  | [] -> 
      some_file := !some_file or !some_mlfile or !some_vfile; []
  | ("-h"|"--help") :: _ -> 
      usage ()
  | ("-no-opt"|"-byte") :: r -> 
      opt := "-byte"; process_cmd_line r
  | ("-full"|"-opt") :: r -> 
      opt := "-opt"; process_cmd_line r
  | "-impredicative-set" :: r ->
      impredicative_set := true; process_cmd_line r
  | "-custom" :: com :: dependencies :: file :: r ->
      some_file := true;
      Special (file,dependencies,com) :: (process_cmd_line r)
  | "-I" :: d :: r ->
      Include d :: (process_cmd_line r)
  | "-R" :: p :: l :: r ->
      RInclude (p,l) :: (process_cmd_line r)
  | ("-I"|"-custom") :: _ -> 
      usage ()
  | "-f" :: file :: r -> 
      make_name := file;
      process_cmd_line ((parse file)@r)
  | ["-f"] -> 
      usage ()
  | "-o" :: file :: r -> 
      makefile_name := file;
      output_channel := (open_out file);
      (process_cmd_line r)
  | v :: "=" :: def :: r -> 
      Def (v,def) :: (process_cmd_line r)
  | f :: r ->
      if Filename.check_suffix f ".v" then begin
        some_vfile := true; 
	V (f^"o") :: (process_cmd_line r)
      end else if Filename.check_suffix f ".ml" then begin
        some_mlfile := true; 
	ML ((Filename.chop_suffix f "ml")^"cmo") :: (process_cmd_line r)
      end else
        Subdir f :: (process_cmd_line r)

let centered_coq_version =
  Coq_config.version ^
  String.make ((10 - String.length Coq_config.version) / 2) ' ' 

let banner () =
  printf
"##############################################################################
##                                                                          ##
##                              Coq Makefile                                ##
##                                                                          ##
##                               %10s                                 ##
##                                                                          ##
##############################################################################

" centered_coq_version

let warning () =
  print "# WARNING\n#\n";
  print "# This Makefile has been automagically generated by coq_makefile\n";
  print "# Edit at your own risks !\n";
  print "#\n# END OF WARNING\n\n"

let print_list l = List.iter (fun x -> print x; print " ") l

let command_line args =
  print "#\n# This Makefile was generated by the command line :\n";
  print "# coq_makefile ";
  print_list args;
  print "\n#\n\n"

let directories_deps l =
  let print_dep f dep = 
    if dep <> [] then begin print f; print ": "; print_list dep; print "\n" end
  in
  let rec iter ((dirs,before) as acc) = function
    | [] -> 
	()
    | (Subdir d) :: l -> 
	print_dep d before; iter (d :: dirs, d :: before) l
    | (ML f) :: l ->
	print_dep f dirs; iter (dirs, f :: before) l
    | (V f) :: l ->
	print_dep f dirs; iter (dirs, f :: before) l
    | (Special (f,_,_)) :: l ->
	print_dep f dirs; iter (dirs, f :: before) l
    | _ :: l -> 
	iter acc l
  in
  iter ([],[]) l

let do_makefile args =
  let l = process_cmd_line args in
  banner ();
  warning ();
  command_line args;
  variables l;
  include_dirs l;
  all_target l;
  let sps = special  l in
  custom sps;
  let sds = subdirs l in
  implicit ();
  standard sds sps;
  (* TEST directories_deps l; *)
  warning ();
  if not (!output_channel == stdout) then close_out !output_channel;
  exit 0

let main () =
  let args =
    if Array.length Sys.argv = 1 then usage ();
    List.tl (Array.to_list Sys.argv)
  in
  do_makefile args

let _ = Printexc.catch main ()

