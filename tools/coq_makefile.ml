
(* $Id$ *)

(* créer un Makefile pour un développement Coq automatiquement *)

type target =
  | ML of string (* ML file : foo.ml -> (ML "foo") *)
  | V of string  (* V file : foo.v -> (V "foo") *)
  | Special of string * string * string (* file, dependencies, command *)
  | Subdir of string
  | Def of string * string (* X=foo -> Def ("X","foo") *)
  | Include of string

let output_channel = ref stdout

let some_file = ref false

let some_vfile = ref false

let some_mlfile = ref false

let opt = ref "-opt"

let print x = output_string !output_channel x

let rec print_list sep = function
  | [ x ] -> print x
  | x::l -> print x ; print sep ; print_list sep l
  | [] -> ()

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
  command dependencies file] ... [-I dir] ... [VARIABLE = value] ...
  [-full] [-no-opt] [-f file] [-o file] [-h] [--help]

[file.v]: Coq file to be compiled
[file.ml]: ML file to be compiled
[subdirectory] : subdirectory that should be \"made\"
[-custom command dependencies file]: add target \"file\" with command
  \"command\" and dependencies \"dependencies\"
[-I dir]: look for dependencies in \"dir\"
[VARIABLE = value]: Add the variable definition \"VARIABLE=value\"
[-full]: \"opt\" should use \"coqc -full\" instead of \"coqc -opt\"
[-no-opt]: target \"opt\" should be equivalent to \"byte\"
[-f file]: take the contents of file as arguments
[-o file]: output should go in file file 
[-h]: print this usage summary
[--help]: equivalent to [-h]\n";
  exit 1

let standard sds =
  print "byte::\n";
  print "\t$(MAKE) all \"OPT=\"\n\n";
  print "opt::\n";
  if !opt = "" then print "\t@echo \"WARNING: opt is disabled\"\n";
  print "\t$(MAKE) all \"OPT="; print !opt ; print "\"\n\n";
  if !some_file then print "include .depend\n\n";
  print "depend::\n";
  if !some_file then begin
    print "\trm .depend\n";
    print "\t$(COQDEP) -i $(LIBS) *.v *.ml *.mli >.depend\n";
    print "\t$(COQDEP) $(LIBS) -suffix .html *.v >>.depend\n";
    if !some_mlfile then print "\t$(P4DEP) *.ml >>.depend\n"
  end;
  List.iter
    (fun x -> print "\t(cd "; print x; print " ; $(MAKE) depend)\n")
    sds;
  print "\n";
  print "install::\n";
  print "\t@if test -z $(TARGETDIR); then echo \"You must set TARGETDIR (for instance with 'make TARGETDIR=foobla install')\"; exit 1; fi\n";
  if !some_vfile then print "\tcp -f *.vo $(TARGETDIR)\n";
  if !some_mlfile then print "\tcp -f *.cmo $(TARGETDIR)\n";
  List.iter
    (fun x -> print "\t(cd "; print x; print " ; $(MAKE) install)\n")
    sds;
  print "\n";
  print "Makefile::\n";
  print "\tmv -f Makefile Makefile.bak\n";
  print "\tcoq_makefile -f Make -o Makefile\n";
  print "\n";
  print "clean::\n";
  print "\trm -f *.cmo *.cmi *.cmx *.o *.vo *.vi *~\n";
  List.iter
    (fun x -> print "\t(cd "; print x; print " ; $(MAKE) clean)\n")
    sds;
  print "\n";
  print "archclean::\n";
  print "\trm -f *.cmx *.o\n";
  List.iter
    (fun x -> print "\t(cd "; print x; print " ; $(MAKE) archclean)\n")
    sds;
  print "\n"

let implicit () =
  let ml_rules () =
    print ".mli.cmi:\n\t$(CAMLC) $(ZDEBUG) $(ZFLAGS) $<\n\n" ;
    print ".ml.cmo:\n\t$(CAMLC) $(ZDEBUG) $(ZFLAGS) $<\n\n" ;
    print ".ml.cmx:\n\t$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) $<\n\n" ;
    print ".ml4.cmo:\n\t$(CAMLC) -pp $(P4) $(ZDEBUG) $(ZFLAGS) -impl $<\n\n";
    print ".ml4.cmx:\n\t$(CAMLOPTC) -pp $(P4) $(ZDEBUG) $(ZFLAGS)\n\n"
  and v_rule () =
    print ".v.vo:\n\t$(COQC) $(COQDEBUG) $(COQFLAGS) $*\n\n" ;
    print ".v.vi:\n\t$(COQC) -i $(COQDEBUG) $(COQFLAGS) $*\n\n" ;
    print ".v.g:\n\t$(GALLINA) $<\n\n" ;
    print ".v.html:\n\t$(COQ2HTML) $<\n\n" ;
    print ".v.tex:\n\t$(COQ2LATEX) $< -latex -o $@\n\n" ;
    print ".v.g.html:\n\t$(GALLINA) -stdout $< | $(COQ2HTML) -f > $@\n\n" ;
    print 
      ".v.g.tex:\n\t$(GALLINA) -stdout $< | $(COQ2LATEX) - -latex -o $@\n\n"
  and ml_suffixes =
    if !some_mlfile then 
      [ ".mli" ; ".ml" ; ".cmo" ; ".cmi"; ".cmx" ]
    else 
      []
  and v_suffixes =
    if !some_vfile then 
      [ ".v" ; ".vo" ; ".vi" ; ".g" ; ".html" ; ".tex" ;
	".g.tex" ; ".g.html" ] 
    else 
      []
  in
  let suffixes = ml_suffixes @ v_suffixes in
  if suffixes <> [] then begin
    print ".SUFFIXES: " ; print_list " " suffixes ;
    print "\n\n"
  end;
  if !some_mlfile then ml_rules ();
  if !some_vfile then v_rule ()

let variables l =
  let rec var_aux = function
    | [] -> ()
    | Def(v,def)::r -> print v ; print "=" ; print def ; print "\n";var_aux r
    | _::r -> var_aux r
  in
  section "Variables definitions.";
  print "CAMLP4LIB=`camlp4 -where`\n";
  print "MAKE=make \"COQBIN=$(COQBIN)\" \"OPT=$(OPT)\"\n";
  print "COQSRC=-I $(COQTOP)/src/tactics -I $(COQTOP)/src/proofs \\
  -I $(COQTOP)/src/syntax -I $(COQTOP)/src/env -I $(COQTOP)/src/lib/util \\
  -I $(COQTOP)/src/constr -I $(COQTOP)/tactics -I $(COQTOP)/src/meta \\
  -I $(COQTOP)/src/parsing -I $(COQTOP)/src/typing -I $(CAMLP4LIB)\n";
  print "ZFLAGS=$(LIBS) $(COQSRC)\n";
  print "FULLOPT=$(OPT:-opt=-full)\n";
  if !opt="-opt" then
    print "COQFLAGS=-q $(OPT) $(LIBS)\n"
  else begin
    print "OPTCOQ=";
    print "$(OPT:-opt="; print !opt; print ")\n";
    print "COQFLAGS=-q $(OPTCOQ) $(LIBS)\n"
  end;
  print "COQC=$(COQBIN)coqc\n";
  print "COQFULL=$(COQBIN)coqc $(FULLOPT) -q $(LIBS)\n";
  print "GALLINA=gallina\n";
  print "COQ2HTML=coq2html\n";
  print "COQ2LATEX=coq2latex\n";
  print "CAMLC=ocamlc -c\n";
  print "CAMLOPTC=ocamlopt -c\n";
  print "CAMLLINK=ocamlc\n";
  print "CAMLOPTLINK=ocamlopt\n";
  print "COQDEP=$(COQBIN)coqdep -c\n";
  print "P4=$(COQBIN)call_camlp4 -I $(COQTOP)/src/parsing \\
  -I $(COQTOP)/theories/INIT -I $(COQTOP)/tactics\n";
  print "P4DEP=$(COQBIN)camlp4dep\n";
  var_aux l;
  print "\n"

let include_dirs l =
  let rec include_aux = function
    | [] -> []
    | Include x :: r -> ("-I "^x) :: (include_aux r)
    | _ :: r -> include_aux r
  in
  let i = "-I ." :: (include_aux l) in
  if i <> [] then begin
    section "Libraries definition.";
    print "LIBS="; print_list "\\\n  " i; print "\n\n"
  end

let special l =
  let pr_sp (file,dependencies,com) =
    print file; print ": "; print dependencies; print "\n";
    print "\t"; print com; print "\n\n"
  in
  let rec sp_aux = function
    | [] -> []
    | Special(file,dependencies,com)::r -> (file,dependencies,com)::(sp_aux r)
    | _::r -> sp_aux r
  in
  let sps = sp_aux l in
  if sps <> [] then section "Custom targets.";
  List.iter pr_sp sps

let subdirs l =
  let rec subdirs_aux = function
    | [] -> []
    | Subdir x :: r -> x::(subdirs_aux r)
    | _ :: r -> subdirs_aux r
  and pr_subdir s =
    print s ; print "::\n\tcd " ; print s ; print " ; $(MAKE) all\n\n"
  in
  let sds = subdirs_aux l in
  if sds <> [] then section "Subdirectories.";
  List.iter pr_subdir sds;
  section "Special targets.";
  print ".PHONY: " ;
  print_list " "
    ("all"::"opt"::"byte"::"archclean"::"clean"::"install"::"depend"::sds);
  print "\n\n";
  sds

(* Extract gallina/html filenames (foo.v) from the list of all targets *)

let rec other_files suff = function
  | V n :: r -> 
      let f = (Filename.chop_suffix n "vo") ^ suff in
      f :: (other_files suff r)
  | _   :: r -> other_files suff r
  | []       -> []

let gfiles = other_files "g"
let hfiles = other_files "html"
let tfiles = other_files "tex"
let vifiles = other_files "vi"
let gtfiles l = List.map (fun f -> f^".tex") (gfiles l)
let ghfiles l = List.map (fun f -> f^".html") (gfiles l)

let all_target l =
  let rec fnames = function
    | ML n :: r -> n::(fnames r)
    | Subdir n ::r -> n::(fnames r)
    | V n :: r -> n::(fnames r)
    | Special (n,_,_) :: r -> n::(fnames r)
    | Include _ :: r -> fnames r
    | Def _ :: r -> fnames r
    | [] -> []
  in
  section "Definition of the \"all\" target.";
  print "all:: "; print_list "\\\n  " (fnames l) ;
  print "\n\n" ;
  if !some_vfile then begin
    print "spec:: "; print_list "\\\n  " (vifiles l) ;
    print "\n\n";
    print "gallina:: "; print_list "\\\n  " (gfiles l) ;
    print "\n\n";
    print "html:: "; print_list "\\\n  " (hfiles l) ;
    print "\n\n";
    print "tex:: "; print_list "\\\n  " (tfiles l) ;
    print "\n\n";
    print "gallinatex:: "; print_list "\\\n  " (gtfiles l) ;
    print "\n\n";
    print "gallinahtml:: "; print_list "\\\n  " (ghfiles l) ;
    print "\n\n";
  end

let parse f =
  let rec string = parser 
    | [< '' ' | '\n' | '\t' >] -> ""
    | [< 'c ; s >] -> (String.make 1 c)^(string s)
    | [< >] -> ""
  and string2 = parser 
    | [< ''"' >] -> ""
    | [< 'c ; s >] -> (String.make 1 c)^(string2 s)
  and skip_comment = parser 
    | [< ''\n' ; s >] -> s
    | [< 'c ; s >] -> skip_comment s
    | [< >] -> [< >]
  and args = parser 
    | [< '' ' | '\n' | '\t'; s >] -> args s
    | [< ''#' ; s >] -> args (skip_comment s)
    | [< ''"' ; str = string2 ; s >] -> (""^str)::args s
    | [< 'c ; str = string ; s >] -> ((String.make 1 c)^str)::(args s)
    | [< >] -> []
  in
  let c = open_in f in
  let res = args (Stream.of_channel c) in
  close_in c;
  res

let rec process_cmd_line = function
  | [] -> 
      some_file := !some_file or !some_mlfile or !some_vfile ; []
  | ("-h"|"--help") :: _ -> 
      usage ()
  | "-no-opt" :: r -> 
      opt := "" ; process_cmd_line r
  | "-full"::r -> 
      opt := "-full" ; process_cmd_line r
  | "-custom" :: com :: dependencies :: file :: r ->
      some_file := true;
      Special (file,dependencies,com) :: (process_cmd_line r)
  | "-I" :: d :: r ->
      Include d :: (process_cmd_line r)
  | ("-I" | "-h" | "--help" | "-custom") :: _ -> 
      usage ()
  | "-f"::file::r -> 
      process_cmd_line ((parse file)@r)
  | ["-f"] -> 
      usage ()
  | "-o" :: file :: r -> 
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

let banner () =
  print
"##############################################################################
##                 The Calculus of Inductive Constructions                  ##
##                                                                          ##
##                                Projet Coq                                ##
##                                                                          ##
##                     INRIA                        ENS-CNRS                ##
##              Rocquencourt                        Lyon                    ##
##                                                                          ##
##                                Coq V6.1                                  ##
##                                                                          ##
##                                                                          ##
##############################################################################

"

let warning () =
  print "# WARNING\n#\n";
  print "# This Makefile has been automagically generated by coq_makefile\n";
  print "# Edit at your own risks !\n";
  print "#\n# END OF WARNING\n\n"

let command_line args =
  print "#\n# This Makefile was generated by the command line :\n";
  print "# coq_makefile ";
  List.iter (fun x -> print x; print " ") args;
  print "\n#\n\n"

let do_makefile args =
  let l = process_cmd_line args in
  banner ();
  warning ();
  command_line args;
  variables l;
  include_dirs l;
  all_target l;
  special l;
  let sds = subdirs l in
  implicit ();
  standard sds;
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

