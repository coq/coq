(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(******************************************************************************)
(*                                                                            *)
(*                               PROJECT HELM                                 *)
(*                                                                            *)
(*                     A module to print Coq objects in XML                   *)
(*                                                                            *)
(*                Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>               *)
(*                                 06/12/2000                                 *)
(*                                                                            *)
(* This module adds to the vernacular interpreter the functions that fullfill *)
(* the new commands defined in Xml.v                                          *)
(*                                                                            *)
(******************************************************************************)
(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Util;;
open Vernacinterp;;

open Extend;;
open Genarg;;
open Pp;;
open Pcoq;;

(* File name *)

let wit_filename, rawwit_filename = Genarg.create_arg "filename"
let filename = Pcoq.create_generic_entry "filename" rawwit_filename
let _ = Tacinterp.add_genarg_interp "filename"
  (fun ist x ->
    (in_gen wit_filename
      (out_gen (wit_opt wit_string)
	(Tacinterp.genarg_interp ist
	  (in_gen (wit_opt rawwit_string)
	    (out_gen rawwit_filename x))))))

GEXTEND Gram
  GLOBAL: filename;
  filename: [ [ IDENT "File"; fn = STRING -> Some fn | -> None ] ];
END

let pr_filename = function Some fn -> str " File" ++ str fn | None -> mt ()

let _ = 
  Pptactic.declare_extra_genarg_pprule 
    (rawwit_filename, pr_filename)
    (wit_filename, pr_filename)

(* Disk name *)

let wit_diskname, rawwit_diskname = Genarg.create_arg "diskname"
let diskname = create_generic_entry "diskname" rawwit_diskname
let _ = Tacinterp.add_genarg_interp "diskname"
  (fun ist x ->
    (in_gen wit_diskname
      (out_gen (wit_opt wit_string)
	(Tacinterp.genarg_interp ist
	  (in_gen (wit_opt rawwit_string)
	    (out_gen rawwit_diskname x))))))

GEXTEND Gram
  GLOBAL: diskname;
  diskname: [ [ IDENT "Disk"; fn = STRING -> Some fn | -> None ] ];
END

open Pp

let pr_diskname = function Some fn -> str " Disk" ++ str fn | None -> mt ()

let _ = 
  Pptactic.declare_extra_genarg_pprule 
    (rawwit_diskname, pr_diskname)
    (wit_diskname, pr_diskname)

VERNAC COMMAND EXTEND Xml
| [ "Print" "XML" filename(fn) qualid(id) ] -> [ Xmlcommand.print id fn ]

| [ "Show" "XML" filename(fn) "Proof" ] -> [ Xmlcommand.show fn ]

(*
| [ "Print" "XML" "All" ] -> [ Xmlcommand.printAll () ]

| [ "Print" "XML" "Module" diskname(dn) qualid(id) ] ->
    [ Xmlcommand.printModule id dn ]

| [ "Print" "XML" "Section" diskname(dn) ident(id) ] ->
    [ Xmlcommand.printSection id dn ]
*)
END
(*
vinterp_add "Print"
 (function
     [VARG_QUALID id] ->
        (fun () -> Xmlcommand.print id None)
   | [VARG_QUALID id ; VARG_STRING fn] ->
        (fun () -> Xmlcommand.print id (Some fn))
   | _ -> anomaly "This should be trapped");;

vinterp_add "Show"
 (function
     [] ->
        (fun () -> Xmlcommand.show None)
   | [VARG_STRING fn] ->
        (fun () -> Xmlcommand.show (Some fn))
   | _ -> anomaly "This should be trapped");;

vinterp_add "XmlPrintAll"
 (function
     [] -> (fun () -> Xmlcommand.printAll ())
   | _  -> anomaly "This should be trapped");;

vinterp_add "XmlPrintModule"
 (function
     [VARG_QUALID id] -> (fun () -> Xmlcommand.printModule id None)
   | [VARG_QUALID id ; VARG_STRING dn] ->
        (fun () -> Xmlcommand.printModule id (Some dn))
   | _  -> anomaly "This should be trapped");;

vinterp_add "XmlPrintSection"
 (function
     [VARG_IDENTIFIER id] -> (fun () -> Xmlcommand.printSection id None)
   | [VARG_IDENTIFIER id ; VARG_STRING dn] ->
        (fun () -> Xmlcommand.printSection id (Some dn))
   | _  -> anomaly "This should be trapped");;
*)
