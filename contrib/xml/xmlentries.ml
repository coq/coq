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

open Util;;
open Vernacinterp;;

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
     [VARG_IDENTIFIER id] -> (fun () -> Xmlcommand.printModule id None)
   | [VARG_IDENTIFIER id ; VARG_STRING dn] ->
        (fun () -> Xmlcommand.printModule id (Some dn))
   | _  -> anomaly "This should be trapped");;

vinterp_add "XmlPrintSection"
 (function
     [VARG_IDENTIFIER id] -> (fun () -> Xmlcommand.printSection id None)
   | [VARG_IDENTIFIER id ; VARG_STRING dn] ->
        (fun () -> Xmlcommand.printSection id (Some dn))
   | _  -> anomaly "This should be trapped");;
