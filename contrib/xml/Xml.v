(******************************************************************************)
(*                                                                            *)
(*                               PROJECT HELM                                 *)
(*                                                                            *)
(*                     A tactic to print Coq objects in XML                   *)
(*                                                                            *)
(*                Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>               *)
(*                                 17/11/1999                                 *)
(******************************************************************************)

Declare ML Module "ntrefiner" "xml" "cooking" "xmlcommand" "xmlentries".

Grammar vernac vernac : Ast :=
  xml_print [ "Print" "XML" identarg($id) "." ] ->
               [(Print $id)]

| xml_print_file [ "Print" "XML" "File" stringarg($fn) identarg($id) "." ] ->
               [(Print $id $fn)]

| xml_show [ "Show" "XML" "Proof" "." ] ->
               [(Show)]

| xml_show_file [ "Show" "XML" "File" stringarg($fn) "Proof" "." ] ->
               [(Show $fn)]

| xml_print_all [ "Print" "XML" "All" "." ] ->
               [(XmlPrintAll)]

| xml_print_dir [ "Print" "XML" "Module" identarg($id) "." ] ->
               [(XmlPrintModule $id)]

| xml_print_dir_disk [ "Print" "XML" "Module" "Disk" stringarg($dn) identarg($id) "." ] ->
               [(XmlPrintModule $id $dn)].
