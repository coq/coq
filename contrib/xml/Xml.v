(******************************************************************************)
(*                                                                            *)
(*                               PROJECT HELM                                 *)
(*                                                                            *)
(*                     A tactic to print Coq objects in XML                   *)
(*                                                                            *)
(*                Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>               *)
(*                                 17/11/1999                                 *)
(******************************************************************************)

Declare ML Module "xml" "cooking" "xmlcommand" "xmlentries".

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

| xml_print_module [ "Print" "XML" "Module" identarg($id) "." ] ->
               [(XmlPrintModule $id)]

| xml_print_module_disk [ "Print" "XML" "Module" "Disk" stringarg($dn) identarg($id) "." ] ->
               [(XmlPrintModule $id $dn)]

| xml_print_section [ "Print" "XML" "Section" identarg($id) "." ] ->
               [(XmlPrintSection $id)]

| xml_print_section_disk [ "Print" "XML" "Section" "Disk" stringarg($dn) identarg($id) "." ] ->
               [(XmlPrintSection $id $dn)].
