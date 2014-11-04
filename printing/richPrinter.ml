open RichPp

module Indexer = Indexer (struct type t = Ppannotation.t end)

module RichPpConstr = Ppconstr.RichPp (Indexer)
module RichPpVernac = Ppvernac.RichPp (Indexer)

type rich_pp =
    string
    * Ppannotation.t RichPp.located Xml_datatype.gxml
    * Xml_datatype.xml

let richpp_vernac phrase_ast =
  let raw_pp, rich_pp =
    rich_pp Indexer.get_annotations (fun () -> RichPpVernac.pr_vernac phrase_ast)
  in
  let xml = Ppannotation.(
    xml_of_rich_pp tag_of_annotation attributes_of_annotation rich_pp
  )
  in
  (raw_pp, rich_pp, xml)

