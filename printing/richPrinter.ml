open RichPp

module Indexer = Indexer (struct type t = Ppannotation.t end)

module RichPpConstr = Ppconstr.RichPp (Indexer)
module RichPpVernac = Ppvernac.RichPp (Indexer)
module RichPpTactic = Pptactic.RichPp (Indexer)

type rich_pp =
    string
    * Ppannotation.t RichPp.located Xml_datatype.gxml
    * Xml_datatype.xml

let make_richpp pr ast =
  let raw_pp, rich_pp =
    rich_pp Indexer.get_annotations (fun () -> pr ast)
  in
  let xml = Ppannotation.(
    xml_of_rich_pp tag_of_annotation attributes_of_annotation rich_pp
  )
  in
  (raw_pp, rich_pp, xml)

let richpp_vernac = make_richpp RichPpVernac.pr_vernac
let richpp_constr = make_richpp RichPpConstr.pr_constr_expr
let richpp_tactic env = make_richpp (RichPpTactic.pr_tactic env)
