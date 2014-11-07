open Richpp

module RichppConstr = Ppconstr.Richpp
module RichppVernac = Ppvernac.Richpp
module RichppTactic = Pptactic.Richpp

type rich_pp =
    string
    * Ppannotation.t Richpp.located Xml_datatype.gxml
    * Xml_datatype.xml

let get_annotations obj = Pp.Tag.prj obj Ppannotation.tag

let make_richpp pr ast =
  let raw_pp, rich_pp =
    rich_pp get_annotations (pr ast)
  in
  let xml = Ppannotation.(
    xml_of_rich_pp tag_of_annotation attributes_of_annotation rich_pp
  )
  in
  (raw_pp, rich_pp, xml)

let richpp_vernac = make_richpp RichppVernac.pr_vernac
let richpp_constr = make_richpp RichppConstr.pr_constr_expr
let richpp_tactic env = make_richpp (RichppTactic.pr_tactic env)
