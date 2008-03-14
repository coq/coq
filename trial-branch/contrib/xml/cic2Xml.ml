let print_xml_term ch env sigma cic =
  let ids_to_terms = Hashtbl.create 503 in
  let constr_to_ids = Acic.CicHash.create 503 in
  let ids_to_father_ids = Hashtbl.create 503 in
  let ids_to_inner_sorts = Hashtbl.create 503 in
  let ids_to_inner_types = Hashtbl.create 503 in
  let seed = ref 0 in
  let acic =
   Cic2acic.acic_of_cic_context' true seed ids_to_terms constr_to_ids 
    ids_to_father_ids ids_to_inner_sorts ids_to_inner_types []
    env [] sigma (Unshare.unshare cic) None in
  let xml = Acic2Xml.print_term ids_to_inner_sorts acic in
  Xml.pp_ch xml ch
;;

Tacinterp.declare_xml_printer print_xml_term
;;
