
(* File to include to install the pretty-printers in the ocaml toplevel *)

#use "base_include.ml";;

#install_printer  (* ast *)  prast;;
#install_printer  (* pat *)  prastpat;;
#install_printer  (* patlist *)  prastpatl;;
#install_printer  (* constr *) ppterm0;;
#install_printer  (* type_judgement*) pptype;;
#install_printer  (* judgement*) prj;;
#install_printer  (* goal *)  prgoal;;
#install_printer  (* sigma goal *)  prsigmagoal;;
#install_printer  (* ctxt *)  prctxt;;
#install_printer  (* proof *)  pproof;;
#install_printer  (* global_constraints *)  prevd;;
#install_printer  (* readable_constraints *)  prevc;;
#install_printer  (* walking_constraints *)  prwc;;
#install_printer  (* universe *)  print_uni;;
#install_printer  (* universes *)  pp_universes;;
#install_printer  (* clenv *) prclenv;;
