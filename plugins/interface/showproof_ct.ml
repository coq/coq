(*****************************************************************************)
(*
   Vers Ctcoq
*)

open Metasyntax
open Printer
open Pp
open Translate
open Ascent
open Vtp
open Xlate

let ct_text x = CT_coerce_ID_to_TEXT (CT_ident x);;

let sps s =
  ct_text s
    ;;


let sphs s =
  ct_text s
    ;;

let spe = sphs "";;
let spb = sps " ";;
let spr = sps "Retour chariot pour Show proof";;

let spnb n =
   let s = ref "" in
   for i=1 to n do s:=(!s)^" "; done; sps !s
;;


let rec spclean l =
  match l with
    [] -> []
   |x::l -> if x=spe then (spclean l) else x::(spclean l)
;;


let spnb n =
   let s = ref "" in
   for i=1 to n do s:=(!s)^" "; done; sps !s
;;

let ct_FORMULA_constr = Hashtbl.create 50;;

let stde()  = (Global.env())

;;

let spt t =
   let f = (translate_constr true (stde()) t) in
   Hashtbl.add ct_FORMULA_constr f t;
   CT_text_formula f
;;



let root_of_text_proof t=
  CT_text_op [ct_text "root_of_text_proof";
              t]
    ;;

let spshrink info t =
  CT_text_op [ct_text "shrink";
	      CT_text_op [ct_text info;
                          t]]
;;

let spuselemma intro x y =
  CT_text_op [ct_text "uselemma";
              ct_text intro;
	      x;y]
;;

let sptoprove p t =
  CT_text_op [ct_text "to_prove";
	      CT_text_path p;
              ct_text "goal";
	      (spt t)]
;;
let sphyp p h t =
  CT_text_op [ct_text "hyp";
	      CT_text_path p;
	      ct_text h;
              (spt t)]
;;
let sphypt p h t =
  CT_text_op [ct_text "hyp_with_type";
	      CT_text_path p;
	      ct_text h;
              (spt t)]
;;

let spwithtac x t =
    CT_text_op [ct_text "with_tactic";
                ct_text t;
                x]
;;


let spv l =
   let l= spclean l in
   CT_text_v l
;;

let sph l =
   let l= spclean l in
   CT_text_h l
;;


let sphv l =
   let l= spclean l in
   CT_text_hv l
;;

let rec prlist_with_sep f g l =
    match l with
      [] -> hov 0 (mt ())
     |x::l1 -> hov 0 ((g x) ++ (f ()) ++ (prlist_with_sep f g l1))
;;

let rec sp_print x =
   match x with
     | CT_coerce_ID_to_TEXT (CT_ident s)
       -> (match s with
	     | "\n" -> fnl ()
	     | "Retour chariot pour Show proof" -> fnl ()
	     |_ -> str s)
     | CT_text_formula  f -> pr_lconstr (Hashtbl.find ct_FORMULA_constr f)
     | CT_text_op [CT_coerce_ID_to_TEXT (CT_ident "to_prove");
		   CT_text_path (CT_signed_int_list p);
		   CT_coerce_ID_to_TEXT (CT_ident "goal");
		   g] ->
      let _p=(List.map (fun y -> match y with
	                 (CT_coerce_INT_to_SIGNED_INT
			      (CT_int x)) -> x
		       | _ -> raise (Failure "sp_print")) p) in
      h 0 (str "<b>" ++ sp_print g ++ str "</b>")
 |   CT_text_op [CT_coerce_ID_to_TEXT (CT_ident "uselemma");
              CT_coerce_ID_to_TEXT (CT_ident intro);
	      l;g] ->
      h 0 (str ("<i>("^intro^" ") ++ sp_print l ++ str ")</i>" ++ sp_print g)
 |   CT_text_op [CT_coerce_ID_to_TEXT (CT_ident "hyp");
	      CT_text_path (CT_signed_int_list p);
	      CT_coerce_ID_to_TEXT (CT_ident hyp);
              g]  ->
      let _p=(List.map (fun y -> match y with
	                  (CT_coerce_INT_to_SIGNED_INT
			      (CT_int x)) -> x
		       | _ -> raise (Failure "sp_print")) p) in
            h 0 (str hyp)

  |   CT_text_op [CT_coerce_ID_to_TEXT (CT_ident "hyp_with_type");
	      CT_text_path (CT_signed_int_list p);
	      CT_coerce_ID_to_TEXT (CT_ident hyp);
              g]  ->
      let _p=(List.map (fun y -> match y with
                         (CT_coerce_INT_to_SIGNED_INT
			      (CT_int x)) -> x
		       | _ -> raise (Failure "sp_print")) p) in
      h 0 (sp_print g ++ spc () ++ str "<i>(" ++ str hyp ++ str ")</i>")

  | CT_text_h l ->
      h 0 (prlist_with_sep (fun () -> mt ())
	     (fun y -> sp_print y) l)
  | CT_text_v l ->
      v 0 (prlist_with_sep (fun () -> mt ())
		(fun y -> sp_print y) l)
  | CT_text_hv l ->
      h 0 (prlist_with_sep (fun () -> mt ())
	     (fun y -> sp_print y) l)
  | CT_text_op [CT_coerce_ID_to_TEXT (CT_ident "shrink");
	      CT_text_op [CT_coerce_ID_to_TEXT (CT_ident info); t]]  ->
                   h 0 (str ("("^info^": ") ++ sp_print t ++ str ")")
  | CT_text_op [CT_coerce_ID_to_TEXT (CT_ident "root_of_text_proof");
              t]->
                    sp_print t
  | _ -> str "..."
;;

