(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Printers for the ocaml toplevel. *)

open System
open Pp
open Ast
open Names
open Sign
open Univ
open Proof_trees
open Environ
open Printer
open Refiner
open Tacmach
open Term
open Clenv
open Errors

let _ = Termast.print_evar_arguments := true

let pP s = pP (hOV 0 s)

let prast c = pP(print_ast c)

let prastpat c = pP(print_astpat c)
let prastpatl c = pP(print_astlpat c)
let ppterm = (fun x -> pP(prterm x))
let pprawterm = (fun x -> pP(pr_rawterm x))
let pppattern = (fun x -> pP(pr_pattern x))
let pptype = (fun x -> pP(prtype x))

let prid id = pP [< 'sTR(string_of_id id) >]

let prconst (sp,j) =
    pP [< 'sTR"#"; 'sTR(string_of_path sp); 
	  'sTR"="; prterm j.uj_val >]

let prvar ((id,a)) =
    pP [< 'sTR"#" ; 'sTR(string_of_id id) ; 'sTR":" ; 
	  prterm a >]

let genprj f j =
  let (c,t) = Termast.with_casts f j in [< c; 'sTR " : "; t >]

let prj j = pP (genprj prjudge j)


let prsp sp = pP[< 'sTR(string_of_path sp) >]

let prqualid qid = pP[< Nametab.pr_qualid qid >]

let prgoal g = pP(prgl g)

let prsigmagoal g = pP(prgl (sig_it g))

let prgls gls = pP(pr_gls gls)

let prglls glls = pP(pr_glls glls)

let prctxt ctxt = pP(pr_ctxt ctxt)

let pproof p = pP(print_proof Evd.empty empty_named_context p)

let prevd evd = pP(pr_decls evd)

let prevc evc = pP(pr_evc evc)

let prwc wc = pP(pr_evc wc)

let prclenv clenv = pP(pr_clenv clenv)

let print_uni u = (pP (pr_uni u))

let pp_universes u = pP [< 'sTR"[" ; pr_universes u ; 'sTR"]" >]

let ppenv e = pP (pr_rel_context e (rel_context e))

let cnt = ref 0

let constr_display csr =
  let rec term_display c = match kind_of_term c with
  | IsRel n -> "Rel("^(string_of_int n)^")"
  | IsMeta n -> "Meta("^(string_of_int n)^")"
  | IsVar id -> "Var("^(string_of_id id)^")"
  | IsSort s -> "Sort("^(sort_display s)^")"
  | IsCast (c,t) -> "Cast("^(term_display c)^","^(term_display t)^")"
  | IsProd (na,t,c) ->
      "Prod("^(name_display na)^","^(term_display t)^","^(term_display c)^")\n"
  | IsLambda (na,t,c) ->
      "Lambda("^(name_display na)^","^(term_display t)^","^(term_display c)^")\n"
  | IsLetIn (na,b,t,c) ->
      "LetIn("^(name_display na)^","^(term_display b)^","
      ^(term_display t)^","^(term_display c)^")"
  | IsApp (c,l) -> "App("^(term_display c)^","^(array_display l)^")\n"
  | IsEvar (e,l) -> "Evar("^(string_of_int e)^","^(array_display l)^")"
  | IsConst (c,l) -> "Const("^(string_of_path c)^","^(array_display l)^")"
  | IsMutInd ((sp,i),l) ->
      "MutInd(("^(string_of_path sp)^","^(string_of_int i)^"),"
      ^(array_display l)^")"
  | IsMutConstruct (((sp,i),j),l) ->
      "MutConstruct((("^(string_of_path sp)^","^(string_of_int i)^"),"
      ^(string_of_int j)^"),"^(array_display l)^")"
  | IsMutCase (ci,p,c,bl) ->
      "MutCase(<abs>,"^(term_display p)^","^(term_display c)^","
      ^(array_display bl)^")"
  | IsFix ((t,i),(lna,tl,bl)) ->
      "Fix(([|"^(Array.fold_right (fun x i -> (string_of_int x)^(if not(i="")
        then (";"^i) else "")) t "")^"|],"^(string_of_int i)^"),"
      ^(array_display tl)^","
      ^(Array.fold_right (fun x i -> (name_display x)^(if not(i="")
        then (";"^i) else "")) lna "")^","
      ^(array_display bl)^")"
  | IsCoFix(i,(lna,tl,bl)) ->
      "CoFix("^(string_of_int i)^"),"
      ^(array_display tl)^","
      ^(Array.fold_right (fun x i -> (name_display x)^(if not(i="")
        then (";"^i) else "")) lna "")^","
      ^(array_display bl)^")"

  and array_display v =
    "[|"^
    (Array.fold_right
       (fun x i -> (term_display x)^(if not(i="") then (";"^i) else ""))
       v "")^"|]"

  and sort_display = function
    | Prop(Pos) -> "Prop(Pos)"
    | Prop(Null) -> "Prop(Null)"
    | Type u ->
	incr cnt; pP [< 'sTR "with "; 'iNT !cnt; pr_uni u; 'fNL >];
	"Type("^(string_of_int !cnt)^")"

  and name_display = function
    | Name id -> "Name("^(string_of_id id)^")"
    | Anonymous -> "Anonymous"

  in
    mSG [<'sTR (term_display csr);'fNL>]

open Format;;

let print_pure_constr csr =
  let rec term_display c = match kind_of_term c with
  | IsRel n -> print_string "#"; print_int n
  | IsMeta n -> print_string "Meta("; print_int n; print_string ")"
  | IsVar id -> print_string (string_of_id id)
  | IsSort s -> sort_display s
  | IsCast (c,t) -> open_hovbox 1;
      print_string "("; (term_display c); print_cut();
      print_string "::"; (term_display t); print_string ")"; close_box()
  | IsProd (Name(id),t,c) ->
      open_hovbox 1;
      print_string"("; print_string (string_of_id id); 
      print_string ":"; box_display t; 
      print_string ")"; print_cut(); 
      box_display c; close_box()
  | IsProd (Anonymous,t,c) ->
      print_string"("; box_display t; print_cut(); print_string "->";
      box_display c; print_string ")"; 
  | IsLambda (na,t,c) ->
      print_string "["; name_display na;
      print_string ":"; box_display t; print_string "]";
      print_cut(); box_display c; 
  | IsLetIn (na,b,t,c) ->
      print_string "["; name_display na; print_string "="; 
      box_display b; print_cut();
      print_string ":"; box_display t; print_string "]";
      print_cut(); box_display c; 
  | IsApp (c,l) -> 
      print_string "("; 
      box_display c; 
      Array.iter (fun x -> print_space (); box_display x) l;
      print_string ")"
  | IsEvar (e,l) -> print_string "Evar#"; print_int e; print_string "{";
      Array.iter (fun x -> print_space (); box_display x) l;
      print_string"}"
  | IsConst (c,l) -> print_string "Cons(";
      sp_display c;
      print_string "){";
      Array.iter (fun x -> print_space (); box_display x) l;
      print_string"}"
  | IsMutInd ((sp,i),l) ->
      print_string "Ind(";
      sp_display sp;
      print_string ","; print_int i;
      print_string "){";
      Array.iter (fun x -> print_space (); box_display x) l;
      print_string"}"
  | IsMutConstruct (((sp,i),j),l) ->
      print_string "Constr(";
      sp_display sp;
      print_string ",";
      print_int i; print_string ","; print_int j; print_string ")";
      Array.iter (fun x -> print_space (); box_display x) l;
  | IsMutCase (ci,p,c,bl) ->
      open_vbox 0;
      print_string "<"; box_display p; print_string ">";
      print_cut(); print_string "Case";
      print_space(); box_display c; print_space (); print_string "of";
      open_vbox 0;
      Array.iter (fun x ->  print_cut();  box_display x) bl;
      close_box();
      print_cut(); 
      print_string "end"; 
      close_box()
  | IsFix ((t,i),(lna,tl,bl)) ->
      print_string "Fix("; print_int i; print_string ")"; 
      print_cut();
      open_vbox 0;
      let rec print_fix () =
        for k = 0 to Array.length tl do
	  open_vbox 0;
	  name_display lna.(k); print_string "/"; 
	  print_int t.(k); print_cut(); print_string ":";
	  box_display tl.(k) ; print_cut(); print_string ":=";
	  box_display bl.(k); close_box ();
	  print_cut()
        done
      in print_string"{"; print_fix(); print_string"}"
  | IsCoFix(i,(lna,tl,bl)) ->
      print_string "CoFix("; print_int i; print_string ")"; 
      print_cut();
      open_vbox 0;
      let rec print_fix () =
        for k = 0 to Array.length tl do
          open_vbox 1;
	  name_display lna.(k);  print_cut(); print_string ":";
	  box_display tl.(k) ; print_cut(); print_string ":=";
	  box_display bl.(k); close_box ();
	  print_cut();
        done
      in print_string"{"; print_fix (); print_string"}"

  and box_display c = open_hovbox 1; term_display c; close_box()

  and sort_display = function
    | Prop(Pos) -> print_string "Set"
    | Prop(Null) -> print_string "Prop"
    | Type u -> open_hbox();
	print_string "Type("; pP (pr_uni u); print_string ")"; close_box()

  and name_display = function
    | Name id -> print_string (string_of_id id)
    | Anonymous -> print_string "_"
(* Remove the top names for library and Scratch to avoid long names *)
  and sp_display sp = let ls = 
    match (dirpath sp) with 
        ("Scratch"::l)-> l
      | ("Coq"::_::l) -> l 
      | l             -> l
  in  List.iter (fun x -> print_string x; print_string ".") ls;
      print_string (string_of_id  (basename sp))

  in
     box_display csr; print_newline()
(*
let _ =
  Vernacentries.add "PrintConstr"
    (function
       | [VARG_CONSTR c] -> 
	   (fun () ->
              let (evmap,sign) = Command.get_current_context () in
  	      constr_display (Astterm.interp_constr evmap sign c))
       | _ -> bad_vernac_args "PrintConstr")

let _ =
  Vernacentries.add "PrintPureConstr"
    (function
       | [VARG_CONSTR c] -> 
	   (fun () ->
              let (evmap,sign) = Command.get_current_context () in
  	      print_pure_constr (Astterm.interp_constr evmap sign c))
       | _ -> bad_vernac_args "PrintPureConstr")
*)
