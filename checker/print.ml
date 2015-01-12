(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Format
open Cic
open Names

let print_instance i = Pp.pp (Univ.Instance.pr i)

let print_pure_constr csr =
  let rec term_display c = match  c with
  | Rel n -> print_string "#"; print_int n
  | Meta n -> print_string "Meta("; print_int n; print_string ")"
  | Var id -> print_string (Id.to_string id)
  | Sort s -> sort_display s
  | Cast (c,_, t) -> open_hovbox 1;
      print_string "("; (term_display c); print_cut();
      print_string "::"; (term_display t); print_string ")"; close_box()
  | Prod (Name(id),t,c) ->
      open_hovbox 1;
      print_string"("; print_string (Id.to_string id);
      print_string ":"; box_display t;
      print_string ")"; print_cut();
      box_display c; close_box()
  | Prod (Anonymous,t,c) ->
      print_string"("; box_display t; print_cut(); print_string "->";
      box_display c; print_string ")";
  | Lambda (na,t,c) ->
      print_string "["; name_display na;
      print_string ":"; box_display t; print_string "]";
      print_cut(); box_display c;
  | LetIn (na,b,t,c) ->
      print_string "["; name_display na; print_string "=";
      box_display b; print_cut();
      print_string ":"; box_display t; print_string "]";
      print_cut(); box_display c;
  | App (c,l) ->
      print_string "(";
      box_display c;
      Array.iter (fun x -> print_space (); box_display x) l;
      print_string ")"
  | Evar _ -> print_string "Evar#"
  | Const (c,u) -> print_string "Cons(";
      sp_con_display c;
      print_string ","; print_instance u;
      print_string ")"
  | Ind ((sp,i),u) ->
      print_string "Ind(";
      sp_display sp;
      print_string ","; print_int i;
      print_string ","; print_instance u;
      print_string ")"
  | Construct (((sp,i),j),u) ->
      print_string "Constr(";
      sp_display sp;
      print_string ",";
      print_int i; print_string ","; print_int j; 
      print_string ","; print_instance u; print_string ")"
  | Case (ci,p,c,bl) ->
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
  | Fix ((t,i),(lna,tl,bl)) ->
      print_string "Fix("; print_int i; print_string ")";
      print_cut();
      open_vbox 0;
      let print_fix () =
        for k = 0 to (Array.length tl) - 1 do
	  open_vbox 0;
	  name_display lna.(k); print_string "/";
	  print_int t.(k); print_cut(); print_string ":";
	  box_display tl.(k) ; print_cut(); print_string ":=";
	  box_display bl.(k); close_box ();
	  print_cut()
        done
      in print_string"{"; print_fix(); print_string"}"
  | CoFix(i,(lna,tl,bl)) ->
      print_string "CoFix("; print_int i; print_string ")";
      print_cut();
      open_vbox 0;
      let print_fix () =
        for k = 0 to (Array.length tl) - 1 do
          open_vbox 1;
	  name_display lna.(k);  print_cut(); print_string ":";
	  box_display tl.(k) ; print_cut(); print_string ":=";
	  box_display bl.(k); close_box ();
	  print_cut();
        done
      in print_string"{"; print_fix (); print_string"}"
  | Proj (p, c) ->
    print_string "Proj("; sp_con_display p; print_string ","; 
    box_display c; print_string ")"

  and box_display c = open_hovbox 1; term_display c; close_box()

  and sort_display = function
    | Prop(Pos) -> print_string "Set"
    | Prop(Null) -> print_string "Prop"
    | Type u -> print_string "Type("; Pp.pp (Univ.pr_uni u); print_string ")"

  and name_display = function
    | Name id -> print_string (Id.to_string id)
    | Anonymous -> print_string "_"
(* Remove the top names for library and Scratch to avoid long names *)
  and sp_display sp =
(*    let dir,l = decode_kn sp in
    let ls =
      match List.rev_map Id.to_string (DirPath.repr dir) with
          ("Top"::l)-> l
	| ("Coq"::_::l) -> l
	| l             -> l
    in  List.iter (fun x -> print_string x; print_string ".") ls;*)
      print_string (debug_string_of_mind sp)
  and sp_con_display sp =
(*    let dir,l = decode_kn sp in
    let ls =
      match List.rev_map Id.to_string (DirPath.repr dir) with
          ("Top"::l)-> l
	| ("Coq"::_::l) -> l
	| l             -> l
    in  List.iter (fun x -> print_string x; print_string ".") ls;*)
      print_string (debug_string_of_con sp)

  in
    try
     box_display csr; print_flush()
    with e ->
	print_string (Printexc.to_string e);print_flush ();
	raise e



