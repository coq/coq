(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Printers for the ocaml toplevel. *)

open System
open Pp
open Ast
open Names
open Libnames
open Nameops
open Sign
open Univ
open Proof_trees
open Environ
open Printer
open Refiner
open Tacmach
open Term
open Termops
open Clenv
open Cerrors

let _ = Constrextern.print_evar_arguments := true

let pP s = pp (hov 0 s)

let prast c = pp(print_ast c)

let prastpat c = pp(print_astpat c)
let prastpatl c = pp(print_astlpat c)
let ppterm x = pp(prterm x)
let ppsterm x = ppterm (Declarations.force x)
let ppterm_univ x = Constrextern.with_universes ppterm x
let pprawterm = (fun x -> pp(pr_rawterm x))
let pppattern = (fun x -> pp(pr_pattern x))
let pptype = (fun x -> pp(prtype x))

let safe_prglobal = function 
  | ConstRef kn -> pp (str "CONSTREF(" ++ pr_kn kn ++ str ")")
  | IndRef (kn,i) -> pp (str "INDREF(" ++ pr_kn kn ++ str "," ++ 
			  int i ++ str ")")
  | ConstructRef ((kn,i),j) -> pp (str "INDREF(" ++ pr_kn kn ++ str "," ++ 
				      int i ++ str "," ++ int j ++ str ")")
  | VarRef id -> pp (str "VARREF(" ++ pr_id id ++ str ")")

let prglobal x = try pp(pr_global x) with _ -> safe_prglobal x

let prid id = pp (pr_id id)
let prlab l = pp (pr_lab l)

let prmsid msid = pp (str (debug_string_of_msid msid))
let prmbid mbid = pp (str (debug_string_of_mbid mbid))

let prdir dir = pp (pr_dirpath dir)

let prmp mp = pp(str (string_of_mp mp))
let prkn kn = pp(pr_kn kn)

let prsp sp = pp(pr_sp sp)

let prqualid qid = pp(pr_qualid qid)

let prconst (sp,j) =
    pp (str"#" ++ pr_kn sp ++ str"=" ++ prterm j.uj_val)

let prvar ((id,a)) =
    pp (str"#" ++ pr_id id ++ str":" ++ prterm a)

let genprj f j = let (c,t) = f j in (c ++ str " : " ++ t)

let prj j = pp (genprj prjudge j)

let prgoal g = pp(prgl g)

let prsigmagoal g = pp(prgl (sig_it g))

let prgls gls = pp(pr_gls gls)

let prglls glls = pp(pr_glls glls)

let pproof p = pp(print_proof Evd.empty empty_named_context p)

let prevd evd = pp(pr_decls evd)

let prevc evc = pp(pr_evc evc)

let prwc wc = pp(pr_evc wc)

let prclenv clenv = pp(pr_clenv clenv)

let print_uni u = (pp (pr_uni u))

let pp_universes u = pp (str"[" ++ pr_universes u ++ str"]")

let ppenv e = pp
  (str "[" ++ pr_named_context_of e ++ str "]" ++ spc() ++
   str "[" ++ pr_rel_context e (rel_context e) ++ str "]")

let pptac = (fun x -> pp(Pptactic.pr_glob_tactic x))

let pr_obj obj = Format.print_string (Libobject.object_tag obj)

let cnt = ref 0

let constr_display csr =
  let rec term_display c = match kind_of_term c with
  | Rel n -> "Rel("^(string_of_int n)^")"
  | Meta n -> "Meta("^(string_of_int n)^")"
  | Var id -> "Var("^(string_of_id id)^")"
  | Sort s -> "Sort("^(sort_display s)^")"
  | Cast (c,t) -> "Cast("^(term_display c)^","^(term_display t)^")"
  | Prod (na,t,c) ->
      "Prod("^(name_display na)^","^(term_display t)^","^(term_display c)^")\n"
  | Lambda (na,t,c) ->
      "Lambda("^(name_display na)^","^(term_display t)^","^(term_display c)^")\n"
  | LetIn (na,b,t,c) ->
      "LetIn("^(name_display na)^","^(term_display b)^","
      ^(term_display t)^","^(term_display c)^")"
  | App (c,l) -> "App("^(term_display c)^","^(array_display l)^")\n"
  | Evar (e,l) -> "Evar("^(string_of_int e)^","^(array_display l)^")"
  | Const c -> "Const("^(string_of_kn c)^")"
  | Ind (sp,i) ->
      "MutInd("^(string_of_kn sp)^","^(string_of_int i)^")"
  | Construct ((sp,i),j) ->
      "MutConstruct(("^(string_of_kn sp)^","^(string_of_int i)^"),"
      ^(string_of_int j)^")"
  | Case (ci,p,c,bl) ->
      "MutCase(<abs>,"^(term_display p)^","^(term_display c)^","
      ^(array_display bl)^")"
  | Fix ((t,i),(lna,tl,bl)) ->
      "Fix(([|"^(Array.fold_right (fun x i -> (string_of_int x)^(if not(i="")
        then (";"^i) else "")) t "")^"|],"^(string_of_int i)^"),"
      ^(array_display tl)^","
      ^(Array.fold_right (fun x i -> (name_display x)^(if not(i="")
        then (";"^i) else "")) lna "")^","
      ^(array_display bl)^")"
  | CoFix(i,(lna,tl,bl)) ->
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
	incr cnt; pp (str "with " ++ int !cnt ++ pr_uni u ++ fnl ());
	"Type("^(string_of_int !cnt)^")"

  and name_display = function
    | Name id -> "Name("^(string_of_id id)^")"
    | Anonymous -> "Anonymous"

  in
    msg (str (term_display csr) ++fnl ())

open Format;;

let print_pure_constr csr =
  let rec term_display c = match kind_of_term c with
  | Rel n -> print_string "#"; print_int n
  | Meta n -> print_string "Meta("; print_int n; print_string ")"
  | Var id -> print_string (string_of_id id)
  | Sort s -> sort_display s
  | Cast (c,t) -> open_hovbox 1;
      print_string "("; (term_display c); print_cut();
      print_string "::"; (term_display t); print_string ")"; close_box()
  | Prod (Name(id),t,c) ->
      open_hovbox 1;
      print_string"("; print_string (string_of_id id); 
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
  | Evar (e,l) -> print_string "Evar#"; print_int e; print_string "{";
      Array.iter (fun x -> print_space (); box_display x) l;
      print_string"}"
  | Const c -> print_string "Cons(";
      sp_display c;
      print_string ")"
  | Ind (sp,i) ->
      print_string "Ind(";
      sp_display sp;
      print_string ","; print_int i;
      print_string ")"
  | Construct ((sp,i),j) ->
      print_string "Constr(";
      sp_display sp;
      print_string ",";
      print_int i; print_string ","; print_int j; print_string ")"
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
  | CoFix(i,(lna,tl,bl)) ->
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
	print_string "Type("; pp (pr_uni u); print_string ")"; close_box()

  and name_display = function
    | Name id -> print_string (string_of_id id)
    | Anonymous -> print_string "_"
(* Remove the top names for library and Scratch to avoid long names *)
  and sp_display sp = 
(*    let dir,l = decode_kn sp in
    let ls = 
      match List.rev (List.map string_of_id (repr_dirpath dir)) with 
          ("Top"::l)-> l
	| ("Coq"::_::l) -> l 
	| l             -> l
    in  List.iter (fun x -> print_string x; print_string ".") ls;*)
      print_string (string_of_kn sp)

  in
     box_display csr; print_flush()
(*
let _ =
  Vernacentries.add "PrintConstr"
    (function
       | [VARG_CONSTR c] -> 
	   (fun () ->
              let (evmap,sign) = Command.get_current_context () in
  	      constr_display (Constrintern.interp_constr evmap sign c))
       | _ -> bad_vernac_args "PrintConstr")

let _ =
  Vernacentries.add "PrintPureConstr"
    (function
       | [VARG_CONSTR c] -> 
	   (fun () ->
              let (evmap,sign) = Command.get_current_context () in
  	      print_pure_constr (Constrintern.interp_constr evmap sign c))
       | _ -> bad_vernac_args "PrintPureConstr")
*)

let ppfconstr c = ppterm (Closure.term_of_fconstr c)
