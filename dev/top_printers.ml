
(* Printers for the ocaml toplevel. *)

open System
open Pp
open Ast
open Names
open Sign
open Univ
open Proof_trees
open Environ
(* open Generic *)
open Printer
open Refiner
open Tacmach
open Term
open Vernacinterp
open Clenv

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

let constr_display csr =
  let rec term_display c = match kind_of_term c with
  | IsRel n -> "Rel("^(string_of_int n)^")"
  | IsMeta n -> "Meta("^(string_of_int n)^")"
  | IsVar id -> "Var("^(string_of_id id)^")"
  | IsSort s -> "Sort("^(sort_display s)^")"
  | IsXtra s -> "Xtra("^s^")"
  | IsCast (c,t) -> "Cast("^(term_display c)^","^(term_display t)^")"
  | IsProd (na,t,c) ->
      "Prod("^(name_display na)^","^(term_display t)^","^(term_display c)^")"
  | IsLambda (na,t,c) ->
      "Lambda("^(name_display na)^","^(term_display t)^","^(term_display c)^")"
  | IsLetIn (na,b,t,c) ->
      "LetIn("^(name_display na)^","^(term_display b)^","
      ^(term_display t)^","^(term_display c)^")"
  | IsApp (c,l) -> "App("^(term_display c)^","^(array_display l)^")"
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
  | IsFix ((t,i),(tl,lna,bl)) ->
      "Fix(([|"^(Array.fold_right (fun x i -> (string_of_int x)^(if not(i="")
        then (";"^i) else "")) t "")^"|],"^(string_of_int i)^"),"
      ^(array_display tl)^","
      ^(List.fold_right (fun x i -> (name_display x)^(if not(i="")
        then (";"^i) else "")) lna "")^","
      ^(array_display bl)^")"
  | IsCoFix(i,(tl,lna,bl)) ->
      "CoFix("^(string_of_int i)^"),"
      ^(array_display tl)^","
      ^(List.fold_right (fun x i -> (name_display x)^(if not(i="")
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
    | Type _ -> "Type"

  and name_display = function
    | Name id -> "Name("^(string_of_id id)^")"
    | Anonymous -> "Anonymous"

  in
    mSG [<'sTR (term_display csr);'fNL>]

let _ =
  Vernacentries.add "PrintConstr"
    (function
       | [VARG_CONSTR c] -> 
	   (fun () ->
              let (evmap,sign) = Command.get_current_context () in
  	      constr_display (Astterm.interp_constr evmap sign c))
       | _ -> bad_vernac_args "PrintConstr")
