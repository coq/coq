
(* Printers for the ocaml toplevel. *)

open System
open Pp
open Ast
open Names
open Sign
open Univ
open Proof_trees
open Environ
open Generic
open Printer
open Refiner
open Tacmach
open Term
open Vernacinterp
open Clenv

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

let pproof p = pP(print_proof Evd.empty empty_var_context p)

let prevd evd = pP(pr_decls evd)

let prevc evc = pP(pr_evc evc)

let prwc wc = pP(pr_evc wc)

let prclenv clenv = pP(pr_clenv clenv)

let p_uni u = 
    [< 'sTR(string_of_path u.u_sp) ;
       'sTR "." ;
      'iNT u.u_num >]

let print_uni u = (pP (p_uni u))

let pp_universes u = pP [< 'sTR"[" ; pr_universes u ; 'sTR"]" >]

let constr_display csr =
  let rec term_display = function
    | DOP0 a -> "DOP0("^(oper_display a)^")"
    | DOP1(a,b) -> "DOP1("^(oper_display a)^","^(term_display b)^")"
    | DOP2(a,b,c) ->
        "DOP2("^(oper_display a)^","^(term_display b)^","^(term_display c)^")"
    | DOPN(a,b) ->
        "DOPN("^(oper_display a)^",[|"^(Array.fold_right (fun x i ->
        (term_display x)^(if not(i="") then (";"^i) else "")) b "")^"|])"
    | DOPL(a,b) ->
        "DOPL("^(oper_display a)^",[|"^(List.fold_right (fun x i ->
        (term_display x)^(if not(i="") then (";"^i) else "")) b "")^"|]"
    | DLAM(a,b) -> "DLAM("^(name_display a)^","^(term_display b)^")"
    | DLAMV(a,b) ->
        "DLAMV("^(name_display a)^",[|"^(Array.fold_right (fun x i ->
        (term_display x)^(if not(i="") then (";"^i) else "")) b "")^"|]"
    | VAR a -> "VAR "^(string_of_id a)
    | Rel a -> "Rel "^(string_of_int a)
  and oper_display = function
    | Meta a -> "?"^(string_of_int a)
    | Sort a -> "Sort("^(sort_display a)^")"
    | Cast -> "Cast"
    | Prod -> "Prod"
    | Lambda -> "Lambda"
    | AppL -> "AppL"
    | Const sp -> "Const("^(string_of_path sp)^")"
    | Abst sp -> "Abst("^(string_of_path sp)^")"
    | MutInd(sp,i) -> "MutInd("^(string_of_path sp)^","^(string_of_int i)^")"
    | MutConstruct((sp,i),j) ->
        "MutConstruct(("^(string_of_path sp)^","^(string_of_int i)^"),"^
        (string_of_int j)^")"
    | MutCase _ -> "MutCase(<abs>)"
    | Evar i -> "Evar("^(string_of_int i)^")"
    | Fix(t,i) ->
        "Fix([|"^(Array.fold_right (fun x i -> (string_of_int x)^(if not(i="")
        then (";"^i) else "")) t "")^"|],"^(string_of_int i)^")"
    | CoFix i -> "CoFix "^(string_of_int i)
    | XTRA s -> "XTRA("^s^")"
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
