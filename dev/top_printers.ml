
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
open Clenv

let pP s = pP (hOV 0 s)

let prast c = pP(print_ast c)

let prastpat c = pP(print_astpat c)
let prastpatl c = pP(print_astlpat c)
let ppterm0 = (fun x -> pP(term0 (gLOB nil_sign) x))
let pprawterm = (fun x -> pP(prrawterm x))
let pppattern = (fun x -> pP(prpattern x))
let pptype = (fun x -> pP(prtype x))

let prid id = pP [< 'sTR(string_of_id id) >]

let prconst (sp,j) =
    pP [< 'sTR"#"; 'sTR(string_of_path sp); 
	  'sTR"="; term0 (gLOB nil_sign) j.uj_val >]

let prvar ((id,a)) =
    pP [< 'sTR"#" ; 'sTR(string_of_id id) ; 'sTR":" ; 
	  term0 (gLOB nil_sign) a >]

let genprj f j = [< (f (gLOB nil_sign)j.uj_val); 
                 'sTR " : ";
               (f (gLOB nil_sign)j.uj_type);
                  'sTR " : ";
               (f  (gLOB nil_sign)j.uj_kind)>]

let prj j = pP (genprj term0 j)


let prsp sp = pP[< 'sTR(string_of_path sp) >]

let prgoal g = pP(prgl g)

let prsigmagoal g = pP(prgl (sig_it g))

let prgls gls = pP(pr_gls gls)

let prglls glls = pP(pr_glls glls)

let prctxt ctxt = pP(pr_ctxt ctxt)

let pproof p = pP(print_proof Evd.empty nil_sign p)

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

