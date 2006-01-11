(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Sign
open Environ
open Global
open Declare
open Libnames
open Nametab
open Ppconstr
open Evd
open Proof_type
open Refiner
open Pfedit
open Ppconstr
open Constrextern

let emacs_str s = if !Options.print_emacs then s else "" 

(**********************************************************************)
(** Terms                                                             *)

  (* [at_top] means ids of env must be avoided in bound variables *)
let pr_constr_core at_top env t =
  pr_constr_expr (extern_constr at_top env t)
let pr_lconstr_core at_top env t =
  pr_lconstr_expr (extern_constr at_top env t)

let pr_lconstr_env_at_top env = pr_lconstr_core true env
let pr_lconstr_env env = pr_lconstr_core false env
let pr_constr_env env = pr_constr_core false env

  (* NB do not remove the eta-redexes! Global.env() has side-effects... *)
let pr_lconstr t = pr_lconstr_env (Global.env()) t
let pr_constr t = pr_constr_env (Global.env()) t

let pr_type_core at_top env t =
  pr_constr_expr (extern_type at_top env t)
let pr_ltype_core at_top env t =
  pr_lconstr_expr (extern_type at_top env t)

let pr_ltype_env_at_top env = pr_ltype_core true env
let pr_ltype_env env = pr_ltype_core false env
let pr_type_env env = pr_type_core false env

let pr_ltype t = pr_ltype_env (Global.env()) t
let pr_type t = pr_type_env (Global.env()) t

let pr_ljudge_env env j =
  (pr_lconstr_env env j.uj_val, pr_lconstr_env env j.uj_type)

let pr_ljudge j = pr_ljudge_env (Global.env()) j

let pr_lrawconstr_env env c =
  pr_lconstr_expr (extern_rawconstr (vars_of_env env) c)
let pr_rawconstr_env env c = 
  pr_constr_expr (extern_rawconstr (vars_of_env env) c)

let pr_lrawconstr c =
  pr_lconstr_expr (extern_rawconstr Idset.empty c)
let pr_rawconstr c =
  pr_constr_expr (extern_rawconstr Idset.empty c)

let pr_cases_pattern t =
  pr_cases_pattern_expr (extern_cases_pattern Idset.empty t)

let pr_constr_pattern_env env c =
  pr_constr_expr (extern_constr_pattern (names_of_rel_context env) c)
let pr_constr_pattern t =
  pr_constr_expr (extern_constr_pattern empty_names_context t)

let _ = Termops.set_print_constr pr_lconstr_env

(**********************************************************************)
(* Global references *)

let pr_global_env = pr_global_env
let pr_global = pr_global_env Idset.empty

let pr_constant env cst = pr_global_env (vars_of_env env) (ConstRef cst)
let pr_existential env ev = pr_lconstr_env env (mkEvar ev)
let pr_inductive env ind = pr_lconstr_env env (mkInd ind)
let pr_constructor env cstr = pr_lconstr_env env (mkConstruct cstr)

let pr_evaluable_reference ref =
 let ref' = match ref with
  | EvalConstRef const -> ConstRef const
  | EvalVarRef sp -> VarRef sp in
 pr_global ref'

(**********************************************************************)
(* Contexts and declarations                                          *)

let pr_var_decl env (id,c,typ) =
  let pbody = match c with
    | None ->  (mt ())
    | Some c ->
	(* Force evaluation *) 
	let pb = pr_lconstr_env env c in
	(str" := " ++ pb ++ cut () ) in
  let pt = pr_ltype_env env typ in
  let ptyp = (str" : " ++ pt) in
  (pr_id id ++ hov 0 (pbody ++ ptyp))

let pr_rel_decl env (na,c,typ) =
  let pbody = match c with
    | None -> mt ()
    | Some c ->
	(* Force evaluation *) 
	let pb = pr_lconstr_env env c in
	(str":=" ++ spc () ++ pb ++ spc ()) in
  let ptyp = pr_ltype_env env typ in
  match na with
  | Anonymous -> hov 0 (str"<>" ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)
  | Name id -> hov 0 (pr_id id ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)


(* Prints out an "env" in a nice format.  We print out the
 * signature,then a horizontal bar, then the debruijn environment.
 * It's printed out from outermost to innermost, so it's readable. *)

(* Prints a signature, all declarations on the same line if possible *)
let pr_named_context_of env =
  hv 0 (fold_named_context
	  (fun env d pps -> pps ++ ws 2 ++ pr_var_decl env d)
          env ~init:(mt ()))

let pr_named_context env ne_context = 
  hv 0 (Sign.fold_named_context
	  (fun d pps -> pps ++ ws 2 ++ pr_var_decl env d)
          ne_context ~init:(mt ()))

let pr_rel_context env rel_context =
  let rec prec env = function
    | [] -> (mt ()) 
    | [b] -> str "(" ++ pr_rel_decl env b ++ str")"
    | b::rest ->
        let pb = pr_rel_decl env b in
        let penvtl = prec (push_rel b env) rest in
        str "(" ++ pb ++ str")" ++ spc () ++ penvtl
  in 
  hov 0 (prec env (List.rev rel_context))

let pr_rel_context_of env =
  pr_rel_context env (rel_context env)

(* Prints an env (variables and de Bruijn). Separator: newline *)
let pr_context_unlimited env =
  let sign_env =
    fold_named_context
      (fun env d pps ->
         let pidt =  pr_var_decl env d in (pps ++ fnl () ++ pidt))
      env ~init:(mt ()) 
  in
  let db_env =
    fold_rel_context
      (fun env d pps ->
         let pnat = pr_rel_decl env d in (pps ++ fnl () ++ pnat))
      env ~init:(mt ())
  in 
  (sign_env ++ db_env)

let pr_ne_context_of header env =
  if Environ.rel_context env = empty_rel_context &
    Environ.named_context env = empty_named_context  then (mt ())
  else let penv = pr_context_unlimited env in (header ++ penv ++ fnl ())

let pr_context_limit n env =
  let named_context = Environ.named_context env in
  let lgsign = List.length named_context in
  if n >= lgsign then 
    pr_context_unlimited env
  else
    let k = lgsign-n in
    let _,sign_env =
      fold_named_context
        (fun env d (i,pps) ->
           if i < k then 
	     (i+1, (pps ++str "."))
	   else
             let pidt = pr_var_decl env d in
	     (i+1, (pps ++ fnl () ++
		      str (emacs_str (String.make 1 (Char.chr 253))) ++
		      pidt)))
        env ~init:(0,(mt ())) 
    in
    let db_env =
      fold_rel_context
        (fun env d pps ->
           let pnat = pr_rel_decl env d in
	   (pps ++ fnl () ++
	      str (emacs_str (String.make 1 (Char.chr 253))) ++
	      pnat))
        env ~init:(mt ())
    in 
    (sign_env ++ db_env)

let pr_context_of env = match Options.print_hyps_limit () with 
  | None -> hv 0 (pr_context_unlimited env)
  | Some n -> hv 0 (pr_context_limit n env)


(* display complete goal *)
let pr_goal g =
  let env = evar_env g in
  let penv = pr_context_of env in
  let pc = pr_ltype_env_at_top env g.evar_concl in
  str"  " ++ hv 0 (penv ++ fnl () ++
		   str (emacs_str (String.make 1 (Char.chr 253)))  ++
                   str "============================" ++ fnl ()  ++
                   str" "  ++ pc) ++ fnl ()

(* display the conclusion of a goal *)
let pr_concl n g =
  let env = evar_env g in
  let pc = pr_ltype_env_at_top env g.evar_concl in
  str (emacs_str (String.make 1 (Char.chr 253)))  ++
  str "subgoal " ++ int n ++ str " is:" ++ cut () ++ str" "  ++ pc

(* display evar type: a context and a type *)
let pr_evgl_sign gl = 
  let ps = pr_named_context_of (evar_env gl) in
  let pc = pr_lconstr gl.evar_concl in
  hov 0 (str"["  ++ ps ++ spc () ++ str"|- "  ++ pc ++ str"]")

(* Print an enumerated list of existential variables *)
let rec pr_evars_int i = function
  | [] -> (mt ())
  | (ev,evd)::rest ->
      let pegl = pr_evgl_sign evd in 
      let pei = pr_evars_int (i+1) rest in
      (hov 0 (str "Existential " ++ int i ++ str " =" ++ spc () ++
              str (string_of_existential ev)  ++ str " : " ++ pegl)) ++ 
      fnl () ++ pei

let pr_subgoal n =
  let rec prrec p = function
    | [] -> error "No such goal"
    | g::rest ->
       	if p = 1 then
          let pg = pr_goal g in
          v 0 (str "subgoal " ++ int n ++ str " is:" ++ cut () ++ pg)
       	else 
	  prrec (p-1) rest
  in 
  prrec n

(* Print open subgoals. Checks for uninstantiated existential variables *)
let pr_subgoals sigma = function 
  | [] -> 
      let exl = Evarutil.non_instantiated sigma in 
      if exl = [] then 
	(str"Proof completed."  ++ fnl ())
      else
        let pei = pr_evars_int 1 exl in
        (str "No more subgoals but non-instantiated existential " ++
           str "variables :"  ++fnl () ++ (hov 0 pei))
  | [g] ->
      let pg = pr_goal g in
      v 0 (str ("1 "^"subgoal") ++cut () ++ pg)
  | g1::rest ->
      let rec pr_rec n = function
        | [] -> (mt ())
        | g::rest ->
            let pc = pr_concl n g in
            let prest = pr_rec (n+1) rest in
            (cut () ++ pc ++ prest) 
      in
      let pg1 = pr_goal g1 in
      let prest = pr_rec 2 rest in
      v 0 (int(List.length rest+1) ++ str" subgoals" ++ cut () 
	   ++ pg1 ++ prest ++ fnl ())


let pr_subgoals_of_pfts pfts = 
  let gls = fst (Refiner.frontier (proof_of_pftreestate pfts)) in 
  let sigma = (top_goal_of_pftreestate pfts).sigma in
  pr_subgoals sigma gls

let pr_open_subgoals () =
  let pfts = get_pftreestate () in
  match focus() with
    | 0 -> 
	pr_subgoals_of_pfts pfts
    | n -> 
	let pf = proof_of_pftreestate pfts in
	let gls = fst (frontier pf) in 
	assert (n > List.length gls);
	if List.length gls < 2 then 
	  pr_subgoal n gls
	else 
	  v 0 (int(List.length gls) ++ str" subgoals" ++ cut () ++
	  pr_subgoal n gls)

let pr_nth_open_subgoal n =
  let pf = proof_of_pftreestate (get_pftreestate ()) in
  pr_subgoal n (fst (frontier pf))

(* Elementary tactics *)

let pr_prim_rule = function
  | Intro id -> 
      str"intro " ++ pr_id id
	
  | Intro_replacing id -> 
      (str"intro replacing "  ++ pr_id id)
	
  | Cut (b,id,t) ->
      if b then
        (str"assert " ++ pr_constr t)
      else
        (str"cut " ++ pr_constr t ++ str ";[intro " ++ pr_id id ++ str "|idtac]")
	
  | FixRule (f,n,[]) ->
      (str"fix " ++ pr_id f ++ str"/" ++ int n)
      
  | FixRule (f,n,others) -> 
      let rec print_mut = function
	| (f,n,ar)::oth -> 
           pr_id f ++ str"/" ++ int n ++ str" : " ++ pr_lconstr ar ++ print_mut oth
        | [] -> mt () in
      (str"fix " ++ pr_id f ++ str"/" ++ int n ++
         str" with " ++ print_mut others)

  | Cofix (f,[]) ->
      (str"cofix " ++ pr_id f)

  | Cofix (f,others) ->
      let rec print_mut = function
	| (f,ar)::oth ->
	  (pr_id f ++ str" : " ++ pr_lconstr ar ++ print_mut oth)
        | [] -> mt () in
      (str"cofix " ++ pr_id f ++  str" with " ++ print_mut others)

  | Refine c -> 
      str(if occur_meta c then "refine " else "exact ") ++
      Constrextern.with_meta_as_hole pr_constr c
      
  | Convert_concl (c,_) ->
      (str"change "  ++ pr_constr c)
      
  | Convert_hyp (id,None,t) ->
      (str"change "  ++ pr_constr t  ++ spc ()  ++ str"in "  ++ pr_id id)

  | Convert_hyp (id,Some c,t) ->
      (str"change "  ++ pr_constr c  ++ spc ()  ++ str"in "
       ++ pr_id id ++ str" (type of "  ++ pr_id id ++ str ")")
      
  | Thin ids ->
      (str"clear "  ++ prlist_with_sep pr_spc pr_id ids)
      
  | ThinBody ids ->
      (str"clearbody "  ++ prlist_with_sep pr_spc pr_id ids)
      
  | Move (withdep,id1,id2) ->
      (str (if withdep then "dependent " else "") ++
	 str"move "  ++ pr_id id1 ++ str " after " ++ pr_id id2)

  | Rename (id1,id2) ->
      (str "rename " ++ pr_id id1 ++ str " into " ++ pr_id id2)
