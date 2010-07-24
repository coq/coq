(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
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
open Evd
open Proof_type
open Decl_mode
open Refiner
open Pfedit
open Ppconstr
open Constrextern
open Tacexpr

let emacs_str s alts =
  match !Flags.print_emacs, !Flags.print_emacs_safechar with
    | true, true -> alts
    | true , false -> s
    | false,_ -> ""

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

let pr_open_lconstr_env env (_,c) = pr_lconstr_env env c
let pr_open_constr_env env (_,c) = pr_constr_env env c

  (* NB do not remove the eta-redexes! Global.env() has side-effects... *)
let pr_lconstr t = pr_lconstr_env (Global.env()) t
let pr_constr t = pr_constr_env (Global.env()) t

let pr_open_lconstr (_,c) = pr_lconstr c
let pr_open_constr (_,c) = pr_constr c

let pr_constr_under_binders_env_gen pr env (ids,c) =
  (* Warning: clashes can occur with variables of same name in env but *)
  (* we also need to preserve the actual names of the patterns *)
  (* So what to do? *)
  let assums = List.map (fun id -> (Name id,(* dummy *) mkProp)) ids in
  pr (push_rels_assum assums env) c

let pr_constr_under_binders_env = pr_constr_under_binders_env_gen pr_constr_env
let pr_lconstr_under_binders_env = pr_constr_under_binders_env_gen pr_lconstr_env

let pr_constr_under_binders c = pr_constr_under_binders_env (Global.env()) c
let pr_lconstr_under_binders c = pr_lconstr_under_binders_env (Global.env()) c

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

let pr_lconstr_pattern_env env c =
  pr_lconstr_pattern_expr (extern_constr_pattern (names_of_rel_context env) c)
let pr_constr_pattern_env env c =
  pr_constr_pattern_expr (extern_constr_pattern (names_of_rel_context env) c)

let pr_lconstr_pattern t =
  pr_lconstr_pattern_expr (extern_constr_pattern empty_names_context t)
let pr_constr_pattern t =
  pr_constr_pattern_expr (extern_constr_pattern empty_names_context t)

let pr_sort s = pr_rawsort (extern_sort s)

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
  pr_global (Tacred.global_of_evaluable_reference ref)

(*let pr_rawterm t =
  pr_lconstr (Constrextern.extern_rawconstr Idset.empty t)*)

(*open Pattern

let pr_pattern t = pr_pattern_env (Global.env()) empty_names_context t*)

(**********************************************************************)
(* Contexts and declarations                                          *)

let pr_var_decl env (id,c,typ) =
  let pbody = match c with
    | None ->  (mt ())
    | Some c ->
	(* Force evaluation *)
	let pb = pr_lconstr_env env c in
	let pb = if isCast c then surround pb else pb in
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
	let pb = if isCast c then surround pb else pb in
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
  let make_decl_list env d pps = pr_var_decl env d :: pps in
  let psl = List.rev (fold_named_context make_decl_list env ~init:[]) in
  hv 0 (prlist_with_sep (fun _ -> ws 2) (fun x -> x) psl)

let pr_named_context env ne_context =
  hv 0 (Sign.fold_named_context
	  (fun d pps -> pps ++ ws 2 ++ pr_var_decl env d)
          ne_context ~init:(mt ()))

let pr_rel_context env rel_context =
  pr_binders (extern_rel_context None env rel_context)

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
		      str (emacs_str (String.make 1 (Char.chr 253)) "") ++
		      pidt)))
        env ~init:(0,(mt ()))
    in
    let db_env =
      fold_rel_context
        (fun env d pps ->
           let pnat = pr_rel_decl env d in
	   (pps ++ fnl () ++
	      str (emacs_str (String.make 1 (Char.chr 253)) "") ++
	      pnat))
        env ~init:(mt ())
    in
    (sign_env ++ db_env)

let pr_context_of env = match Flags.print_hyps_limit () with
  | None -> hv 0 (pr_context_unlimited env)
  | Some n -> hv 0 (pr_context_limit n env)

(* display goal parts (Proof mode) *)

let pr_restricted_named_context among env =
  hv 0 (fold_named_context
	  (fun env ((id,_,_) as d) pps ->
	     if true || Idset.mem id among then
	       pps ++
		 fnl () ++ str (emacs_str (String.make 1 (Char.chr 253)) "") ++
		 pr_var_decl env d
	     else
	       pps)
          env ~init:(mt ()))


let pr_predicate pr_elt (b, elts) =
  let pr_elts = prlist_with_sep spc pr_elt elts in
    if b then
      str"all" ++
	(if elts = [] then mt () else str" except: " ++ pr_elts)
    else
      if elts = [] then str"none" else pr_elts

let pr_cpred p = pr_predicate pr_con (Cpred.elements p)
let pr_idpred p = pr_predicate Nameops.pr_id (Idpred.elements p)

let pr_transparent_state (ids, csts) =
  hv 0 (str"VARIABLES: " ++ pr_idpred ids ++ fnl () ++
	str"CONSTANTS: " ++ pr_cpred csts ++ fnl ())

let pr_subgoal_metas metas env=
  let pr_one (meta,typ) =
    str "?" ++ int meta ++ str " : " ++
      hov 0 (pr_ltype_env_at_top env typ) ++ fnl () ++
      str (emacs_str (String.make 1 (Char.chr 253)) "") in
    hv 0 (prlist_with_sep mt pr_one metas)

(* display complete goal *)
let default_pr_goal g =
  let env = evar_unfiltered_env g in
  let preamb,thesis,penv,pc =
    if g.evar_extra = None then
          mt (), mt (),
	  pr_context_of env,
	  pr_ltype_env_at_top env g.evar_concl
    else
      (str "     *** Declarative Mode ***" ++ fnl ()++fnl ()),
      (str "thesis := "  ++ fnl ()),
       pr_context_of env,
       pr_ltype_env_at_top env g.evar_concl
  in
    preamb ++
    str"  " ++ hv 0 (penv ++ fnl () ++
		       str (emacs_str (String.make 1 (Char.chr 253)) "")  ++
		       str "============================" ++ fnl ()  ++
		       thesis ++ str " " ++  pc) ++ fnl ()

(* display the conclusion of a goal *)
let pr_concl n g =
  let env = evar_env g in
  let pc = pr_ltype_env_at_top env g.evar_concl in
    str (emacs_str (String.make 1 (Char.chr 253)) "")  ++
      str "subgoal " ++ int n ++ str " is:" ++ cut () ++ str" "  ++ pc

(* display evar type: a context and a type *)
let pr_evgl_sign gl =
  let ps = pr_named_context_of (evar_unfiltered_env gl) in
  let _,l = list_filter2 (fun b c -> not b) (evar_filter gl,evar_context gl) in
  let ids = List.rev (List.map pi1 l) in
  let warn =
    if ids = [] then mt () else
      (str "(" ++ prlist_with_sep pr_comma pr_id ids ++ str " cannot be used)")
  in
  let pc = pr_lconstr gl.evar_concl in
  hov 0 (str"[" ++ ps ++ spc () ++ str"|- "  ++ pc ++ str"]" ++ spc () ++ warn)

(* Print an enumerated list of existential variables *)
let rec pr_evars_int i = function
  | [] -> (mt ())
  | (ev,evd)::rest ->
      let pegl = pr_evgl_sign evd in
      let pei = pr_evars_int (i+1) rest in
      (hov 0 (str "Existential " ++ int i ++ str " =" ++ spc () ++
              str (string_of_existential ev)  ++ str " : " ++ pegl)) ++
      fnl () ++ pei

let default_pr_subgoal n =
  let rec prrec p = function
    | [] -> error "No such goal."
    | g::rest ->
       	if p = 1 then
          let pg = default_pr_goal g in
          v 0 (str "subgoal " ++ int n ++ str " is:" ++ cut () ++ pg)
       	else
	  prrec (p-1) rest
  in
  prrec n

(* Print open subgoals. Checks for uninstantiated existential variables *)
let default_pr_subgoals close_cmd sigma = function
  | [] ->
      begin
	match close_cmd with
	  Some cmd ->
	    (str "Subproof completed, now type " ++ str cmd ++
	       str "." ++ fnl ())
	| None ->
	    let exl = Evarutil.non_instantiated sigma in
	      if exl = [] then
		(str"Proof completed." ++ fnl ())
	      else
		let pei = pr_evars_int 1 exl in
		  (str "No more subgoals but non-instantiated existential " ++
		     str "variables:" ++ fnl () ++ (hov 0 pei))
      end
  | [g] ->
      let pg = default_pr_goal g in
      v 0 (str ("1 "^"subgoal") ++cut () ++ pg)
  | g1::rest ->
      let rec pr_rec n = function
        | [] -> (mt ())
        | g::rest ->
            let pc = pr_concl n g in
            let prest = pr_rec (n+1) rest in
            (cut () ++ pc ++ prest)
      in
      let pg1 = default_pr_goal g1 in
      let prest = pr_rec 2 rest in
      v 0 (int(List.length rest+1) ++ str" subgoals" ++ cut ()
	   ++ pg1 ++ prest ++ fnl ())


(**********************************************************************)
(* Abstraction layer                                                  *)


type printer_pr = {
 pr_subgoals            : string option -> evar_map -> goal list -> std_ppcmds;
 pr_subgoal             : int -> goal list -> std_ppcmds;
 pr_goal                : goal -> std_ppcmds;
}

let default_printer_pr = {
 pr_subgoals = default_pr_subgoals;
 pr_subgoal  = default_pr_subgoal;
 pr_goal     = default_pr_goal;
}

let printer_pr = ref default_printer_pr

let set_printer_pr = (:=) printer_pr

let pr_subgoals x = !printer_pr.pr_subgoals x
let pr_subgoal  x = !printer_pr.pr_subgoal  x
let pr_goal     x = !printer_pr.pr_goal     x

(* End abstraction layer                                              *)
(**********************************************************************)

let pr_open_subgoals () =
  let pfts = get_pftreestate () in
  let gls = fst (frontier (proof_of_pftreestate pfts)) in
  match focus() with
    | 0 ->
        let sigma = (top_goal_of_pftreestate pfts).sigma in
        let close_cmd = Decl_mode.get_end_command pfts in
        pr_subgoals close_cmd sigma gls
    | n ->
	assert (n > List.length gls);
	if List.length gls < 2 then
	  pr_subgoal n gls
	else
	  (* LEM TODO: this way of saying how many subgoals has to be abstracted out*)
	  v 0 (int(List.length gls) ++ str" subgoals" ++ cut () ++
	  pr_subgoal n gls)

let pr_nth_open_subgoal n =
  let pf = proof_of_pftreestate (get_pftreestate ()) in
  pr_subgoal n (fst (frontier pf))

(* Elementary tactics *)

let pr_prim_rule = function
  | Intro id ->
      str"intro " ++ pr_id id

  | Cut (b,replace,id,t) ->
     if b then
       (* TODO: express "replace" *)
       (str"assert " ++ str"(" ++ pr_id id ++ str":" ++ pr_lconstr t ++ str")")
     else
       let cl = if replace then str"clear " ++ pr_id id ++ str"; " else mt() in
       (str"cut " ++ pr_constr t ++
        str ";[" ++ cl ++ str"intro " ++ pr_id id ++ str"|idtac]")

  | FixRule (f,n,[],_) ->
      (str"fix " ++ pr_id f ++ str"/" ++ int n)

  | FixRule (f,n,others,j) ->
      if j<>0 then warning "Unsupported printing of \"fix\"";
      let rec print_mut = function
	| (f,n,ar)::oth ->
           pr_id f ++ str"/" ++ int n ++ str" : " ++ pr_lconstr ar ++ print_mut oth
        | [] -> mt () in
      (str"fix " ++ pr_id f ++ str"/" ++ int n ++
         str" with " ++ print_mut others)

  | Cofix (f,[],_) ->
      (str"cofix " ++ pr_id f)

  | Cofix (f,others,j) ->
      if j<>0 then warning "Unsupported printing of \"fix\"";
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
	 str"move "  ++ pr_id id1 ++ pr_move_location pr_id id2)

  | Order ord ->
      (str"order "  ++ prlist_with_sep pr_spc pr_id ord)

  | Rename (id1,id2) ->
      (str "rename " ++ pr_id id1 ++ str " into " ++ pr_id id2)

  | Change_evars ->
      (* This is internal tactic and cannot be replayed at user-level.
         Function pr_rule_dot below is used when we want to hide
         Change_evars *)
      str "Evar change"


(* Backwards compatibility *)

let prterm = pr_lconstr


(* spiwack: printer function for sets of Environ.assumption.
            It is used primarily by the Print Assumption command. *)
let pr_assumptionset env s =
  if (Environ.ContextObjectMap.is_empty s) then
    str "Closed under the global context"
  else
    let (vars,axioms,opaque) =
      Environ.ContextObjectMap.fold (fun t typ r ->
	let (v,a,o) = r in
	match t with
	| Variable id -> (  Some (
	                      Option.default (fnl ()) v
			   ++ str (string_of_id id)
			   ++ str " : "
	                   ++ pr_ltype typ
	                   ++ fnl ()
			    )
	                 ,
	                   a, o)
	| Axiom kn    -> ( v ,
			     Some (
			      Option.default (fnl ()) a
			   ++ (pr_constant env kn)
	                   ++ str " : "
	                   ++ pr_ltype typ
	                   ++ fnl ()
			     )
			 , o
			 )
	| Opaque kn    -> ( v , a ,
			     Some (
			      Option.default (fnl ()) o
			   ++ (pr_constant env kn)
	                   ++ str " : "
	                   ++ pr_ltype typ
	                   ++ fnl ()
			     )
			 )
      )
	s (None,None,None)
    in
    let (vars,axioms,opaque) =
      ( Option.map (fun p -> str "Section Variables:" ++ p) vars ,
	Option.map (fun p -> str "Axioms:" ++ p) axioms ,
	Option.map (fun p -> str "Opaque constants:" ++ p) opaque
      )
    in
    (Option.default (mt ()) vars) ++ (Option.default (mt ()) axioms)
      ++ (Option.default (mt ()) opaque)

let cmap_to_list m = Cmap.fold (fun k v acc -> v :: acc) m []

open Typeclasses

let pr_instance i = 
  pr_global (instance_impl i)
    
let pr_instance_gmap insts =
  prlist_with_sep fnl (fun (gr, insts) ->
    prlist_with_sep fnl pr_instance (cmap_to_list insts))
    (Gmap.to_list insts)
