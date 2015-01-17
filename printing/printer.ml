(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Term
open Vars
open Environ
open Globnames
open Nametab
open Evd
open Proof_type
open Refiner
open Pfedit
open Constrextern
open Ppconstr
open Declarations

let emacs_str s =
  if !Flags.print_emacs then s else ""
let delayed_emacs_cmd s =
  if !Flags.print_emacs then s () else str ""

let get_current_context () =
  try Pfedit.get_current_goal_context ()
  with e when Logic.catchable_exception e ->
    (Evd.empty, Global.env())

(**********************************************************************)
(** Terms                                                             *)

(* [goal_concl_style] means that all names of goal/section variables
   and all names of rel variables (if any) in the given env and all short
   names of global definitions of the current module must be avoided while
   printing bound variables.
   Otherwise, short names of global definitions are printed qualified
   and only names of goal/section variables and rel names that do
   _not_ occur in the scope of the binder to be printed are avoided. *)

let pr_constr_core goal_concl_style env sigma t =
  pr_constr_expr (extern_constr goal_concl_style env sigma t)
let pr_lconstr_core goal_concl_style env sigma t =
  pr_lconstr_expr (extern_constr goal_concl_style env sigma t)

let pr_lconstr_env env = pr_lconstr_core false env
let pr_constr_env env = pr_constr_core false env
let _ = Hook.set Proofview.Refine.pr_constr pr_constr_env

let pr_lconstr_goal_style_env env = pr_lconstr_core true env
let pr_constr_goal_style_env env = pr_constr_core true env

let pr_open_lconstr_env env sigma (_,c) = pr_lconstr_env env sigma c
let pr_open_constr_env env sigma (_,c) = pr_constr_env env sigma c

  (* NB do not remove the eta-redexes! Global.env() has side-effects... *)
let pr_lconstr t =
  let (sigma, env) = get_current_context () in
  pr_lconstr_env env sigma t
let pr_constr t =
  let (sigma, env) = get_current_context () in
  pr_constr_env env sigma t

let pr_open_lconstr (_,c) = pr_lconstr c
let pr_open_constr (_,c) = pr_constr c

let pr_constr_under_binders_env_gen pr env sigma (ids,c) =
  (* Warning: clashes can occur with variables of same name in env but *)
  (* we also need to preserve the actual names of the patterns *)
  (* So what to do? *)
  let assums = List.map (fun id -> (Name id,(* dummy *) mkProp)) ids in
  pr (Termops.push_rels_assum assums env) sigma c

let pr_constr_under_binders_env = pr_constr_under_binders_env_gen pr_constr_env
let pr_lconstr_under_binders_env = pr_constr_under_binders_env_gen pr_lconstr_env

let pr_constr_under_binders c =
  let (sigma, env) = get_current_context () in
  pr_constr_under_binders_env env sigma c
let pr_lconstr_under_binders c =
  let (sigma, env) = get_current_context () in
  pr_lconstr_under_binders_env env sigma c

let pr_type_core goal_concl_style env sigma t =
  pr_constr_expr (extern_type goal_concl_style env sigma t)
let pr_ltype_core goal_concl_style env sigma t =
  pr_lconstr_expr (extern_type goal_concl_style env sigma t)

let pr_goal_concl_style_env env = pr_ltype_core true env
let pr_ltype_env env = pr_ltype_core false env
let pr_type_env env = pr_type_core false env

let pr_ltype t =
    let (sigma, env) = get_current_context () in
    pr_ltype_env env sigma t
let pr_type t =
    let (sigma, env) = get_current_context () in
    pr_type_env env sigma t

let pr_ljudge_env env sigma j =
  (pr_lconstr_env env sigma j.uj_val, pr_lconstr_env env sigma j.uj_type)

let pr_ljudge j =
  let (sigma, env) = get_current_context () in
  pr_ljudge_env env sigma j

let pr_lglob_constr_env env c =
  pr_lconstr_expr (extern_glob_constr (Termops.vars_of_env env) c)
let pr_glob_constr_env env c =
  pr_constr_expr (extern_glob_constr (Termops.vars_of_env env) c)

let pr_lglob_constr c =
  let (sigma, env) = get_current_context () in
  pr_lglob_constr_env env c
let pr_glob_constr c =
  let (sigma, env) = get_current_context () in
  pr_glob_constr_env env c

let pr_closed_glob_env env sigma c =
  pr_constr_expr (extern_closed_glob false env sigma c)
let pr_closed_glob c =
  let (sigma, env) = get_current_context () in
  pr_closed_glob_env env sigma c

let pr_lconstr_pattern_env env sigma c =
  pr_lconstr_pattern_expr (extern_constr_pattern (Termops.names_of_rel_context env) sigma c)
let pr_constr_pattern_env env sigma c =
  pr_constr_pattern_expr (extern_constr_pattern (Termops.names_of_rel_context env) sigma c)

let pr_cases_pattern t =
  pr_cases_pattern_expr (extern_cases_pattern Names.Id.Set.empty t)

let pr_lconstr_pattern t =
  let (sigma, env) = get_current_context () in
  pr_lconstr_pattern_env env sigma t
let pr_constr_pattern t =
  let (sigma, env) = get_current_context () in
  pr_constr_pattern_env env sigma t

let pr_sort sigma s = pr_glob_sort (extern_sort sigma s)

let _ = Termops.set_print_constr 
  (fun env t -> pr_lconstr_expr (extern_constr ~lax:true false env Evd.empty t))

let pr_in_comment pr x = str "(* " ++ pr x ++ str " *)"

(** Term printers resilient to [Nametab] errors *)

(** When the nametab isn't up-to-date, the term printers above
    could raise [Not_found] during [Nametab.shortest_qualid_of_global].
    In this case, we build here a fully-qualified name based upon
    the kernel modpath and label of constants, and the idents in
    the [mutual_inductive_body] for the inductives and constructors
    (needs an environment for this). *)

let id_of_global env = function
  | ConstRef kn -> Label.to_id (Constant.label kn)
  | IndRef (kn,0) -> Label.to_id (MutInd.label kn)
  | IndRef (kn,i) ->
    (Environ.lookup_mind kn env).mind_packets.(i).mind_typename
  | ConstructRef ((kn,i),j) ->
    (Environ.lookup_mind kn env).mind_packets.(i).mind_consnames.(j-1)
  | VarRef v -> v

let rec dirpath_of_mp = function
  | MPfile sl -> sl
  | MPbound uid -> DirPath.make [MBId.to_id uid]
  | MPdot (mp,l) ->
    Libnames.add_dirpath_suffix (dirpath_of_mp mp) (Label.to_id l)

let dirpath_of_global = function
  | ConstRef kn -> dirpath_of_mp (Constant.modpath kn)
  | IndRef (kn,_) | ConstructRef ((kn,_),_) ->
    dirpath_of_mp (MutInd.modpath kn)
  | VarRef _ -> DirPath.empty

let qualid_of_global env r =
  Libnames.make_qualid (dirpath_of_global r) (id_of_global env r)

let safe_gen f env sigma c =
  let orig_extern_ref = Constrextern.get_extern_reference () in
  let extern_ref loc vars r =
    try orig_extern_ref loc vars r
    with e when Errors.noncritical e ->
      Libnames.Qualid (loc, qualid_of_global env r)
  in
  Constrextern.set_extern_reference extern_ref;
  try
    let p = f env sigma c in
    Constrextern.set_extern_reference orig_extern_ref;
    p
  with e when Errors.noncritical e ->
    Constrextern.set_extern_reference orig_extern_ref;
    str "??"

let safe_pr_lconstr_env = safe_gen pr_lconstr_env
let safe_pr_constr_env = safe_gen pr_constr_env
let safe_pr_lconstr t =
  let (sigma, env) = get_current_context () in
  safe_pr_lconstr_env env sigma t

let safe_pr_constr t =
  let (sigma, env) = get_current_context () in
  safe_pr_constr_env env sigma t

let pr_universe_ctx c =
  if !Detyping.print_universes && not (Univ.UContext.is_empty c) then
    fnl()++pr_in_comment (fun c -> v 0 
      (Univ.pr_universe_context Universes.pr_with_global_universes c)) c
  else
    mt()

(**********************************************************************)
(* Global references *)

let pr_global_env = pr_global_env
let pr_global = pr_global_env Id.Set.empty

let pr_puniverses f env (c,u) =
  f env c ++ 
  (if !Constrextern.print_universes then
    str"(*" ++ Univ.Instance.pr Universes.pr_with_global_universes u ++ str"*)"
   else mt ())

let pr_constant env cst = pr_global_env (Termops.vars_of_env env) (ConstRef cst)
let pr_existential_key = Evd.pr_existential_key
let pr_existential env sigma ev = pr_lconstr_env env sigma (mkEvar ev)
let pr_inductive env ind = pr_lconstr_env env Evd.empty (mkInd ind)
let pr_constructor env cstr = pr_lconstr_env env Evd.empty (mkConstruct cstr)

let pr_pconstant = pr_puniverses pr_constant
let pr_pinductive = pr_puniverses pr_inductive
let pr_pconstructor = pr_puniverses pr_constructor

let pr_evaluable_reference ref =
  pr_global (Tacred.global_of_evaluable_reference ref)

(*let pr_glob_constr t =
  pr_lconstr (Constrextern.extern_glob_constr Id.Set.empty t)*)

(*open Pattern

let pr_pattern t = pr_pattern_env (Global.env()) empty_names_context t*)

(**********************************************************************)
(* Contexts and declarations                                          *)

let pr_var_decl_skel pr_id env sigma (id,c,typ) =
  let pbody = match c with
    | None ->  (mt ())
    | Some c ->
	(* Force evaluation *)
	let pb = pr_lconstr_env env sigma c in
	let pb = if isCast c then surround pb else pb in
	(str" := " ++ pb ++ cut () ) in
  let pt = pr_ltype_env env sigma typ in
  let ptyp = (str" : " ++ pt) in
  (pr_id id ++ hov 0 (pbody ++ ptyp))

let pr_var_decl env sigma (id,c,typ) =
  pr_var_decl_skel pr_id env sigma (id,c,typ)

let pr_var_list_decl env sigma (l,c,typ) =
  hov 0 (pr_var_decl_skel (fun ids -> prlist_with_sep pr_comma pr_id ids) env sigma (l,c,typ))

let pr_rel_decl env sigma (na,c,typ) =
  let pbody = match c with
    | None -> mt ()
    | Some c ->
	(* Force evaluation *)
	let pb = pr_lconstr_env env sigma c in
	let pb = if isCast c then surround pb else pb in
	(str":=" ++ spc () ++ pb ++ spc ()) in
  let ptyp = pr_ltype_env env sigma typ in
  match na with
  | Anonymous -> hov 0 (str"<>" ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)
  | Name id -> hov 0 (pr_id id ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)


(* Prints out an "env" in a nice format.  We print out the
 * signature,then a horizontal bar, then the debruijn environment.
 * It's printed out from outermost to innermost, so it's readable. *)

(* Prints a signature, all declarations on the same line if possible *)
let pr_named_context_of env sigma =
  let make_decl_list env d pps = pr_var_decl env sigma d :: pps in
  let psl = List.rev (fold_named_context make_decl_list env ~init:[]) in
  hv 0 (prlist_with_sep (fun _ -> ws 2) (fun x -> x) psl)

let pr_named_context env sigma ne_context =
  hv 0 (Context.fold_named_context
	  (fun d pps -> pps ++ ws 2 ++ pr_var_decl env sigma d)
          ne_context ~init:(mt ()))

let pr_rel_context env sigma rel_context =
  pr_binders (extern_rel_context None env sigma rel_context)

let pr_rel_context_of env sigma =
  pr_rel_context env sigma (rel_context env)

(* Prints an env (variables and de Bruijn). Separator: newline *)
let pr_context_unlimited env sigma =
  let sign_env =
    Context.fold_named_list_context
      (fun d pps ->
         let pidt =  pr_var_list_decl env sigma d in
         (pps ++ fnl () ++ pidt))
      (Termops.compact_named_context (named_context env)) ~init:(mt ())
  in
  let db_env =
    fold_rel_context
      (fun env d pps ->
         let pnat = pr_rel_decl env sigma d in (pps ++ fnl () ++ pnat))
      env ~init:(mt ())
  in
  (sign_env ++ db_env)

let pr_ne_context_of header env sigma =
  if List.is_empty (Environ.rel_context env) &&
    List.is_empty (Environ.named_context env)  then (mt ())
  else let penv = pr_context_unlimited env sigma in (header ++ penv ++ fnl ())

let pr_context_limit n env sigma =
  let named_context = Environ.named_context env in
  let lgsign = List.length named_context in
  if n >= lgsign then
    pr_context_unlimited env sigma
  else
    let k = lgsign-n in
    let _,sign_env =
      Context.fold_named_list_context
        (fun d (i,pps) ->
           if i < k then
	     (i+1, (pps ++str "."))
	   else
             let pidt = pr_var_list_decl env sigma d in
	     (i+1, (pps ++ fnl () ++
		      str (emacs_str "") ++
		      pidt)))
        (Termops.compact_named_context (Environ.named_context env)) ~init:(0,(mt ()))
    in
    let db_env =
      fold_rel_context
        (fun env d pps ->
           let pnat = pr_rel_decl env sigma d in
	   (pps ++ fnl () ++
	      str (emacs_str "") ++
	      pnat))
        env ~init:(mt ())
    in
    (sign_env ++ db_env)

let pr_context_of env sigma = match Flags.print_hyps_limit () with
  | None -> hv 0 (pr_context_unlimited env sigma)
  | Some n -> hv 0 (pr_context_limit n env sigma)

(* display goal parts (Proof mode) *)

let pr_predicate pr_elt (b, elts) =
  let pr_elts = prlist_with_sep spc pr_elt elts in
    if b then
      str"all" ++
	(if List.is_empty elts then mt () else str" except: " ++ pr_elts)
    else
      if List.is_empty elts then str"none" else pr_elts

let pr_cpred p = pr_predicate (pr_constant (Global.env())) (Cpred.elements p)
let pr_idpred p = pr_predicate Nameops.pr_id (Id.Pred.elements p)

let pr_transparent_state (ids, csts) =
  hv 0 (str"VARIABLES: " ++ pr_idpred ids ++ fnl () ++
	str"CONSTANTS: " ++ pr_cpred csts ++ fnl ())

(* display complete goal *)
let default_pr_goal gs =
  let (g,sigma) = Goal.V82.nf_evar (project gs) (sig_it gs) in
  let env = Goal.V82.env sigma g in
  let preamb,thesis,penv,pc =
    mt (), mt (),
    pr_context_of env sigma,
    pr_goal_concl_style_env env sigma (Goal.V82.concl sigma g)
  in
    preamb ++
    str"  " ++ hv 0 (penv ++ fnl () ++
		       str (emacs_str "")  ++
		       str "============================" ++ fnl ()  ++
		       thesis ++ str " " ++  pc)

(* display a goal tag *)
let pr_goal_tag g =
  let s = " (ID " ^ Goal.uid g ^ ")" in
  str (emacs_str s)

let display_name = false

(* display a goal name *)
let pr_goal_name sigma g =
  if display_name then str " " ++ Pp.surround (pr_id (Evd.evar_ident g sigma))
  else mt ()

(* display the conclusion of a goal *)
let pr_concl n sigma g =
  let (g,sigma) = Goal.V82.nf_evar sigma g in
  let env = Goal.V82.env sigma g in
  let pc = pr_goal_concl_style_env env sigma (Goal.V82.concl sigma g) in
    str (emacs_str "")  ++
      str "subgoal " ++ int n ++ pr_goal_tag g ++ pr_goal_name sigma g ++
      str " is:" ++ cut () ++ str" "  ++ pc

(* display evar type: a context and a type *)
let pr_evgl_sign sigma evi =
  let env = evar_env evi in
  let ps = pr_named_context_of env sigma in
  let _, l = match Filter.repr (evar_filter evi) with
  | None -> [], []
  | Some f -> List.filter2 (fun b c -> not b) f (evar_context evi)
  in
  let ids = List.rev_map pi1 l in
  let warn =
    if List.is_empty ids then mt () else
      (str "(" ++ prlist_with_sep pr_comma pr_id ids ++ str " cannot be used)")
  in
  let pc = pr_lconstr_env env sigma evi.evar_concl in
  hov 0 (str"[" ++ ps ++ spc () ++ str"|- "  ++ pc ++ str"]" ++ spc () ++ warn)

(* Print an existential variable *)

let pr_evar sigma (evk, evi) =
  let pegl = pr_evgl_sign sigma evi in
  hov 0 (pr_existential_key sigma evk ++ str " : " ++ pegl)

(* Print an enumerated list of existential variables *)
let rec pr_evars_int_hd head sigma i = function
  | [] -> mt ()
  | (evk,evi)::rest ->
      (hov 0 (head i ++ pr_evar sigma (evk,evi))) ++
      (match rest with [] -> mt () | _ -> fnl () ++ pr_evars_int_hd head sigma (i+1) rest)

let pr_evars_int sigma i evs = pr_evars_int_hd (fun i -> str "Existential " ++ int i ++ str " =" ++ spc ()) sigma i (Evar.Map.bindings evs)

let pr_evars sigma evs = pr_evars_int_hd (fun i -> mt ()) sigma 1 (Evar.Map.bindings evs)

let default_pr_subgoal n sigma =
  let rec prrec p = function
    | [] -> error "No such goal."
    | g::rest ->
	if Int.equal p 1 then
          let pg = default_pr_goal { sigma=sigma ; it=g; } in
          v 0 (str "subgoal " ++ int n ++ pr_goal_tag g ++ pr_goal_name sigma g 
	       ++ str " is:" ++ cut () ++ pg)
	else
	  prrec (p-1) rest
  in
  prrec n

let pr_internal_existential_key ev = str (string_of_existential ev)

let emacs_print_dependent_evars sigma seeds =
  let evars () =
    let evars = Evarutil.gather_dependent_evars sigma seeds in
    let evars =
      Evar.Map.fold begin fun e i s ->
	let e' = pr_internal_existential_key e in
	match i with
	| None -> s ++ str" " ++ e' ++ str " open,"
	| Some i ->
	  s ++ str " " ++ e' ++ str " using " ++
	    Evar.Set.fold begin fun d s ->
	      pr_internal_existential_key d ++ str " " ++ s
	    end i (str ",")
      end evars (str "")
    in
    fnl () ++
    str "(dependent evars:" ++ evars ++ str ")" ++ fnl ()
  in
  delayed_emacs_cmd evars

(* Print open subgoals. Checks for uninstantiated existential variables *)
(* spiwack: [seeds] is for printing dependent evars in emacs mode. *)
(* spiwack: [pr_first] is true when the first goal must be singled out
   and printed in its entirety. *)
(* courtieu: in emacs mode, even less cases where the first goal is printed
   in its entirety *)
let default_pr_subgoals ?(pr_first=true) close_cmd sigma seeds shelf stack goals =
  (** Printing functions for the extra informations. *)
  let rec print_stack a = function
    | [] -> Pp.int a
    | b::l -> Pp.int a ++ str"-" ++ print_stack b l
  in
  let print_unfocused l =
    match l with
    | [] -> None
    | a::l -> Some (str"unfocused: " ++ print_stack a l)
  in
  let print_shelf l =
    match l with
    | [] -> None
    | _ -> Some (str"shelved: " ++ Pp.int (List.length l))
  in
  let rec print_comma_separated_list a l =
    match l with
    | [] -> a
    | b::l -> print_comma_separated_list (a++str", "++b) l
  in
  let print_extra_list l =
    match l with
    | [] -> Pp.mt ()
    | a::l -> Pp.spc () ++ str"(" ++ print_comma_separated_list a l ++ str")"
  in
  let extra = Option.List.flatten [ print_unfocused stack ; print_shelf shelf ] in
  let print_extra = print_extra_list extra in
  let focused_if_needed =
    let needed = not (CList.is_empty extra) && pr_first in
    if needed then str" focused "
    else str" " (* non-breakable space *)
  in
  (** Main function *)
  let rec pr_rec n = function
    | [] -> (mt ())
    | g::rest ->
        let pc = pr_concl n sigma g in
        let prest = pr_rec (n+1) rest in
        (cut () ++ pc ++ prest)
  in
  let print_multiple_goals g l =
    if pr_first then
      default_pr_goal { it = g ; sigma = sigma; } ++ fnl () ++
      pr_rec 2 l
    else 
      pr_rec 1 (g::l)
  in
  match goals with
  | [] ->
      begin
	match close_cmd with
	  Some cmd ->
	    (str "Subproof completed, now type " ++ str cmd ++
	       str ".")
	| None ->
	    let exl = Evarutil.non_instantiated sigma in
	    if Evar.Map.is_empty exl then
	      (str"No more subgoals."
	       ++ emacs_print_dependent_evars sigma seeds)
	    else
	      let pei = pr_evars_int sigma 1 exl in
	      (str "No more subgoals but non-instantiated existential " ++
		 str "variables:" ++ fnl () ++ (hov 0 pei)
	       ++ emacs_print_dependent_evars sigma seeds ++ fnl () ++
                 str "You can use Grab Existential Variables.")
      end
  | [g] when not !Flags.print_emacs ->
      let pg = default_pr_goal { it = g ; sigma = sigma; } in
      v 0 (
	str "1" ++ focused_if_needed ++ str"subgoal" ++ print_extra
        ++ pr_goal_tag g ++ pr_goal_name sigma g ++ cut () ++ pg
	++ emacs_print_dependent_evars sigma seeds
      )
  | g1::rest ->
      let goals = print_multiple_goals g1 rest in
      v 0 (
	int(List.length rest+1) ++ focused_if_needed ++ str"subgoals" ++
          print_extra ++
          str ((if display_name then (fun x -> x) else emacs_str) ", subgoal 1")
        ++ pr_goal_tag g1
        ++ pr_goal_name sigma g1 ++ cut ()
	++ goals
	++ emacs_print_dependent_evars sigma seeds
      )

(**********************************************************************)
(* Abstraction layer                                                  *)


type printer_pr = {
 pr_subgoals            : ?pr_first:bool -> string option -> evar_map -> evar list -> Goal.goal list -> int list -> goal list -> std_ppcmds;
 pr_subgoal             : int -> evar_map -> goal list -> std_ppcmds;
 pr_goal                : goal sigma -> std_ppcmds;
}

let default_printer_pr = {
 pr_subgoals = default_pr_subgoals;
 pr_subgoal  = default_pr_subgoal;
 pr_goal     = default_pr_goal;
}

let printer_pr = ref default_printer_pr

let set_printer_pr = (:=) printer_pr

let pr_subgoals ?pr_first x = !printer_pr.pr_subgoals ?pr_first x
let pr_subgoal  x = !printer_pr.pr_subgoal  x
let pr_goal     x = !printer_pr.pr_goal     x

(* End abstraction layer                                              *)
(**********************************************************************)

let pr_open_subgoals ?(proof=Proof_global.give_me_the_proof ()) () =
  (* spiwack: it shouldn't be the job of the printer to look up stuff
     in the [evar_map], I did stuff that way because it was more
     straightforward, but seriously, [Proof.proof] should return
     [evar_info]-s instead. *)
  let p = proof in
  let (goals , stack , shelf, given_up, sigma ) = Proof.proof p in
  let stack = List.map (fun (l,r) -> List.length l + List.length r) stack in
  let seeds = Proof.V82.top_evars p in
  begin match goals with
  | [] -> let { Evd.it = bgoals ; sigma = bsigma } = Proof.V82.background_subgoals p in
          begin match bgoals,shelf,given_up with
	  | [] , [] , [] -> pr_subgoals None sigma seeds shelf stack goals
          | [] , [] , _ ->
	     msg_info (str "No more goals, however there are goals you gave up. You need to go back and solve them.");
	     fnl ()
            ++ pr_subgoals ~pr_first:false None bsigma seeds [] [] given_up
          | [] , _ , _ ->
	    msg_info (str "All the remaining goals are on the shelf.");
	    fnl ()
            ++ pr_subgoals ~pr_first:false None bsigma seeds [] [] shelf
	  | _ , _, _ ->
	    msg_info (str "This subproof is complete, but there are still unfocused goals." ++
			(match Proof_global.Bullet.suggest p
			 with None  -> str"" | Some s -> fnl () ++ str s));
	    fnl () ++ pr_subgoals ~pr_first:false None bsigma seeds shelf [] bgoals
	  end
  | _ -> pr_subgoals None sigma seeds shelf stack goals
  end

let pr_nth_open_subgoal n =
  let pf = get_pftreestate () in
  let { it=gls ; sigma=sigma } = Proof.V82.subgoals pf in
  pr_subgoal n sigma gls

let pr_goal_by_id id =
  let p = Proof_global.give_me_the_proof () in
  let g = Goal.get_by_uid id in
  let pr gs =
    v 0 (str ("goal / evar " ^ id ^ " is:") ++ cut ()
	 ++ pr_goal gs)
  in
  try
    Proof.in_proof p (fun sigma -> pr {it=g;sigma=sigma;})
  with Not_found -> error "Invalid goal identifier."

(* Elementary tactics *)

let pr_prim_rule = function
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
      if not (Int.equal j 0) then msg_warning (strbrk "Unsupported printing of \"fix\"");
      let rec print_mut = function
	| (f,n,ar)::oth ->
           pr_id f ++ str"/" ++ int n ++ str" : " ++ pr_lconstr ar ++ print_mut oth
        | [] -> mt () in
      (str"fix " ++ pr_id f ++ str"/" ++ int n ++
         str" with " ++ print_mut others)

  | Cofix (f,[],_) ->
      (str"cofix " ++ pr_id f)

  | Cofix (f,others,j) ->
      if not (Int.equal j 0) then msg_warning (strbrk "Unsupported printing of \"fix\"");
      let rec print_mut = function
	| (f,ar)::oth ->
	  (pr_id f ++ str" : " ++ pr_lconstr ar ++ print_mut oth)
        | [] -> mt () in
      (str"cofix " ++ pr_id f ++  str" with " ++ print_mut others)
  | Refine c ->
      str(if Termops.occur_meta c then "refine " else "exact ") ++
      Constrextern.with_meta_as_hole pr_constr c

  | Thin ids ->
      (str"clear "  ++ pr_sequence pr_id ids)

  | Move (id1,id2) ->
      (str"move "  ++ pr_id id1 ++ Miscprint.pr_move_location pr_id id2)

(* Backwards compatibility *)

let prterm = pr_lconstr


(* Printer function for sets of Assumptions.assumptions.
   It is used primarily by the Print Assumptions command. *)

open Assumptions

let pr_assumptionset env s =
  if ContextObjectMap.is_empty s then
    str "Closed under the global context"
  else
    let safe_pr_constant env kn =
      try pr_constant env kn
      with Not_found ->
	let mp,_,lab = repr_con kn in
	str (string_of_mp mp ^ "." ^ Label.to_string lab)
    in
    let safe_pr_ltype typ =
      try str " : " ++ pr_ltype typ
      with e when Errors.noncritical e -> mt ()
    in
    let fold t typ accu =
      let (v, a, o, tr) = accu in
      match t with
      | Variable id ->
        let var = str (Id.to_string id) ++ str " : " ++ pr_ltype typ in
        (var :: v, a, o, tr)
      | Axiom kn ->
        let ax = safe_pr_constant env kn ++ safe_pr_ltype typ in
        (v, ax :: a, o, tr)
      | Opaque kn ->
        let opq = safe_pr_constant env kn ++ safe_pr_ltype typ in
        (v, a, opq :: o, tr)
      | Transparent kn ->
        let tran = safe_pr_constant env kn ++ safe_pr_ltype typ in
        (v, a, o, tran :: tr)
    in
    let (vars, axioms, opaque, trans) = 
      ContextObjectMap.fold fold s ([], [], [], [])
    in
    let opt_list title = function
    | [] -> None
    | l ->
      let section =
        title ++ fnl () ++
        v 0 (prlist_with_sep fnl (fun s -> s) l) in
      Some section
    in
    let assums = [
      opt_list (str "Transparent constants:") trans;
      opt_list (str "Section Variables:") vars;
      opt_list (str "Axioms:") axioms;
      opt_list (str "Opaque constants:") opaque;
    ] in
    prlist_with_sep fnl (fun x -> x) (Option.List.flatten assums)

let xor a b = 
  (a && not b) || (not a && b)

let pr_polymorphic b = 
  let print = xor (Flags.is_universe_polymorphism ()) b in
  if print then
    if b then str"Polymorphic " else str"Monomorphic "
  else mt ()

