(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Closure
open Util
open Names
open Nameops
open Term
open Termops
open Sign
open Evd
open Environ
open Evarutil
open Proof_type
open Tacred
open Typing
open Libnames
open Nametab

(*
let is_bind = function
  | Tacexpr.Cbindings _ -> true
  | _ -> false
*)

(* Functions on goals *)

let mk_goal hyps cl = 
  { evar_hyps = hyps; evar_concl = cl; 
    evar_body = Evar_empty}

(* Functions on proof trees *)

let ref_of_proof pf =
  match pf.ref with
    | None -> failwith "rule_of_proof"
    | Some r -> r

let rule_of_proof pf =
  let (r,_) = ref_of_proof pf in r

let children_of_proof pf = 
  let (_,cl) = ref_of_proof pf in cl
				    
let goal_of_proof pf = pf.goal

let subproof_of_proof pf = match pf.ref with
  | Some (Tactic (_,pf), _) -> pf
  | _ -> failwith "subproof_of_proof"

let status_of_proof pf = pf.open_subgoals

let is_complete_proof pf = pf.open_subgoals = 0

let is_leaf_proof pf = (pf.ref = None)

let is_tactic_proof pf = match pf.ref with
  | Some (Tactic _, _) -> true
  | _ -> false


(*******************************************************************)
(*            Constraints for existential variables                *)
(*******************************************************************)

(* A readable constraint is a global constraint plus a focus set
   of existential variables and a signature. *)

(* Functions on readable constraints *)
			     
let mt_evcty gc = 
  { it = empty_named_context; sigma = gc }

let rc_of_gc evds gl = 
  { it = gl.evar_hyps; sigma = evds }

let rc_add evc (k,v) = 
  { it  = evc.it;
    sigma = Evd.add evc.sigma k v }

let get_hyps  evc = evc.it
let get_env   evc = Global.env_of_context evc.it
let get_gc    evc = evc.sigma

let pf_lookup_name_as_renamed env ccl s =
  Detyping.lookup_name_as_renamed env ccl s

let pf_lookup_index_as_renamed env ccl n =
  Detyping.lookup_index_as_renamed env ccl n

(*********************************************************************)
(*                  Pretty printing functions                        *)
(*********************************************************************)

open Pp
open Printer

(* Il faudrait parametrer toutes les pr_term, term_env, etc. par la
  strategie de renommage choisie pour Termast (en particulier, il
  faudrait pouvoir etre sur que lookup_as_renamed qui est utilisé par
  Intros Until fonctionne exactement comme on affiche le but avec
  term_env *)

let pf_lookup_name_as_renamed hyps ccl s =
  Detyping.lookup_name_as_renamed hyps ccl s

let pf_lookup_index_as_renamed ccl n =
  Detyping.lookup_index_as_renamed ccl n

let pr_idl idl = prlist_with_sep pr_spc pr_id idl

let pr_goal g =
  let env = evar_env g in
  let penv = pr_context_of env in
  let pc = prterm_env_at_top env g.evar_concl in
  str"  " ++ hv 0 (penv ++ fnl () ++
		   str (emacs_str (String.make 1 (Char.chr 253)))  ++
                   str "============================" ++ fnl ()  ++
                   str" "  ++ pc) ++ fnl ()

let pr_concl n g =
  let env = evar_env g in
  let pc = prterm_env_at_top env g.evar_concl in
  str (emacs_str (String.make 1 (Char.chr 253)))  ++
  str "subgoal " ++ int n ++ str " is:" ++ cut () ++ str" "  ++ pc

(* print the subgoals but write Subtree proved! even in case some existential 
   variables remain unsolved, pr_subgoals_existential is a safer version 
   of pr_subgoals *)

let pr_subgoals = function
  | [] -> (str"Proof completed." ++ fnl ())
  | [g] ->
      let pg = pr_goal g in v 0 (str ("1 "^"subgoal") ++cut () ++ pg)
  | g1::rest ->
      let rec pr_rec n = function
        | [] -> (mt ())
        | g::rest ->
            let pg = pr_concl n g in
            let prest = pr_rec (n+1) rest in
            (cut () ++ pg ++ prest) 
      in
      let pg1 = pr_goal g1 in
      let pgr = pr_rec 2 rest in
      v 0 (int(List.length rest+1) ++ str" subgoals" ++ cut () ++ pg1 ++ pgr)

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

let pr_seq evd = 
  let env = evar_env evd
  and cl = evd.evar_concl
  in
  let pdcl = pr_named_context_of env in
  let pcl = prterm_env_at_top env cl in
  hov 0 (pdcl  ++ spc ()  ++ hov 0 (str"|- "  ++ pcl))

let prgl gl =
  let pgl = pr_seq gl in
  (str"["  ++ pgl  ++ str"]"  ++ spc ())

let pr_evgl gl =
  let phyps = pr_idl (List.rev (ids_of_named_context gl.evar_hyps)) in
  let pc = prterm gl.evar_concl in
  hov 0 (str"["  ++ phyps ++ spc () ++ str"|- "  ++ pc ++ str"]")

let pr_evgl_sign gl = 
  let ps = pr_named_context_of (evar_env gl) in
  let pc = prterm gl.evar_concl in
  hov 0 (str"["  ++ ps ++ spc () ++ str"|- "  ++ pc ++ str"]")

(*  evd.evgoal.lc seems to be printed twice *)
let pr_decl evd =
  let pevgl = pr_evgl evd in
  let pb =
    match evd.evar_body with
      | Evar_empty -> (fnl ())
      | Evar_defined c -> let pc = prterm c in (str" => "  ++ pc ++  fnl ())
  in
  h 0 (pevgl ++ pb)

let pr_evd evd = 
  prlist_with_sep pr_fnl
    (fun (ev,evd) ->
       let pe = pr_decl evd in 
       h 0 (str (string_of_existential ev)  ++ str"=="  ++ pe))
    (Evd.to_list evd)
    
let pr_decls decls = pr_evd decls
		       
let pr_evc evc =
  let pe = pr_evd evc.sigma in
  (pe)

let pr_evars = 
  prlist_with_sep pr_fnl
    (fun (ev,evd) ->
       let pegl = pr_evgl_sign evd in 
       (str (string_of_existential ev) ++ str " : " ++ pegl))

(* Print an enumerated list of existential variables *)
let rec pr_evars_int i = function
  | [] -> (mt ())
  | (ev,evd)::rest ->
      let pegl = pr_evgl_sign evd in 
      let pei = pr_evars_int (i+1) rest in
      (hov 0 (str "Existential " ++ int i ++ str " =" ++ spc () ++
              str (string_of_existential ev)  ++ str " : " ++ pegl)) ++ 
      fnl () ++ pei

(* Equivalent to pr_subgoals but start from the prooftree and 
   check for uninstantiated existential variables *)

let pr_subgoals_existential sigma = function 
  | [] -> 
      let exl = Evd.non_instantiated sigma in 
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
