(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

let status_of_proof pf = pf.status

let is_complete_proof pf = pf.status = Complete_proof

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
  faudrait pouvoir etre sur que lookup_as_renamed qui est utilis� par
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
  | [] -> (str"Subtree proved!" ++ fnl ())
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
  let phyps = pr_idl (ids_of_named_context gl.evar_hyps) in
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
       h 0 (pr_id (id_of_existential ev)  ++ str"=="  ++ pe))
    (Evd.to_list evd)
    
let pr_decls decls = pr_evd decls
		       
let pr_evc evc =
  let pe = pr_evd evc.sigma in
  (pe)

let pr_evars = 
  prlist_with_sep pr_fnl
    (fun (ev,evd) ->
       let pegl = pr_evgl_sign evd in 
       (pr_id (id_of_existential ev) ++ str " : " ++ pegl))

(* Print an enumerated list of existential variables *)
let rec pr_evars_int i = function
  | [] -> (mt ())
  | (ev,evd)::rest ->
      let pegl = pr_evgl_sign evd in 
      let pei = pr_evars_int (i+1) rest in
      (hov 0 (str "Existential " ++ int i ++ str " =" ++ spc () ++
              pr_id (id_of_existential ev)  ++ str " : " ++ pegl)) ++ 
      fnl () ++ pei

let pr_subgoals_existential sigma = function 
  | [] -> 
      let exl = Evd.non_instantiated sigma in 
      if exl = [] then 
	(str"Subtree proved!"  ++ fnl ())
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

(*
open Ast
open Termast
open Tacexpr
open Rawterm

let ast_of_cvt_bind f = function
  | (NoDepBinding n,c) -> ope ("BINDING", [(num n); ope ("CONSTR",[(f c)])])
  | (DepBinding  id,c) -> ope ("BINDING", [nvar id; ope  ("CONSTR",[(f c)])]) 
  | (AnonymousBinding,c) -> ope ("BINDING", [ope ("CONSTR",[(f c)])])

let rec ast_of_cvt_intro_pattern = function
  | WildPat   -> ope ("WILDCAR",[])
  | IdPat id  -> nvar id
(*  | DisjPat l -> ope ("DISJPATTERN",  (List.map ast_of_cvt_intro_pattern l))*)
  | ConjPat l -> ope ("CONJPATTERN",  (List.map ast_of_cvt_intro_pattern l))
*)
(*
(* Gives the ast list corresponding to a reduction flag *)
open RedFlags

let last_of_cvt_flags red =
  (if (red_set red fBETA) then [ope("Beta",[])]
   else [])@
  (let (n_unf,lconst) = red_get_const red in
   let lqid =
     List.map
       (function
	  | EvalVarRef id -> nvar id
	  | EvalConstRef kn ->
	      ast_of_qualid
                (shortest_qualid_of_global None (ConstRef kn)))
       lconst in
   if lqid = [] then []
   else if n_unf then [ope("Delta",[]);ope("UnfBut",lqid)]
   else [ope("Delta",[]);ope("Unf",lqid)])@
  (if (red_set red fIOTA) then [ope("Iota",[])]
   else [])
*)
(*
(* Gives the ast corresponding to a reduction expression *)
open Rawterm

let ast_of_cvt_redexp = function
  | Red _ -> ope ("Red",[])
  | Hnf -> ope("Hnf",[])
  | Simpl -> ope("Simpl",[])
(*
  | Cbv flg -> ope("Cbv",last_of_cvt_flags flg)
  | Lazy flg -> ope("Lazy",last_of_cvt_flags flg)
*)
  | Unfold l ->
    ope("Unfold",List.map (fun (locc,sp) -> ope("UNFOLD",
      [match sp with
	| EvalVarRef id -> nvar id
	| EvalConstRef kn -> 					
	    ast_of_qualid
	      (shortest_qualid_of_global None (ConstRef kn))]
      @(List.map num locc))) l)
  | Fold l ->
    ope("Fold",List.map (fun c -> ope ("CONSTR",
      [ast_of_constr false (Global.env ()) c])) l)
  | Pattern l ->
    ope("Pattern",List.map (fun (locc,csr) -> ope("PATTERN",
      [ope ("CONSTR",[ast_of_constr false (Global.env ()) csr])]@
      (List.map num locc))) l)
*)
(* Gives the ast corresponding to a tactic argument *)
(*
let ast_of_cvt_arg = function
  | Identifier id   -> nvar id
(*
  | Qualid qid      -> ast_of_qualid qid
*)
  | Quoted_string s -> string s
  | Integer n       -> num n 
(*  | Command c       -> ope ("CONSTR",[c])*)
  | Constr  c       -> 
    ope ("CONSTR",[ast_of_constr false (Global.env ()) c])
  | OpenConstr  (_,c)       -> 
    ope ("CONSTR",[ast_of_constr false (Global.env ()) c])
  | Constr_context _ ->
    anomalylabstrm "ast_of_cvt_arg" (str
      "Constr_context argument could not be used")
  | Clause idl      -> 
      let transl = function
	| InHyp id -> ope ("INHYP", [nvar id])
	| InHypType id -> ope ("INHYPTYPE", [nvar id]) in
      ope ("CLAUSE", List.map transl idl)
(*
  | Bindings bl     -> ope ("BINDINGS", 
			    List.map (ast_of_cvt_bind (fun x -> x)) bl)
  | Cbindings bl    -> 
      ope ("BINDINGS", 
	   List.map 
	     (ast_of_cvt_bind
		(ast_of_constr false (Global.env ()))) bl)
*)
(* TODO
  | Tacexp ast      -> ope ("TACTIC",[ast])
  | Tac (tac,ast) -> ast
*)
  | Redexp red -> ope("REDEXP",[ast_of_cvt_redexp red])
  | Fixexp (id,n,c) -> ope ("FIXEXP",[nvar id; num n; ope ("CONSTR",[ast_of_constr false (Global.env ()) c])])
  | Cofixexp (id,c) -> ope ("COFIXEXP",[nvar id; ope ("CONSTR",[ast_of_constr false (Global.env ()) c])])
(*  | Intropattern p ->  ast_of_cvt_intro_pattern p*)
  | Letpatterns (gl_occ_opt,hyp_occ_list) ->
     let hyps_pats =
       List.map
	 (fun (id,l) ->
	    ope ("HYPPATTERN", nvar id :: (List.map num l)))
	 hyp_occ_list in
     let all_pats =
       match gl_occ_opt with
	 | None -> hyps_pats
	 | Some l -> hyps_pats @ [ope ("CCLPATTERN", List.map num l)] in
     ope ("LETPATTERNS", all_pats)
*)
