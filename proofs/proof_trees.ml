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
open Term
open Sign
open Evd
open Stamps
open Environ
open Evarutil
open Proof_type
open Tacred
open Typing

let is_bind = function
  | Bindings _ -> true
  | _ -> false

let lc_toList lc = Intset.elements lc

(* Functions on goals *)

let mk_goal ctxt hyps cl = 
  { evar_hyps = hyps; evar_concl = cl; 
    evar_body = Evar_empty; evar_info = Some ctxt }

(* Functions on the information associated with existential variables  *)

let mt_ctxt lc = { pgm = None; lc = lc }

let get_ctxt gl = out_some gl.evar_info

let get_pgm gl = (out_some gl.evar_info).pgm

let set_pgm pgm ctxt = { ctxt with pgm = pgm }

let get_lc gl = (out_some gl.evar_info).lc

let set_lc lc ctxt = { ctxt with lc = lc }

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

let subproof_of_proof pf =
  match pf.subproof with
    | None -> failwith "subproof_of_proof"
    | Some pf -> pf

let status_of_proof pf = pf.status

let is_complete_proof pf = pf.status = Complete_proof

let is_leaf_proof pf = (pf.ref = None)

let is_tactic_proof pf = (pf.subproof <> None)


(*******************************************************************)
(*            Constraints for existential variables                *)
(*******************************************************************)

(* A local constraint is just a set of section_paths *)

(* recall : type local_constraints = Intset.t *)

(* A global constraint is a mappings of existential variables
   with some extra information for the program and mimick
   tactics. *)

type global_constraints  = enamed_declarations timestamped

(* A readable constraint is a global constraint plus a focus set
   of existential variables and a signature. *)

type evar_recordty = {
  focus : local_constraints;
  hyps  : named_context;
  decls : enamed_declarations }

and readable_constraints = evar_recordty timestamped

(* Functions on readable constraints *)
			     
let mt_evcty lc gc = 
  ts_mk { focus = lc; hyps = empty_named_context; decls = gc }

let evc_of_evds evds gl = 
  ts_mk { focus = (get_lc gl); hyps = gl.evar_hyps; decls = evds }

let rc_of_gc gc gl = evc_of_evds (ts_it gc) gl
		       
let rc_add evc (k,v) = 
  ts_mod
    (fun evc -> { focus = (Intset.add k evc.focus);
                  hyps  = evc.hyps;
                  decls = Evd.add evc.decls k v })
    evc

let get_hyps  evc = (ts_it evc).hyps
let get_env   evc = Global.env_of_context (ts_it evc).hyps
let get_focus evc = (ts_it evc).focus
let get_decls evc = (ts_it evc).decls
let get_gc    evc = (ts_mk (ts_it evc).decls)

let remap evc (k,v) = 
  ts_mod
    (fun evc -> { focus = evc.focus;
                  hyps  = evc.hyps;
                  decls = Evd.add evc.decls k v })
    evc

let lc_exists f lc = Intset.fold (fun e b -> (f e) or b) lc false

(* [mentions sigma sp loc] is true exactly when [loc] is defined, and [sp] is
 * on [loc]'s access list, or an evar on [loc]'s access list mentions [sp]. *)

let rec mentions sigma sp loc =
  let loc_evd = Evd.map (ts_it sigma).decls loc in 
  match loc_evd.evar_body with 
    | Evar_defined _ -> (Intset.mem sp (get_lc loc_evd) 
			 or lc_exists (mentions sigma sp) (get_lc loc_evd))
    | _ -> false

(* ACCESSIBLE SIGMA SP LOC is true exactly when SP is on LOC's access list,
 * or there exists a LOC' on LOC's access list such that
 * MENTIONS SIGMA SP LOC' is true. *)

let rec accessible sigma sp loc =
  let loc_evd = Evd.map (ts_it sigma).decls loc in 
  lc_exists (fun loc' -> sp = loc' or mentions sigma sp loc') (get_lc loc_evd)


(* [ctxt_access sigma sp] is true when SIGMA is accessing a current
 * accessibility list ACCL, and SP is either on ACCL, or is mentioned
 * in the body of one of the ACCL. *)

let ctxt_access sigma sp =
  lc_exists (fun sp' -> sp' = sp or mentions sigma sp sp') (ts_it sigma).focus


let pf_lookup_name_as_renamed hyps ccl s =
  Detyping.lookup_name_as_renamed hyps ccl s

let pf_lookup_index_as_renamed ccl n =
  Detyping.lookup_index_as_renamed ccl n

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
  [< 'sTR"  "; hV 0 [< penv; 'fNL;
		       'sTR (emacs_str (String.make 1 (Char.chr 253))) ;
                       'sTR "============================"; 'fNL ;
                       'sTR" " ; pc>]; 'fNL>]

let pr_concl n g =
  let env = evar_env g in
  let pc = prterm_env_at_top env g.evar_concl in
  [< 'sTR (emacs_str (String.make 1 (Char.chr 253))) ;
     'sTR "subgoal ";'iNT n;'sTR " is:";'cUT;'sTR" " ; pc >]

(* print the subgoals but write Subtree proved! even in case some existential 
   variables remain unsolved, pr_subgoals_existential is a safer version 
   of pr_subgoals *)

let pr_subgoals = function
  | [] -> [< 'sTR"Subtree proved!" ; 'fNL >]
  | [g] ->
      let pg = pr_goal g in v 0 [< 'sTR ("1 "^"subgoal");'cUT; pg >]
  | g1::rest ->
      let rec pr_rec n = function
        | [] -> [< >]
        | g::rest ->
            let pg = pr_concl n g in
            let prest = pr_rec (n+1) rest in
            [< 'cUT; pg; prest >] 
      in
      let pg1 = pr_goal g1 in
      let pgr = pr_rec 2 rest in
      v 0 [< 'iNT(List.length rest+1) ; 'sTR" subgoals" ;'cUT; pg1; pgr >]

let pr_subgoal n =
  let rec prrec p = function
    | [] -> error "No such goal"
    | g::rest ->
       	if p = 1 then
          let pg = pr_goal g in
          v 0 [< 'sTR "subgoal ";'iNT n;'sTR " is:"; 'cUT; pg >]
       	else 
	  prrec (p-1) rest
  in 
  prrec n

let pr_pgm ctxt = match ctxt.pgm with
  | None -> [< >]
  | Some pgm -> let ppgm = fprterm pgm in [< 'sTR"Realizer " ; ppgm >]
					    
let pr_ctxt ctxt =
  let pc = pr_pgm ctxt in [< 'sTR"[" ; pc; 'sTR"]" >]

let pr_seq evd = 
  let env = evar_env evd
  and cl = evd.evar_concl
  and info = match evd.evar_info with 
    | Some i -> i 
    | None -> anomaly "pr_seq : info = None"
  in
  let pc = pr_ctxt info in
  let pdcl = pr_named_context_of env in
  let pcl = prterm_env_at_top env cl in
  hOV 0 [< pc; pdcl ; 'sPC ; hOV 0 [< 'sTR"|- " ; pcl >] >]

let prgl gl =
  let plc = pr_idl (List.map id_of_existential (lc_toList (get_lc gl))) in
  let pgl = pr_seq gl in
  [< 'sTR"[[" ; plc; 'sTR"]" ; pgl ; 'sTR"]" ; 'sPC >]

let pr_evgl gl =
  let plc = pr_idl (List.map id_of_existential (lc_toList (get_lc gl))) in
  let phyps = pr_idl (ids_of_named_context gl.evar_hyps) in
  let pc = prterm gl.evar_concl in
  hOV 0 [< 'sTR"[[" ; plc; 'sTR"] " ; phyps; 'sPC; 'sTR"|- " ; pc; 'sTR"]" >]

let pr_evgl_sign gl = 
  let plc = pr_idl (List.map id_of_existential (lc_toList (get_lc gl))) in
  let ps = pr_named_context_of (evar_env gl) in
  let pc = prterm gl.evar_concl in
  hOV 0 [< 'sTR"[[" ; plc ; 'sTR"] " ; ps; 'sPC; 'sTR"|- " ; pc; 'sTR"]" >]

(*  evd.evgoal.lc seems to be printed twice *)
let pr_decl evd =
  let pevgl = pr_evgl evd in
  let pb =
    match evd.evar_body with
      | Evar_empty -> [< 'fNL >]
      | Evar_defined c -> let pc = prterm c in [< 'sTR" => " ; pc;  'fNL  >]
  in
  h 0 [< pevgl; pb >]

let pr_evd evd = 
  prlist_with_sep pr_fnl
    (fun (ev,evd) ->
       let pe = pr_decl evd in 
       h 0 [< pr_id (id_of_existential ev) ; 'sTR"==" ; pe >])
    (Evd.to_list evd)
    
let pr_decls decls = pr_evd (ts_it decls)
		       
let pr_focus accl = pr_idl (List.map id_of_existential (lc_toList accl))

let pr_evc evc =
  let stamp = ts_stamp evc in
  let evc   = ts_it evc in
  let pe = pr_evd evc.decls in
  [< 'sTR"#" ; 'iNT stamp ; 'sTR"[" ; pr_focus evc.focus ; 'sTR"]=" ; pe >]

let pr_evars = 
  prlist_with_sep pr_fnl
    (fun (ev,evd) ->
       let pegl = pr_evgl_sign evd in 
       [< pr_id (id_of_existential ev); 'sTR " : "; pegl >])

(* Print an enumerated list of existential variables *)
let rec pr_evars_int i = function
  | [] -> [< >]
  | (ev,evd)::rest ->
      let pegl = pr_evgl_sign evd in 
      let pei = pr_evars_int (i+1) rest in
      [< (hOV 0 [< 'sTR "Existential "; 'iNT i; 'sTR " ="; 'sPC;
                   pr_id (id_of_existential ev) ; 'sTR " : "; pegl >]); 
	 'fNL ; pei >]

let pr_subgoals_existential sigma = function 
  | [] -> 
      let exl = Evd.non_instantiated sigma in 
      if exl = [] then 
	[< 'sTR"Subtree proved!" ; 'fNL >]
      else
        let pei = pr_evars_int 1 exl in
        [< 'sTR "No more subgoals but non-instantiated existential ";
           'sTR "variables :" ;'fNL; (hOV 0 pei) >]
  | [g] ->
      let pg = pr_goal g in
      v 0 [< 'sTR ("1 "^"subgoal");'cUT; pg >]
  | g1::rest ->
      let rec pr_rec n = function
        | [] -> [< >]
        | g::rest ->
            let pc = pr_concl n g in
            let prest = pr_rec (n+1) rest in
            [< 'cUT; pc; prest >] 
      in
      let pg1 = pr_goal g1 in
      let prest = pr_rec 2 rest in
      v 0 [< 'iNT(List.length rest+1) ; 'sTR" subgoals" ;'cUT; pg1; prest;
             'fNL >]

open Ast
open Termast
open Pretty

let ast_of_cvt_bind f = function
  | (NoDep n,c) -> ope ("BINDING", [(num n); ope ("COMMAND",[(f c)])])
  | (Dep  id,c) -> ope ("BINDING", [nvar (string_of_id id);
                                      ope  ("COMMAND",[(f c)])]) 
  | (Com,c)     -> ope ("BINDING", [ope ("COMMAND",[(f c)])])

let rec ast_of_cvt_intro_pattern = function
  | IdPat id  -> nvar (string_of_id id) 
  | DisjPat l -> ope ("DISJPATTERN",  (List.map ast_of_cvt_intro_pattern l))
  | ConjPat l -> ope ("CONJPATTERN",  (List.map ast_of_cvt_intro_pattern l))
  | ListPat l -> ope ("LISTPATTERN",  (List.map ast_of_cvt_intro_pattern l))

(* Gives the ast list corresponding to a reduction flag *)
let last_of_cvt_flags (_,red) =
  (if (red_set red BETA) then [ope("Beta",[])]
   else [])@
  (let (n_unf,lconst) = red_get_const red in
   let lqid =
     List.map
       (function
	  | EvalVarRef id -> nvar (string_of_id id)
	  | EvalConstRef sp ->
	      ast_of_qualid (Global.qualid_of_global (ConstRef sp)))
       lconst in
   if lqid = [] then []
   else if n_unf then [ope("Delta",[]);ope("UnfBut",lqid)]
   else [ope("Delta",[]);ope("Unf",lqid)])@
  (if (red_set red IOTA) then [ope("Iota",[])]
   else [])

(* Gives the ast corresponding to a reduction expression *)
let ast_of_cvt_redexp = function
  | Red _ -> ope ("Red",[])
  | Hnf -> ope("Hnf",[])
  | Simpl -> ope("Simpl",[])
  | Cbv flg -> ope("Cbv",last_of_cvt_flags flg)
  | Lazy flg -> ope("Lazy",last_of_cvt_flags flg)
  | Unfold l ->
    ope("Unfold",List.map (fun (locc,sp) -> ope("UNFOLD",
      [match sp with
	| EvalVarRef id -> nvar (string_of_id id)
	| EvalConstRef sp -> 					
	    ast_of_qualid (Global.qualid_of_global (ConstRef sp))]
      @(List.map num locc))) l)
  | Fold l ->
    ope("Fold",List.map (fun c -> ope ("COMMAND",
      [ast_of_constr false (Global.env ()) c])) l)
  | Pattern l ->
    ope("Pattern",List.map (fun (locc,csr,_) -> ope("PATTERN",
      [ope ("COMMAND",[ast_of_constr false (Global.env ()) csr])]@
      (List.map num locc))) l)

(* Gives the ast corresponding to a tactic argument *)
let ast_of_cvt_arg = function
  | Identifier id   -> nvar (string_of_id id) 
  | Qualid qid      -> nvar (Nametab.string_of_qualid qid) 
  | Quoted_string s -> str s
  | Integer n       -> num n 
  | Command c       -> ope ("COMMAND",[c])
  | Constr  c       -> 
    ope ("COMMAND",[ast_of_constr false (Global.env ()) c])
  | OpenConstr  (_,c)       -> 
    ope ("COMMAND",[ast_of_constr false (Global.env ()) c])
  | Constr_context _ ->
    anomalylabstrm "ast_of_cvt_arg" [<'sTR
      "Constr_context argument could not be used">]
  | Clause idl      -> ope ("CLAUSE", List.map (compose nvar string_of_id) idl)
  | Bindings bl     -> ope ("BINDINGS", 
			    List.map (ast_of_cvt_bind (fun x -> x)) bl)
  | Cbindings bl    -> 
      ope ("BINDINGS", 
	   List.map 
	     (ast_of_cvt_bind
		(ast_of_constr false (Global.env ()))) bl)
  | Tacexp ast      -> ope ("TACTIC",[ast])
  | Tac (tac,ast) -> ast
  | Redexp red -> ope("REDEXP",[ast_of_cvt_redexp red])
  | Fixexp (id,n,c) -> ope ("FIXEXP",[(nvar (string_of_id id)); 
                                      (num n); 
                                      ope ("COMMAND",[c])]) 
  | Cofixexp (id,c) -> ope ("COFIXEXP",[(nvar (string_of_id id)); 
                                          (ope ("COMMAND",[c]))])
  | Intropattern p ->  ast_of_cvt_intro_pattern p
  | Letpatterns (gl_occ_opt,hyp_occ_list) ->
     let hyps_pats =
       List.map
	 (fun (id,l) ->
	    ope ("HYPPATTERN", nvar (string_of_id id) :: (List.map num l)))
	 hyp_occ_list in
     let all_pats =
       match gl_occ_opt with
	 | None -> hyps_pats
	 | Some l -> hyps_pats @ [ope ("CCLPATTERN", List.map num l)] in
     ope ("LETPATTERNS", all_pats)

