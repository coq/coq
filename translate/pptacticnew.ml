(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Names
open Nameops
open Environ
open Util
open Extend
open Ppextend
open Ppconstrnew
open Tacexpr
open Rawterm
open Topconstr
open Genarg
open Libnames
open Pptactic

let pr_arg pr x = spc () ++ pr x

let pr_ltac_constant sp = pr_qualid (Nametab.shortest_qualid_of_tactic sp)

let pr_evaluable_reference = function 
  | EvalVarRef id -> pr_id id
  | EvalConstRef sp -> pr_global Idset.empty (Libnames.ConstRef sp)

let pr_inductive vars ind = pr_global vars (Libnames.IndRef ind)

let pr_quantified_hypothesis = function
  | AnonHyp n -> int n
  | NamedHyp id -> pr_id id 

let pr_quantified_hypothesis_arg h = spc () ++ pr_quantified_hypothesis h

(*
let pr_binding prc = function
  | NamedHyp id, c -> hov 1 (pr_id id ++ str " := " ++ cut () ++ prc c)
  | AnonHyp n, c -> hov 1 (int n ++ str " := " ++ cut () ++ prc c)
*)

let pr_esubst prc l =
  let pr_qhyp = function
      (_,AnonHyp n,c) -> str "(" ++ int n ++ str" := " ++ prc c ++ str ")"
    | (_,NamedHyp id,c) -> str "(" ++ pr_id id ++ str" := " ++ prc c ++ str ")"
  in
  prlist_with_sep spc pr_qhyp l

let pr_bindings_gen for_ex prlc prc = function
  | ImplicitBindings l ->
      spc () ++ (if for_ex then mt() else str "with ") ++
      hv 0 (prlist_with_sep spc prc l)
  | ExplicitBindings l ->
      spc () ++ (if for_ex then mt() else str "with ") ++
      hv 0 (pr_esubst prlc l)
  | NoBindings -> mt ()

let pr_bindings prlc prc = pr_bindings_gen false prlc prc

let pr_with_bindings prlc prc (c,bl) = prc c ++ pr_bindings prlc prc bl

let pr_with_names = function
  | [] -> mt ()
  | ids -> spc () ++ str "as [" ++
      hv 0 (prlist_with_sep (fun () -> spc () ++ str "| ")
              (prlist_with_sep spc pr_id) ids ++ str "]")

let rec pr_intro_pattern = function
  | IntroOrAndPattern pll ->
      str "[" ++
      hv 0 (prlist_with_sep pr_bar (prlist_with_sep spc pr_intro_pattern) pll)
      ++ str "]"

  | IntroWildcard -> str "_"
  | IntroIdentifier id -> pr_id id

let pr_hyp_location pr_id = function
  | InHyp id -> spc () ++ pr_id id
  | InHypType id -> spc () ++ str "(type of " ++ pr_id id ++ str ")"

let pr_clause pr_id = function
  | [] -> mt ()
  | l -> spc () ++ hov 0 (str "in" ++ prlist (pr_hyp_location pr_id) l)

let pr_clause_pattern pr_id = function
  | (None, []) -> mt ()
  | (glopt,l) ->
      str " in" ++
      prlist
        (fun (id,nl) -> prlist (pr_arg int) nl 
	  ++ spc () ++ pr_id id) l ++
        pr_opt (fun nl -> prlist_with_sep spc int nl ++ str " Goal") glopt

let pr_induction_arg prc = function
  | ElimOnConstr c -> prc c
  | ElimOnIdent (_,id) -> pr_id id
  | ElimOnAnonHyp n -> int n

let pr_match_pattern pr_pat = function
  | Term a -> pr_pat a
  | Subterm (None,a) -> str "[" ++ pr_pat a ++ str "]"
  | Subterm (Some id,a) -> pr_id id ++ str "[" ++ pr_pat a ++ str "]"

let pr_match_hyps pr_pat = function
  | NoHypId mp -> str "_:" ++ pr_match_pattern pr_pat mp
  | Hyp ((_,id),mp) -> pr_id id ++ str ":" ++ pr_match_pattern pr_pat mp

let pr_match_rule m pr pr_pat = function
  | Pat ([],mp,t) when m ->
      str "[" ++ pr_match_pattern pr_pat mp ++ str "]"
      ++ spc () ++ str "=>" ++ brk (1,4) ++ pr t
  | Pat (rl,mp,t) ->
      str "[" ++ prlist_with_sep (fun () -> str",") (pr_match_hyps pr_pat) rl ++
      spc () ++ str "|-" ++ spc () ++ pr_match_pattern pr_pat mp ++ spc () ++
      str "] =>" ++ brk (1,4) ++ pr t
  | All t -> str "_" ++ spc () ++ str "=>" ++ brk (1,4) ++ pr t

let pr_funvar = function
  | None -> spc () ++ str "()"
  | Some id -> spc () ++ pr_id id

let pr_let_clause k pr prc pr_cst = function
  | ((_,id),None,t) ->
      hov 0 (str k ++ pr_id id ++ str " :=" ++ brk (1,1) ++
             pr (TacArg t))
  | ((_,id),Some c,t) ->
      hv 0 (str k ++ pr_id id ++ str" :" ++ brk(1,2) ++
      pr_may_eval prc prc pr_cst c ++
      str " :=" ++ brk (1,1) ++ pr (TacArg t))

let pr_let_clauses pr prc pr_cst = function
  | hd::tl ->
      hv 0
        (pr_let_clause "let " pr prc pr_cst hd ++ spc () ++
         prlist_with_sep spc (pr_let_clause "with " pr prc pr_cst) tl)
  | [] -> anomaly "LetIn must declare at least one binding"

let pr_rec_clause pr ((_,id),(l,t)) =
  pr_id id ++ prlist pr_funvar l ++ str "=>" ++ spc () ++ pr t

let pr_rec_clauses pr l = 
  prlist_with_sep (fun () -> fnl () ++ str "and ") (pr_rec_clause pr) l

let pr_hintbases = function
  | None -> spc () ++ str "with *"
  | Some [] -> mt ()
  | Some l ->
      spc () ++ hov 2 (str "with" ++ prlist (fun s -> spc () ++ str s) l)

let pr_autoarg_adding = function
  | [] -> mt ()
  | l ->
      spc () ++ str "Adding [" ++
        hv 0 (prlist_with_sep spc pr_reference l) ++ str "]"

let pr_autoarg_destructing = function
  | true -> spc () ++ str "Destructing"
  | false -> mt ()

let pr_autoarg_usingTDB = function
  | true -> spc () ++ str "Using TDB"
  | false -> mt ()

let rec pr_tacarg_using_rule pr_gen = function
  | Egrammar.TacTerm s :: l, al -> spc () ++ str s ++ pr_tacarg_using_rule pr_gen (l,al)
  | Egrammar.TacNonTerm _ :: l, a :: al -> pr_gen a ++ pr_tacarg_using_rule pr_gen (l,al)
  | [], [] -> mt ()
  | _ -> failwith "Inconsistent arguments of extended tactic"


open Closure

let make_pr_tac (pr_tac,pr_tac0,pr_constr,pr_lconstr,pr_pat,pr_cst,pr_ind,pr_ref,pr_ident,pr_extend) =

let pr_bindings env = pr_bindings (pr_lconstr env) (pr_constr env) in
let pr_ex_bindings env = pr_bindings_gen true (pr_lconstr env) (pr_constr env) in
let pr_with_bindings env = pr_with_bindings (pr_lconstr env) (pr_constr env) in
let pr_eliminator env cb = str "using" ++ pr_arg (pr_with_bindings env) cb in
let pr_constrarg env c = spc () ++ pr_constr env c in
let pr_lconstrarg env c = spc () ++ pr_lconstr env c in

let pr_intarg n = spc () ++ int n in

  (* Printing tactics as arguments *)
let rec pr_atom0 env = function
  | TacIntroPattern [] -> str "intros"
  | TacIntroMove (None,None) -> str "intro"
  | TacAssumption -> str "assumption"
  | TacAnyConstructor None -> str "constructor"
  | TacTrivial (Some []) -> str "trivial"
  | TacAuto (None,Some []) -> str "auto"
  | TacAutoTDB None -> str "autotdb"
  | TacDestructConcl -> str "dconcl"
  | TacReflexivity -> str "reflexivity"
  | TacSymmetry -> str "symmetry"
  | t -> str "(" ++ pr_atom1 env t ++ str ")"

  (* Main tactic printer *)
and pr_atom1 env = function
  | TacExtend (_,s,l) ->
      pr_extend (pr_constr env) (pr_lconstr env) (pr_tac env) s l
  | TacAlias (_,s,l,_) ->
      pr_extend (pr_constr env) (pr_lconstr env) (pr_tac env) s (List.map snd l)

  (* Basic tactics *)
  | TacIntroPattern [] as t -> pr_atom0 env t
  | TacIntroPattern (_::_ as p) -> 
      hov 1 (str "intros" ++ spc () ++ prlist_with_sep spc pr_intro_pattern p)
  | TacIntrosUntil h ->
      hv 1 (str "intros until" ++ pr_arg pr_quantified_hypothesis h)
  | TacIntroMove (None,None) as t -> pr_atom0 env t
  | TacIntroMove (Some id1,None) -> str "intro " ++ pr_id id1
  | TacIntroMove (ido1,Some (_,id2)) ->
      hov 1
      (str "intro" ++ pr_opt pr_id ido1 ++ spc () ++ str "after " ++ pr_id id2)
  | TacAssumption as t -> pr_atom0 env t
  | TacExact c -> hov 1 (str "exact" ++ pr_lconstrarg env c)
  | TacApply cb -> hov 1 (str "apply " ++ pr_with_bindings env cb)
  | TacElim (cb,cbo) ->
      hov 1 (str "elim" ++ pr_arg (pr_with_bindings env) cb ++ 
        pr_opt (pr_eliminator env) cbo)
  | TacElimType c -> hov 1 (str "elimtype" ++ pr_lconstrarg env c)
  | TacCase cb -> hov 1 (str "case" ++ spc () ++ pr_with_bindings env cb)
  | TacCaseType c -> hov 1 (str "CaseType" ++ pr_lconstrarg env c)
  | TacFix (ido,n) -> hov 1 (str "fix" ++ pr_opt pr_id ido ++ pr_intarg n)
  | TacMutualFix (id,n,l) ->
      hov 1 (str "fix" ++ spc () ++ pr_id id ++ pr_intarg n ++ spc () ++
        hov 0 (str "with" ++ brk (1,1) ++
          prlist_with_sep spc
	    (fun (id,n,c) ->
	      spc () ++ pr_id id ++ pr_intarg n ++ pr_constrarg env c)
	  l))
  | TacCofix ido -> hov 1 (str "cofix" ++ pr_opt pr_id ido)
  | TacMutualCofix (id,l) ->
      hov 1 (str "cofix" ++ spc () ++ pr_id id ++ spc () ++
        hov 0 (str "with" ++ brk (1,1) ++
          prlist (fun (id,c) -> spc () ++ pr_id id ++ pr_constrarg env c)
	  l))
  | TacCut c -> hov 1 (str "cut" ++ pr_lconstrarg env c)
  | TacTrueCut (None,c) -> 
      hov 1 (str "assert" ++ pr_lconstrarg env c)
  | TacTrueCut (Some id,c) -> 
      hov 1 (str "assert" ++ spc () ++ pr_id id ++ str ":" ++
             pr_lconstrarg env c)
  | TacForward (false,na,c) ->
      hov 1 (str "assert" ++ pr_arg pr_name na ++ str " :=" ++
             pr_lconstrarg env c)
  | TacForward (true,na,c) ->
      hov 1 (str "pose" ++ pr_arg pr_name na ++ str " :=" ++
             pr_lconstrarg env c)
  | TacGeneralize l ->
      hov 1 (str "generalize" ++ spc () ++
             prlist_with_sep spc (pr_constr env) l)
  | TacGeneralizeDep c ->
      hov 1 (str "generalize" ++ spc () ++ str "dependent" ++
             pr_lconstrarg env c)
  | TacLetTac (id,c,cl) ->
      hov 1 (str "lettac" ++ spc () ++ pr_id id ++ str " :=" ++
        pr_constrarg env c ++ pr_clause_pattern pr_ident cl)
  | TacInstantiate (n,c) ->
      hov 1 (str "instantiate" ++ pr_arg int n ++ pr_lconstrarg env c)

  (* Derived basic tactics *)
  | TacOldInduction h ->
      hov 1 (str "oldinduction" ++ pr_arg pr_quantified_hypothesis h)
  | TacNewInduction (h,e,ids) ->
      hov 1 (str "induction" ++ spc () ++
             pr_induction_arg (pr_lconstr env) h ++
             pr_opt (pr_eliminator env) e ++ pr_with_names ids)
  | TacOldDestruct h ->
      hov 1 (str "olddestruct" ++ pr_arg pr_quantified_hypothesis h)
  | TacNewDestruct (h,e,ids) ->
      hov 1 (str "destruct" ++ spc () ++
             pr_induction_arg (pr_lconstr env) h ++
             pr_opt (pr_eliminator env) e ++ pr_with_names ids)
  | TacDoubleInduction (h1,h2) ->
      hov 1
        (str "double induction" ++ 
         pr_arg pr_quantified_hypothesis h1 ++
 	 pr_arg pr_quantified_hypothesis h2)
  | TacDecomposeAnd c ->
      hov 1 (str "decompose record" ++ pr_lconstrarg env c)
  | TacDecomposeOr c ->
      hov 1 (str "decompose sum" ++ pr_lconstrarg env c)
  | TacDecompose (l,c) ->
      let vars = Termops.vars_of_env env in
      hov 1 (str "decompose" ++ spc () ++
        hov 0 (str "[" ++ prlist_with_sep spc (pr_or_metanum (pr_ind vars)) l
	  ++ str "]" ++ pr_lconstrarg env c))
  | TacSpecialize (n,c) ->
      hov 1 (str "specialize " ++ pr_opt int n ++ pr_with_bindings env c)
  | TacLApply c -> 
      hov 1 (str "lapply" ++ pr_lconstrarg env c)

  (* Automation tactics *)
  | TacTrivial (Some []) as x -> pr_atom0 env x
  | TacTrivial db -> hov 0 (str "trivial" ++ pr_hintbases db)
  | TacAuto (None,Some []) as x -> pr_atom0 env x
  | TacAuto (n,db) -> hov 0 (str "auto" ++ pr_opt int n ++ pr_hintbases db)
  | TacAutoTDB None as x -> pr_atom0 env x
  | TacAutoTDB (Some n) -> hov 0 (str "autotdb" ++ spc () ++ int n)
  | TacDestructHyp (true,(_,id)) -> hov 0 (str "cdhyp" ++ spc () ++ pr_id id)
  | TacDestructHyp (false,(_,id)) -> hov 0 (str "dhyp" ++ spc () ++ pr_id id)
  | TacDestructConcl as x -> pr_atom0 env x
  | TacSuperAuto (n,l,b1,b2) ->
      hov 1 (str "superauto" ++ pr_opt int n ++ pr_autoarg_adding l ++ 
             pr_autoarg_destructing b1 ++ pr_autoarg_usingTDB b2)
  | TacDAuto (n,p) ->
      hov 1 (str "auto" ++ pr_opt int n ++ str "decomp" ++ pr_opt int p)

  (* Context management *)
  | TacClear l ->
      hov 1 (str "clear" ++ spc () ++ prlist_with_sep spc (pr_or_metanum pr_id) l)
  | TacClearBody l ->
      hov 1 (str "clear" ++ spc () ++ prlist_with_sep spc (pr_or_metanum pr_id) l)
  | TacMove (b,(_,id1),(_,id2)) ->
      (* Rem: only b = true is available for users *)
      assert b;
      hov 1
        (str "move" ++ brk (1,1) ++ pr_id id1 ++ spc () ++ 
	 str "after" ++ brk (1,1) ++ pr_id id2)
  | TacRename ((_,id1),(_,id2)) ->
      hov 1
        (str "rename" ++ brk (1,1) ++ pr_id id1 ++ spc () ++ 
	 str "into" ++ brk (1,1) ++ pr_id id2)

  (* Constructors *)
  | TacLeft l -> hov 1 (str "left" ++ pr_bindings env l)
  | TacRight l -> hov 1 (str "right" ++ pr_bindings env l)
  | TacSplit (false,l) -> hov 1 (str "split" ++ pr_bindings env l)
  | TacSplit (true,l) -> hov 1 (str "exists" ++ pr_ex_bindings env l)
  | TacAnyConstructor (Some t) ->
      hov 1 (str "constructor" ++ pr_arg (pr_tac0 env) t)
  | TacAnyConstructor None as t -> pr_atom0 env t
  | TacConstructor (n,l) ->
      hov 1 (str "constructor" ++ pr_or_metaid pr_intarg n ++
             pr_bindings env l)

  (* Conversion *)  
  | TacReduce (r,h) ->
      hov 1 (pr_red_expr (pr_constr env,pr_lconstr env,pr_cst) r ++
             pr_clause pr_ident h)
  | TacChange (occ,c,h) -> (* A Verifier *)
      hov 1 (str "change" ++ brk (1,1) ++
      (match occ with
          None -> mt()
        | Some(ocl,c1) ->
            hov 1 (prlist (fun i -> int i ++ spc()) ocl ++
                   pr_constr env c1) ++ spc() ++ str "with ") ++
      pr_constr env c ++ pr_clause pr_ident h)

  (* Equivalence relations *)
  | (TacReflexivity | TacSymmetry) as x -> pr_atom0 env x
  | TacTransitivity c -> str "transitivity" ++ pr_lconstrarg env c in

let ltop = (5,E) in
let lseq = 5 in
let ltactical = 3 in
let lorelse = 2 in
let llet = 1 in
let lfun = 1 in
let labstract = 1 in
let lmatch = 1 in
let latom = 0 in
let lcall = 1 in
let leval = 1 in
let ltatom = 1 in

let pr_seq_body pr tl =
  hv 0 (str "[ " ++
        prlist_with_sep (fun () -> spc () ++ str "| ") (pr ltop) tl ++
        str " ]") in

let rec pr_tac env inherited tac =
  let (strm,prec) = match tac with
  | TacAbstract (t,None) ->
      str "abstract " ++ pr_tac env (labstract,E) t, labstract
  | TacAbstract (t,Some s) -> 
      hov 0
       (str "abstract " ++ pr_tac env ltop t ++ spc () ++
        str "using " ++ pr_id s),
      labstract
  | TacLetRecIn (l,t) -> 
      hv 0
        (str "let rec " ++ pr_rec_clauses (pr_tac env ltop) l ++ str " in" ++
         fnl () ++ pr_tac env (llet,E) t),
      llet
  | TacLetIn (llc,u) ->
      v 0
       (hv 0 (pr_let_clauses (pr_tac env ltop) (pr_constr env) pr_cst llc ++ 
       str " in") ++
       fnl () ++ pr_tac env (llet,E) u),
      llet
  | TacLetCut llc -> assert false
  | TacMatch (t,lrul) ->
      hov 0 (str "match " ++
             pr_may_eval (pr_constr env) (pr_lconstr env) pr_cst t
        ++ str " with"
        ++ prlist
	  (fun r -> fnl () ++ str "| " ++
            pr_match_rule true (pr_tac env ltop) pr_pat r)
	lrul
        ++ fnl() ++ str "end"),
      lmatch
  | TacMatchContext (lr,lrul) ->
      hov 0 (
	str (if lr then "match reverse context with" else "match context with")
	++ prlist
	  (fun r -> fnl () ++ str "| " ++
            pr_match_rule false (pr_tac env ltop) pr_pat r)
	lrul
        ++ fnl() ++ str "end"),
      lmatch
  | TacFun (lvar,body) ->
      hov 2 (str "fun" ++
        prlist pr_funvar lvar ++ str " =>" ++ spc () ++
        pr_tac env (lfun,E) body),
      lfun
  | TacThens (t,tl) -> 
      hov 1 (pr_tac env (lseq,E) t ++ str " &" ++ spc () ++
             pr_seq_body (pr_tac env) tl),
      lseq
  | TacThen (t1,t2) ->
      hov 1 (pr_tac env (lseq,E) t1 ++ str " &" ++ spc () ++
             pr_tac env (lseq,L) t2),
      lseq
  | TacTry t ->
      hov 1 (str "try" ++ spc () ++ pr_tac env (ltactical,E) t),
      ltactical
  | TacDo (n,t) ->
      hov 1 (str "do " ++ int n ++ spc () ++ pr_tac env (ltactical,E) t),
      ltactical
  | TacRepeat t ->
      hov 1 (str "repeat" ++ spc () ++ pr_tac env (ltactical,E) t),
      ltactical
  | TacProgress t ->
      hov 1 (str "progress" ++ spc () ++ pr_tac env (ltactical,E) t),
      ltactical
  | TacInfo t ->
      hov 1 (str "info" ++ spc () ++ pr_tac env (ltactical,E) t),
      ltactical
  | TacOrelse (t1,t2) ->
      hov 1 (pr_tac env (lorelse,L) t1 ++ str " ||" ++ brk (1,1) ++
             pr_tac env (lorelse,E) t2),
      lorelse
  | TacFail (0,"") -> str "fail", latom
  | TacFail (n,s) -> 
      str "fail" ++ (if n=0 then mt () else pr_arg int n) ++
      (if s="" then mt() else str " \"" ++ str s ++ str "\""), latom
  | TacFirst tl ->
      str "first" ++ spc () ++ pr_seq_body (pr_tac env) tl, llet
  | TacSolve tl ->
      str "solve" ++ spc () ++ pr_seq_body (pr_tac env) tl, llet
  | TacId -> str "idtac", latom
  | TacAtom (_,t) -> hov 1 (pr_atom1 env t), ltatom
  | TacArg(Tacexp e) -> pr_tac0 env e, latom
  | TacArg(ConstrMayEval (ConstrTerm c)) -> str "'" ++ pr_constr env c, latom
  | TacArg(ConstrMayEval c) ->
      pr_may_eval (pr_constr env) (pr_lconstr env) pr_cst c, leval
  | TacArg(Integer n) -> int n, latom
  | TacArg(TacCall(_,f,l)) ->
      hov 1 (pr_ref f ++ spc () ++
             prlist_with_sep spc (pr_tacarg env) l),
      lcall
  | TacArg a -> pr_tacarg env a, latom
  in
  if prec_less prec inherited then strm
  else str"(" ++ strm ++ str")"

and pr_tacarg env = function
  | TacDynamic (_,t) -> str ("<dynamic ["^(Dyn.tag t)^"]>")
  | MetaIdArg (_,s) -> str ("$" ^ s)
  | Identifier id -> pr_id id
  | TacVoid -> str "()"
  | Reference r -> pr_ref r
  | ConstrMayEval (ConstrTerm c) -> pr_constr env c
  | (ConstrMayEval _|TacCall _|Tacexp _|Integer _) as a ->
      str "'" ++ pr_tac env (latom,E) (TacArg a)

in ((fun env -> pr_tac env ltop),
    (fun env -> pr_tac env (latom,E)),
    pr_match_rule)

let pi1 (a,_,_) = a
let pi2 (_,a,_) = a
let pi3 (_,_,a) = a

let rec raw_printers =
    (pr_raw_tactic, 
     pr_raw_tactic0,
     Ppconstrnew.pr_constr_env,
     Ppconstrnew.pr_lconstr_env,
     Ppconstrnew.pr_pattern,
     pr_or_metanum pr_reference,
     (fun _ -> pr_reference),
     pr_reference,
     pr_or_metaid (pr_located pr_id),
     Pptactic.pr_raw_extend)

and pr_raw_tactic env (t:raw_tactic_expr) =
  pi1 (make_pr_tac raw_printers) env t

and pr_raw_tactic0 env t =
  pi2 (make_pr_tac raw_printers) env t

and pr_raw_match_rule env t =
  pi3 (make_pr_tac raw_printers) env t

let pr_and_constr_expr pr (c,_) = pr c

let rec glob_printers =
    (pr_glob_tactic, 
     pr_glob_tactic0,
     (fun env -> pr_and_constr_expr (Ppconstrnew.pr_rawconstr_env env)),
     (fun env -> pr_and_constr_expr (Ppconstrnew.pr_lrawconstr_env env)),
     Printer.pr_pattern,
     pr_or_metanum (pr_or_var (pr_and_short_name pr_evaluable_reference)),
     (fun vars -> pr_or_var (pr_inductive vars)),
     pr_or_var (pr_located pr_ltac_constant),
     pr_located pr_id,
     Pptactic.pr_glob_extend)

and pr_glob_tactic env (t:glob_tactic_expr) =
  pi1 (make_pr_tac glob_printers) env t

and pr_glob_tactic0 env t =
  pi2 (make_pr_tac glob_printers) env t

and pr_glob_match_rule env t =
  pi3 (make_pr_tac glob_printers) env t

let (pr_tactic,_,_) =
  make_pr_tac
    (pr_glob_tactic,
     pr_glob_tactic0,
     Printer.prterm_env,
     Printer.prterm_env,
     Printer.pr_pattern,
     pr_evaluable_reference,
     pr_inductive,
     pr_ltac_constant,
     pr_id,
     Pptactic.pr_extend)
