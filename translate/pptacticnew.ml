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

let sep_v = fun _ -> str"," ++ spc()

let strip_prod_binders_expr n ty =
  let rec strip_ty acc n ty =
    match ty with
        Topconstr.CProdN(_,bll,a) ->
          let nb =
            List.fold_left (fun i (nal,_) -> i + List.length nal) 0 bll in
          if nb >= n then (List.rev (bll@acc), a)
          else strip_ty (bll@acc) (n-nb) a
      | Topconstr.CArrow(_,a,b) ->
          if n=1 then
            (List.rev (([(dummy_loc,Anonymous)],a)::acc), b)
          else strip_ty (([(dummy_loc,Anonymous)],a)::acc) (n-1) b
      | _ -> error "Cannot translate fix tactic: not enough products" in
  strip_ty [] n ty


(* In v8 syntax only double quote char is escaped by repeating it *)
let rec escape_string_v8 s =
  let rec escape_at s i =
    if i<0 then s
    else if s.[i] == '"' then
      let s' = String.sub s 0 i^"\""^String.sub s i (String.length s - i) in
      escape_at s' (i-1)
    else escape_at s (i-1) in
  escape_at s (String.length s - 1)

let qstringnew s = str ("\""^escape_string_v8 s^"\"")
let qsnew = qstringnew

let translate_v7_ltac = function
  | "DiscrR" -> "discrR"
  | "Sup0" -> "prove_sup0"
  | "SupOmega" -> "omega_sup"
  | "Sup" -> "prove_sup"
  | "RCompute" -> "Rcompute"
  | "IntroHypG" -> "intro_hyp_glob"
  | "IntroHypL" -> "intro_hyp_pt"
  | "IsDiff_pt" -> "is_diff_pt"
  | "IsDiff_glob" -> "is_diff_glob"
  | "IsCont_pt" -> "is_cont_pt"
  | "IsCont_glob" -> "is_cont_glob"
  | "RewTerm" -> "rew_term"
  | "ConsProof" -> "deriv_proof"
  | "SimplifyDerive" -> "simplify_derive"
  | "Reg" -> "reg" (* ??? *)
  | "SplitAbs" -> "split_case_Rabs"
  | "SplitAbsolu" -> "split_Rabs"
  | "SplitRmult" -> "split_Rmult"
  | "CaseEqk" -> "case_eq"
  | "SqRing" -> "ring_Rsqr"
  | "TailSimpl" -> "tail_simpl"
  | "CoInduction" -> "coinduction"
  | "ElimCompare" -> "elim_compare"
  | "CCsolve" -> "CCsolve"  (* ?? *)
  | "ArrayAccess" -> "array_access"
  | "MemAssoc" -> "mem_assoc"
  | "SeekVarAux" -> "seek_var_aux"
  | "SeekVar" -> "seek_var"
  | "NumberAux" -> "number_aux"
  | "Number" -> "number"
  | "BuildVarList" -> "build_varlist"
  | "Assoc" -> "assoc"
  | "Remove" -> "remove"
  | "Union" -> "union"
  | "RawGiveMult" -> "raw_give_mult"
  | "GiveMult" -> "give_mult"
  | "ApplyAssoc" -> "apply_assoc"
  | "ApplyDistrib" -> "apply_distrib"
  | "GrepMult" -> "grep_mult"
  | "WeakReduce" -> "weak_reduce"
  | "Multiply" -> "multiply"
  | "ApplyMultiply" -> "apply_multiply"
  | "ApplyInverse" -> "apply_inverse"
  | "StrongFail" -> "strong_fail"
  | "InverseTestAux" -> "inverse_test_aux"
  | "InverseTest" -> "inverse_test"
  | "ApplySimplif" -> "apply_simplif"
  | "Unfolds" -> "unfolds"
  | "Reduce" -> "reduce"
  | "Field_Gen_Aux" -> "field_gen_aux"
  | "Field_Gen" -> "field_gen"
  | "EvalWeakReduce" -> "eval_weak_reduce"
  | "Field_Term" -> "field_term"
  | "Fourier" -> "fourier" (* ou Fourier ?? *)
  | "FourierEq" -> "fourier_eq"
  | "S_to_plus" -> "rewrite_S_to_plus_term"
  | "S_to_plus_eq" -> "rewrite_S_to_plus"
  | "NatRing" -> "ring_nat"
  | "Solve1" -> "solve1"
  | "Solve2" -> "solve2"
  | "Elim_eq_term" -> "elim_eq_term"
  | "Elim_eq_Z" -> "elim_eq_Z"
  | "Elim_eq_pos" -> "elim_eq_pos"
  | "Elim_Zcompare" -> "elim_Zcompare"
  | "ProveStable" -> "prove_stable"
  | "interp_A" -> "interp_A"
  | "InitExp" -> "init_exp"
  | "SimplInv" -> "simpl_inv"
  | "Map" -> "map_tactic"
  | "BuildMonomAux" -> "build_monom_aux"
  | "BuildMonom" -> "build_monom"
  | "SimplMonomAux" -> "simpl_monom_aux"
  | "SimplMonom" -> "simpl_monom"
  | "SimplAllMonoms" -> "simpl_all_monomials"
  | "AssocDistrib" -> "assoc_distrib"
  | "NowShow" -> "now_show"
  | ("subst"|"simpl"|"elim"|"destruct"|"apply"|"intro" (* ... *)) as x ->
      let x' = x^"_" in
      msgerrnl
      (str ("Warning: '"^
         x^"' is now a primitive tactic; it has been translated to '"^x'^"'"));
      x'
  | x -> x

let id_of_ltac_v7_id id = 
  id_of_string (translate_v7_ltac (string_of_id id))

let pr_ltac_or_var pr = function
  | ArgArg x -> pr x
  | ArgVar (loc,id) ->
      pr_with_comments loc (pr_id (id_of_ltac_v7_id id))

let pr_arg pr x = spc () ++ pr x

let pr_ltac_constant sp =
  (* Source de bug: le nom le plus court n'est pas forcement correct 
     apres renommage *)
  let qid = Nametab.shortest_qualid_of_tactic sp in
  let dir,id = repr_qualid qid in
  pr_qualid (make_qualid dir (id_of_ltac_v7_id id))

let pr_evaluable_reference_env env = function 
  | EvalVarRef id -> pr_id (Constrextern.v7_to_v8_id id)
  | EvalConstRef sp -> pr_global (Termops.vars_of_env env) (Libnames.ConstRef sp)

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
    | (_,NamedHyp id,c) ->
        str "(" ++ pr_id id ++ str" := " ++ prc c ++ str ")"
  in
  prlist_with_sep spc pr_qhyp l

let pr_bindings_gen for_ex prlc prc = function
  | ImplicitBindings l ->
      spc () ++
      hv 2 ((if for_ex then mt() else str "with" ++ spc ()) ++
            prlist_with_sep spc prc l)
  | ExplicitBindings l ->
      spc () ++
      hv 2 ((if for_ex then mt() else str "with" ++ spc ()) ++
            pr_esubst prlc l)
  | NoBindings -> mt ()

let pr_bindings prlc prc = pr_bindings_gen false prlc prc

let pr_with_bindings prlc prc (c,bl) =
  if Options.do_translate () then
    (* translator calls pr_with_bindings on rawconstr: we cast it! *)
    let bl' = translate_with_bindings (fst (Obj.magic c) : rawconstr) bl in
    hov 1 (prc c ++ pr_bindings prlc prc bl')
  else
    hov 1 (prc c ++ pr_bindings prlc prc bl)

let pr_with_constr prc = function
  | None -> mt ()
  | Some c -> spc () ++ hov 1 (str "with" ++ spc () ++ prc c)

(* Translator copy of pr_intro_pattern based on a translating "pr_id" *)
let rec pr_intro_pattern = function
  | IntroOrAndPattern pll -> pr_case_intro_pattern pll
  | IntroWildcard -> str "_"
  | IntroIdentifier id -> pr_id id
and pr_case_intro_pattern = function
  | [_::_ as pl] ->
      str "(" ++ hov 0 (prlist_with_sep pr_coma pr_intro_pattern pl) ++ str ")"
  | pll ->
      str "[" ++
      hv 0 (prlist_with_sep pr_bar 
        (fun l -> hov 0 (prlist_with_sep spc pr_intro_pattern l)) pll)
      ++ str "]"

let pr_with_names = function
  | None -> mt ()
  | Some ipat -> spc () ++ hov 1 (str "as" ++ spc () ++ pr_intro_pattern ipat)

let pr_occs pp = function
    [] -> pp
  | nl -> hov 1 (pp ++ spc() ++ str"at " ++
                 hov 0 (prlist_with_sep spc int nl))

let pr_hyp_location pr_id = function
  | id, occs, InHyp -> spc () ++ pr_occs (pr_id id) occs
  | id, occs, InHypTypeOnly ->
      spc () ++ pr_occs (str "(type of " ++ pr_id id ++ str ")") occs
  | id, occs, InHypValueOnly ->
      spc () ++ pr_occs (str "(value of " ++ pr_id id ++ str ")") occs

let pr_hyp_location pr_id (id,occs,(hl,hl')) =
  if !hl' <> None then pr_hyp_location pr_id (id,occs,out_some !hl')
  else
    (if hl = InHyp && Options.do_translate () then 
      msgerrnl (h 0 (str "Translator warning: Unable to detect if " ++ pr_id id ++ spc () ++ str "denotes a local definition"));
    pr_hyp_location pr_id (id,occs,hl))

let pr_in pp = spc () ++ hov 0 (str "in" ++ pp)

let pr_simple_clause pr_id = function
  | [] -> mt ()
  | l -> pr_in (spc () ++ prlist_with_sep spc pr_id l)

let pr_clauses pr_id = function
    { onhyps=None; onconcl=true; concl_occs=nl } ->
      pr_in (pr_occs (str " *") nl)
  | { onhyps=None; onconcl=false } -> pr_in (str " * |-")
  | { onhyps=Some l; onconcl=true; concl_occs=nl } -> 
      pr_in (prlist_with_sep (fun () -> str",") (pr_hyp_location pr_id) l
             ++ pr_occs (str" |- *") nl)
  | { onhyps=Some l; onconcl=false } ->
      pr_in (prlist_with_sep (fun()->str",") (pr_hyp_location pr_id) l)

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
  | ElimOnIdent (loc,id) -> pr_with_comments loc (pr_id id)
  | ElimOnAnonHyp n -> int n

let pr_induction_kind = function
  | SimpleInversion -> str "simple inversion"
  | FullInversion -> str "inversion"
  | FullInversionClear -> str "inversion_clear"

let pr_match_pattern pr_pat = function
  | Term a -> pr_pat a
  | Subterm (None,a) -> str "context [" ++ pr_pat a ++ str "]"
  | Subterm (Some id,a) ->
      str "context " ++ pr_id id ++ str "[" ++ pr_pat a ++ str "]"

let pr_match_hyps pr_pat = function
  | Hyp (nal,mp) -> pr_lname nal ++ str ":" ++ pr_match_pattern pr_pat mp

let pr_match_rule m pr pr_pat = function
  | Pat ([],mp,t) when m ->
      pr_match_pattern pr_pat mp ++
      spc () ++ str "=>" ++ brk (1,4) ++ pr t
  | Pat (rl,mp,t) ->
      prlist_with_sep (fun () -> str",") (pr_match_hyps pr_pat) rl ++
      spc () ++ str "|-" ++ spc () ++ pr_match_pattern pr_pat mp ++ spc () ++
      str "=>" ++ brk (1,4) ++ pr t
  | All t -> str "_" ++ spc () ++ str "=>" ++ brk (1,4) ++ pr t

let pr_funvar = function
  | None -> spc () ++ str "_"
  | Some id -> spc () ++ pr_id id

let pr_let_clause k pr = function
  | (id,None,t) ->
      hov 0 (str k ++ pr_lident id ++ str " :=" ++ brk (1,1) ++
             pr (TacArg t))
  | (id,Some c,t) ->
      hv 0 (str k ++ pr_lident id ++ str" :" ++ brk(1,2) ++
      pr c ++
      str " :=" ++ brk (1,1) ++ pr (TacArg t))

let pr_let_clauses pr = function
  | hd::tl ->
      hv 0
        (pr_let_clause "let " pr hd ++
         prlist (fun t -> spc () ++ pr_let_clause "with " pr t) tl)
  | [] -> anomaly "LetIn must declare at least one binding"

let pr_rec_clause pr (id,(l,t)) =
  hov 0
    (pr_lident id ++ prlist pr_funvar l ++ str " :=") ++ spc () ++ pr t

let pr_rec_clauses pr l = 
  prlist_with_sep (fun () -> fnl () ++ str "with ") (pr_rec_clause pr) l

let pr_seq_body pr tl =
  hv 0 (str "[ " ++
        prlist_with_sep (fun () -> spc () ++ str "| ") pr tl ++
        str " ]")

let pr_as_names_force force ids (pp,ids') =
  pr_with_names 
    (if (!pp or force) & List.exists ((<>) (ref [])) ids'
    then Some (IntroOrAndPattern (List.map (fun x -> !x) ids'))
    else ids)

let duplicate force nodup ids pr = function
  | [] -> pr (pr_as_names_force force ids (ref false,[]))
  | x::l when List.for_all (fun y -> snd x=snd y) l ->
      pr (pr_as_names_force force ids x)
  | l ->
     if List.exists (fun (b,ids) -> !b) l & (force or
	 List.exists (fun (_,ids) -> ids <> (snd (List.hd l))) (List.tl l))
      then 
        if nodup then begin
          msgerrnl
            (h 0 (str "Translator warning: Unable to enforce v7 names while translating Induction/NewDestruct/NewInduction. Names in the different branches are") ++ brk (0,0) ++
            hov 0 (prlist_with_sep spc
              (fun id -> hov 0 (pr_as_names_force true ids id))
              (List.rev l)));
          pr (pr_as_names_force force ids (ref false,[]))
        end
        else
          pr_seq_body (fun x -> pr (pr_as_names_force force ids x)) (List.rev l)
      else pr (pr_as_names_force force ids (ref false,[]))

let pr_hintbases = function
  | None -> spc () ++ str "with *"
  | Some [] -> mt ()
  | Some l ->
      spc () ++ hov 2 (str "with" ++ prlist (fun s -> spc () ++ str s) l)

let pr_autoarg_adding = function
  | [] -> mt ()
  | l ->
      spc () ++ str "adding [" ++
        hv 0 (prlist_with_sep spc pr_reference l) ++ str "]"

let pr_autoarg_destructing = function
  | true -> spc () ++ str "destructing"
  | false -> mt ()

let pr_autoarg_usingTDB = function
  | true -> spc () ++ str "using tdb"
  | false -> mt ()

let rec pr_tacarg_using_rule pr_gen = function
  | Egrammar.TacTerm s :: l, al -> spc () ++ str s ++ pr_tacarg_using_rule pr_gen (l,al)
  | Egrammar.TacNonTerm _ :: l, a :: al -> pr_gen a ++ pr_tacarg_using_rule pr_gen (l,al)
  | [], [] -> mt ()
  | _ -> failwith "Inconsistent arguments of extended tactic"

let pr_then () = str ";"


open Closure

let make_pr_tac (pr_tac,pr_tac0,pr_constr,pr_lconstr,pr_pat,pr_cst,pr_ind,pr_ref,pr_ident,pr_extend,strip_prod_binders) =

let pr_bindings env = pr_bindings (pr_lconstr env) (pr_constr env) in
let pr_ex_bindings env = pr_bindings_gen true (pr_lconstr env) (pr_constr env) in
let pr_with_bindings env = pr_with_bindings (pr_lconstr env) (pr_constr env) in
let pr_eliminator env cb = str "using" ++ pr_arg (pr_with_bindings env) cb in
let pr_constrarg env c = spc () ++ pr_constr env c in
let pr_lconstrarg env c = spc () ++ pr_lconstr env c in

let pr_intarg n = spc () ++ int n in

let pr_binder_fix env (nal,t) =
(*  match t with
  | CHole _ -> spc() ++ prlist_with_sep spc (pr_lname) nal
  | _ ->*)
    let s =
      prlist_with_sep spc (pr_lname) nal ++ str ":" ++
      pr_lconstr env t in
    spc() ++ hov 1 (str"(" ++ s ++ str")") in

let pr_fix_tac env (id,n,c) =
  let rec set_nth_name avoid n = function
      (nal,ty)::bll ->
        if n <= List.length nal then
          match list_chop (n-1) nal with
              _, (_,Name id) :: _ -> id, (nal,ty)::bll
            | bef, (loc,Anonymous) :: aft ->
                let id = next_ident_away_from (id_of_string"y") avoid in
                id, ((bef@(loc,Name id)::aft, ty)::bll)
            | _ -> assert false
        else
          let (id,bll') = set_nth_name avoid (n-List.length nal) bll in
          (id,(nal,ty)::bll')
    | [] -> assert false in
  let (bll,ty) = strip_prod_binders n c in
  let names =
    List.fold_left
      (fun ln (nal,_) -> List.fold_left
          (fun ln na -> match na with (_,Name id) -> id::ln | _ -> ln)
          ln nal)
      [] bll in
  let idarg,bll = set_nth_name names n bll in
  let annot =
    if List.length names = 1 then mt()
    else spc() ++ str"{struct " ++ pr_id idarg ++ str"}" in
  hov 1 (str"(" ++ pr_id id ++ 
        prlist (pr_binder_fix env) bll ++ annot ++ str" :" ++
        pr_lconstrarg env ty ++ str")") in
(*  spc() ++
  hov 0 (pr_id id ++ pr_intarg n ++ str":" ++ pr_constrarg
    env c)
*)
let pr_cofix_tac env (id,c) =
  hov 1 (str"(" ++ pr_id id ++ str" :" ++ pr_lconstrarg env c ++ str")") in


  (* Printing tactics as arguments *)
let rec pr_atom0 env = function
  | TacIntroPattern [] -> str "intros"
  | TacIntroMove (None,None) -> str "intro"
  | TacAssumption -> str "assumption"
  | TacAnyConstructor None -> str "constructor"
  | TacTrivial (Some []) -> str "trivial"
  | TacAuto (None,Some []) -> str "auto"
(*  | TacAutoTDB None -> str "autotdb"
  | TacDestructConcl -> str "dconcl"*)
  | TacReflexivity -> str "reflexivity"
  | t -> str "(" ++ pr_atom1 env t ++ str ")"

  (* Main tactic printer *)
and pr_atom1 env = function
  | TacAutoTDB _ | TacDestructHyp _ | TacDestructConcl
  | TacSuperAuto _ | TacExtend (_,
    ("GTauto"|"GIntuition"|"TSimplif"|
     "LinearIntuition"),_) ->
      errorlabstrm "Obsolete V8" (str "Tactic is not ported to V8.0")
  | TacExtend (loc,s,l) ->
      pr_with_comments loc
        (pr_extend (pr_constr env) (pr_lconstr env) (pr_tac env) s l)
  | TacAlias (loc,s,l,_) ->
      pr_with_comments loc
        (pr_extend (pr_constr env) (pr_lconstr env) (pr_tac env) s
          (List.map snd l))

  (* Basic tactics *)
  | TacIntroPattern [] as t -> pr_atom0 env t
  | TacIntroPattern (_::_ as p) -> 
      hov 1 (str "intros" ++ spc () ++ prlist_with_sep spc pr_intro_pattern p)
  | TacIntrosUntil h ->
      hv 1 (str "intros until" ++ pr_arg pr_quantified_hypothesis h)
  | TacIntroMove (None,None) as t -> pr_atom0 env t
  | TacIntroMove (Some id1,None) -> str "intro " ++ pr_id id1
  | TacIntroMove (ido1,Some id2) ->
      hov 1
      (str "intro" ++ pr_opt pr_id ido1 ++ spc () ++ str "after " ++
       pr_lident id2)
  | TacAssumption as t -> pr_atom0 env t
  | TacExact c -> hov 1 (str "exact" ++ pr_constrarg env c)
  | TacApply cb -> hov 1 (str "apply" ++ spc () ++ pr_with_bindings env cb)
  | TacElim (cb,cbo) ->
      hov 1 (str "elim" ++ pr_arg (pr_with_bindings env) cb ++ 
        pr_opt (pr_eliminator env) cbo)
  | TacElimType c -> hov 1 (str "elimtype" ++ pr_constrarg env c)
  | TacCase cb -> hov 1 (str "case" ++ spc () ++ pr_with_bindings env cb)
  | TacCaseType c -> hov 1 (str "casetype" ++ pr_constrarg env c)
  | TacFix (ido,n) -> hov 1 (str "fix" ++ pr_opt pr_id ido ++ pr_intarg n)
  | TacMutualFix (id,n,l) ->
      hov 1 (str "fix" ++ spc () ++ pr_id id ++ pr_intarg n ++ spc() ++
             str"with " ++ prlist_with_sep spc (pr_fix_tac env) l)
  | TacCofix ido -> hov 1 (str "cofix" ++ pr_opt pr_id ido)
  | TacMutualCofix (id,l) ->
      hov 1 (str "cofix" ++ spc () ++ pr_id id ++ spc() ++
             str"with " ++ prlist_with_sep spc (pr_cofix_tac env) l)
  | TacCut c -> hov 1 (str "cut" ++ pr_constrarg env c)
  | TacTrueCut (Anonymous,c) -> 
      hov 1 (str "assert" ++ pr_constrarg env c)
  | TacTrueCut (Name id,c) -> 
      hov 1 (str "assert" ++ spc () ++
             hov 1 (str"(" ++ pr_id id ++ str " :" ++
                    pr_lconstrarg env c ++ str")"))
  | TacForward (false,na,c) ->
      hov 1 (str "assert" ++ spc () ++
             hov 1 (str"(" ++ pr_name na ++ str " :=" ++
                    pr_lconstrarg env c ++ str")"))
  | TacForward (true,Anonymous,c) ->
      if Options.do_translate () then
        (* Pose was buggy and was wrongly substituted in conclusion in v7 *)
        hov 1 (str "set" ++ pr_constrarg env c)
      else
        hov 1 (str "pose" ++ pr_constrarg env c)
  | TacForward (true,Name id,c) ->
      if Options.do_translate () then
      hov 1 (str "set" ++ spc() ++
             hov 1 (str"(" ++ pr_id id ++ str " :=" ++
                    pr_lconstrarg env c ++ str")"))
      else
      hov 1 (str "pose" ++ spc() ++
             hov 1 (str"(" ++ pr_id id ++ str " :=" ++
                    pr_lconstrarg env c ++ str")"))
  | TacGeneralize l ->
      hov 1 (str "generalize" ++ spc () ++
             prlist_with_sep spc (pr_constr env) l)
  | TacGeneralizeDep c ->
      hov 1 (str "generalize" ++ spc () ++ str "dependent" ++
             pr_constrarg env c)
  | TacLetTac (Anonymous,c,cl) ->
      hov 1 (str "set" ++ pr_constrarg env c) ++ pr_clauses pr_ident cl
  | TacLetTac (Name id,c,cl) ->
      hov 1 (str "set" ++ spc () ++
             hov 1 (str"(" ++ pr_id id ++ str " :=" ++
                    pr_lconstrarg env c ++ str")") ++
             pr_clauses pr_ident cl)
  | TacInstantiate (n,c,cls) ->
      hov 1 (str "instantiate" ++ spc() ++
             hov 1 (str"(" ++ pr_arg int n ++ str" :=" ++
                    pr_lconstrarg env c ++ str ")" ++ 
		    pr_clauses pr_ident cls))
  (* Derived basic tactics *)
  | TacSimpleInduction (h,l) ->
      if List.exists (fun (pp,_) -> !pp) !l then
        duplicate true true None (fun pnames -> 
          hov 1 (str "induction" ++ pr_arg pr_quantified_hypothesis h ++
          pnames)) !l
      else
      hov 1 (str "simple induction" ++ pr_arg pr_quantified_hypothesis h)
  | TacNewInduction (h,e,(ids,l)) ->
      duplicate false true ids (fun pnames ->
      hov 1 (str "induction" ++ spc () ++
             pr_induction_arg (pr_constr env) h ++ pnames ++
             pr_opt (pr_eliminator env) e)) !l
  | TacSimpleDestruct h ->
      hov 1 (str "simple destruct" ++ pr_arg pr_quantified_hypothesis h)
  | TacNewDestruct (h,e,(ids,l)) ->
      duplicate false true ids (fun pnames ->
      hov 1 (str "destruct" ++ spc () ++
             pr_induction_arg (pr_constr env) h ++ pnames ++
             pr_opt (pr_eliminator env) e)) !l
  | TacDoubleInduction (h1,h2) ->
      hov 1
        (str "double induction" ++  
         pr_arg pr_quantified_hypothesis h1 ++
 	 pr_arg pr_quantified_hypothesis h2)
  | TacDecomposeAnd c ->
      hov 1 (str "decompose record" ++ pr_constrarg env c)
  | TacDecomposeOr c ->
      hov 1 (str "decompose sum" ++ pr_constrarg env c)
  | TacDecompose (l,c) ->
      let vars = Termops.vars_of_env env in
      hov 1 (str "decompose" ++ spc () ++
        hov 0 (str "[" ++ prlist_with_sep spc (pr_ind vars) l
	  ++ str "]" ++ pr_constrarg env c))
  | TacSpecialize (n,c) ->
      hov 1 (str "specialize" ++ spc () ++ pr_opt int n ++ pr_with_bindings env c)
  | TacLApply c -> 
      hov 1 (str "lapply" ++ pr_constrarg env c)

  (* Automation tactics *)
  | TacTrivial (Some []) as x -> pr_atom0 env x
  | TacTrivial db -> hov 0 (str "trivial" ++ pr_hintbases db)
  | TacAuto (None,Some []) as x -> pr_atom0 env x
  | TacAuto (n,db) -> hov 0 (str "auto" ++ pr_opt int n ++ pr_hintbases db)
(*  | TacAutoTDB None as x -> pr_atom0 env x
  | TacAutoTDB (Some n) -> hov 0 (str "autotdb" ++ spc () ++ int n)
  | TacDestructHyp (true,id) ->
      hov 0 (str "cdhyp" ++ spc () ++ pr_lident id)
  | TacDestructHyp (false,id) ->
      hov 0 (str "dhyp" ++ spc () ++ pr_lident id)
  | TacDestructConcl as x -> pr_atom0 env x
  | TacSuperAuto (n,l,b1,b2) ->
      hov 1 (str "superauto" ++ pr_opt int n ++ pr_autoarg_adding l ++ 
             pr_autoarg_destructing b1 ++ pr_autoarg_usingTDB b2)*)
  | TacDAuto (n,p) ->
      hov 1 (str "auto" ++ pr_opt int n ++ str "decomp" ++ pr_opt int p)

  (* Context management *)
  | TacClear l ->
      hov 1 (str "clear" ++ spc () ++ prlist_with_sep spc pr_ident l)
  | TacClearBody l ->
      hov 1 (str "clearbody" ++ spc () ++ prlist_with_sep spc pr_ident l)
  | TacMove (b,id1,id2) ->
      (* Rem: only b = true is available for users *)
      assert b;
      hov 1
        (str "move" ++ brk (1,1) ++ pr_ident id1 ++ spc () ++ 
	 str "after" ++ brk (1,1) ++ pr_ident id2)
  | TacRename (id1,id2) ->
      hov 1
        (str "rename" ++ brk (1,1) ++ pr_ident id1 ++ spc () ++ 
	 str "into" ++ brk (1,1) ++ pr_ident id2)

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
      hov 1 (pr_red_expr (pr_constr env,pr_lconstr env,pr_cst env) r ++
             pr_clauses pr_ident h)
  | TacChange (occ,c,h) ->
      hov 1 (str "change" ++ brk (1,1) ++
      (match occ with
          None -> mt()
        | Some([],c1) ->
            hov 1 (pr_constr env c1 ++ spc() ++ str "with ")
        | Some(ocl,c1) ->
            hov 1 (pr_constr env c1 ++ spc() ++
	           str "at " ++ prlist_with_sep spc int ocl) ++ spc() ++
	           str "with ") ++
      pr_constr env c ++ pr_clauses pr_ident h)

  (* Equivalence relations *)
  | TacReflexivity as x -> pr_atom0 env x
  | TacSymmetry cls -> str "symmetry " ++ pr_clauses pr_ident cls
  | TacTransitivity c -> str "transitivity" ++ pr_constrarg env c

  (* Equality and inversion *)
  | TacInversion (DepInversion (k,c,ids),hyp) ->
      hov 1 (str "dependent " ++ pr_induction_kind k ++ spc () ++
      pr_quantified_hypothesis hyp ++
      pr_with_names ids ++ pr_with_constr (pr_constr env) c)
  | TacInversion (NonDepInversion (k,cl,ids),hyp) ->
      hov 1 (pr_induction_kind k ++ spc () ++
      pr_quantified_hypothesis hyp ++
      pr_with_names ids ++ pr_simple_clause pr_ident cl)
  | TacInversion (InversionUsing (c,cl),hyp) ->
      hov 1 (str "inversion" ++ spc() ++ pr_quantified_hypothesis hyp ++ 
      spc () ++ str "using" ++ spc () ++ pr_constr env c ++ 
      pr_simple_clause pr_ident cl)

in

let ltop = (5,E) in
let lseq = 5 in
let ltactical = 3 in
let lorelse = 2 in
let llet = 1 in
let lfun = 1 in
let labstract = 3 in
let lmatch = 1 in
let latom = 0 in
let lcall = 1 in
let leval = 1 in
let ltatom = 1 in

let rec pr_tac env inherited tac =
  let (strm,prec) = match tac with
  | TacAbstract (t,None) ->
      str "abstract " ++ pr_tac env (labstract,L) t, labstract
  | TacAbstract (t,Some s) -> 
      hov 0
       (str "abstract (" ++ pr_tac env (labstract,L) t ++ str")" ++ spc () ++
        str "using " ++ pr_id s),
      labstract
  | TacLetRecIn (l,t) -> 
      hv 0
        (str "let rec " ++ pr_rec_clauses (pr_tac env ltop) l ++ str " in" ++
         fnl () ++ pr_tac env (llet,E) t),
      llet
  | TacLetIn (llc,u) ->
      v 0
       (hv 0 (pr_let_clauses (pr_tac env ltop) llc
       ++ str " in") ++
       fnl () ++ pr_tac env (llet,E) u),
      llet
  | TacMatch (t,lrul) ->
      hov 0 (str "match " ++ pr_tac env ltop t ++ str " with"
        ++ prlist
	  (fun r -> fnl () ++ str "| " ++
            pr_match_rule true (pr_tac env ltop) pr_pat r)
	lrul
        ++ fnl() ++ str "end"),
      lmatch
  | TacMatchContext (lr,lrul) ->
      hov 0 (
	str (if lr then "match reverse goal with" else "match goal with")
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
      hov 1 (pr_tac env (lseq,E) t ++ pr_then () ++ spc () ++
             pr_seq_body (pr_tac env ltop) tl),
      lseq
  | TacThen (t1,t2) ->
      let pp2 =
        (* Hook for translation names in induction/destruct *)
        match t2 with
          | TacAtom (_,TacSimpleInduction (h,l)) ->
              if List.exists (fun (pp,ids) -> !pp) !l then
                duplicate true false None (fun pnames ->
                  hov 1 
                  (str "induction" ++ pr_arg pr_quantified_hypothesis h ++
                  pnames)) !l
              else
                hov 1
                  (str "simple induction" ++ pr_arg pr_quantified_hypothesis h)
          | TacAtom (_,TacNewInduction (h,e,(ids,l))) ->
              duplicate false false ids (fun pnames -> 
                hov 1 (str "induction" ++ spc () ++
                pr_induction_arg (pr_constr env) h ++ pnames ++
                pr_opt (pr_eliminator env) e)) !l
          | TacAtom (_,TacNewDestruct (h,e,(ids,l))) ->
              duplicate false false ids (fun pnames ->
                hov 1 (str "destruct" ++ spc () ++
                pr_induction_arg (pr_constr env) h ++ pnames ++
                pr_opt (pr_eliminator env) e)) !l
              (* end hook *)
          | _ -> pr_tac env (lseq,L) t2 in
      hov 1 (pr_tac env (lseq,E) t1 ++ pr_then () ++ spc () ++ pp2),
      lseq
  | TacTry t ->
      hov 1 (str "try" ++ spc () ++ pr_tac env (ltactical,E) t),
      ltactical
  | TacDo (n,t) ->
      hov 1 (str "do " ++ pr_or_var int n ++ spc () ++ pr_tac env (ltactical,E) t),
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
  | TacFail (ArgArg 0,"") -> str "fail", latom
  | TacFail (n,s) -> 
      str "fail" ++ (if n=ArgArg 0 then mt () else pr_arg (pr_or_var int) n) ++
      (if s="" then mt() else qsnew s), latom
  | TacFirst tl ->
      str "first" ++ spc () ++ pr_seq_body (pr_tac env ltop) tl, llet
  | TacSolve tl ->
      str "solve" ++ spc () ++ pr_seq_body (pr_tac env ltop) tl, llet
  | TacId "" -> str "idtac", latom
  | TacId s -> str "idtac" ++ (qsnew s), latom
  | TacAtom (loc,t) ->
      pr_with_comments loc (hov 1 (pr_atom1 env t)), ltatom
  | TacArg(Tacexp e) -> pr_tac0 env e, latom
  | TacArg(ConstrMayEval (ConstrTerm c)) ->
      str "constr:" ++ pr_constr env c, latom
  | TacArg(ConstrMayEval c) ->
      pr_may_eval (pr_constr env) (pr_lconstr env) (pr_cst env) c, leval
  | TacArg(TacFreshId sopt) -> str "fresh" ++ pr_opt qsnew sopt, latom
  | TacArg(Integer n) -> int n, latom
  | TacArg(TacCall(loc,f,l)) ->
      pr_with_comments loc
        (hov 1 (pr_ref f ++ spc () ++
         prlist_with_sep spc (pr_tacarg env) l)),
      lcall
  | TacArg a -> pr_tacarg env a, latom
  in
  if prec_less prec inherited then strm
  else str"(" ++ strm ++ str")"

and pr_tacarg env = function
  | TacDynamic (loc,t) ->
      pr_with_comments loc (str ("<dynamic ["^(Dyn.tag t)^"]>"))
  | MetaIdArg (loc,s) -> pr_with_comments loc (str ("$" ^ s))
  | IntroPattern ipat -> str "ipattern:" ++ pr_intro_pattern ipat
  | TacVoid -> str "()"
  | Reference r -> pr_ref r
  | ConstrMayEval c ->
      pr_may_eval (pr_constr env) (pr_lconstr env) (pr_cst env) c
  | TacFreshId sopt -> str "fresh" ++ pr_opt qsnew sopt
  | (TacCall _|Tacexp _|Integer _) as a ->
      str "ltac:" ++ pr_tac env (latom,E) (TacArg a)

in ((fun env -> pr_tac env ltop),
    (fun env -> pr_tac env (latom,E)),
    pr_match_rule)

let pi1 (a,_,_) = a
let pi2 (_,a,_) = a
let pi3 (_,_,a) = a

let strip_prod_binders_rawterm n (ty,_) =
  let rec strip_ty acc n ty =
    if n=0 then (List.rev acc, (ty,None)) else
      match ty with
          Rawterm.RProd(loc,na,a,b) ->
            strip_ty (([dummy_loc,na],(a,None))::acc) (n-1) b
        | _ -> error "Cannot translate fix tactic: not enough products" in
  strip_ty [] n ty

let strip_prod_binders_constr n ty =
  let rec strip_ty acc n ty =
    if n=0 then (List.rev acc, ty) else
      match Term.kind_of_term ty with
          Term.Prod(na,a,b) ->
            strip_ty (([dummy_loc,na],a)::acc) (n-1) b
        | _ -> error "Cannot translate fix tactic: not enough products" in
  strip_ty [] n ty


let rec raw_printers =
    (pr_raw_tactic, 
     pr_raw_tactic0,
     Ppconstrnew.pr_constr_env,
     Ppconstrnew.pr_lconstr_env,
     Ppconstrnew.pr_pattern,
     (fun _ -> pr_reference),
     (fun _ -> pr_reference),
     pr_reference,
     pr_or_metaid pr_lident,
     Pptactic.pr_raw_extend,
     strip_prod_binders_expr)

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
     (fun env -> pr_and_constr_expr (Ppconstrnew.pr_rawconstr_env_no_translate env)),
     (fun env -> pr_and_constr_expr (Ppconstrnew.pr_lrawconstr_env_no_translate env)),
     (fun c -> Ppconstrnew.pr_constr_pattern_env (Global.env()) c),
     (fun env -> pr_or_var (pr_and_short_name (pr_evaluable_reference_env env))),
     (fun vars -> pr_or_var (pr_inductive vars)),
     pr_ltac_or_var (pr_located pr_ltac_constant),
     pr_lident,
     Pptactic.pr_glob_extend,
     strip_prod_binders_rawterm)

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
     pr_term_env,
     pr_lterm_env,
     Ppconstrnew.pr_constr_pattern,
     pr_evaluable_reference_env,
     pr_inductive,
     pr_ltac_constant,
     pr_id,
     Pptactic.pr_extend,
     strip_prod_binders_constr)

