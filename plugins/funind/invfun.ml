(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ltac_plugin
open Declarations
open CErrors
open Util
open Names
open Term
open Constr
open Context
open EConstr
open Vars
open Pp
open Globnames
open Tacticals.New
open Tactics
open Indfun_common
open Tacmach.New
open Tactypes
open Termops
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration

module PN = Proofview.Notations
module PG = Proofview.Goal

let observe_tac = Indfun_common.observe_tac ~header:Pp.(str "invfun")

let thin ids = Tactics.clear ids

(* (\* [id_to_constr id] finds the term associated to [id] in the global environment *\) *)
(* let id_to_constr id = *)
(*   try *)
(*     Constrintern.global_reference id *)
(*   with Not_found -> *)
(*     raise (UserError ("",str "Cannot find " ++ Ppconstr.pr_id id)) *)


let make_eq () =
  try
    EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref "core.eq.type"))
  with _ -> assert false

(* [generate_type g_to_f f graph i] build the completeness (resp. correctness) lemma type if [g_to_f = true]
   (resp. g_to_f = false) where [graph]  is the graph of [f] and is the [i]th function in the block.

   [generate_type true f i] returns
   \[\forall (x_1:t_1)\ldots(x_n:t_n), let fv := f x_1\ldots x_n in, forall res,
   graph\ x_1\ldots x_n\ res \rightarrow res = fv \] decomposed as the context and the conclusion

   [generate_type false f i] returns
   \[\forall (x_1:t_1)\ldots(x_n:t_n), let fv := f x_1\ldots x_n in, forall res,
   res = fv \rightarrow graph\ x_1\ldots x_n\ res\] decomposed as the context and the conclusion
*)

let generate_type evd g_to_f f graph i =
  (*i we deduce the number of arguments of the function and its returned type from the graph i*)
  let evd',graph =
    Evd.fresh_global  (Global.env ()) !evd  (Globnames.IndRef (fst (destInd !evd graph)))
  in
  evd:=evd';
  let sigma, graph_arity = Typing.type_of (Global.env ()) !evd graph in
  evd := sigma;
  let ctxt,_ = decompose_prod_assum !evd graph_arity in
  let fun_ctxt,res_type =
    match ctxt with
    | [] | [_] -> anomaly (Pp.str "Not a valid context.")
    | decl :: fun_ctxt -> fun_ctxt, RelDecl.get_type decl
  in
  let rec args_from_decl i accu = function
    | [] -> accu
    | LocalDef _ :: l ->
      args_from_decl (succ i) accu l
    | _ :: l ->
      let t = mkRel i in
      args_from_decl (succ i) (t :: accu) l
  in
  (*i We need to name the vars [res] and [fv] i*)
  let filter = fun decl -> match RelDecl.get_name decl with
    | Name id -> Some id
    | Anonymous -> None
  in
  let named_ctxt = Id.Set.of_list (List.map_filter filter fun_ctxt) in
  let res_id = Namegen.next_ident_away_in_goal (Id.of_string "_res") named_ctxt in
  let fv_id = Namegen.next_ident_away_in_goal (Id.of_string "fv") (Id.Set.add res_id named_ctxt) in
  (*i we can then type the argument to be applied to the function [f] i*)
  let args_as_rels = Array.of_list (args_from_decl 1 [] fun_ctxt) in
  (*i
    the hypothesis [res = fv] can then be computed
    We will need to lift it by one in order to use it as a conclusion
    i*)
  let make_eq = make_eq ()
  in
  let res_eq_f_of_args =
    mkApp(make_eq ,[|lift 2 res_type;mkRel 1;mkRel 2|])
  in
  (*i
    The hypothesis [graph\ x_1\ldots x_n\ res] can then be computed
    We will need to lift it by one in order to use it as a conclusion
    i*)
  let args_and_res_as_rels = Array.of_list (args_from_decl 3 [] fun_ctxt) in
  let args_and_res_as_rels = Array.append args_and_res_as_rels [|mkRel 1|] in
  let graph_applied = mkApp(graph, args_and_res_as_rels) in
  (*i The [pre_context]  is the defined to be the context corresponding to
    \[\forall (x_1:t_1)\ldots(x_n:t_n), let fv := f x_1\ldots x_n in, forall res,  \]
    i*)
  let pre_ctxt =
    LocalAssum (make_annot (Name res_id) Sorts.Relevant, lift 1 res_type) ::
    LocalDef (make_annot (Name fv_id) Sorts.Relevant, mkApp (f,args_as_rels), res_type) :: fun_ctxt
  in
  (*i and we can return the solution depending on which lemma type we are defining i*)
  if g_to_f
  then LocalAssum (make_annot Anonymous Sorts.Relevant,graph_applied)::pre_ctxt,(lift 1 res_eq_f_of_args),graph
  else LocalAssum (make_annot Anonymous Sorts.Relevant,res_eq_f_of_args)::pre_ctxt,(lift 1 graph_applied),graph


(*
   [find_induction_principle f] searches and returns the [body] and the [type] of [f_rect]

   WARNING: while convertible, [type_of body] and [type] can be non equal
*)
let find_induction_principle evd f =
  let f_as_constant,u =  match EConstr.kind !evd f with
    | Const c' -> c'
    | _ -> user_err Pp.(str "Must be used with a function")
  in
  let infos = find_Function_infos f_as_constant in
  match infos.rect_lemma with
  | None -> raise Not_found
  | Some rect_lemma ->
    let evd',rect_lemma = Evd.fresh_global  (Global.env ()) !evd  (Globnames.ConstRef rect_lemma) in
    let evd',typ = Typing.type_of ~refresh:true (Global.env ()) evd' rect_lemma in
    evd:=evd';
    rect_lemma,typ


let rec generate_fresh_id x avoid i =
  if i == 0
  then []
  else
    let id = Namegen.next_ident_away_in_goal x (Id.Set.of_list avoid) in
    id::(generate_fresh_id x (id::avoid) (pred i))


(* [prove_fun_correct funs_constr graphs_constr schemes lemmas_types_infos i ]
   is the tactic used to prove correctness lemma.

   [funs_constr], [graphs_constr] [schemes] [lemmas_types_infos] are the mutually recursive functions
   (resp. graphs of the functions and principles and correctness lemma types) to prove correct.

   [i] is the indice of the function to prove correct

   The lemma to prove if suppose to have been generated by [generate_type] (in $\zeta$ normal form that is
   it looks like~:
   [\forall (x_1:t_1)\ldots(x_n:t_n), forall res,
   res = f x_1\ldots x_n in, \rightarrow graph\ x_1\ldots x_n\ res]


   The sketch of the proof is the following one~:
   \begin{enumerate}
   \item intros until $x_n$
   \item $functional\ induction\ (f.(i)\ x_1\ldots x_n)$ using schemes.(i)
   \item for each generated branch intro [res] and [hres :res = f x_1\ldots x_n], rewrite [hres] and the
   apply the corresponding constructor of the corresponding graph inductive.
   \end{enumerate}

*)
let prove_fun_correct evd funs_constr graphs_constr schemes lemmas_types_infos i =
  (* first of all we recreate the lemmas types to be used as predicates of the induction principle
       that is~:
       \[fun (x_1:t_1)\ldots(x_n:t_n)=> fun  fv => fun res => res = fv \rightarrow graph\ x_1\ldots x_n\ res\]
  *)
  (* we the get the definition of the graphs block *)
  PG.enter begin fun gl ->
    let graph_ind,u = destInd evd graphs_constr.(i) in
    let kn = fst graph_ind in
    let mib,_ = Global.lookup_inductive graph_ind in
    (* and the principle to use in this lemma in $\zeta$ normal form *)
    let f_principle,princ_type = schemes.(i) in
    let princ_type = Reductionops.nf_zeta (Global.env ()) evd princ_type in
    let princ_infos = Tactics.compute_elim_sig evd princ_type in
    (* The number of args of the function is then easily computable *)
    let nb_fun_args = nb_prod (project gl) (pf_concl gl) - 2 in
    let args_names = generate_fresh_id (Id.of_string "x") [] nb_fun_args in
    let ids = args_names@(pf_ids_of_hyps gl) in
    (* Since we cannot ensure that the functional principle is defined in the
       environment and due to the bug #1174, we will need to pose the principle
       using a name
    *)
    let principle_id = Namegen.next_ident_away_in_goal (Id.of_string "princ") (Id.Set.of_list ids) in
    let ids = principle_id :: ids in
    (* We get the branches of the principle *)
    let branches = List.rev princ_infos.branches in
    (* and built the intro pattern for each of them *)
    let intro_pats =
      List.map
        (fun decl ->
           List.map
             (fun id -> CAst.make @@ IntroNaming (Namegen.IntroIdentifier id))
             (generate_fresh_id (Id.of_string "y") ids (List.length (fst (decompose_prod_assum evd (RelDecl.get_type decl)))))
        )
        branches
    in
    (* before building the full intro pattern for the principle *)
    let eq_ind = make_eq () in
    let eq_construct = mkConstructUi (destInd evd eq_ind, 1) in
    (* The next to referencies will be used to find out which constructor to apply in each branch *)
    let ind_number = ref 0
    and min_constr_number = ref 0 in
    (* The tactic to prove the ith branch of the principle *)
    let prove_branche i =
      (* We get the identifiers of this branch *)
      let pre_args =
        List.fold_right
          (fun {CAst.v=pat} acc ->
             match pat with
             | IntroNaming (Namegen.IntroIdentifier id) -> id::acc
             | _ -> anomaly (Pp.str "Not an identifier.")
          )
          (List.nth intro_pats (pred i))
          []
      in
      (* and get the real args of the branch by unfolding the defined constant *)
      (*
         We can then recompute the arguments of the constructor.
         For each [hid] introduced by this branch, if [hid] has type
         $forall res, res=fv -> graph.(j)\ x_1\ x_n res$ the corresponding arguments of the constructor are
         [ fv (hid fv (refl_equal fv)) ].
         If [hid] has another type the corresponding argument of the constructor is [hid]
      *)
      let constructor_args gl =
        List.fold_right
          (fun hid acc ->
             let type_of_hid = pf_unsafe_type_of gl (mkVar hid) in
             let sigma = project gl in
             match EConstr.kind sigma type_of_hid with
             | Prod(_,_,t') ->
               begin
                 match EConstr.kind sigma t' with
                 | Prod(_,t'',t''') ->
                   begin
                     match EConstr.kind sigma t'',EConstr.kind sigma t''' with
                     | App(eq,args), App(graph',_)
                       when
                         (EConstr.eq_constr sigma eq eq_ind) &&
                         Array.exists  (EConstr.eq_constr_nounivs sigma graph') graphs_constr ->
                       (args.(2)::(mkApp(mkVar hid,[|args.(2);(mkApp(eq_construct,[|args.(0);args.(2)|]))|]))
                        ::acc)
                     | _ -> mkVar hid ::  acc
                   end
                 | _ -> mkVar hid :: acc
               end
             | _ -> mkVar hid :: acc
          ) pre_args []
      in
      (* in fact we must also add the parameters to the constructor args *)
      let constructor_args gl =
        let params_id = fst (List.chop princ_infos.nparams args_names) in
        (List.map mkVar params_id)@(constructor_args gl)
      in
      (* We then get the constructor corresponding to this branch and
         modifies the references has needed i.e.
         if the constructor is the last one of the current inductive then
         add one the number of the inductive to take and add the number of constructor of the previous
         graph to the minimal constructor number
      *)
      let constructor =
        let constructor_num = i - !min_constr_number in
        let length = Array.length (mib.Declarations.mind_packets.(!ind_number).Declarations.mind_consnames) in
        if constructor_num <= length
        then
          begin
            (kn,!ind_number),constructor_num
          end
        else
          begin
            incr ind_number;
            min_constr_number := !min_constr_number + length ;
            (kn,!ind_number),1
          end
      in
      (* we can then build the final proof term *)
      let app_constructor gl = applist((mkConstructU(constructor,u)),constructor_args gl) in
      (* an apply the tactic *)
      let res,hres =
        match generate_fresh_id (Id.of_string "z") (ids(* @this_branche_ids *)) 2 with
        | [res;hres] -> res,hres
        | _ -> assert false
      in
      (* observe (str "constructor := " ++ Printer.pr_lconstr_env (pf_env g) app_constructor); *)
      (
        tclTHENLIST
          [ observe_tac (fun _ _ -> Pp.str "h_intro_patterns ")
              (let l = (List.nth intro_pats (pred i)) in
               match l with
               | [] -> tclIDTAC
               | _ -> intro_patterns false l
              )
          ; (* unfolding of all the defined variables introduced by this branch *)
            (* observe_tac "unfolding" pre_tac; *)
            (* $zeta$ normalizing of the conclusion *)
            reduce
              (Genredexpr.Cbv
                 { Redops.all_flags with
                   Genredexpr.rDelta = false
                 ; Genredexpr.rConst = []
                 }
              )
              Locusops.onConcl
          ; observe_tac (fun _ _ -> Pp.str "toto ") tclIDTAC
          ; (* introducing the result of the graph and the equality hypothesis *)
            observe_tac (fun _ _ -> Pp.str "introducing") ((tclMAP Simple.intro) [res;hres])
          ; (* replacing [res] with its value *)
            observe_tac (fun _ _ -> Pp.str "rewriting res value") (Equality.rewriteLR (mkVar hres))
          ; (* Conclusion *)
            observe_tac (fun _ _ -> Pp.str "exact") (PG.enter (fun gl -> exact_check (app_constructor gl)))
          ]
      )
    in
    (* end of branche proof *)
    let lemmas =
      Array.map
        (fun ((_,(ctxt,concl))) ->
           match ctxt with
           | [] | [_] | [_;_] -> anomaly (Pp.str "bad context.")
           | hres::res::decl::ctxt ->
             let res = EConstr.it_mkLambda_or_LetIn
                 (EConstr.it_mkProd_or_LetIn concl [hres;res])
                 (LocalAssum (RelDecl.get_annot decl, RelDecl.get_type decl) :: ctxt)
             in
             res)
        lemmas_types_infos
    in
    let param_names = fst (List.chop princ_infos.nparams args_names) in
    let params = List.map mkVar param_names in
    let lemmas = Array.to_list (Array.map (fun c -> applist(c,params)) lemmas) in
    (* The bindings of the principle
       that is the params of the principle and the different lemma types
    *)
    let bindings gl =
      let params_bindings,avoid =
        List.fold_left2
          (fun (bindings,avoid) decl p ->
             let id = Namegen.next_ident_away (Nameops.Name.get_id (RelDecl.get_name decl)) (Id.Set.of_list avoid) in
             p::bindings,id::avoid
          )
          ([],pf_ids_of_hyps gl)
          princ_infos.params
          (List.rev params)
      in
      let lemmas_bindings gl =
        List.rev (fst  (List.fold_left2
                          (fun (bindings,avoid) decl p ->
                             let id = Namegen.next_ident_away (Nameops.Name.get_id (RelDecl.get_name decl)) (Id.Set.of_list avoid) in
                             (Reductionops.nf_zeta (pf_env gl) (project gl) p)::bindings,id::avoid)
                          ([],avoid)
                          princ_infos.predicates
                          (lemmas)))
      in
      (params_bindings@lemmas_bindings gl)
    in
    tclTHENLIST
      [ observe_tac (fun _ _ -> Pp.str "principle")
          (assert_by
             (Name principle_id)
             princ_type
             (exact_check f_principle))
      ; observe_tac (fun _ _ -> Pp.str "intro args_names")
          (tclMAP (fun id -> (Simple.intro id)) args_names)
      ; (* observe_tac "titi" (pose_proof (Name (Id.of_string "__")) (Reductionops.nf_beta Evd.empty  ((mkApp (mkVar principle_id,Array.of_list bindings))))); *)
        observe_tac (fun _ _ -> Pp.str "idtac") tclIDTAC;
        tclTHEN_i
          (observe_tac
             (fun _ _ -> Pp.str "functional_induction")
             (PG.enter (fun gl ->
                  let term = mkApp (mkVar principle_id,Array.of_list (bindings gl)) in
                  let _gl', _ty = pf_eapply (Typing.type_of ~refresh:true) gl term in
                  apply term
                )
             )
          )
          (fun i -> observe_tac (fun _ _ -> Pp.(str "proving branche " ++ int i)) (prove_branche i))
      ]
  end

(* [generalize_dependent_of x hyp g]
   generalize every hypothesis which depends of [x] but [hyp]
*)
let generalize_dependent_of x hyp =
  let open Context.Named.Declaration in
  PG.(enter begin fun gl ->
      tclMAP
        (function
          | LocalAssum ({binder_name=id},t)
            when not (Id.equal id hyp) &&
                 (Termops.occur_var (pf_env gl) (project gl) x t) ->
            tclTHEN (Tactics.generalize [mkVar id]) (thin [id])
          | _ -> tclIDTAC
        )
        (hyps gl) end
    )

(* [intros_with_rewrite] do the intros in each branch and treat each new hypothesis
       (unfolding, substituting, destructing cases \ldots)
*)
let tauto =
  let dp = List.map Id.of_string ["Tauto" ; "Init"; "Coq"] in
  let mp = ModPath.MPfile (DirPath.make dp) in
  let kn = KerName.make mp (Label.make "tauto") in
  let body = Tacenv.interp_ltac kn in
  Tacinterp.eval_tactic body

let rec intros_with_rewrite () = observe_tac Pp.(fun _ _ -> str "intros_with_rewrite") (intros_with_rewrite_aux ())
and intros_with_rewrite_aux () =
  let eq_ind = make_eq () in
  PG.enter begin fun gl ->
    let sigma = project gl in
    match EConstr.kind sigma (pf_concl gl) with
    | Prod(_,t,t') ->
      begin
        match EConstr.kind sigma t with
        | App(eq,args) when (EConstr.eq_constr sigma eq eq_ind)  ->
          if Reductionops.is_conv (pf_env gl) (project gl) args.(1) args.(2)
          then
            let id = pf_get_new_id (Id.of_string "y") gl in
            tclTHENLIST
              [ Simple.intro id
              ; thin [id]
              ; intros_with_rewrite ()
              ]
          else if isVar sigma args.(1) && (Environ.evaluable_named (destVar sigma args.(1)) (pf_env gl))
          then tclTHENLIST
              [ unfold_in_concl [(Locus.AllOccurrences, Names.EvalVarRef (destVar sigma args.(1)))]
              ; tclMAP (fun id -> tclTRY(unfold_in_hyp [(Locus.AllOccurrences, Names.EvalVarRef (destVar sigma args.(1)))]
                                           ((destVar sigma args.(1)),Locus.InHyp)))
                  (pf_ids_of_hyps gl)
              ; intros_with_rewrite ()
              ]
          else if isVar sigma args.(2) && (Environ.evaluable_named (destVar sigma args.(2)) (pf_env gl))
          then tclTHENLIST
              [ unfold_in_concl [(Locus.AllOccurrences, Names.EvalVarRef (destVar sigma args.(2)))]
              ; tclMAP (fun id -> tclTRY
                           (unfold_in_hyp [(Locus.AllOccurrences, Names.EvalVarRef (destVar sigma args.(2)))] ((destVar sigma args.(2)),Locus.InHyp)))
                  (pf_ids_of_hyps gl)
              ; intros_with_rewrite ()
              ]
          else if isVar sigma args.(1)
          then
            let id = pf_get_new_id (Id.of_string "y") gl in
            tclTHENLIST [ Simple.intro id
                        ; generalize_dependent_of (destVar sigma args.(1)) id
                        ; tclTRY (Equality.rewriteLR (mkVar id))
                        ; intros_with_rewrite ()
                        ]
          else if isVar sigma args.(2)
          then
            let id = pf_get_new_id (Id.of_string "y") gl  in
            tclTHENLIST [ Simple.intro id
                        ; generalize_dependent_of (destVar sigma args.(2)) id
                        ; tclTRY (Equality.rewriteRL (mkVar id))
                        ; intros_with_rewrite ()
                        ]
          else
            begin
              let id = pf_get_new_id (Id.of_string "y") gl  in
              tclTHENLIST
                [ Simple.intro id
                ; tclTRY (Equality.rewriteLR (mkVar id))
                ; intros_with_rewrite ()
                ]
            end
        | Ind _ when EConstr.eq_constr sigma t (EConstr.of_constr (UnivGen.constr_of_monomorphic_global @@ Coqlib.lib_ref "core.False.type")) ->
          tauto
        | Case(_,_,v,_) ->
          tclTHENLIST
            [ simplest_case v
            ; intros_with_rewrite ()
            ]
        | LetIn _ ->
          tclTHENLIST
            [ reduce (Genredexpr.Cbv
                        {Redops.all_flags
                         with Genredexpr.rDelta = false;
                        })
                Locusops.onConcl
            ; intros_with_rewrite ()
            ]
        | _ ->
          let id = pf_get_new_id (Id.of_string "y") gl in
          tclTHENLIST
            [ Simple.intro id
            ; intros_with_rewrite ()
            ]
      end
    | LetIn _ ->
      tclTHENLIST
        [ reduce (Genredexpr.Cbv { Redops.all_flags with Genredexpr.rDelta = false; }) Locusops.onConcl
        ; intros_with_rewrite ()
        ]
    | _ -> tclIDTAC
  end

let rec reflexivity_with_destruct_cases () =
  let destruct_case () =
    try
      PG.enter begin fun gl ->
        match EConstr.kind (project gl) (snd (destApp (project gl) (pf_concl gl))).(2) with
        | Case(_,_,v,_) ->
          tclTHENLIST
            [ simplest_case v
            ; intros
            ; observe_tac Pp.(fun _ _ -> str "reflexivity_with_destruct_cases") (reflexivity_with_destruct_cases ())
            ]
        | _ -> reflexivity
      end
    with e when CErrors.noncritical e -> reflexivity
  in
  let eq_ind = make_eq () in
  let my_inj_flags = Some {
      Equality.keep_proof_equalities = false;
      injection_in_context = false; (* for compatibility, necessary *)
      injection_pattern_l2r_order = false; (* probably does not matter; except maybe with dependent hyps *)
    } in
  let discr_inject =
    (* XXX missing *)
    Tacticals.New.onAllHypsAndConcl (
      fun sc ->
        PG.enter (fun gl ->
        match sc with
          None -> tclIDTAC
        | Some id ->
          match EConstr.kind (project gl) (pf_unsafe_type_of gl (mkVar id)) with
          | App(eq,[|_;t1;t2|]) when EConstr.eq_constr (project gl) eq eq_ind ->
            if Equality.discriminable (pf_env gl) (project gl) t1 t2
            then Equality.discrHyp id
            else if Equality.injectable (pf_env gl) (project gl) ~keep_proofs:None t1 t2
            then tclTHENLIST [Equality.injHyp my_inj_flags None id; thin [id]; intros_with_rewrite ()]
            else tclIDTAC
          | _ -> tclIDTAC
          )
    )
  in
  (tclFIRST
     [ observe_tac (fun _ _ -> Pp.str "reflexivity_with_destruct_cases : reflexivity") reflexivity
     ; observe_tac (fun _ _ -> Pp.str "reflexivity_with_destruct_cases : destruct_case") (destruct_case ())
     ; (*  We reach this point ONLY if
           the same value is matched (at least) two times
           along binding path.
           In this case, either we have a discriminable hypothesis and we are done,
           either at least an injectable one and we do the injection before continuing
       *)
       observe_tac (fun _ _ -> Pp.str "reflexivity_with_destruct_cases : others")
         (tclTHEN (tclPROGRESS discr_inject ) (reflexivity_with_destruct_cases ()))
     ])

(* [prove_fun_complete funs graphs schemes lemmas_types_infos i]
   is the tactic used to prove completeness lemma.

   [funcs], [graphs] [schemes] [lemmas_types_infos] are the mutually recursive functions
   (resp. definitions of the graphs of the functions, principles and correctness lemma types) to prove correct.

   [i] is the indice of the function to prove complete

   The lemma to prove if suppose to have been generated by [generate_type] (in $\zeta$ normal form that is
   it looks like~:
   [\forall (x_1:t_1)\ldots(x_n:t_n), forall res,
   graph\ x_1\ldots x_n\ res, \rightarrow  res = f x_1\ldots x_n in]


   The sketch of the proof is the following one~:
   \begin{enumerate}
   \item intros until $H:graph\ x_1\ldots x_n\ res$
   \item $elim\ H$ using schemes.(i)
   \item for each generated branch, intro  the news hyptohesis, for each such hyptohesis [h], if [h] has
   type [x=?] with [x] a variable, then subst [x],
   if [h] has type [t=?] with [t] not a variable then rewrite [t] in the subterms, else
   if [h] is a match then destruct it, else do just introduce it,
   after all intros, the conclusion should be a reflexive equality.
   \end{enumerate}

*)

let prove_fun_complete funcs graphs schemes lemmas_types_infos i =
  (* We compute the types of the different mutually recursive lemmas
     in $\zeta$ normal form
  *)
  PG.enter (fun gl ->
  let lemmas =
    Array.map
      (fun (_,(ctxt,concl)) -> Reductionops.nf_zeta (pf_env gl) (project gl) (EConstr.it_mkLambda_or_LetIn concl ctxt))
      lemmas_types_infos
  in
  (* We get the constant and the principle corresponding to this lemma *)
  let f = funcs.(i) in
  let graph_principle = Reductionops.nf_zeta (pf_env gl) (project gl) (EConstr.of_constr schemes.(i))  in
  let princ_type = pf_unsafe_type_of gl graph_principle in
  let princ_infos = Tactics.compute_elim_sig (project gl) princ_type in
  (* Then we get the number of argument of the function
     and compute a fresh name for each of them
  *)
  let nb_fun_args = nb_prod (project gl) (pf_concl gl) - 2 in
  let args_names = generate_fresh_id (Id.of_string "x") [] nb_fun_args in
  let ids = args_names@(pf_ids_of_hyps gl) in
  (* and fresh names for res H and the principle (cf bug bug #1174) *)
  let res,hres,graph_principle_id =
    match generate_fresh_id (Id.of_string "z") ids 3 with
    | [res;hres;graph_principle_id] -> res,hres,graph_principle_id
    | _ -> assert false
  in
  let ids = res::hres::graph_principle_id::ids in
  (* we also compute fresh names for each hyptohesis of each branch
     of the principle *)
  let branches = List.rev princ_infos.branches in
  let intro_pats =
    List.map
      (fun decl ->
         List.map
           (fun id -> id)
           (generate_fresh_id (Id.of_string "y") ids (nb_prod (project gl) (RelDecl.get_type decl)))
      )
      branches
  in
  (* We will need to change the function by its body
     using [f_equation] if it is recursive (that is the graph is infinite
     or unfold if the graph is finite
  *)
  let rewrite_tac j ids =
    let graph_def = graphs.(j) in
    let infos =
      try find_Function_infos (fst (destConst (project gl) funcs.(j)))
      with Not_found ->  user_err Pp.(str "No graph found")
    in
    if infos.is_general
    || Rtree.is_infinite Declareops.eq_recarg graph_def.mind_recargs
    then
      let eq_lemma =
        try Option.get (infos).equation_lemma
        with Option.IsNone -> anomaly (Pp.str "Cannot find equation lemma.")
      in
      tclTHENLIST
        [ tclMAP (fun id -> Simple.intro id) ids
        ; Equality.rewriteLR (mkConst eq_lemma)
        ; (* Don't forget to $\zeta$ normlize the term since the principles
             have been $\zeta$-normalized *)
          reduce
            (Genredexpr.Cbv
               { Redops.all_flags with
                 Genredexpr.rDelta = false
               })
            Locusops.onConcl
        ; generalize (List.map mkVar ids)
        ; thin ids
        ]
    else
      unfold_in_concl [(Locus.AllOccurrences, Names.EvalConstRef (fst (destConst (project gl) f)))]
  in
  (* The proof of each branche itself *)
  let ind_number = ref 0 in
  let min_constr_number = ref 0 in
  let prove_branche i =
    (* we fist compute the inductive corresponding to the branch *)
    let this_ind_number =
      let constructor_num = i - !min_constr_number in
      let length = Array.length (graphs.(!ind_number).Declarations.mind_consnames) in
      if constructor_num <= length
      then !ind_number
      else
        begin
          incr ind_number;
          min_constr_number := !min_constr_number + length;
          !ind_number
        end
    in
    let this_branche_ids = List.nth intro_pats (pred i) in
    tclTHENLIST[
      (* we expand the definition of the function *)
      observe_tac (fun _ _ -> Pp.str "rewrite_tac") (rewrite_tac this_ind_number this_branche_ids);
      (* introduce hypothesis with some rewrite *)
      observe_tac (fun _ _ -> Pp.str "intros_with_rewrite (all)") (intros_with_rewrite ());
      (* The proof is (almost) complete *)
      observe_tac (fun _ _ -> Pp.str "reflexivity") (reflexivity_with_destruct_cases ())
    ]
  in
  let params_names = fst (List.chop princ_infos.nparams args_names) in
  let open EConstr in
  let params = List.map mkVar params_names in
  tclTHENLIST
    [ tclMAP (fun id -> Simple.intro id) (args_names@[res;hres])
    ; observe_tac (fun _ _ -> Pp.str "h_generalize")
        (generalize [mkApp(applist(graph_principle,params),Array.map (fun c -> applist(c,params)) lemmas)])
    ; Simple.intro graph_principle_id
    ; observe_tac (fun _ _ -> Pp.mt ())
        (tclTHEN_i
           (observe_tac (fun _ _ -> Pp.str "elim") (elim false None (mkVar hres,NoBindings) (Some (mkVar graph_principle_id,NoBindings))))
           (fun i -> observe_tac (fun _ _ -> Pp.str "prove_branche") (prove_branche i)))
    ]
    )

(* [derive_correctness make_scheme funs graphs] create correctness and completeness
   lemmas for each function in [funs] w.r.t. [graphs]

   [make_scheme] is Functional_principle_types.make_scheme (dependency pb) and
*)

let derive_correctness make_scheme (funs: pconstant list) (graphs:inductive list) =
  assert (funs <> []);
  assert (graphs <> []);
  let funs = Array.of_list funs and graphs = Array.of_list graphs in
  let map (c, u) = mkConstU (c, EInstance.make u) in
  let funs_constr = Array.map map funs  in
  (* XXX STATE Why do we need this... why is the toplevel protection not enough *)
  funind_purify
    (fun () ->
       let env = Global.env () in
       let evd = ref (Evd.from_env env) in
       let graphs_constr = Array.map mkInd graphs in
       let lemmas_types_infos =
         Util.Array.map2_i
           (fun i f_constr graph ->
              (* let const_of_f,u = destConst f_constr in *)
              let (type_of_lemma_ctxt,type_of_lemma_concl,graph) =
                generate_type evd false f_constr graph i
              in
              let type_info = (type_of_lemma_ctxt,type_of_lemma_concl) in
              graphs_constr.(i) <- graph;
              let type_of_lemma = EConstr.it_mkProd_or_LetIn type_of_lemma_concl type_of_lemma_ctxt in
              let sigma, _ = Typing.type_of (Global.env ()) !evd type_of_lemma in
              evd := sigma;
              let type_of_lemma = Reductionops.nf_zeta (Global.env ()) !evd type_of_lemma in
              observe (str "type_of_lemma := " ++ Printer.pr_leconstr_env (Global.env ()) !evd type_of_lemma);
              type_of_lemma,type_info
           )
           funs_constr
           graphs_constr
       in
       let schemes =
         (* The functional induction schemes are computed and not saved if there is more that one function
            if the block contains only one function we can safely reuse [f_rect]
         *)
         try
           if not (Int.equal (Array.length funs_constr) 1) then raise Not_found;
           [| find_induction_principle evd funs_constr.(0) |]
         with Not_found ->
           (

             Array.of_list
               (List.map
                  (fun entry ->
                     (EConstr.of_constr (fst (fst(Future.force entry.Entries.const_entry_body))), EConstr.of_constr (Option.get entry.Entries.const_entry_type ))
                  )
                  (make_scheme evd (Array.map_to_list (fun const -> const,Sorts.InType) funs))
               )
           )
       in
       let proving_tac =
         prove_fun_correct !evd funs_constr graphs_constr schemes lemmas_types_infos
       in
       Array.iteri
         (fun i f_as_constant ->
            let f_id = Label.to_id (Constant.label (fst f_as_constant)) in
            (*i The next call to mk_correct_id is valid since we are constructing the lemma
                Ensures by: obvious
              i*)
            let lem_id = mk_correct_id f_id in
            let (typ,_) = lemmas_types_infos.(i) in
            let lemma = Lemmas.start_lemma
                lem_id
                Decl_kinds.(Global ImportDefaultBehavior,false,Proof Theorem)
                !evd
                typ in
            let lemma = fst @@ Lemmas.by
                (observe_tac (fun _ _ -> Pp.(str "prove correctness (" ++ Id.print f_id ++ str ")"))
                   (proving_tac i)) lemma in
            let () = Lemmas.save_lemma_proved ?proof:None ~lemma ~opaque:Proof_global.Transparent ~idopt:None in
            let finfo = find_Function_infos (fst f_as_constant) in
            (* let lem_cst = fst (destConst (Constrintern.global_reference lem_id)) in *)
            let _,lem_cst_constr = Evd.fresh_global
                (Global.env ()) !evd (Constrintern.locate_reference (Libnames.qualid_of_ident lem_id)) in
            let (lem_cst,_) = destConst !evd lem_cst_constr in
            update_Function {finfo with correctness_lemma = Some lem_cst};

         )
         funs;
       let lemmas_types_infos =
         Util.Array.map2_i
           (fun i f_constr graph ->
              let (type_of_lemma_ctxt,type_of_lemma_concl,graph)   =
                generate_type evd true f_constr graph i
              in
              let type_info = (type_of_lemma_ctxt,type_of_lemma_concl) in
              graphs_constr.(i) <- graph;
              let type_of_lemma =
                EConstr.it_mkProd_or_LetIn type_of_lemma_concl type_of_lemma_ctxt
              in
              let type_of_lemma = Reductionops.nf_zeta env !evd type_of_lemma in
              observe (str "type_of_lemma := " ++ Printer.pr_leconstr_env env !evd type_of_lemma);
              type_of_lemma,type_info
           )
           funs_constr
           graphs_constr
       in

       let (kn,_) as graph_ind,u  = (destInd !evd graphs_constr.(0)) in
       let mib,mip = Global.lookup_inductive graph_ind in
       let sigma, scheme =
         (Indrec.build_mutual_induction_scheme (Global.env ()) !evd
            (Array.to_list
               (Array.mapi
                  (fun i _ -> ((kn,i), EInstance.kind !evd u),true,InType)
                  mib.Declarations.mind_packets
               )
            )
         )
       in
       let schemes =
         Array.of_list scheme
       in
       let proving_tac =
         prove_fun_complete funs_constr mib.Declarations.mind_packets schemes lemmas_types_infos
       in
       Array.iteri
         (fun i f_as_constant ->
            let f_id = Label.to_id (Constant.label (fst f_as_constant)) in
            (*i The next call to mk_complete_id is valid since we are constructing the lemma
                Ensures by: obvious
              i*)
            let lem_id = mk_complete_id f_id in
            let lemma = Lemmas.start_lemma lem_id
                Decl_kinds.(Global ImportDefaultBehavior,false,Proof Theorem) sigma
                (fst lemmas_types_infos.(i)) in
            let lemma = fst (Lemmas.by
                               (observe_tac (fun _ _ -> Pp.(str "prove completeness (" ++ Id.print f_id ++ str ")"))
                                  (proving_tac i)) lemma) in
            let () = Lemmas.save_lemma_proved ?proof:None ~lemma ~opaque:Proof_global.Transparent ~idopt:None in
            let finfo = find_Function_infos (fst f_as_constant) in
            let _,lem_cst_constr = Evd.fresh_global
                (Global.env ()) !evd (Constrintern.locate_reference (Libnames.qualid_of_ident lem_id)) in
            let (lem_cst,_) = destConst !evd lem_cst_constr in
            update_Function {finfo with completeness_lemma = Some lem_cst}
         )
         funs)
    ()

(***********************************************)

(* [revert_graph kn post_tac hid] transforme an hypothesis [hid] having type Ind(kn,num) t1 ... tn res
   when [kn] denotes a graph block  into
   f_num t1... tn = res (by applying [f_complete] to the first type) before apply post_tac on the result

   if the type of hypothesis has not this form or if we cannot find the completeness lemma then we do nothing
*)
let revert_graph kn post_tac hid =
  PG.enter (fun gl ->
  let sigma = project gl in
  let typ = pf_unsafe_type_of gl (mkVar hid) in
  match EConstr.kind sigma typ with
  | App(i,args) when isInd sigma i ->
    let ((kn',num) as ind'),u = destInd sigma i in
    if MutInd.equal kn kn'
    then (* We have generated a graph hypothesis so that we must change it if we can *)
      let info =
        try find_Function_of_graph ind'
        with Not_found -> (* The graphs are mutually recursive but we cannot find one of them !*)
          anomaly (Pp.str "Cannot retrieve infos about a mutual block.")
      in
      (* if we can find a completeness lemma for this function
         then we can come back to the functional form. If not, we do nothing
      *)
      match info.completeness_lemma with
      | None -> tclIDTAC
      | Some f_complete ->
        let f_args,res = Array.chop (Array.length args - 1) args in
        tclTHENLIST
          [ generalize [applist(mkConst f_complete,(Array.to_list f_args)@[res.(0);mkVar hid])]
          ; thin [hid]
          ; Simple.intro hid
          ; post_tac hid
          ]
    else tclIDTAC
  | _ -> tclIDTAC
  )

(*
   [functional_inversion hid fconst f_correct ] is the functional version of [inversion]

   [hid] is the hypothesis to invert, [fconst] is the function to invert and  [f_correct]
   is the correctness lemma for [fconst].

   The sketch is the following~:
   \begin{enumerate}
   \item Transforms the hypothesis [hid] such that its type is now $res\ =\ f\ t_1 \ldots t_n$
   (fails if it is not possible)
   \item replace [hid] with $R\_f t_1 \ldots t_n res$ using [f_correct]
   \item apply [inversion] on [hid]
   \item finally in each branch, replace each  hypothesis [R\_f ..]  by [f ...] using [f_complete] (whenever
   such a lemma exists)
   \end{enumerate}
*)

let functional_inversion kn hid fconst f_correct =
  PG.enter (fun gl ->
  let old_ids = List.fold_right Id.Set.add  (pf_ids_of_hyps gl) Id.Set.empty in
  let sigma = project gl in
  let type_of_h = pf_unsafe_type_of gl (mkVar hid) in
  match EConstr.kind sigma type_of_h with
  | App(eq,args) when EConstr.eq_constr sigma eq (make_eq ())  ->
    let pre_tac,f_args,res =
      match EConstr.kind sigma args.(1),EConstr.kind sigma args.(2) with
      | App(f,f_args),_ when EConstr.eq_constr sigma f fconst ->
        ((fun hid -> intros_symmetry (Locusops.onHyp hid))),f_args,args.(2)
      |_,App(f,f_args) when EConstr.eq_constr sigma f fconst ->
        ((fun hid -> tclIDTAC),f_args,args.(1))
      | _ -> (fun hid -> tclFAIL 1 (mt ())),[||],args.(2)
    in
    tclTHENLIST
      [ PN.(
            generalize [applist(f_correct,(Array.to_list f_args)@[res;mkVar hid])] >>= fun () ->
            pre_tac hid)
      ; thin [hid]
      ; Simple.intro hid
      ; Inv.inv Inv.FullInversion None (NamedHyp hid)
      ; PG.enter (fun gl ->
            let new_ids = List.filter (fun id -> not (Id.Set.mem id old_ids)) (pf_ids_of_hyps gl) in
            tclMAP (revert_graph kn pre_tac)  (hid::new_ids)
          )
      ]
  | _ -> tclFAIL 1 (mt ())
  )

let error msg = user_err Pp.(str msg)

let invfun qhyp f  =
  let f =
    match f with
    | ConstRef f -> f
    | _ -> raise (CErrors.UserError(None,str "Not a function"))
  in
  try
    let finfos = find_Function_infos f in
    let f_correct = mkConst(Option.get finfos.correctness_lemma)
    and kn = fst finfos.graph_ind
    in
    Tactics.try_intros_until (fun hid -> functional_inversion kn hid (mkConst f) f_correct) qhyp
  with
  | Not_found ->  error "No graph found"
  | Option.IsNone  -> error "Cannot use equivalence with graph!"

exception NoFunction

let invfun qhyp f =
  match f with
  | Some f -> invfun qhyp f
  | None ->
    Tactics.try_intros_until
      (fun hid -> PG.enter begin fun g ->
           let sigma = project g in
           let hyp_typ = pf_unsafe_type_of g (mkVar hid)  in
           match EConstr.kind sigma hyp_typ with
           | App(eq,args) when EConstr.eq_constr sigma eq (make_eq ()) ->
             begin
               let f1,_ = decompose_app sigma args.(1) in
               try
                 if not (isConst sigma f1) then raise NoFunction;
                 let finfos = find_Function_infos (fst (destConst sigma f1)) in
                 let f_correct = mkConst(Option.get finfos.correctness_lemma)
                 and kn = fst finfos.graph_ind
                 in
                 functional_inversion kn hid f1 f_correct
               with | NoFunction | Option.IsNone | Not_found ->
               try
                 let f2,_ = decompose_app sigma args.(2) in
                 if not (isConst sigma f2) then raise NoFunction;
                 let finfos = find_Function_infos (fst (destConst sigma f2)) in
                 let f_correct = mkConst(Option.get finfos.correctness_lemma)
                 and kn = fst finfos.graph_ind
                 in
                 functional_inversion kn hid  f2 f_correct
               with
               | NoFunction ->
                 user_err  (str "Hypothesis " ++ Ppconstr.pr_id hid ++ str " must contain at least one Function")
               | Option.IsNone  ->
                 if do_observe ()
                 then
                   error "Cannot use equivalence with graph for any side of the equality"
                 else user_err  (str "Cannot find inversion information for hypothesis " ++ Ppconstr.pr_id hid)
               | Not_found ->
                 if do_observe ()
                 then
                   error "No graph found for any side of equality"
                 else user_err  (str "Cannot find inversion information for hypothesis " ++ Ppconstr.pr_id hid)
             end
           | _ -> user_err  (Ppconstr.pr_id hid ++ str " must be an equality ")
         end)
      qhyp
