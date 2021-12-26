(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module CVars = Vars
open Constr
open Context
open EConstr
open Vars
open Namegen
open Environ
open Pp
open Names
open Libnames
open Globnames
open Nameops
open CErrors
open Util
open UnivGen
open Tacticals
open Tactics
open Nametab
open Tacred
open Glob_term
open Pretyping
open Termops
open Constrintern
open Tactypes
open Genredexpr
open Equality
open Auto
open Eauto
open Indfun_common
open Context.Rel.Declaration

(* Ugly things which should not be here *)

let coq_constant s =
  EConstr.of_constr @@ UnivGen.constr_of_monomorphic_global (Global.env ()) @@ Coqlib.lib_ref s

let coq_init_constant s =
  EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Global.env ()) @@ Coqlib.lib_ref s)

let find_reference sl s =
  let dp = Names.DirPath.make (List.rev_map Id.of_string sl) in
  locate (make_qualid dp (Id.of_string s))

let declare_fun name kind ?univs value =
  let ce = Declare.definition_entry ?univs value (*FIXME *) in
  GlobRef.ConstRef
    (Declare.declare_constant ~name ~kind (Declare.DefinitionEntry ce))

let defined lemma =
  let (_ : _ list) =
    Declare.Proof.save_regular ~proof:lemma ~opaque:Vernacexpr.Transparent
      ~idopt:None
  in
  ()

let def_of_const t =
  match Constr.kind t with
  | Const sp -> (
    try
      match constant_opt_value_in (Global.env ()) sp with
      | Some c -> c
      | _ -> raise Not_found
    with Not_found ->
      anomaly
        ( str "Cannot find definition of constant "
        ++ Id.print (Label.to_id (Constant.label (fst sp)))
        ++ str "." ) )
  | _ -> assert false

let type_of_const env sigma t =
  match EConstr.kind sigma t with
  | Const (sp, u) ->
    let u = EInstance.kind sigma u in
    (* FIXME discarding universe constraints *)
    Typeops.type_of_constant_in env (sp, u)
  | _ -> assert false

let constant sl s = UnivGen.constr_of_monomorphic_global (Global.env ()) (find_reference sl s)

let const_of_ref = function
  | GlobRef.ConstRef kn -> kn
  | _ -> anomaly (Pp.str "ConstRef expected.")

(* Generic values *)
let pf_get_new_ids idl g =
  let ids = Tacmach.pf_ids_of_hyps g in
  let ids = Id.Set.of_list ids in
  List.fold_right
    (fun id acc ->
      next_global_ident_away id (Id.Set.union (Id.Set.of_list acc) ids) :: acc)
    idl []

let next_ident_away_in_goal ids avoid =
  next_ident_away_in_goal (Global.env ()) ids (Id.Set.of_list avoid)

let compute_renamed_type gls id =
  let t = Tacmach.pf_get_hyp_typ id gls in
  if Clenv.rename_with () then
    rename_bound_vars_as_displayed (Global.env ()) (Proofview.Goal.sigma gls)
      (*no avoid*) Id.Set.empty (*no rels*) []
      t
  else
    t

let h'_id = Id.of_string "h'"
let teq_id = Id.of_string "teq"
let ano_id = Id.of_string "anonymous"
let x_id = Id.of_string "x"
let k_id = Id.of_string "k"
let v_id = Id.of_string "v"
let def_id = Id.of_string "def"
let p_id = Id.of_string "p"
let rec_res_id = Id.of_string "rec_res"
let lt = function () -> coq_init_constant "num.nat.lt"
let le = function () -> Coqlib.lib_ref "num.nat.le"
let ex = function () -> coq_init_constant "core.ex.type"
let nat = function () -> coq_init_constant "num.nat.type"

let iter_ref () =
  try find_reference ["Recdef"] "iter"
  with Not_found -> user_err Pp.(str "Module Recdef not loaded.")

let iter_rd = function
  | () -> constr_of_monomorphic_global (Global.env ()) (delayed_force iter_ref)

let eq = function () -> coq_init_constant "core.eq.type"
let le_lt_SS = function () -> constant ["Recdef"] "le_lt_SS"
let le_lt_n_Sm = function () -> coq_constant "num.nat.le_lt_n_Sm"
let le_trans = function () -> coq_constant "num.nat.le_trans"
let le_lt_trans = function () -> coq_constant "num.nat.le_lt_trans"
let lt_S_n = function () -> coq_constant "num.nat.lt_S_n"
let le_n = function () -> coq_init_constant "num.nat.le_n"

let coq_sig_ref = function
  | () -> find_reference ["Coq"; "Init"; "Specif"] "sig"

let coq_O = function () -> coq_init_constant "num.nat.O"
let coq_S = function () -> coq_init_constant "num.nat.S"
let lt_n_O = function () -> coq_constant "num.nat.nlt_0_r"
let max_ref = function () -> find_reference ["Recdef"] "max"

let max_constr = function
  | () ->
    EConstr.of_constr (constr_of_monomorphic_global (Global.env ()) (delayed_force max_ref))

let f_S t = mkApp (delayed_force coq_S, [|t|])

let rec n_x_id ids n =
  if Int.equal n 0 then []
  else
    let x = next_ident_away_in_goal x_id ids in
    x :: n_x_id (x :: ids) (n - 1)

let simpl_iter clause =
  reduce
    (Lazy
       { rBeta = true
       ; rMatch = true
       ; rFix = true
       ; rCofix = true
       ; rZeta = true
       ; rDelta = false
       ; rConst = [EvalConstRef (const_of_ref (delayed_force iter_ref))] })
    clause

(* Others ugly things ... *)
let (value_f : Constr.t list -> GlobRef.t -> Constr.t) =
  let open Term in
  let open Constr in
  fun al fterm ->
    let rev_x_id_l =
      List.fold_left
        (fun x_id_l _ ->
          let x_id = next_ident_away_in_goal x_id x_id_l in
          x_id :: x_id_l)
        [] al
    in
    let context =
      List.map
        (fun (x, c) -> LocalAssum (make_annot (Name x) Sorts.Relevant, c))
        (List.combine rev_x_id_l (List.rev al))
    in
    let env = Environ.push_rel_context context (Global.env ()) in
    let glob_body =
      DAst.make
      @@ GCases
           ( RegularStyle
           , None
           , [ ( DAst.make
                 @@ GApp
                      ( DAst.make @@ GRef (fterm, None)
                      , List.rev_map
                          (fun x_id -> DAst.make @@ GVar x_id)
                          rev_x_id_l )
               , (Anonymous, None) ) ]
           , [ CAst.make
                 ( [v_id]
                 , [ DAst.make
                     @@ PatCstr
                          ( (destIndRef (delayed_force coq_sig_ref), 1)
                          , [ DAst.make @@ PatVar (Name v_id)
                            ; DAst.make @@ PatVar Anonymous ]
                          , Anonymous ) ]
                 , DAst.make @@ GVar v_id ) ] )
    in
    let body = fst (understand env (Evd.from_env env) glob_body) (*FIXME*) in
    let body = EConstr.Unsafe.to_constr body in
    it_mkLambda_or_LetIn body context

let (declare_f :
      Id.t -> Decls.logical_kind -> Constr.t list -> GlobRef.t -> GlobRef.t) =
 fun f_id kind input_type fterm_ref ->
  declare_fun f_id kind (value_f input_type fterm_ref)

module New = struct
  open Tacticals

  let observe_tac = New.observe_tac ~header:(Pp.mt ())

  let observe_tclTHENLIST s tacl =
    if do_observe () then
      let rec aux n = function
        | [] -> tclIDTAC
        | [tac] ->
          observe_tac (fun env sigma -> s env sigma ++ spc () ++ int n) tac
        | tac :: tacl ->
          observe_tac
            (fun env sigma -> s env sigma ++ spc () ++ int n)
            (tclTHEN tac (aux (succ n) tacl))
      in
      aux 0 tacl
    else tclTHENLIST tacl
end

(* Conclusion tactics *)

(* The boolean value is_mes expresses that the termination is expressed
  using a measure function instead of a well-founded relation. *)
let tclUSER tac is_mes l =
  let open Tacticals in
  let clear_tac =
    match l with
    | None -> tclIDTAC
    | Some l -> tclMAP (fun id -> tclTRY (clear [id])) (List.rev l)
  in
  New.observe_tclTHENLIST
    (fun _ _ -> str "tclUSER1")
    [ clear_tac
    ; ( if is_mes then
        New.observe_tclTHENLIST
          (fun _ _ -> str "tclUSER2")
          [ unfold_in_concl
              [ ( Locus.AllOccurrences
                , evaluable_of_global_reference
                    (delayed_force Indfun_common.ltof_ref) ) ]
          ; tac ]
      else tac ) ]

let tclUSER_if_not_mes concl_tac is_mes names_to_suppress =
  if is_mes then
    Tacticals.tclCOMPLETE (Simple.apply (delayed_force well_founded_ltof))
  else
    (* tclTHEN (Simple.apply (delayed_force acc_intro_generator_function) ) *)
    tclUSER concl_tac is_mes names_to_suppress

(* Traveling term.
   Both definitions of [f_terminate] and [f_equation] use the same generic
   traveling mechanism.
*)

(* [check_not_nested forbidden e] checks that [e] does not contains any variable
   of [forbidden]
*)
let check_not_nested env sigma forbidden e =
  let rec check_not_nested e =
    match EConstr.kind sigma e with
    | Rel _ -> ()
    | Int _ | Float _ -> ()
    | Var x ->
      if Id.List.mem x forbidden then
        user_err
          (str "check_not_nested: failure " ++ Id.print x ++ str ".")
    | Meta _ | Evar _ | Sort _ -> ()
    | Cast (e, _, t) -> check_not_nested e; check_not_nested t
    | Prod (_, t, b) -> check_not_nested t; check_not_nested b
    | Lambda (_, t, b) -> check_not_nested t; check_not_nested b
    | LetIn (_, v, t, b) ->
      check_not_nested t; check_not_nested b; check_not_nested v
    | App (f, l) -> check_not_nested f
    | Array (_u, t, def, ty) ->
      Array.iter check_not_nested t;
      check_not_nested def;
      check_not_nested ty
    | Proj (p, c) -> check_not_nested c
    | Const _ -> ()
    | Ind _ -> ()
    | Construct _ -> ()
    | Case (_, _, pms, (_, t), _, e, a) ->
      Array.iter check_not_nested pms;
      check_not_nested t;
      check_not_nested e;
      Array.iter (fun (_, c) -> check_not_nested c) a
    | Fix _ -> user_err Pp.(str "check_not_nested : Fix")
    | CoFix _ -> user_err Pp.(str "check_not_nested : Fix")
  in
  try check_not_nested e
  with UserError p ->
    user_err
      (str "on expr : " ++ Printer.pr_leconstr_env env sigma e ++ str " " ++ p ++ str ".")

(* ['a info] contains the local information for traveling *)
type 'a infos =
  { nb_arg : int
  ; (* function number of arguments *)
    concl_tac : unit Proofview.tactic
  ; (* final tactic to finish proofs *)
    rec_arg_id : Id.t
  ; (*name of the declared recursive argument *)
    is_mes : bool
  ; (* type of recursion *)
    ih : Id.t
  ; (* induction hypothesis name *)
    f_id : Id.t
  ; (* function name *)
    f_constr : constr
  ; (* function term *)
    f_terminate : constr
  ; (* termination proof term *)
    func : GlobRef.t
  ; (* functional reference *)
    info : 'a
  ; is_main_branch : bool
  ; (* on the main branch or on a matched expression *)
    is_final : bool
  ; (* final first order term or not *)
    values_and_bounds : (Id.t * Id.t) list
  ; eqs : Id.t list
  ; forbidden_ids : Id.t list
  ; acc_inv : constr lazy_t
  ; acc_id : Id.t
  ; args_assoc : (constr list * constr) list }

type ('a, 'b) journey_info_tac =
     'a
  -> (* the arguments of the constructor *)
     'b infos
  -> (* infos of the caller *)
     ('b infos -> unit Proofview.tactic)
  -> (* the continuation tactic of the caller *)
     'b infos
  -> (* argument of the tactic *)
     unit Proofview.tactic

(* journey_info : specifies the actions to do on the different term constructors during the traveling of the term
*)
type journey_info =
  { letiN : (Name.t * constr * types * constr, constr) journey_info_tac
  ; lambdA : (Name.t * types * constr, constr) journey_info_tac
  ; casE :
         (   (constr infos -> unit Proofview.tactic)
          -> constr infos
          -> unit Proofview.tactic)
      -> ( case_info
           * constr
           * case_invert
           * constr
           * constr array
         , constr )
         journey_info_tac
  ; otherS : (unit, constr) journey_info_tac
  ; apP : (constr * constr list, constr) journey_info_tac
  ; app_reC : (constr * constr list, constr) journey_info_tac
  ; message : string }

let add_vars sigma forbidden e =
  let rec aux forbidden e =
    match EConstr.kind sigma e with
    | Var x -> x :: forbidden
    | _ -> EConstr.fold sigma aux forbidden e
  in
  aux forbidden e

let treat_case forbid_new_ids to_intros finalize_tac nb_lam e infos :
    unit Proofview.tactic =
  Proofview.Goal.enter (fun g ->
      let rev_context, b = decompose_lam_n (Proofview.Goal.sigma g) nb_lam e in
      let ids =
        List.fold_left
          (fun acc (na, _) ->
            let pre_id =
              match na.binder_name with Name x -> x | Anonymous -> ano_id
            in
            pre_id :: acc)
          [] rev_context
      in
      let rev_ids = pf_get_new_ids (List.rev ids) g in
      let new_b = substl (List.map mkVar rev_ids) b in
      New.observe_tclTHENLIST
        (fun _ _ -> str "treat_case1")
        [ h_intros (List.rev rev_ids)
        ; intro_using_then teq_id (fun _ -> Proofview.tclUNIT ())
        ; Tacticals.onLastHypId (fun heq ->
              New.observe_tclTHENLIST
                (fun _ _ -> str "treat_case2")
                [ clear to_intros
                ; h_intros to_intros
                ; Proofview.Goal.enter (fun g' ->
                      let sigma = Proofview.Goal.sigma g' in
                      let ty_teq = Tacmach.pf_get_hyp_typ heq g' in
                      let teq_lhs, teq_rhs =
                        let _, args =
                          try destApp sigma ty_teq with DestKO -> assert false
                        in
                        (args.(1), args.(2))
                      in
                      let new_b' =
                        Termops.replace_term sigma teq_lhs teq_rhs new_b
                      in
                      let new_infos =
                        { infos with
                          info = new_b'
                        ; eqs = heq :: infos.eqs
                        ; forbidden_ids =
                            ( if forbid_new_ids then
                              add_vars sigma infos.forbidden_ids new_b'
                            else infos.forbidden_ids ) }
                      in
                      finalize_tac new_infos) ]) ])

let rec travel_aux jinfo continuation_tac (expr_info : constr infos) =
  Proofview.Goal.enter (fun g ->
      let sigma = Proofview.Goal.sigma g in
      let env = Proofview.Goal.env g in
      match EConstr.kind sigma expr_info.info with
      | CoFix _ | Fix _ ->
        user_err Pp.(str "Function cannot treat local fixpoint or cofixpoint")
      | Array _ -> user_err Pp.(str "Function cannot treat arrays")
      | Proj _ -> user_err Pp.(str "Function cannot treat projections")
      | LetIn (na, b, t, e) ->
        let new_continuation_tac =
          jinfo.letiN (na.binder_name, b, t, e) expr_info continuation_tac
        in
        travel jinfo new_continuation_tac
          {expr_info with info = b; is_final = false}
      | Rel _ -> anomaly (Pp.str "Free var in goal conclusion!")
      | Prod _ -> (
        try
          check_not_nested env sigma
            (expr_info.f_id :: expr_info.forbidden_ids)
            expr_info.info;
          jinfo.otherS () expr_info continuation_tac expr_info
        with e when CErrors.noncritical e ->
          user_err
            ( str "the term "
            ++ Printer.pr_leconstr_env env sigma expr_info.info
            ++ str " can not contain a recursive call to "
            ++ Id.print expr_info.f_id ) )
      | Lambda (n, t, b) -> (
        try
          check_not_nested env sigma
            (expr_info.f_id :: expr_info.forbidden_ids)
            expr_info.info;
          jinfo.otherS () expr_info continuation_tac expr_info
        with e when CErrors.noncritical e ->
          user_err
            ( str "the term "
            ++ Printer.pr_leconstr_env env sigma expr_info.info
            ++ str " can not contain a recursive call to "
            ++ Id.print expr_info.f_id ++ str ".") )
      | Case (ci, u, pms, t, iv, a, l) ->
        let (ci, t, iv, a, l) = EConstr.expand_case env sigma (ci, u, pms, t, iv, a, l) in
        let continuation_tac_a =
          jinfo.casE (travel jinfo) (ci, t, iv, a, l) expr_info continuation_tac
        in
        travel jinfo continuation_tac_a
          {expr_info with info = a; is_main_branch = false; is_final = false}
      | App _ -> (
        let f, args = decompose_app sigma expr_info.info in
        if EConstr.eq_constr sigma f expr_info.f_constr then
          jinfo.app_reC (f, args) expr_info continuation_tac expr_info
        else
          match EConstr.kind sigma f with
          | App _ -> assert false (* f is coming from a decompose_app *)
          | Const _ | Construct _ | Rel _ | Evar _ | Meta _ | Ind _ | Sort _
           |Prod _ | Var _ ->
            let new_infos = {expr_info with info = (f, args)} in
            let new_continuation_tac =
              jinfo.apP (f, args) expr_info continuation_tac
            in
            travel_args jinfo expr_info.is_main_branch new_continuation_tac
              new_infos
          | Case _ ->
            user_err
              ( str "the term "
              ++ Printer.pr_leconstr_env env sigma expr_info.info
              ++ str
                   " can not contain an applied match (See Limitation in \
                    Section 2.3 of refman)." )
          | _ ->
            anomaly
              ( Pp.str "travel_aux : unexpected "
              ++ Printer.pr_leconstr_env env sigma expr_info.info
              ++ Pp.str "." ) )
      | Cast (t, _, _) -> travel jinfo continuation_tac {expr_info with info = t}
      | Const _ | Var _ | Meta _ | Evar _ | Sort _ | Construct _ | Ind _
       |Int _ | Float _ ->
        let new_continuation_tac = jinfo.otherS () expr_info continuation_tac in
        new_continuation_tac expr_info)

and travel_args jinfo is_final continuation_tac infos =
  let f_args', args = infos.info in
  match args with
  | [] -> continuation_tac {infos with info = f_args'; is_final}
  | arg :: args' ->
    let new_continuation_tac new_infos =
      let new_arg = new_infos.info in
      travel_args jinfo is_final continuation_tac
        {new_infos with info = (mkApp (f_args', [|new_arg|]), args')}
    in
    travel jinfo new_continuation_tac {infos with info = arg; is_final = false}

and travel jinfo continuation_tac expr_info =
  New.observe_tac
    (fun env sigma ->
      str jinfo.message ++ Printer.pr_leconstr_env env sigma expr_info.info)
    (travel_aux jinfo continuation_tac expr_info)

(* Termination proof *)

let rec prove_lt hyple =
  Proofview.Goal.enter (fun g ->
      let sigma = Proofview.Goal.sigma g in
      try
        let varx, varz =
          match decompose_app sigma (Proofview.Goal.concl g) with
          | _, x :: z :: _ when isVar sigma x && isVar sigma z -> (x, z)
          | _ -> assert false
        in
        let h =
          List.find
            (fun id ->
              match decompose_app sigma (Tacmach.pf_get_hyp_typ id g) with
              | _, t :: _ -> EConstr.eq_constr sigma t varx
              | _ -> false)
            hyple
        in
        let y =
          List.hd
            (List.tl
               (snd (decompose_app sigma (Tacmach.pf_get_hyp_typ h g))))
        in
        New.observe_tclTHENLIST
          (fun _ _ -> str "prove_lt1")
          [ apply (mkApp (le_lt_trans (), [|varx; y; varz; mkVar h|]))
          ; New.observe_tac (fun _ _ -> str "prove_lt") (prove_lt hyple) ]
      with Not_found ->
        New.observe_tclTHENLIST
          (fun _ _ -> str "prove_lt2")
          [ apply (delayed_force lt_S_n)
          ; New.observe_tac
              (fun _ _ ->
                str "assumption: "
                ++ Printer.Debug.pr_goal g)
              assumption ])

let rec destruct_bounds_aux infos (bound, hyple, rechyps) lbounds =
  let open Tacticals in
  Proofview.Goal.enter (fun g ->
      match lbounds with
      | [] ->
        let ids = Tacmach.pf_ids_of_hyps g in
        let s_max = mkApp (delayed_force coq_S, [|bound|]) in
        let k = next_ident_away_in_goal k_id ids in
        let ids = k :: ids in
        let h' = next_ident_away_in_goal h'_id ids in
        let ids = h' :: ids in
        let def = next_ident_away_in_goal def_id ids in
        New.observe_tclTHENLIST
          (fun _ _ -> str "destruct_bounds_aux1")
          [ split (ImplicitBindings [s_max])
          ; intro_then (fun id ->
                New.observe_tac
                  (fun _ _ -> str "destruct_bounds_aux")
                  (tclTHENS
                     (simplest_case (mkVar id))
                     [ New.observe_tclTHENLIST
                         (fun _ _ -> str "")
                         [ intro_using_then h_id
                             (* We don't care about the refreshed name,
                                accessed only through auto? *)
                             (fun _ -> Proofview.tclUNIT ())
                         ; simplest_elim
                             (mkApp (delayed_force lt_n_O, [|s_max|]))
                         ; default_full_auto ]
                     ; New.observe_tclTHENLIST
                         (fun _ _ -> str "destruct_bounds_aux2")
                         [ New.observe_tac
                             (fun _ _ -> str "clearing k ")
                             (clear [id])
                         ; h_intros [k; h'; def]
                         ; New.observe_tac
                             (fun _ _ -> str "simple_iter")
                             (simpl_iter Locusops.onConcl)
                         ; New.observe_tac
                             (fun _ _ -> str "unfold functional")
                             (unfold_in_concl
                                [ ( Locus.OnlyOccurrences [1]
                                  , evaluable_of_global_reference infos.func )
                                ])
                         ; New.observe_tclTHENLIST
                             (fun _ _ -> str "test")
                             [ list_rewrite true
                                 (List.fold_right
                                    (fun e acc -> (mkVar e, true) :: acc)
                                    infos.eqs
                                    (List.map (fun e -> (e, true)) rechyps))
                             ; (* list_rewrite true *)
                               (*   (List.map (fun e -> (mkVar e,true)) infos.eqs) *)
                               (*   ; *)
                               New.observe_tac
                                 (fun _ _ -> str "finishing")
                                 (tclORELSE intros_reflexivity
                                    (New.observe_tac
                                       (fun _ _ -> str "calling prove_lt")
                                       (prove_lt hyple))) ] ] ])) ]
      | (_, v_bound) :: l ->
        New.observe_tclTHENLIST
          (fun _ _ -> str "destruct_bounds_aux3")
          [ simplest_elim (mkVar v_bound)
          ; clear [v_bound]
          ; tclDO 2 intro
          ; onNthHypId 1 (fun p_hyp ->
                onNthHypId 2 (fun p ->
                    New.observe_tclTHENLIST
                      (fun _ _ -> str "destruct_bounds_aux4")
                      [ simplest_elim
                          (mkApp (delayed_force max_constr, [|bound; mkVar p|]))
                      ; tclDO 3 intro
                      ; onNLastHypsId 3 (fun lids ->
                            match lids with
                            | [hle2; hle1; pmax] ->
                              destruct_bounds_aux infos
                                ( mkVar pmax
                                , hle1 :: hle2 :: hyple
                                , mkVar p_hyp :: rechyps )
                                l
                            | _ -> assert false) ])) ])

let destruct_bounds infos =
  destruct_bounds_aux infos
    (delayed_force coq_O, [], [])
    infos.values_and_bounds

let terminate_app f_and_args expr_info continuation_tac infos =
  if expr_info.is_final && expr_info.is_main_branch then
    New.observe_tclTHENLIST
      (fun _ _ -> str "terminate_app1")
      [ continuation_tac infos
      ; New.observe_tac
          (fun _ _ -> str "first split")
          (split (ImplicitBindings [infos.info]))
      ; New.observe_tac
          (fun _ _ -> str "destruct_bounds (1)")
          (destruct_bounds infos) ]
  else continuation_tac infos

let terminate_others _ expr_info continuation_tac infos =
  if expr_info.is_final && expr_info.is_main_branch then
    New.observe_tclTHENLIST
      (fun _ _ -> str "terminate_others")
      [ continuation_tac infos
      ; New.observe_tac
          (fun _ _ -> str "first split")
          (split (ImplicitBindings [infos.info]))
      ; New.observe_tac
          (fun _ _ -> str "destruct_bounds")
          (destruct_bounds infos) ]
  else continuation_tac infos

let terminate_letin (na, b, t, e) expr_info continuation_tac info =
  Proofview.Goal.enter (fun g ->
      let sigma = Proofview.Goal.sigma g in
      let env = Proofview.Goal.env g in
      let new_e = subst1 info.info e in
      let new_forbidden =
        let forbid =
          try
            check_not_nested env sigma
              (expr_info.f_id :: expr_info.forbidden_ids)
              b;
            true
          with e when CErrors.noncritical e -> false
        in
        if forbid then
          match na with
          | Anonymous -> info.forbidden_ids
          | Name id -> id :: info.forbidden_ids
        else info.forbidden_ids
      in
      continuation_tac {info with info = new_e; forbidden_ids = new_forbidden})

let pf_type c tac =
  let open Tacticals in
  Proofview.Goal.enter (fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let evars, ty = Typing.type_of env sigma c in
      tclTHEN (Proofview.Unsafe.tclEVARS evars) (tac ty))

let pf_typel l tac =
  let rec aux tys l =
    match l with
    | [] -> tac (List.rev tys)
    | hd :: tl -> pf_type hd (fun ty -> aux (ty :: tys) tl)
  in
  aux [] l

(* This is like the previous one except that it also rewrite on all
  hypotheses except the ones given in the first argument.  All the
  modified hypotheses are generalized in the process and should be
  introduced back later; the result is the pair of the tactic and the
  list of hypotheses that have been generalized and cleared. *)
let mkDestructEq not_on_hyp env sigma expr =
  let hyps = EConstr.named_context env in
  let to_revert =
    Util.List.map_filter
      (fun decl ->
        let open Context.Named.Declaration in
        let id = get_id decl in
        if
          Id.List.mem id not_on_hyp
          || not (Termops.dependent sigma expr (get_type decl))
        then None
        else Some id)
      hyps
  in
  let to_revert_constr = List.rev_map mkVar to_revert in
  let sigma, type_of_expr = Typing.type_of env sigma expr in
  let new_hyps =
    mkApp (Lazy.force refl_equal, [|type_of_expr; expr|]) :: to_revert_constr
  in
  let tac =
    pf_typel new_hyps (fun _ ->
        New.observe_tclTHENLIST
          (fun _ _ -> str "mkDestructEq")
          [ generalize new_hyps
          ; Proofview.Goal.enter (fun g2 ->
                let changefun patvars env sigma =
                  pattern_occs
                    [(Locus.AllOccurrencesBut [1], expr)]
                    (Proofview.Goal.env g2) sigma (Proofview.Goal.concl g2)
                in
                change_in_concl ~check:true None changefun)
          ; simplest_case expr ])
  in
  (sigma, tac, to_revert)

let terminate_case next_step (ci, a, iv, t, l) expr_info continuation_tac infos
    =
  let open Tacticals in
  Proofview.Goal.enter (fun g ->
      let sigma = Proofview.Goal.sigma g in
      let env = Proofview.Goal.env g in
      let f_is_present =
        try
          check_not_nested env sigma
            (expr_info.f_id :: expr_info.forbidden_ids)
            a;
          false
        with e when CErrors.noncritical e -> true
      in
      let a' = infos.info in
      let new_info =
        { infos with
          info = mkCase (EConstr.contract_case env sigma (ci, a, iv, a', l))
        ; is_main_branch = expr_info.is_main_branch
        ; is_final = expr_info.is_final }
      in
      let sigma, destruct_tac, rev_to_thin_intro =
        mkDestructEq [expr_info.rec_arg_id] env sigma a'
      in
      let to_thin_intro = List.rev rev_to_thin_intro in
      New.observe_tac
        (fun _ _ ->
          str "treating cases ("
          ++ int (Array.length l)
          ++ str ")" ++ spc ()
          ++ Printer.pr_leconstr_env env sigma a')
        ((* We used to try-catch the error from tclTHENS before the
            port to the new engine, not sure if it's worth putting it back *)
          tclTHENS destruct_tac
            (List.map_i
               (fun i e ->
                  New.observe_tac
                    (fun _ _ -> str "do treat case")
                    (treat_case f_is_present to_thin_intro
                       (next_step continuation_tac)
                       ci.ci_cstr_ndecls.(i) e new_info))
               0 (Array.to_list l))))

let terminate_app_rec (f, args) expr_info continuation_tac _ =
  let open Tacticals in
  Proofview.Goal.enter (fun g ->
      let sigma = Proofview.Goal.sigma g in
      let env = Proofview.Goal.env g in
      List.iter
        (check_not_nested env sigma (expr_info.f_id :: expr_info.forbidden_ids))
        args;
      try
        let v =
          List.assoc_f
            (List.equal (EConstr.eq_constr sigma))
            args expr_info.args_assoc
        in
        let new_infos = {expr_info with info = v} in
        New.observe_tclTHENLIST
          (fun _ _ -> str "terminate_app_rec")
          [ continuation_tac new_infos
          ; ( if expr_info.is_final && expr_info.is_main_branch then
              New.observe_tclTHENLIST
                (fun _ _ -> str "terminate_app_rec1")
                [ New.observe_tac
                    (fun _ _ -> str "first split")
                    (split (ImplicitBindings [new_infos.info]))
                ; New.observe_tac
                    (fun _ _ -> str "destruct_bounds (3)")
                    (destruct_bounds new_infos) ]
            else Proofview.tclUNIT () ) ]
      with Not_found ->
        New.observe_tac
          (fun _ _ -> str "terminate_app_rec not found")
          (tclTHENS
             (simplest_elim (mkApp (mkVar expr_info.ih, Array.of_list args)))
             [ New.observe_tclTHENLIST
                 (fun _ _ -> str "terminate_app_rec2")
                 [ intro_using_then rec_res_id
                     (* refreshed name gotten from onNthHypId *)
                     (fun _ -> Proofview.tclUNIT ())
                 ; intro
                 ; onNthHypId 1 (fun v_bound ->
                       onNthHypId 2 (fun v ->
                           let new_infos =
                             { expr_info with
                               info = mkVar v
                             ; values_and_bounds =
                                 (v, v_bound) :: expr_info.values_and_bounds
                             ; args_assoc =
                                 (args, mkVar v) :: expr_info.args_assoc }
                           in
                           New.observe_tclTHENLIST
                             (fun _ _ -> str "terminate_app_rec3")
                             [ continuation_tac new_infos
                             ; ( if
                                 expr_info.is_final && expr_info.is_main_branch
                               then
                                 New.observe_tclTHENLIST
                                   (fun _ _ -> str "terminate_app_rec4")
                                   [ New.observe_tac
                                       (fun _ _ -> str "first split")
                                       (split
                                          (ImplicitBindings [new_infos.info]))
                                   ; New.observe_tac
                                       (fun _ _ -> str "destruct_bounds (2)")
                                       (destruct_bounds new_infos) ]
                               else Proofview.tclUNIT () ) ])) ]
             ; New.observe_tac
                 (fun _ _ -> str "proving decreasing")
                 (tclTHENS (* proof of args < formal args *)
                    (apply (Lazy.force expr_info.acc_inv))
                    [ New.observe_tac (fun _ _ -> str "assumption") assumption
                    ; New.observe_tclTHENLIST
                        (fun _ _ -> str "terminate_app_rec5")
                        [ tclTRY
                            (list_rewrite true
                               (List.map
                                  (fun e -> (mkVar e, true))
                                  expr_info.eqs))
                        ; tclUSER expr_info.concl_tac true
                            (Some
                               ( expr_info.ih :: expr_info.acc_id
                               :: (fun (x, y) -> y)
                                    (List.split expr_info.values_and_bounds) ))
                        ] ]) ]))

let terminate_info =
  { message = "prove_terminate with term "
  ; letiN = terminate_letin
  ; lambdA = (fun _ _ _ _ -> assert false)
  ; casE = terminate_case
  ; otherS = terminate_others
  ; apP = terminate_app
  ; app_reC = terminate_app_rec }

let prove_terminate = travel terminate_info

(* Equation proof *)

let equation_case next_step case expr_info continuation_tac infos =
  New.observe_tac
    (fun _ _ -> str "equation case")
    (terminate_case next_step case expr_info continuation_tac infos)

let rec prove_le () =
  let open Tacticals in
  Proofview.Goal.enter (fun g ->
      let sigma = Proofview.Goal.sigma g in
      let x, z =
        let _, args = decompose_app sigma (Proofview.Goal.concl g) in
        (List.hd args, List.hd (List.tl args))
      in
      tclFIRST
        [ assumption
        ; apply (delayed_force le_n)
        ; begin
            try
              let matching_fun c =
                match EConstr.kind sigma c with
                | App (c, [|x0; _|]) ->
                  EConstr.isVar sigma x0
                  && Id.equal (destVar sigma x0) (destVar sigma x)
                  && EConstr.isRefX sigma (le ()) c
                | _ -> false
              in
              let h, t =
                List.find
                  (fun (_, t) -> matching_fun t)
                  (Tacmach.pf_hyps_types g)
              in
              let y =
                let _, args = decompose_app sigma t in
                List.hd (List.tl args)
              in
              New.observe_tclTHENLIST
                (fun _ _ -> str "prove_le")
                [ apply (mkApp (le_trans (), [|x; y; z; mkVar h|]))
                ; New.observe_tac
                    (fun _ _ -> str "prove_le (rec)")
                    (prove_le ()) ]
            with Not_found -> Tacticals.tclFAIL (mt ())
          end ])

let rec make_rewrite_list expr_info max = function
  | [] -> Proofview.tclUNIT ()
  | (_, p, hp) :: l ->
    let open Tacticals in
    New.observe_tac
      (fun _ _ -> str "make_rewrite_list")
      (tclTHENS
         (New.observe_tac
            (fun _ _ -> str "rewrite heq on " ++ Id.print p)
            (Proofview.Goal.enter (fun g ->
                 let sigma = Proofview.Goal.sigma g in
                 let t_eq = compute_renamed_type g hp in
                 let k, def =
                   let k_na, _, t = destProd sigma t_eq in
                   let _, _, t = destProd sigma t in
                   let def_na, _, _ = destProd sigma t in
                   ( Nameops.Name.get_id k_na.binder_name
                   , Nameops.Name.get_id def_na.binder_name )
                 in
                 general_rewrite ~where:None ~l2r:false Locus.AllOccurrences ~freeze:true
                   (* dep proofs also: *) ~dep:true ~with_evars:false
                   ( mkVar hp
                   , ExplicitBindings
                       [ CAst.make @@ (NamedHyp (CAst.make def), expr_info.f_constr)
                       ; CAst.make @@ (NamedHyp (CAst.make k), f_S max) ] )
                   )))
         [ make_rewrite_list expr_info max l
         ; New.observe_tclTHENLIST
             (fun _ _ -> str "make_rewrite_list")
             [ (* x < S max proof *)
               apply (delayed_force le_lt_n_Sm)
             ; New.observe_tac (fun _ _ -> str "prove_le(2)") (prove_le ()) ] ])

let make_rewrite expr_info l hp max =
  let open Tacticals in
  tclTHENFIRST
    (New.observe_tac
       (fun _ _ -> str "make_rewrite")
       (make_rewrite_list expr_info max l))
    (New.observe_tac
       (fun _ _ -> str "make_rewrite")
       (tclTHENS
          (Proofview.Goal.enter (fun g ->
               let sigma = Proofview.Goal.sigma g in
               let t_eq = compute_renamed_type g hp in
               let k, def =
                 let k_na, _, t = destProd sigma t_eq in
                 let _, _, t = destProd sigma t in
                 let def_na, _, _ = destProd sigma t in
                 ( Nameops.Name.get_id k_na.binder_name
                 , Nameops.Name.get_id def_na.binder_name )
               in
               New.observe_tac
                 (fun _ _ -> str "general_rewrite_bindings")
                 (general_rewrite ~where:None ~l2r:false Locus.AllOccurrences ~freeze:true
                    (* dep proofs also: *) ~dep:true ~with_evars:false
                    ( mkVar hp
                    , ExplicitBindings
                        [ CAst.make @@ (NamedHyp (CAst.make def), expr_info.f_constr)
                        ; CAst.make @@ (NamedHyp (CAst.make k), f_S (f_S max)) ] )
                    )))
          [ New.observe_tac
              (fun _ _ -> str "make_rewrite finalize")
              ((* tclORELSE( h_reflexivity) *)
               New.observe_tclTHENLIST
                 (fun _ _ -> str "make_rewrite")
                 [ simpl_iter Locusops.onConcl
                 ; New.observe_tac
                     (fun _ _ -> str "unfold functional")
                     (unfold_in_concl
                        [ ( Locus.OnlyOccurrences [1]
                          , evaluable_of_global_reference expr_info.func ) ])
                 ; list_rewrite true
                     (List.map (fun e -> (mkVar e, true)) expr_info.eqs)
                 ; New.observe_tac
                     (fun _ _ -> str "h_reflexivity")
                     intros_reflexivity ])
          ; New.observe_tclTHENLIST
              (fun _ _ -> str "make_rewrite1")
              [ (* x < S (S max) proof *)
                apply (EConstr.of_constr (delayed_force le_lt_SS))
              ; New.observe_tac (fun _ _ -> str "prove_le (3)") (prove_le ()) ]
          ]))

let rec compute_max rew_tac max l =
  match l with
  | [] -> rew_tac max
  | (_, p, _) :: l ->
    let open Tacticals in
    New.observe_tclTHENLIST
      (fun _ _ -> str "compute_max")
      [ simplest_elim (mkApp (delayed_force max_constr, [|max; mkVar p|]))
      ; tclDO 3 intro
      ; onNLastHypsId 3 (fun lids ->
            match lids with
            | [hle2; hle1; pmax] -> compute_max rew_tac (mkVar pmax) l
            | _ -> assert false) ]

let rec destruct_hex expr_info acc l =
  let open Tacticals in
  match l with
  | [] -> (
    match List.rev acc with
    | [] -> Proofview.tclUNIT ()
    | (_, p, hp) :: tl ->
      New.observe_tac
        (fun _ _ -> str "compute max ")
        (compute_max (make_rewrite expr_info tl hp) (mkVar p) tl) )
  | (v, hex) :: l ->
    New.observe_tclTHENLIST
      (fun _ _ -> str "destruct_hex")
      [ simplest_case (mkVar hex)
      ; clear [hex]
      ; tclDO 2 intro
      ; onNthHypId 1 (fun hp ->
            onNthHypId 2 (fun p ->
                New.observe_tac
                  (fun _ _ ->
                    str "destruct_hex after " ++ Id.print hp ++ spc ()
                    ++ Id.print p)
                  (destruct_hex expr_info ((v, p, hp) :: acc) l))) ]

let rec intros_values_eq expr_info acc =
  let open Tacticals in
  tclORELSE
    (New.observe_tclTHENLIST
       (fun _ _ -> str "intros_values_eq")
       [ tclDO 2 intro
       ; onNthHypId 1 (fun hex ->
             onNthHypId 2 (fun v ->
                 intros_values_eq expr_info ((v, hex) :: acc))) ])
    (tclCOMPLETE (destruct_hex expr_info [] acc))

let equation_others _ expr_info continuation_tac infos =
  let open Tacticals in
  if expr_info.is_final && expr_info.is_main_branch then
    New.observe_tac
      (fun env sigma ->
        str "equation_others (cont_tac +intros) "
        ++ Printer.pr_leconstr_env env sigma expr_info.info)
      (tclTHEN (continuation_tac infos)
         (New.observe_tac
            (fun env sigma ->
              str "intros_values_eq equation_others "
              ++ Printer.pr_leconstr_env env sigma expr_info.info)
            (intros_values_eq expr_info [])))
  else
    New.observe_tac
      (fun env sigma ->
        str "equation_others (cont_tac) "
        ++ Printer.pr_leconstr_env env sigma expr_info.info)
      (continuation_tac infos)

let equation_app f_and_args expr_info continuation_tac infos =
  if expr_info.is_final && expr_info.is_main_branch then
    New.observe_tac
      (fun _ _ -> str "intros_values_eq equation_app")
      (intros_values_eq expr_info [])
  else continuation_tac infos

let equation_app_rec (f, args) expr_info continuation_tac info =
  Proofview.Goal.enter (fun g ->
      let sigma = Proofview.Goal.sigma g in
      try
        let v =
          List.assoc_f
            (List.equal (EConstr.eq_constr sigma))
            args expr_info.args_assoc
        in
        let new_infos = {expr_info with info = v} in
        New.observe_tac
          (fun _ _ -> str "app_rec found")
          (continuation_tac new_infos)
      with Not_found ->
        if expr_info.is_final && expr_info.is_main_branch then
          New.observe_tclTHENLIST
            (fun _ _ -> str "equation_app_rec")
            [ simplest_case (mkApp (expr_info.f_terminate, Array.of_list args))
            ; continuation_tac
                { expr_info with
                  args_assoc =
                    (args, delayed_force coq_O) :: expr_info.args_assoc }
            ; New.observe_tac
                (fun _ _ -> str "app_rec intros_values_eq")
                (intros_values_eq expr_info []) ]
        else
          New.observe_tclTHENLIST
            (fun _ _ -> str "equation_app_rec1")
            [ simplest_case (mkApp (expr_info.f_terminate, Array.of_list args))
            ; New.observe_tac
                (fun _ _ -> str "app_rec not_found")
                (continuation_tac
                   { expr_info with
                     args_assoc =
                       (args, delayed_force coq_O) :: expr_info.args_assoc }) ])

let equation_info =
  { message = "prove_equation with term "
  ; letiN = (fun _ -> assert false)
  ; lambdA = (fun _ _ _ _ -> assert false)
  ; casE = equation_case
  ; otherS = equation_others
  ; apP = equation_app
  ; app_reC = equation_app_rec }

let prove_eq = travel equation_info

(* wrappers *)
(* [compute_terminate_type] computes the type of the Definition f_terminate from the type of f_F
*)
let compute_terminate_type nb_args func =
  let open Term in
  let open Constr in
  let open CVars in
  let _, a_arrow_b, _ =
    destLambda (def_of_const (constr_of_monomorphic_global (Global.env ()) func))
  in
  let rev_args, b = decompose_prod_n nb_args a_arrow_b in
  let left =
    mkApp
      ( delayed_force iter_rd
      , Array.of_list
          ( lift 5 a_arrow_b :: mkRel 3
          :: constr_of_monomorphic_global (Global.env ()) func
          :: mkRel 1
          :: List.rev (List.map_i (fun i _ -> mkRel (6 + i)) 0 rev_args) ) )
  in
  let right = mkRel 5 in
  let delayed_force c = EConstr.Unsafe.to_constr (delayed_force c) in
  let equality = mkApp (delayed_force eq, [|lift 5 b; left; right|]) in
  let result =
    mkProd (make_annot (Name def_id) Sorts.Relevant, lift 4 a_arrow_b, equality)
  in
  let cond = mkApp (delayed_force lt, [|mkRel 2; mkRel 1|]) in
  let nb_iter =
    mkApp
      ( delayed_force ex
      , [| delayed_force nat
         ; mkLambda
             ( make_annot (Name p_id) Sorts.Relevant
             , delayed_force nat
             , mkProd
                 ( make_annot (Name k_id) Sorts.Relevant
                 , delayed_force nat
                 , mkArrow cond Sorts.Relevant result ) ) |] )
  in
  let value =
    mkApp
      ( constr_of_monomorphic_global (Global.env ()) (Util.delayed_force coq_sig_ref)
      , [|b; mkLambda (make_annot (Name v_id) Sorts.Relevant, b, nb_iter)|] )
  in
  compose_prod rev_args value

let termination_proof_header is_mes input_type ids args_id relation rec_arg_num
    rec_arg_id tac wf_tac : unit Proofview.tactic =
  let open Tacticals in
  Proofview.Goal.enter (fun g ->
      let nargs = List.length args_id in
      let pre_rec_args =
        List.rev_map mkVar (fst (List.chop (rec_arg_num - 1) args_id))
      in
      let relation = substl pre_rec_args relation in
      let input_type = substl pre_rec_args input_type in
      let wf_thm = next_ident_away_in_goal (Id.of_string "wf_R") ids in
      let wf_rec_arg =
        next_ident_away_in_goal
          (Id.of_string ("Acc_" ^ Id.to_string rec_arg_id))
          (wf_thm :: ids)
      in
      let hrec =
        next_ident_away_in_goal hrec_id (wf_rec_arg :: wf_thm :: ids)
      in
      let acc_inv =
        lazy
          (mkApp
             ( delayed_force acc_inv_id
             , [|input_type; relation; mkVar rec_arg_id|] ))
      in
      tclTHEN (h_intros args_id)
        (tclTHENS
           (New.observe_tac
              (fun _ _ -> str "first assert")
              (assert_before (Name wf_rec_arg)
                 (mkApp
                    ( delayed_force acc_rel
                    , [|input_type; relation; mkVar rec_arg_id|] ))))
           [ (* accesibility proof *)
             tclTHENS
               (New.observe_tac
                  (fun _ _ -> str "second assert")
                  (assert_before (Name wf_thm)
                     (mkApp
                        (delayed_force well_founded, [|input_type; relation|]))))
               [ (* interactive proof that the relation is well_founded *)
                 New.observe_tac
                   (fun _ _ -> str "wf_tac")
                   (wf_tac is_mes (Some args_id))
               ; (* this gives the accessibility argument *)
                 New.observe_tac
                   (fun _ _ -> str "apply wf_thm")
                   (Simple.apply (mkApp (mkVar wf_thm, [|mkVar rec_arg_id|])))
               ]
           ; (* rest of the proof *)
             New.observe_tclTHENLIST
               (fun _ _ -> str "rest of proof")
               [ New.observe_tac
                   (fun _ _ -> str "generalize")
                   (onNLastHypsId (nargs + 1)
                      (tclMAP (fun id ->
                           tclTHEN (Tactics.generalize [mkVar id]) (clear [id]))))
               ; New.observe_tac (fun _ _ -> str "fix") (fix hrec (nargs + 1))
               ; h_intros args_id
               ; Simple.intro wf_rec_arg
               ; New.observe_tac
                   (fun _ _ -> str "tac")
                   (tac wf_rec_arg hrec wf_rec_arg acc_inv) ] ]))

let rec instantiate_lambda sigma t l =
  match l with
  | [] -> t
  | a :: l ->
    let _, _, body = destLambda sigma t in
    instantiate_lambda sigma (subst1 a body) l

let whole_start concl_tac nb_args is_mes func input_type relation rec_arg_num :
    unit Proofview.tactic =
  Proofview.Goal.enter (fun g ->
      let sigma = Proofview.Goal.sigma g in
      let hyps = Proofview.Goal.hyps g in
      let ids = Termops.ids_of_named_context hyps in
      let func_body = def_of_const (constr_of_monomorphic_global (Global.env ()) func) in
      let func_body = EConstr.of_constr func_body in
      let f_name, _, body1 = destLambda sigma func_body in
      let f_id =
        match f_name.binder_name with
        | Name f_id -> next_ident_away_in_goal f_id ids
        | Anonymous -> anomaly (Pp.str "Anonymous function.")
      in
      let n_names_types, _ = decompose_lam_n sigma nb_args body1 in
      let n_ids, ids =
        List.fold_left
          (fun (n_ids, ids) (n_name, _) ->
            match n_name.binder_name with
            | Name id ->
              let n_id = next_ident_away_in_goal id ids in
              (n_id :: n_ids, n_id :: ids)
            | _ -> anomaly (Pp.str "anonymous argument."))
          ([], f_id :: ids)
          n_names_types
      in
      let rec_arg_id = List.nth n_ids (rec_arg_num - 1) in
      let expr =
        instantiate_lambda sigma func_body (mkVar f_id :: List.map mkVar n_ids)
      in
      termination_proof_header is_mes input_type ids n_ids relation rec_arg_num
        rec_arg_id
        (fun rec_arg_id hrec acc_id acc_inv ->
          prove_terminate
            (fun infos -> Proofview.tclUNIT ())
            { is_main_branch = true
            ; (* we are on the main branche (i.e. still on a match ... with .... end *)
              is_final = true
            ; (* and on leaf (more or less) *)
              f_terminate = delayed_force coq_O
            ; nb_arg = nb_args
            ; concl_tac
            ; rec_arg_id
            ; is_mes
            ; ih = hrec
            ; f_id
            ; f_constr = mkVar f_id
            ; func
            ; info = expr
            ; acc_inv
            ; acc_id
            ; values_and_bounds = []
            ; eqs = []
            ; forbidden_ids = []
            ; args_assoc = [] })
        (fun b ids -> tclUSER_if_not_mes concl_tac b ids))

(* Goal represented as a type, doesn't take into account section variables *)
let abstract_type sigma gl =
  let open EConstr in
  let genv = Global.env () in
  let evi = Evd.find sigma gl in
  let env = Evd.evar_filtered_env genv evi in
  let is_proof_var decl =
    try ignore (Environ.lookup_named (Context.Named.Declaration.get_id decl) genv); false
    with Not_found -> true in
  Environ.fold_named_context_reverse (fun t decl ->
                                        if is_proof_var decl then
                                          let decl = Termops.map_named_decl EConstr.of_constr decl in
                                          mkNamedProd_or_LetIn decl t
                                        else
                                          t
                                      ) ~init:(Evd.evar_concl evi) env

let get_current_subgoals_types pstate =
  let p = Declare.Proof.get pstate in
  let Proof.{goals = sgs; sigma; _} = Proof.data p in
  (sigma, List.map (abstract_type sigma) sgs)

exception EmptySubgoals

let build_and_l sigma l =
  let and_constr =
    UnivGen.constr_of_monomorphic_global (Global.env ()) @@ Coqlib.lib_ref "core.and.type"
  in
  let conj_constr = Coqlib.lib_ref "core.and.conj" in
  let mk_and p1 p2 = mkApp (EConstr.of_constr and_constr, [|p1; p2|]) in
  let rec is_well_founded t =
    match EConstr.kind sigma t with
    | Prod (_, _, t') -> is_well_founded t'
    | App (_, _) ->
      let f, _ = decompose_app sigma t in
      EConstr.eq_constr sigma f (well_founded ())
    | _ -> false
  in
  let compare t1 t2 =
    let b1, b2 = (is_well_founded t1, is_well_founded t2) in
    if (b1 && b2) || not (b1 || b2) then 0 else if b1 && not b2 then 1 else -1
  in
  let l = List.sort compare l in
  let rec f = function
    | [] -> raise EmptySubgoals
    | [p] -> (p, tclIDTAC, 1)
    | p1 :: pl ->
      let c, tac, nb = f pl in
      ( mk_and p1 c
      , tclTHENS
          (apply (EConstr.of_constr (constr_of_monomorphic_global (Global.env ()) conj_constr)))
          [tclIDTAC; tac]
      , nb + 1 )
  in
  f l

let is_rec_res id =
  let rec_res_name = Id.to_string rec_res_id in
  let id_name = Id.to_string id in
  try
    String.equal
      (String.sub id_name 0 (String.length rec_res_name))
      rec_res_name
  with Invalid_argument _ -> false

let clear_goals sigma =
  let rec clear_goal t =
    match EConstr.kind sigma t with
    | Prod (({binder_name = Name id} as na), t', b) ->
      let b' = clear_goal b in
      if noccurn sigma 1 b' && is_rec_res id then Vars.lift (-1) b'
      else if b' == b then t
      else mkProd (na, t', b')
    | _ -> EConstr.map sigma clear_goal t
  in
  List.map clear_goal

let build_new_goal_type lemma =
  let sigma, sub_gls_types = get_current_subgoals_types lemma in
  (* Pp.msgnl (str "sub_gls_types1 := " ++ Util.prlist_with_sep (fun () -> Pp.fnl () ++ Pp.fnl ()) Printer.pr_lconstr sub_gls_types); *)
  let sub_gls_types = clear_goals sigma sub_gls_types in
  (* Pp.msgnl (str "sub_gls_types2 := " ++ Pp.prlist_with_sep (fun () -> Pp.fnl () ++ Pp.fnl ()) Printer.pr_lconstr sub_gls_types); *)
  let res = build_and_l sigma sub_gls_types in
  (sigma, res)

let is_opaque_constant c =
  let cb = Global.lookup_constant c in
  let open Vernacexpr in
  match cb.Declarations.const_body with
  | Declarations.OpaqueDef _ -> Opaque
  | Declarations.Undef _ -> Opaque
  | Declarations.Def _ -> Transparent
  | Declarations.Primitive _ -> Opaque

let open_new_goal ~lemma build_proof sigma using_lemmas ref_ goal_name
    (gls_type, decompose_and_tac, nb_goal) =
  (* Pp.msgnl (str "gls_type := " ++ Printer.pr_lconstr gls_type); *)
  let current_proof_name = Declare.Proof.get_name lemma in
  let name =
    match goal_name with
    | Some s -> s
    | None -> (
      try add_suffix current_proof_name "_subproof"
      with e when CErrors.noncritical e ->
        anomaly (Pp.str "open_new_goal with an unnamed theorem.") )
  in
  let na = next_global_ident_away name Id.Set.empty in
  if Termops.occur_existential sigma gls_type then
    CErrors.user_err Pp.(str "\"abstract\" cannot handle existentials");
  let hook _ =
    let opacity =
      let na_ref = qualid_of_ident na in
      let na_global = Smartlocate.global_with_alias na_ref in
      match na_global with
      | GlobRef.ConstRef c -> is_opaque_constant c
      | _ -> anomaly ~label:"equation_lemma" (Pp.str "not a constant.")
    in
    let lemma = mkConst (Names.Constant.make1 (Lib.make_kn na)) in
    ref_ := Value (EConstr.Unsafe.to_constr lemma);
    let lid = ref [] in
    let h_num = ref (-1) in
    let env = Global.env () in
    let start_tac =
      let open Tacmach in
      let open Tacticals in
      Proofview.Goal.enter (fun gl ->
          let hid = next_ident_away_in_goal h_id (pf_ids_of_hyps gl) in
          New.observe_tclTHENLIST
            (fun _ _ -> mt ())
            [ generalize [lemma]
            ; Simple.intro hid
            ; Proofview.Goal.enter (fun gl ->
                  let ids = pf_ids_of_hyps gl in
                  tclTHEN
                    (Elim.h_decompose_and (mkVar hid))
                    (Proofview.Goal.enter (fun gl ->
                         let ids' = pf_ids_of_hyps gl in
                         lid := List.rev (List.subtract Id.equal ids' ids);
                         if List.is_empty !lid then lid := [hid];
                         tclIDTAC))) ])
    in
    let end_tac =
      let open Tacmach in
      let open Tacticals in
      Proofview.Goal.enter (fun gl ->
          let sigma = project gl in
          match EConstr.kind sigma (pf_concl gl) with
          | App (f, _) when EConstr.eq_constr sigma f (well_founded ()) ->
            Auto.h_auto None [] (Some [])
          | _ ->
            incr h_num;
            tclCOMPLETE
              (tclFIRST
                 [ tclTHEN
                     (eapply_with_bindings
                        (mkVar (List.nth !lid !h_num), NoBindings))
                     e_assumption
                 ; Eauto.eauto_with_bases ~depth:5
                     [(fun _ sigma -> (sigma, Lazy.force refl_equal))]
                     [Hints.Hint_db.empty TransparentState.empty false] ]))
    in
    let lemma = build_proof env (Evd.from_env env) start_tac end_tac in
    let (_ : _ list) =
      Declare.Proof.save_regular ~proof:lemma ~opaque:opacity ~idopt:None
    in
    ()
  in
  let info = Declare.Info.make ~hook:(Declare.Hook.make hook) () in
  let cinfo = Declare.CInfo.make ~name:na ~typ:gls_type () in
  let lemma = Declare.Proof.start ~cinfo ~info sigma in
  let lemma =
    if Indfun_common.is_strict_tcc () then
      fst @@ Declare.Proof.by tclIDTAC lemma
    else
      fst
      @@ Declare.Proof.by
           (tclTHEN decompose_and_tac
              (tclORELSE
                 (tclFIRST
                    (List.map
                       (fun c ->
                         Tacticals.tclTHENLIST
                           [ intros
                           ; Simple.apply
                               (fst (interp_constr (Global.env ()) Evd.empty c))
                             (*FIXME*)
                           ; Tacticals.tclCOMPLETE Auto.default_auto ])
                       using_lemmas))
                 tclIDTAC))
           lemma
  in
  if Declare.Proof.get_open_goals lemma = 0 then (defined lemma; None)
  else Some lemma

let com_terminate interactive_proof tcc_lemma_name tcc_lemma_ref is_mes
    fonctional_ref input_type relation rec_arg_num thm_name using_lemmas nb_args
    ctx hook =
  let start_proof env ctx tac_start tac_end =
    let cinfo =
      Declare.CInfo.make ~name:thm_name
        ~typ:(EConstr.of_constr (compute_terminate_type nb_args fonctional_ref))
        ()
    in
    let info = Declare.Info.make ~hook () in
    let lemma = Declare.Proof.start ~cinfo ~info ctx in
    let lemma =
      fst
      @@ Declare.Proof.by
           (New.observe_tac (fun _ _ -> str "starting_tac") tac_start)
           lemma
    in
    fst
    @@ Declare.Proof.by
         (New.observe_tac
            (fun _ _ -> str "whole_start")
            (whole_start tac_end nb_args is_mes fonctional_ref input_type
               relation rec_arg_num))
         lemma
  in
  let lemma =
    start_proof
      Global.(env ())
      ctx Tacticals.tclIDTAC Tacticals.tclIDTAC
  in
  try
    let sigma, new_goal_type = build_new_goal_type lemma in
    let sigma = Evd.from_ctx (Evd.evar_universe_context sigma) in
    open_new_goal ~lemma start_proof sigma using_lemmas tcc_lemma_ref
      (Some tcc_lemma_name) new_goal_type
  with EmptySubgoals ->
    (* a non recursive function declared with measure ! *)
    tcc_lemma_ref := Not_needed;
    if interactive_proof then Some lemma else (defined lemma; None)

let start_equation (f : GlobRef.t) (term_f : GlobRef.t)
    (cont_tactic : Id.t list -> unit Proofview.tactic) =
  Proofview.Goal.enter (fun g ->
      let sigma = Proofview.Goal.sigma g in
      let ids = Tacmach.pf_ids_of_hyps g in
      let terminate_constr = constr_of_monomorphic_global (Global.env ()) term_f in
      let terminate_constr = EConstr.of_constr terminate_constr in
      let nargs =
        nb_prod sigma (EConstr.of_constr (type_of_const (Global.env ()) sigma terminate_constr))
      in
      let x = n_x_id ids nargs in
      New.observe_tac
        (fun _ _ -> str "start_equation")
        (New.observe_tclTHENLIST
           (fun _ _ -> str "start_equation")
           [ h_intros x
           ; unfold_in_concl
               [(Locus.AllOccurrences, evaluable_of_global_reference f)]
           ; New.observe_tac
               (fun _ _ -> str "simplest_case")
               (simplest_case
                  (mkApp (terminate_constr, Array.of_list (List.map mkVar x))))
           ; New.observe_tac (fun _ _ -> str "prove_eq") (cont_tactic x) ]))

let com_eqn uctx nb_arg eq_name functional_ref f_ref terminate_ref
    equation_lemma_type =
  let open CVars in
  let opacity =
    match terminate_ref with
    | GlobRef.ConstRef c -> is_opaque_constant c
    | _ -> anomaly ~label:"terminate_lemma" (Pp.str "not a constant.")
  in
  let evd = Evd.from_ctx uctx in
  let f_constr = constr_of_monomorphic_global (Global.env ()) f_ref in
  let equation_lemma_type = subst1 f_constr equation_lemma_type in
  let info = Declare.Info.make () in
  let cinfo =
    Declare.CInfo.make ~name:eq_name
      ~typ:(EConstr.of_constr equation_lemma_type)
      ()
  in
  let lemma = Declare.Proof.start ~cinfo evd ~info in
  let lemma =
    fst
    @@ Declare.Proof.by
         (start_equation f_ref terminate_ref (fun x ->
              prove_eq
                (fun _ -> Proofview.tclUNIT ())
                { nb_arg
                ; f_terminate =
                    EConstr.of_constr
                      (constr_of_monomorphic_global (Global.env ()) terminate_ref)
                ; f_constr = EConstr.of_constr f_constr
                ; concl_tac = Tacticals.tclIDTAC
                ; func = functional_ref
                ; info =
                    instantiate_lambda Evd.empty
                      (EConstr.of_constr
                         (def_of_const
                            (constr_of_monomorphic_global (Global.env ()) functional_ref)))
                      (EConstr.of_constr f_constr :: List.map mkVar x)
                ; is_main_branch = true
                ; is_final = true
                ; values_and_bounds = []
                ; eqs = []
                ; forbidden_ids = []
                ; acc_inv = lazy (assert false)
                ; acc_id = Id.of_string "____"
                ; args_assoc = []
                ; f_id = Id.of_string "______"
                ; rec_arg_id = Id.of_string "______"
                ; is_mes = false
                ; ih = Id.of_string "______" }))
         lemma
  in
  let _ =
    Flags.silently
      (fun () ->
        let (_ : _ list) =
          Declare.Proof.save_regular ~proof:lemma ~opaque:opacity ~idopt:None
        in
        ())
      ()
  in
  ()

(*      Pp.msgnl (fun _ _ -> str "eqn finished"); *)

let recursive_definition ~interactive_proof ~is_mes function_name rec_impls
    type_of_f r rec_arg_num eq generate_induction_principle using_lemmas :
    Declare.Proof.t option =
  let open Term in
  let open Constr in
  let open CVars in
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, function_type =
    interp_type_evars ~program_mode:false env evd type_of_f
  in
  let function_r = Sorts.Relevant in
  (* TODO relevance *)
  let env =
    EConstr.push_named
      (Context.Named.Declaration.LocalAssum
         (make_annot function_name function_r, function_type))
      env
  in
  (* Pp.msgnl (str "function type := " ++ Printer.pr_lconstr function_type);  *)
  let evd, ty =
    interp_type_evars ~program_mode:false env evd ~impls:rec_impls eq
  in
  let evd = Evd.minimize_universes evd in
  let equation_lemma_type =
    Reductionops.nf_betaiotazeta env evd (Evarutil.nf_evar evd ty)
  in
  let function_type =
    EConstr.to_constr ~abort_on_undefined_evars:false evd function_type
  in
  let equation_lemma_type = EConstr.Unsafe.to_constr equation_lemma_type in
  (* Pp.msgnl (fun _ _ -> str "lemma type := " ++ Printer.pr_lconstr equation_lemma_type ++ fnl ()); *)
  let res_vars, eq' = decompose_prod equation_lemma_type in
  let env_eq' =
    Environ.push_rel_context
      (List.map (fun (x, y) -> LocalAssum (x, y)) res_vars)
      env
  in
  let eq' = Reductionops.nf_zeta env_eq' evd (EConstr.of_constr eq') in
  let eq' = EConstr.Unsafe.to_constr eq' in
  let res =
    (*     Pp.msgnl (fun _ _ -> str "res_var :=" ++ Printer.pr_lconstr_env (push_rel_context (List.map (function (x,t) -> (x,None,t)) res_vars) env) eq'); *)
    (*     Pp.msgnl (fun _ _ -> str "rec_arg_num := " ++ str (fun _ _ -> string_of_int rec_arg_num)); *)
    (*     Pp.msgnl (fun _ _ -> str "eq' := " ++ str (fun _ _ -> string_of_int rec_arg_num)); *)
    match Constr.kind eq' with
    | App (e, [|_; _; eq_fix|]) ->
      mkLambda
        ( make_annot (Name function_name) Sorts.Relevant
        , function_type
        , subst_var function_name (compose_lam res_vars eq_fix) )
    | _ -> failwith "Recursive Definition (res not eq)"
  in
  let pre_rec_args, function_type_before_rec_arg =
    decompose_prod_n (rec_arg_num - 1) function_type
  in
  let _, rec_arg_type, _ = destProd function_type_before_rec_arg in
  let arg_types =
    List.rev_map snd
      (fst (decompose_prod_n (List.length res_vars) function_type))
  in
  let equation_id = add_suffix function_name "_equation" in
  let functional_id = add_suffix function_name "_F" in
  let term_id = add_suffix function_name "_terminate" in
  let functional_ref =
    let univs = Evd.univ_entry ~poly:false evd in
    declare_fun functional_id Decls.(IsDefinition Definition) ~univs res
  in
  (* Refresh the global universes, now including those of _F *)
  let evd = Evd.from_env (Global.env ()) in
  let env_with_pre_rec_args =
    push_rel_context
      (List.map (function x, t -> LocalAssum (x, t)) pre_rec_args)
      env
  in
  let relation, evuctx = interp_constr env_with_pre_rec_args evd r in
  let evd = Evd.from_ctx evuctx in
  let tcc_lemma_name = add_suffix function_name "_tcc" in
  let tcc_lemma_constr = ref Undefined in
  (* let _ = Pp.msgnl (fun _ _ -> str "relation := " ++ Printer.pr_lconstr_env env_with_pre_rec_args relation) in *)
  let hook {Declare.Hook.S.uctx; _} =
    let term_ref = Nametab.locate (qualid_of_ident term_id) in
    let f_ref =
      declare_f function_name Decls.(IsProof Lemma) arg_types term_ref
    in
    let _ =
      Extraction_plugin.Table.extraction_inline true [qualid_of_ident term_id]
    in
    (*     message "start second proof"; *)
    let stop =
      (* XXX: What is the correct way to get sign at hook time *)
      try
        com_eqn uctx (List.length res_vars) equation_id functional_ref f_ref
          term_ref
          (subst_var function_name equation_lemma_type);
        false
      with e when CErrors.noncritical e ->
        if do_observe () then
          Feedback.msg_debug
            (str "Cannot create equation Lemma " ++ CErrors.print e ++ str ".")
        else
          CErrors.user_err
            ( str "Cannot create equation lemma."
            ++ spc ()
            ++ str "This may be because the function is nested-recursive." );
        true
    in
    if not stop then
      let eq_ref = Nametab.locate (qualid_of_ident equation_id) in
      let f_ref = destConst (constr_of_monomorphic_global (Global.env ()) f_ref)
      and functional_ref =
        destConst (constr_of_monomorphic_global (Global.env ()) functional_ref)
      and eq_ref = destConst (constr_of_monomorphic_global (Global.env ()) eq_ref) in
      generate_induction_principle f_ref tcc_lemma_constr functional_ref eq_ref
        rec_arg_num
        (EConstr.of_constr rec_arg_type)
        (nb_prod evd (EConstr.of_constr res))
        relation
  in
  (* XXX STATE Why do we need this... why is the toplevel protection not enough *)
  funind_purify
    (fun () ->
      com_terminate interactive_proof tcc_lemma_name tcc_lemma_constr is_mes
        functional_ref
        (EConstr.of_constr rec_arg_type)
        relation rec_arg_num term_id using_lemmas (List.length res_vars) evd
        (Declare.Hook.make hook))
    ()
