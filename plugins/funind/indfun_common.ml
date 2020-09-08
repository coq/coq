open Util
open Names
open Pp
open Constr
open Libnames
open Tacmach

let mk_prefix pre id = Id.of_string (pre ^ Id.to_string id)
let mk_rel_id = mk_prefix "R_"
let mk_correct_id id = Nameops.add_suffix (mk_rel_id id) "_correct"
let mk_complete_id id = Nameops.add_suffix (mk_rel_id id) "_complete"
let mk_equation_id id = Nameops.add_suffix id "_equation"

let fresh_id avoid s =
  Namegen.next_ident_away_in_goal (Id.of_string s) (Id.Set.of_list avoid)

let fresh_name avoid s = Name (fresh_id avoid s)

let get_name avoid ?(default = "H") = function
  | Anonymous -> fresh_name avoid default
  | Name n -> Name n

let array_get_start a = Array.init (Array.length a - 1) (fun i -> a.(i))
let locate qid = Nametab.locate qid

let locate_ind ref =
  match locate ref with GlobRef.IndRef x -> x | _ -> raise Not_found

let locate_constant ref =
  match locate ref with GlobRef.ConstRef x -> x | _ -> raise Not_found

let locate_with_msg msg f x = try f x with Not_found -> CErrors.user_err msg

let filter_map filter f =
  let rec it = function
    | [] -> []
    | e :: l -> if filter e then f e :: it l else it l
  in
  it

let chop_rlambda_n =
  let rec chop_lambda_n acc n rt =
    if n == 0 then (List.rev acc, rt)
    else
      match DAst.get rt with
      | Glob_term.GLambda (name, k, t, b) ->
        chop_lambda_n ((name, t, None) :: acc) (n - 1) b
      | Glob_term.GLetIn (name, v, t, b) ->
        chop_lambda_n ((name, v, t) :: acc) (n - 1) b
      | _ ->
        CErrors.user_err ~hdr:"chop_rlambda_n"
          (str "chop_rlambda_n: Not enough Lambdas")
  in
  chop_lambda_n []

let chop_rprod_n =
  let rec chop_prod_n acc n rt =
    if n == 0 then (List.rev acc, rt)
    else
      match DAst.get rt with
      | Glob_term.GProd (name, k, t, b) ->
        chop_prod_n ((name, t) :: acc) (n - 1) b
      | _ ->
        CErrors.user_err ~hdr:"chop_rprod_n"
          (str "chop_rprod_n: Not enough products")
  in
  chop_prod_n []

let list_union_eq eq_fun l1 l2 =
  let rec urec = function
    | [] -> l2
    | a :: l -> if List.exists (eq_fun a) l2 then urec l else a :: urec l
  in
  urec l1

let list_add_set_eq eq_fun x l = if List.exists (eq_fun x) l then l else x :: l
let coq_constant s = UnivGen.constr_of_monomorphic_global @@ Coqlib.lib_ref s

let find_reference sl s =
  let dp = Names.DirPath.make (List.rev_map Id.of_string sl) in
  Nametab.locate (make_qualid dp (Id.of_string s))

let eq = lazy (EConstr.of_constr (coq_constant "core.eq.type"))
let refl_equal = lazy (EConstr.of_constr (coq_constant "core.eq.refl"))

let with_full_print f a =
  let old_implicit_args = Impargs.is_implicit_args ()
  and old_strict_implicit_args = Impargs.is_strict_implicit_args ()
  and old_contextual_implicit_args = Impargs.is_contextual_implicit_args () in
  let old_rawprint = !Flags.raw_print in
  let old_printuniverses = !Constrextern.print_universes in
  let old_printallowmatchdefaultclause =
    Detyping.print_allow_match_default_clause ()
  in
  Constrextern.print_universes := true;
  Goptions.set_bool_option_value Detyping.print_allow_match_default_opt_name
    false;
  Flags.raw_print := true;
  Impargs.make_implicit_args false;
  Impargs.make_strict_implicit_args false;
  Impargs.make_contextual_implicit_args false;
  Dumpglob.pause ();
  try
    let res = f a in
    Impargs.make_implicit_args old_implicit_args;
    Impargs.make_strict_implicit_args old_strict_implicit_args;
    Impargs.make_contextual_implicit_args old_contextual_implicit_args;
    Flags.raw_print := old_rawprint;
    Constrextern.print_universes := old_printuniverses;
    Goptions.set_bool_option_value Detyping.print_allow_match_default_opt_name
      old_printallowmatchdefaultclause;
    Dumpglob.continue ();
    res
  with reraise ->
    Impargs.make_implicit_args old_implicit_args;
    Impargs.make_strict_implicit_args old_strict_implicit_args;
    Impargs.make_contextual_implicit_args old_contextual_implicit_args;
    Flags.raw_print := old_rawprint;
    Constrextern.print_universes := old_printuniverses;
    Goptions.set_bool_option_value Detyping.print_allow_match_default_opt_name
      old_printallowmatchdefaultclause;
    Dumpglob.continue ();
    raise reraise

(**********************)

type function_info =
  { function_constant : Constant.t
  ; graph_ind : inductive
  ; equation_lemma : Constant.t option
  ; correctness_lemma : Constant.t option
  ; completeness_lemma : Constant.t option
  ; rect_lemma : Constant.t option
  ; rec_lemma : Constant.t option
  ; prop_lemma : Constant.t option
  ; sprop_lemma : Constant.t option
  ; is_general : bool
        (* Has this function been defined using general recursive definition *)
  }

(* type function_db  = function_info list *)

(* let function_table = ref ([] : function_db) *)

let from_function = Summary.ref Cmap_env.empty ~name:"functions_db_fn"
let from_graph = Summary.ref Indmap.empty ~name:"functions_db_gr"

(*
let rec do_cache_info finfo = function
  | [] -> raise Not_found
  | (finfo'::finfos as l) ->
      if finfo' == finfo then l
      else if finfo'.function_constant = finfo.function_constant
      then finfo::finfos
      else
        let res = do_cache_info finfo finfos in
        if res == finfos then l else  finfo'::l


let cache_Function (_,(finfos)) =
  let new_tbl =
    try do_cache_info finfos !function_table
    with Not_found -> finfos::!function_table
  in
  if new_tbl != !function_table
  then function_table := new_tbl
*)

let cache_Function (_, finfos) =
  from_function := Cmap_env.add finfos.function_constant finfos !from_function;
  from_graph := Indmap.add finfos.graph_ind finfos !from_graph

let subst_Function (subst, finfos) =
  let do_subst_con c = Mod_subst.subst_constant subst c
  and do_subst_ind i = Mod_subst.subst_ind subst i in
  let function_constant' = do_subst_con finfos.function_constant in
  let graph_ind' = do_subst_ind finfos.graph_ind in
  let equation_lemma' = Option.Smart.map do_subst_con finfos.equation_lemma in
  let correctness_lemma' =
    Option.Smart.map do_subst_con finfos.correctness_lemma
  in
  let completeness_lemma' =
    Option.Smart.map do_subst_con finfos.completeness_lemma
  in
  let rect_lemma' = Option.Smart.map do_subst_con finfos.rect_lemma in
  let rec_lemma' = Option.Smart.map do_subst_con finfos.rec_lemma in
  let prop_lemma' = Option.Smart.map do_subst_con finfos.prop_lemma in
  let sprop_lemma' = Option.Smart.map do_subst_con finfos.sprop_lemma in
  if
    function_constant' == finfos.function_constant
    && graph_ind' == finfos.graph_ind
    && equation_lemma' == finfos.equation_lemma
    && correctness_lemma' == finfos.correctness_lemma
    && completeness_lemma' == finfos.completeness_lemma
    && rect_lemma' == finfos.rect_lemma
    && rec_lemma' == finfos.rec_lemma
    && prop_lemma' == finfos.prop_lemma
    && sprop_lemma' == finfos.sprop_lemma
  then finfos
  else
    { function_constant = function_constant'
    ; graph_ind = graph_ind'
    ; equation_lemma = equation_lemma'
    ; correctness_lemma = correctness_lemma'
    ; completeness_lemma = completeness_lemma'
    ; rect_lemma = rect_lemma'
    ; rec_lemma = rec_lemma'
    ; prop_lemma = prop_lemma'
    ; sprop_lemma = sprop_lemma'
    ; is_general = finfos.is_general }

let discharge_Function (_, finfos) = Some finfos

let pr_ocst env sigma c =
  Option.fold_right
    (fun v acc -> Printer.pr_lconstr_env env sigma (mkConst v))
    c (mt ())

let pr_info env sigma f_info =
  str "function_constant := "
  ++ Printer.pr_lconstr_env env sigma (mkConst f_info.function_constant)
  ++ fnl ()
  ++ str "function_constant_type := "
  ++ ( try
         Printer.pr_lconstr_env env sigma
           (fst
              (Typeops.type_of_global_in_context env
                 (GlobRef.ConstRef f_info.function_constant)))
       with e when CErrors.noncritical e -> mt () )
  ++ fnl () ++ str "equation_lemma := "
  ++ pr_ocst env sigma f_info.equation_lemma
  ++ fnl ()
  ++ str "completeness_lemma :="
  ++ pr_ocst env sigma f_info.completeness_lemma
  ++ fnl ()
  ++ str "correctness_lemma := "
  ++ pr_ocst env sigma f_info.correctness_lemma
  ++ fnl () ++ str "rect_lemma := "
  ++ pr_ocst env sigma f_info.rect_lemma
  ++ fnl () ++ str "rec_lemma := "
  ++ pr_ocst env sigma f_info.rec_lemma
  ++ fnl () ++ str "prop_lemma := "
  ++ pr_ocst env sigma f_info.prop_lemma
  ++ fnl () ++ str "graph_ind := "
  ++ Printer.pr_lconstr_env env sigma (mkInd f_info.graph_ind)
  ++ fnl ()

let pr_table env sigma tb =
  let l = Cmap_env.fold (fun k v acc -> v :: acc) tb [] in
  Pp.prlist_with_sep fnl (pr_info env sigma) l

let in_Function : function_info -> Libobject.obj =
  let open Libobject in
  declare_object
  @@ superglobal_object "FUNCTIONS_DB" ~cache:cache_Function
       ~subst:(Some subst_Function) ~discharge:discharge_Function

let find_or_none id =
  try
    Some
      ( match Nametab.locate (qualid_of_ident id) with
      | GlobRef.ConstRef c -> c
      | _ -> CErrors.anomaly (Pp.str "Not a constant.") )
  with Not_found -> None

let find_Function_infos f = Cmap_env.find_opt f !from_function
let find_Function_of_graph ind = Indmap.find_opt ind !from_graph

let update_Function finfo =
  (* Pp.msgnl (pr_info finfo); *)
  Lib.add_anonymous_leaf (in_Function finfo)

let add_Function is_general f =
  let f_id = Label.to_id (Constant.label f) in
  let equation_lemma = find_or_none (mk_equation_id f_id)
  and correctness_lemma = find_or_none (mk_correct_id f_id)
  and completeness_lemma = find_or_none (mk_complete_id f_id)
  and rect_lemma = find_or_none (Nameops.add_suffix f_id "_rect")
  and rec_lemma = find_or_none (Nameops.add_suffix f_id "_rec")
  and prop_lemma = find_or_none (Nameops.add_suffix f_id "_ind")
  and sprop_lemma = find_or_none (Nameops.add_suffix f_id "_sind")
  and graph_ind =
    match Nametab.locate (qualid_of_ident (mk_rel_id f_id)) with
    | GlobRef.IndRef ind -> ind
    | _ -> CErrors.anomaly (Pp.str "Not an inductive.")
  in
  let finfos =
    { function_constant = f
    ; equation_lemma
    ; completeness_lemma
    ; correctness_lemma
    ; rect_lemma
    ; rec_lemma
    ; prop_lemma
    ; sprop_lemma
    ; graph_ind
    ; is_general }
  in
  update_Function finfos

let pr_table env sigma = pr_table env sigma !from_function

(*********************************)
(* Debugging *)

let do_rewrite_dependent =
  Goptions.declare_bool_option_and_ref ~depr:false
    ~key:["Functional"; "Induction"; "Rewrite"; "Dependent"]
    ~value:true

let do_observe =
  Goptions.declare_bool_option_and_ref ~depr:false ~key:["Function_debug"]
    ~value:false

let observe strm = if do_observe () then Feedback.msg_debug strm else ()
let debug_queue = Stack.create ()

let print_debug_queue b e =
  if not (Stack.is_empty debug_queue) then
    let lmsg, goal = Stack.pop debug_queue in
    if b then
      Feedback.msg_debug
        (hov 1
           ( lmsg
           ++ (str " raised exception " ++ CErrors.print e)
           ++ str " on goal" ++ fnl () ++ goal ))
    else
      Feedback.msg_debug
        (hov 1 (str " from " ++ lmsg ++ str " on goal" ++ fnl () ++ goal))

(* print_debug_queue false e; *)

let do_observe_tac s tac g =
  let goal = Printer.pr_goal g in
  let s = s (pf_env g) (project g) in
  let lmsg = str "observation : " ++ s in
  Stack.push (lmsg, goal) debug_queue;
  try
    let v = tac g in
    ignore (Stack.pop debug_queue);
    v
  with reraise ->
    let reraise = Exninfo.capture reraise in
    if not (Stack.is_empty debug_queue) then
      print_debug_queue true (fst reraise);
    Exninfo.iraise reraise

let observe_tac s tac g =
  if do_observe () then do_observe_tac s tac g else tac g

module New = struct
  let do_observe_tac ~header s tac =
    let open Proofview.Notations in
    let open Proofview in
    Goal.enter (fun gl ->
        let goal = Printer.pr_goal (Goal.print gl) in
        let env, sigma = (Goal.env gl, Goal.sigma gl) in
        let s = s env sigma in
        let lmsg = seq [header; str " : " ++ s] in
        tclLIFT (NonLogical.make (fun () -> Feedback.msg_debug (s ++ fnl ())))
        >>= fun () ->
        tclOR
          ( Stack.push (lmsg, goal) debug_queue;
            tac
            >>= fun v ->
            ignore (Stack.pop debug_queue);
            Proofview.tclUNIT v )
          (fun (exn, info) ->
            if not (Stack.is_empty debug_queue) then print_debug_queue true exn;
            tclZERO ~info exn))

  let observe_tac ~header s tac =
    if do_observe () then do_observe_tac ~header s tac else tac
end

let is_strict_tcc =
  Goptions.declare_bool_option_and_ref ~depr:false ~key:["Function_raw_tcc"]
    ~value:false

exception Building_graph of exn
exception Defining_principle of exn
exception ToShow of exn

let jmeq () =
  try
    Coqlib.check_required_library Coqlib.jmeq_module_name;
    EConstr.of_constr @@ UnivGen.constr_of_monomorphic_global
    @@ Coqlib.lib_ref "core.JMeq.type"
  with e when CErrors.noncritical e -> raise (ToShow e)

let jmeq_refl () =
  try
    Coqlib.check_required_library Coqlib.jmeq_module_name;
    EConstr.of_constr @@ UnivGen.constr_of_monomorphic_global
    @@ Coqlib.lib_ref "core.JMeq.refl"
  with e when CErrors.noncritical e -> raise (ToShow e)

let h_intros l =
  Proofview.V82.of_tactic
    (Tacticals.New.tclMAP (fun x -> Tactics.Simple.intro x) l)

let h_id = Id.of_string "h"
let hrec_id = Id.of_string "hrec"

let well_founded = function
  | () -> EConstr.of_constr (coq_constant "core.wf.well_founded")

let acc_rel = function () -> EConstr.of_constr (coq_constant "core.wf.acc")

let acc_inv_id = function
  | () -> EConstr.of_constr (coq_constant "core.wf.acc_inv")

let well_founded_ltof () =
  EConstr.of_constr (coq_constant "num.nat.well_founded_ltof")

let ltof_ref = function () -> find_reference ["Coq"; "Arith"; "Wf_nat"] "ltof"

let make_eq () =
  try
    EConstr.of_constr
      (UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref "core.eq.type"))
  with _ -> assert false

let evaluable_of_global_reference r =
  (* Tacred.evaluable_of_global_reference (Global.env ()) *)
  match r with
  | GlobRef.ConstRef sp -> EvalConstRef sp
  | GlobRef.VarRef id -> EvalVarRef id
  | _ -> assert false

let list_rewrite (rev : bool) (eqs : (EConstr.constr * bool) list) =
  let open Tacticals in
  (tclREPEAT
     (List.fold_right
        (fun (eq, b) i ->
          tclORELSE
            (Proofview.V82.of_tactic
               ((if b then Equality.rewriteLR else Equality.rewriteRL) eq))
            i)
        (if rev then List.rev eqs else eqs)
        (tclFAIL 0 (mt ()))) [@ocaml.warning "-3"])

let decompose_lam_n sigma n =
  if n < 0 then
    CErrors.user_err
      Pp.(str "decompose_lam_n: integer parameter must be positive");
  let rec lamdec_rec l n c =
    if Int.equal n 0 then (l, c)
    else
      match EConstr.kind sigma c with
      | Lambda (x, t, c) -> lamdec_rec ((x, t) :: l) (n - 1) c
      | Cast (c, _, _) -> lamdec_rec l n c
      | _ ->
        CErrors.user_err Pp.(str "decompose_lam_n: not enough abstractions")
  in
  lamdec_rec [] n

let lamn n env b =
  let open EConstr in
  let rec lamrec = function
    | 0, env, b -> b
    | n, (v, t) :: l, b -> lamrec (n - 1, l, mkLambda (v, t, b))
    | _ -> assert false
  in
  lamrec (n, env, b)

(* compose_lam [xn:Tn;..;x1:T1] b = [x1:T1]..[xn:Tn]b *)
let compose_lam l b = lamn (List.length l) l b

(* prodn n [xn:Tn;..;x1:T1;Gamma] b = (x1:T1)..(xn:Tn)b *)
let prodn n env b =
  let open EConstr in
  let rec prodrec = function
    | 0, env, b -> b
    | n, (v, t) :: l, b -> prodrec (n - 1, l, mkProd (v, t, b))
    | _ -> assert false
  in
  prodrec (n, env, b)

(* compose_prod [xn:Tn;..;x1:T1] b = (x1:T1)..(xn:Tn)b *)
let compose_prod l b = prodn (List.length l) l b

type tcc_lemma_value = Undefined | Value of constr | Not_needed

(* We only "purify" on exceptions. XXX: What is this doing here? *)
let funind_purify f x =
  let st = Vernacstate.freeze_interp_state ~marshallable:false in
  try f x
  with e ->
    let e = Exninfo.capture e in
    Vernacstate.unfreeze_interp_state st;
    Exninfo.iraise e

let tac_type_of g c =
  let sigma, t = Tacmach.pf_type_of g c in
  ({g with Evd.sigma}, t)

(*
   The general form of an induction principle is the following:

   forall prm1 prm2 ... prmp,                          (induction parameters)
   forall Q1...,(Qi:Ti_1 -> Ti_2 ->...-> Ti_ni),...Qq, (predicates)
   branch1, branch2, ... , branchr,                    (branches of the principle)
   forall (x1:Ti_1) (x2:Ti_2) ... (xni:Ti_ni),         (induction arguments)
   (HI: I prm1..prmp x1...xni)                         (optional main induction arg)
   -> (Qi x1...xni HI        (f prm1...prmp x1...xni)).(conclusion)
                   ^^        ^^^^^^^^^^^^^^^^^^^^^^^^
               optional        optional argument added if
               even if HI    principle generated by functional
             present above   induction, only if HI does not exist
             [indarg]                  [farg]

  HI is not present when the induction principle does not come directly from an
  inductive type (like when it is generated by functional induction for
  example). HI is present otherwise BUT may not appear in the conclusion
  (dependent principle). HI and (f...) cannot be both present.

  Principles taken from functional induction have the final (f...).*)

open EConstr
open Vars
open Termops

(* [rel_contexts] and [rel_declaration] actually contain triples, and
   lists are actually in reverse order to fit [compose_prod]. *)
type elim_scheme = {
  params: rel_context;      (* (prm1,tprm1);(prm2,tprm2)...(prmp,tprmp) *)
  nparams: int;               (* number of parameters *)
  predicates: rel_context;  (* (Qq, (Tq_1 -> Tq_2 ->...-> Tq_nq)), (Q1,...) *)
  npredicates: int;           (* Number of predicates *)
  branches: rel_context;    (* branchr,...,branch1 *)
  nbranches: int;             (* Number of branches *)
  args: rel_context;        (* (xni, Ti_ni) ... (x1, Ti_1) *)
  nargs: int;                 (* number of arguments *)
  concl: types;             (* Qi x1...xni HI (f...), HI and (f...)
                               are optional and mutually exclusive *)
  farg_in_concl: bool;        (* true if (f...) appears at the end of conclusion *)
}

type elim_metadata = {
  indarg: types option;     (* Some (I prm1..prmp x1...xni)
                                               if HI is in premisses, None otherwise *)
  indref: GlobRef.t option;
  indarg_in_concl: bool;      (* true if HI appears at the end of conclusion *)
  deppos: int list;
}

let occur_rel sigma n c =
  let res = not (noccurn sigma n c) in
  res

let error_ind_scheme s =
  let s = if not (String.is_empty s) then s^" " else s in
  CErrors.user_err ~hdr:"Tactics" (str "Cannot recognize " ++ str s ++ str "an induction scheme.")

(* This function splits the products of the induction scheme [elimt] into four
   parts:
   - branches, easily detectable (they are not referred by rels in the subterm)
   - what was found before branches (acc1) that is: parameters and predicates
   - what was found after branches (acc3) that is: args and indarg if any
   if there is no branch, we try to fill in acc3 with args/indargs.
   We also return the conclusion.
*)
let decompose_paramspred_branch_args sigma elimt =
  let open Context.Rel.Declaration in
  let rec cut_noccur elimt acc2 =
    match EConstr.kind sigma elimt with
      | Prod(nme,tpe,elimt') ->
          let hd_tpe,_ = decompose_app sigma (snd (decompose_prod_assum sigma tpe)) in
          if not (occur_rel sigma 1 elimt') && isRel sigma hd_tpe
          then cut_noccur elimt' (LocalAssum (nme,tpe)::acc2)
          else let acc3,ccl = decompose_prod_assum sigma elimt in acc2 , acc3 , ccl
      | App(_, _) | Rel _ -> acc2 , [] , elimt
      | _ -> error_ind_scheme "" in
  let rec cut_occur elimt acc1 =
    match EConstr.kind sigma elimt with
      | Prod(nme,tpe,c) when occur_rel sigma 1 c -> cut_occur c (LocalAssum (nme,tpe)::acc1)
      | Prod(nme,tpe,c) -> let acc2,acc3,ccl = cut_noccur elimt [] in acc1,acc2,acc3,ccl
      | App(_, _) | Rel _ -> acc1,[],[],elimt
      | _ -> error_ind_scheme "" in
  let acc1, acc2 , acc3, ccl = cut_occur elimt [] in
  (* Particular treatment when dealing with a dependent empty type elim scheme:
     if there is no branch, then acc1 contains all hyps which is wrong (acc1
     should contain parameters and predicate only). This happens for an empty
     type (See for example Empty_set_ind, as False would actually be ok). Then
     we must find the predicate of the conclusion to separate params_pred from
     args. We suppose there is only one predicate here. *)
  match acc2 with
  | [] ->
    let hyps,ccl = decompose_prod_assum sigma elimt in
    let hd_ccl_pred,_ = decompose_app sigma ccl in
    begin match EConstr.kind sigma hd_ccl_pred with
      | Rel i  -> let acc3,acc1 = List.chop (i-1) hyps in acc1 , [] , acc3 , ccl
      | _ -> error_ind_scheme ""
    end
  | _ -> acc1, acc2 , acc3, ccl

let exchange_hd_app sigma subst_hd t =
  let hd,args= decompose_app sigma t in mkApp (subst_hd,Array.of_list args)

(* Builds an elim_scheme from its type and calling form (const+binding). We
   first separate branches.  We obtain branches, hyps before (params + preds),
   hyps after (args <+ indarg if present>) and conclusion.  Then we proceed as
   follows:

   - separate parameters and predicates in params_preds. For that we build:
 forall (x1:Ti_1)(xni:Ti_ni) (HI:I prm1..prmp x1...xni), DUMMY x1...xni HI/farg
                             ^^^^^^^^^^^^^^^^^^^^^^^^^                  ^^^^^^^
                                       optional                           opt
     Free rels appearing in this term are parameters (branches should not
     appear, and the only predicate would have been Qi but we replaced it by
     DUMMY). We guess this heuristic catches all params.  TODO: generalize to
     the case where args are merged with branches (?) and/or where several
     predicates are cited in the conclusion.

   - finish to fill in the elim_scheme: indarg/farg/args and finally indref. *)
let decompose_elim_scheme sigma elimt =
  let params_preds,branches,args,concl =
    decompose_paramspred_branch_args sigma elimt in

  let ccl = exchange_hd_app sigma (mkVar (Id.of_string "__QI_DUMMY__")) concl in
  let concl_with_args = it_mkProd_or_LetIn ccl args in
  let nparams = Int.Set.cardinal (free_rels sigma concl_with_args) in
  let predicates,params = List.chop (List.length params_preds - nparams) params_preds in
  let farg_in_concl = isApp sigma ccl && isApp sigma (last_arg sigma ccl) in
  {
    concl; params; nparams;
    predicates; npredicates = List.length predicates;
    branches; nbranches = List.length branches;
    farg_in_concl; args; nargs = List.length args
  }

let compute_elim_metadata sigma scheme =
  (* First see if (f x...) is in the conclusion. *)
  if scheme.farg_in_concl then
    { indarg_in_concl = false; indarg = None; indref = None; deppos = []}
  else
    let open Context.Rel.Declaration in
    let rec aux k = function
    | [] -> { indarg_in_concl = false; indarg = None; indref = None; deppos = []}
    | LocalDef (hiname,_,hi)::args -> aux (k+1) args
    | LocalAssum (hiname,hi)::args ->
        (* Look at last arg: is it the indarg? *)
       let hi_ind, hi_args = decompose_app sigma hi in
       let hi_is_ref = isRef sigma hi_ind in
       let hi_nargs = List.length hi_args in
       if hi_is_ref && Int.equal hi_nargs (scheme.nparams + List.length args) then
         let f i l c = if dependent sigma (lift k c) scheme.concl then i::l else l in
         let deppos = List.fold_left_i f 1 [] hi_args in
         { indarg_in_concl = occur_rel sigma 1 scheme.concl;
           indarg = Some hi; indref = Some (fst (destRef sigma hi_ind)); deppos }
       else
         { indarg_in_concl = false; indarg = None; indref = None; deppos = []} in
    aux 1 scheme.args
