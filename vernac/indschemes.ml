(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Hugo Herbelin from contents related to inductive schemes
   initially developed by Christine Paulin (induction schemes), Vincent
   Siles (decidable equality and boolean equality) and Matthieu Sozeau
   (combined scheme) in file command.ml, Sep 2009 *)

(* This file provides entry points for manually or automatically
   declaring new schemes *)

open Pp
open Names
open Util
open Declarations
open Term
open Goptions
open Vernacexpr
open Ind_tables
open Auto_ind_decl
open Eqschemes
open Elimschemes
open Sorts

(** Data of an inductive scheme with name resolved *)
type resolved_scheme = Names.Id.t CAst.t * Indrec.dep_flag * Names.inductive * UnivGen.QualityOrSet.t

(** flag for internal message display *)
type internal_flag =
  | UserAutomaticRequest (* kernel action, a message is displayed *)
  | UserIndividualRequest   (* user action, a message is displayed *)

(* Flags governing automatic synthesis of schemes *)

let elim_flag = ref true
let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Elimination";"Schemes"];
      optread  = (fun () -> !elim_flag) ;
      optwrite = (fun b -> elim_flag := b) }

let bifinite_elim_flag = ref false
let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Nonrecursive";"Elimination";"Schemes"];
      optread  = (fun () -> !bifinite_elim_flag) ;
      optwrite = (fun b -> bifinite_elim_flag := b) }

let case_flag = ref false
let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Case";"Analysis";"Schemes"];
      optread  = (fun () -> !case_flag) ;
      optwrite = (fun b -> case_flag := b) }

let eq_flag = ref false
let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Boolean";"Equality";"Schemes"];
      optread  = (fun () -> !eq_flag) ;
      optwrite = (fun b -> eq_flag := b) }

let is_eq_flag () = !eq_flag

let eq_dec_flag = ref false
let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Decidable";"Equality";"Schemes"];
      optread  = (fun () -> !eq_dec_flag) ;
      optwrite = (fun b -> eq_dec_flag := b) }

let rewriting_flag = ref false
let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Rewriting";"Schemes"];
      optread  = (fun () -> !rewriting_flag) ;
      optwrite = (fun b -> rewriting_flag := b) }

(* Util *)
let define ~poly ~cumulative ?loc name sigma c types =
  let poly =
    PolyFlags.make ~univ_poly:poly
      ~collapse_sort_variables:true (* FIXME sort_poly not supported *)
      ~cumulative
  in
  let info = Declare.Info.make ~poly () in
  let cinfo = Declare.CInfo.make ~name ~typ:types () in
  let fth_ref = Declare.declare_definition ~info:info ~cinfo:cinfo ~opaque:false ~body:c sigma in
  fth_ref

(* Boolean equality *)

let declare_beq_scheme_gen ?locmap names kn =
  ignore (define_mutual_scheme ?locmap beq_scheme_kind names kn)

let debug = CDebug.create ~name:"indschemes" ()

let alarm what internal msg =
  match internal with
  | UserAutomaticRequest ->
    debug Pp.(fun () ->
        hov 0 msg ++ fnl () ++ what ++ str " not defined.");
    None
  | UserIndividualRequest -> Some msg

let try_declare_scheme ?locmap what f internal names kn =
  try f ?locmap names kn
  with e when CErrors.noncritical e ->
  let e = Exninfo.capture e in
  let rec extract_exn = function Logic_monad.TacticFailure e -> extract_exn e | e -> e in
  let msg = match extract_exn (fst e) with
    | ParameterWithoutEquality cst ->
        alarm what internal
          (str "Boolean equality not found for parameter " ++ Printer.pr_global cst ++
           str".")
    | InductiveWithProduct ->
        alarm what internal
          (str "Unable to decide equality of functional arguments.")
    | InductiveWithSort ->
        alarm what internal
          (str "Unable to decide equality of type arguments.")
    | NonSingletonProp ind ->
        alarm what internal
          (str "Cannot extract computational content from proposition " ++
           quote (Printer.pr_inductive (Global.env()) ind) ++ str ".")
    | EqNotFound ind' ->
        alarm what internal
          (str "Boolean equality on " ++
           quote (Printer.pr_inductive (Global.env()) ind') ++
           strbrk " is missing.")
    | UndefinedCst s ->
        alarm what internal
          (strbrk "Required constant " ++ str s ++ str " undefined.")
    | DeclareUniv.AlreadyDeclared (kind, id) as exn ->
      let msg = CErrors.print exn in
      alarm what internal msg
    | DecidabilityMutualNotSupported ->
        alarm what internal
          (str "Decidability lemma for mutual inductive types not supported.")
    | EqUnknown s ->
         alarm what internal
           (str "Found unsupported " ++ str s ++ str " while building Boolean equality.")
    | NoDecidabilityCoInductive ->
         alarm what internal
           (str "Scheme Equality is only for inductive types.")
    | DecidabilityIndicesNotSupported ->
         alarm what internal
           (str "Inductive types with indices not supported.")
    | ConstructorWithNonParametricInductiveType ind ->
         alarm what internal
           (strbrk "Unsupported constructor with an argument whose type is a non-parametric inductive type." ++
            strbrk " Type " ++ quote (Printer.pr_inductive (Global.env()) ind) ++
            str " is applied to an argument which is not a variable.")
    | InternalDependencies ->
         alarm what internal
           (strbrk "Inductive types with internal dependencies in constructors not supported.")
    | e ->
        alarm what internal
          (str "Unexpected error during scheme creation: " ++ CErrors.print e)
  in
  match msg with
  | None -> ()
  | Some msg -> Exninfo.iraise (CErrors.UserError msg, snd e)

let beq_scheme_msg mind =
  let mib = Global.lookup_mind mind in
  (* TODO: mutual inductive case *)
  str "Boolean equality on " ++
    pr_enum (fun ind -> quote (Printer.pr_inductive (Global.env()) ind))
    (List.init (Array.length mib.mind_packets) (fun i -> (mind,i)))

let declare_beq_scheme_with ?locmap l kn =
  try_declare_scheme (beq_scheme_msg kn) declare_beq_scheme_gen UserIndividualRequest l kn

let try_declare_beq_scheme ?locmap kn =
  (* TODO: handle Fix, eventually handle
      proof-irrelevance; improve decidability by depending on decidability
      for the parameters rather than on the bl and lb properties *)
  try_declare_scheme (beq_scheme_msg kn) declare_beq_scheme_gen UserAutomaticRequest [] kn

let declare_beq_scheme ?locmap mi = declare_beq_scheme_with ?locmap [] mi

(* Case analysis schemes *)
let declare_one_case_analysis_scheme ?loc ind =
  let (mib, mip) as specif = Global.lookup_inductive ind in
  let kind = Elimschemes.pseudo_sort_quality_for_elim ind mip in
  let dep, suff =
    if Sorts.Quality.is_qprop kind then case_nodep, Some "case"
    else if not (Inductiveops.always_dependent_elim specif) then
      case_nodep, None
    else case_dep, Some "case" in
  let id = match suff with
    | None -> None
    | Some suff ->
      (* the auto generated eliminator may be called "case" instead of eg "case_nodep" *)
      Some Names.(Id.of_string (Id.to_string mip.mind_typename ^ "_" ^ suff))
  in
  let kelim = Inductiveops.elim_sort (mib,mip) in
  if Inductive.raw_eliminates_to (UnivGen.QualityOrSet.quality kelim) Sorts.Quality.qtype then
    define_individual_scheme ?loc dep id ind

(* Induction/recursion schemes *)

let declare_one_induction_scheme ?loc ind =
  let (mib,mip) as specif = Global.lookup_inductive ind in
  let kind = Elimschemes.pseudo_sort_quality_for_elim ind mip in
  let from_prop = Sorts.Quality.is_qprop kind in
  let depelim = Inductiveops.always_dependent_elim specif in
  let kelim mip = Inductiveops.constant_sorts_below
              @@ Inductiveops.elim_sort (mib,mip) in
  let kelim =
    List.fold_right (fun x acc ->
      List.intersect UnivGen.QualityOrSet.equal acc x)
    (List.map kelim (Array.to_list mib.mind_packets))
    [UnivGen.QualityOrSet.qtype; UnivGen.QualityOrSet.prop; UnivGen.QualityOrSet.set; UnivGen.QualityOrSet.sprop] in
  let kelim =
    if Global.sprop_allowed ()
    then kelim
    else List.filter (fun s -> not (UnivGen.QualityOrSet.is_sprop s)) kelim
  in
  let elims =
    List.filter (fun (sort,_) -> List.mem_f UnivGen.QualityOrSet.equal sort kelim)
      [(UnivGen.QualityOrSet.qtype, "rect");
       (UnivGen.QualityOrSet.prop, "ind");
       (UnivGen.QualityOrSet.set, "rec");
       (UnivGen.QualityOrSet.sprop, "sind")]
  in
  let elims = List.map (fun (to_kind,dflt_suff) ->
      if from_prop then elim_scheme ~dep:false ~to_kind, Some dflt_suff
      else if depelim then elim_scheme ~dep:true ~to_kind, Some dflt_suff
      else elim_scheme ~dep:false ~to_kind, None)
      elims
  in
  List.iter (fun (kind, suff) ->
      let id = match suff with
        | None -> None
        | Some suff ->
          (* the auto generated eliminator may be called "rect" instead of eg "rect_dep" *)
          Some Names.(Id.of_string (Id.to_string mip.mind_typename ^ "_" ^ suff))
      in
      define_individual_scheme ?loc kind id ind)
         elims

let declare_induction_schemes ?(locmap=Locmap.default None) kn =
  let mib = Global.lookup_mind kn in
  if mib.mind_finite <> Declarations.CoFinite then begin
    for i = 0 to Array.length mib.mind_packets - 1 do
      let loc = Ind_tables.Locmap.lookup ~locmap (kn,i) in
      declare_one_induction_scheme (kn,i) ?loc;
    done;
  end

(* Decidable equality *)

let declare_eq_decidability_gen ?locmap names kn =
  let mib = Global.lookup_mind kn in
  if mib.mind_finite <> Declarations.CoFinite then
    define_mutual_scheme ?locmap eq_dec_scheme_kind names kn

let eq_dec_scheme_msg ind = (* TODO: mutual inductive case *)
  str "Decidable equality on " ++ quote (Printer.pr_inductive (Global.env()) ind)

let declare_eq_decidability_scheme_with ?locmap l kn =
  try_declare_scheme ?locmap (eq_dec_scheme_msg (kn,0))
    declare_eq_decidability_gen UserIndividualRequest l kn

let try_declare_eq_decidability ?locmap kn =
  try_declare_scheme ?locmap (eq_dec_scheme_msg (kn,0))
    declare_eq_decidability_gen UserAutomaticRequest [] kn

let declare_eq_decidability ?locmap mi = declare_eq_decidability_scheme_with ?locmap [] mi

let ignore_error f x =
  try f x with e when CErrors.noncritical e -> ()

let declare_rewriting_schemes ?loc ind =
  if Hipattern.is_inductive_equality (Global.env ()) ind then begin
    (* Expect the equality to be symmetric *)
    ignore_error (define_individual_scheme ?loc sym_scheme_kind None) ind;
    define_individual_scheme ?loc rew_r2l_scheme_kind None ind;
    define_individual_scheme ?loc rew_r2l_dep_scheme_kind None ind;
    define_individual_scheme ?loc rew_r2l_forward_dep_scheme_kind None ind;
    (* These ones expect the equality to be symmetric; the first one also *)
    (* needs eq *)
    ignore_error (define_individual_scheme rew_l2r_scheme_kind None) ind;
    ignore_error
      (define_individual_scheme ?loc sym_involutive_scheme_kind None) ind;
    ignore_error
      (define_individual_scheme ?loc rew_l2r_dep_scheme_kind None) ind;
    ignore_error
      (define_individual_scheme ?loc rew_l2r_forward_dep_scheme_kind None) ind
  end

let warn_cannot_build_congruence =
  CWarnings.create ~name:"cannot-build-congruence" ~category:CWarnings.CoreCategories.automation
         (fun () ->
          strbrk "Cannot build congruence scheme because eq is not found")

let declare_congr_scheme ?loc ind =
  let env = Global.env () in
  if Hipattern.is_inductive_equality env ind then begin
    match Rocqlib.lib_ref_opt "core.eq.type" with
    | Some _ -> define_individual_scheme ?loc congr_scheme_kind None ind
    | None -> warn_cannot_build_congruence ()
  end

(* Scheme command *)

(* Boolean on scheme_type cheking if it considered dependent *)
let sch_isdep = function
| SchemeInduction  | SchemeElimination -> true
| SchemeMinimality | SchemeCase        -> false

let sch_isrec = function
| SchemeInduction | SchemeMinimality -> true
| SchemeElimination | SchemeCase -> false

(* Generate suffix for scheme given a target sort *)
let scheme_suffix_gen {sch_type; sch_sort} sort =
  let open Quality in
  let ind_suffix = match sch_isrec sch_type, sch_sort with
    (* The elimination suffix _ind/_sind/_rec/_rect *)
    | true  , Qual (QConstant QProp) -> "_ind"
    | true  , Qual (QConstant QSProp) -> "_sind"
    | true  , Qual (QConstant QType) -> "_rect"
    | true  , Set -> "_rec"
    (* The _case suffix *)
    | false , Qual (QConstant QSProp) -> "_scase"
    | false , Qual (QConstant QType) -> "_caset"
    | false , _ -> "_case"
    | _     , Qual (QVar _ | QGlobal _) -> assert false in
  (* Some schemes are deliminated with _dep or no_dep *)
  let dep_suffix = match sch_isdep sch_type , sort with
    | true  , QConstant QProp  -> "_dep"
    | false , QConstant QType
    | false , QConstant QSProp -> "_nodep"
    | _ , _                    -> "" in
  ind_suffix ^ dep_suffix

let smart_ind qid =
  let ind = Smartlocate.smart_global_inductive qid in
  if Dumpglob.dump() then Dumpglob.add_glob ?loc:qid.loc (IndRef ind);
  ind

(* Resolve the name of a scheme using an environment and extract some
   important data such as the inductive type involved, whether it is a dependent
   eliminator and its sort. *)
let name_and_process_scheme env = function
  | (Some id, {sch_type; sch_qualid; sch_sort}) ->
    (id, sch_isdep sch_type, smart_ind sch_qualid, sch_sort)
  | (None, ({sch_type; sch_qualid; sch_sort} as sch)) ->
    (* If no name has been provided, we build one from the types of the ind requested *)
    let ind = smart_ind sch_qualid in
    let sort_of_ind =
      Elimschemes.pseudo_sort_quality_for_elim ind
        (snd (Inductive.lookup_mind_specif env ind))
    in
    let suffix = scheme_suffix_gen sch sort_of_ind in
    let newid = Nameops.add_suffix (Nametab.basename_of_global (Names.GlobRef.IndRef ind)) suffix in
    let newref = CAst.make newid in
    (newref, sch_isdep sch_type, ind, sch_sort)

let do_mutual_induction_scheme ~register ?(force_mutual=false) env ?(isrec=true) l =
  let sigma = Evd.from_env env in
  let _,_,ind,_ = match l with | x::_ -> x | [] -> assert false in
  let sigma, (ind, inst) = Evd.fresh_inductive_instance env sigma ~rigid:UnivRigid ind in
  let sigma, lrecspec =
    List.fold_left_map (fun sigma (_,dep,ind,sort) ->
        let sigma, sort = Evd.fresh_sort_in_quality ~rigid:UnivRigid sigma sort in
        (sigma, (ind,dep,sort)))
      sigma
      l
  in
  let sigma, listdecl =
    if isrec then Indrec.build_mutual_induction_scheme env sigma ~force_mutual lrecspec inst
    else
      List.fold_left_map (fun sigma (ind,dep,sort) ->
          let sigma, c, _ = Indrec.build_case_analysis_scheme env sigma (ind, inst) dep sort in
          sigma, c)
        sigma lrecspec
  in
  let poly, cumulative =
    (* NB: build_mutual_induction_scheme forces nonempty list of mutual inductives
       (force_mutual is about the generated schemes) *)
    let _,_,ind,_ = List.hd l in
    Global.is_polymorphic (Names.GlobRef.IndRef ind),
    Global.is_cumulative (Names.GlobRef.IndRef ind)
  in
  let is_mutual = isrec && List.length listdecl > 1 in
  let declare decl ({CAst.v=fi; loc},dep,ind, sort) =
    let decltype = Retyping.get_type_of env sigma decl in
    let cst = define ?loc ~poly ~cumulative fi sigma decl (Some decltype) in
    let kind =
      let open Elimschemes in
      let open UnivGen.QualityOrSet in
      if not register then None
      else if is_mutual then None (* don't make induction use mutual schemes *)
      else if isrec then Some (elim_scheme ~dep ~to_kind:sort)
      else match sort with
        | Qual (QConstant QType) -> Some (if dep then case_dep else case_nodep)
        | Qual (QConstant QProp) -> Some (if dep then casep_dep else casep_nodep)
        | Qual (QConstant QSProp) -> Some (if dep then scase_dep else scase_nodep)
        | Set | Qual (QVar _ | QGlobal _) ->
          (* currently we don't have standard scheme kinds for this *)
          None
    in
    match kind with
    | None -> ()
    | Some kind ->
      (* TODO locality *)
      DeclareScheme.declare_scheme SuperGlobal (Ind_tables.scheme_kind_name kind) (GlobRef.IndRef ind, cst)
  in
  let () = List.iter2 declare listdecl l in
  let lrecnames = List.map (fun ({CAst.v},_,_,_) -> v) l in
  Declare.fixpoint_message None lrecnames

let do_scheme ~register env l =
  let isrec = match l with
    | [_, sch] -> sch_isrec sch.sch_type
    | _ ->
      if List.for_all (fun (_,sch) -> sch_isrec sch.sch_type) l
      then true
      else CErrors.user_err Pp.(str "Mutually defined schemes should be recursive.")
  in
  let lnamedepindsort = List.map (name_and_process_scheme env) l in
  do_mutual_induction_scheme ~register env ~isrec lnamedepindsort

let do_scheme_equality ?locmap sch id =
  let mind,_ as ind = smart_ind id in
  match sch with
  | SchemeBooleanEquality | SchemeEquality ->
    declare_beq_scheme ?locmap mind;
    if sch = SchemeEquality then declare_eq_decidability ?locmap mind
  | SchemeRewriting ->
    let loc = Option.bind locmap (fun locmap -> Locmap.lookup ~locmap ind) in
    declare_rewriting_schemes ?loc ind

(**********************************************************************)
(* Combined scheme *)
(* Matthieu Sozeau, Dec 2006 *)

let list_split_rev_at index l =
  let rec aux i acc = function
      hd :: tl when Int.equal i index -> acc, tl
    | hd :: tl -> aux (succ i) (hd :: acc) tl
    | [] -> failwith "List.split_when: Invalid argument"
  in aux 0 [] l

let fold_left' f = function
    [] -> invalid_arg "fold_left'"
  | hd :: tl -> List.fold_left f hd tl

let mk_rocq_and sigma = Evd.fresh_global (Global.env ()) sigma (Rocqlib.lib_ref "core.and.type")
let mk_rocq_conj sigma = Evd.fresh_global (Global.env ()) sigma (Rocqlib.lib_ref "core.and.conj")

let mk_rocq_prod sigma = Evd.fresh_global (Global.env ()) sigma (Rocqlib.lib_ref "core.prod.type")
let mk_rocq_pair sigma = Evd.fresh_global (Global.env ()) sigma (Rocqlib.lib_ref "core.prod.intro")

let build_combined_scheme env schemes =
  let sigma = Evd.from_env env in
  let sigma, defs = List.fold_left_map (fun sigma cst ->
    let sigma, c = Evd.fresh_constant_instance env sigma cst in
    let c = on_snd (EConstr.EInstance.kind sigma) c in
    sigma, (c, Typeops.type_of_constant_in env c)) sigma schemes in
  let find_inductive ty =
    let (ctx, arity) = decompose_prod ty in
    let (_, last) = List.hd ctx in
      match Constr.kind last with
        | Constr.App (ind, args) ->
            let ind = Constr.destInd ind in
            let (_,spec) = Inductive.lookup_mind_specif env (fst ind) in
              ctx, ind, spec.mind_nrealargs
        | _ -> ctx, Constr.destInd last, 0
  in
  let (c, t) = List.hd defs in
  let ctx, ind, nargs = find_inductive t in
  (* We check if ALL the predicates are in Prop, if so we use propositional
     conjunction '/\', otherwise we use the simple product '*'.
  *)
  let inprop =
    let inprop (_,t) =
      Sorts.Quality.is_qprop
        (Retyping.get_sort_quality_of env sigma (EConstr.of_constr t))
    in
    List.for_all inprop defs
  in
  let mk_and, mk_conj =
    if inprop
    then (mk_rocq_and, mk_rocq_conj)
    else (mk_rocq_prod, mk_rocq_pair)
  in
  (* Number of clauses, including the predicates quantification *)
  let prods = Termops.nb_prod sigma (EConstr.of_constr t) - (nargs + 1) in
  let sigma, rocqand  = mk_and sigma in
  let sigma, rocqconj = mk_conj sigma in
  let relargs = Termops.rel_vect 0 prods in
  let concls = List.rev_map
    (fun (cst, t) ->
      Constr.mkApp(Constr.mkConstU cst, relargs),
      snd (decompose_prod_n prods t)) defs in
  let concl_bod, concl_typ =
    fold_left'
      (fun (accb, acct) (cst, x) ->
        Constr.mkApp (EConstr.to_constr sigma rocqconj, [| x; acct; cst; accb |]),
        Constr.mkApp (EConstr.to_constr sigma rocqand, [| x; acct |])) concls
  in
  let ctx, _ =
    list_split_rev_at prods
      (List.rev_map (fun (x, y) -> Context.Rel.Declaration.LocalAssum (x, y)) ctx) in
  let typ = EConstr.of_constr @@ List.fold_left (fun d c -> Term.mkProd_wo_LetIn c d) concl_typ ctx in
  let body = EConstr.of_constr @@ it_mkLambda_or_LetIn concl_bod ctx in
  let sigma = Typing.check env sigma body typ in
  (sigma, body, typ)

let do_combined_scheme name csts =
  let open CAst in
  let sigma,body,typ = build_combined_scheme (Global.env ()) csts in
  (* It is possible for the constants to have different universe
     polymorphism from each other, however that is only when the user
     manually defined at least one of them (as Scheme would pick the
     polymorphism of the inductive block). In that case if they want
     some other polymorphism they can also manually define the
     combined scheme. *)
  let gr = Names.GlobRef.ConstRef (List.hd csts) in
  let poly = Global.is_polymorphic gr in
  let cumulative = Global.is_cumulative gr in
  ignore (define ~poly ~cumulative ?loc:name.loc name.v sigma body (Some typ));
  Declare.fixpoint_message None [name.v]

(**********************************************************************)
(* Scheme for the all predicate and its theorem *)

let do_scheme_all_predicate ?all_depth ~declare_mind kn mib strpos sAll keyAll =
  (* generate all predicate *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, (_, u) = Evd.fresh_inductive_instance ~rigid:UState.univ_rigid env sigma (kn,0) in
  let (uctx, mentry) = AllScheme.generate_all_predicate env sigma kn u mib strpos sAll in
  (* declare it *)
  let poly_flag = PolyFlags.make ~univ_poly:true ~collapse_sort_variables:true ~cumulative:true in
  let univs = UState.univ_entry ~poly:poly_flag uctx in
  let kn_nested = declare_mind ?all_depth mentry univs in
  (* register it *)
  let () = Array.iteri (fun i _ -> DeclareScheme.declare_scheme
              SuperGlobal keyAll (GlobRef.IndRef (kn,i), GlobRef.IndRef (kn_nested,i))
            ) mib.mind_packets in
  kn_nested

let do_scheme_all_theorem kn mib kn_nested focus strpos sAllThm keyAllThm =
  (* generate all theorem *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, (_, u) = Evd.fresh_inductive_instance ~sort_rigid:true ~rigid:UState.univ_rigid env sigma (kn,focus) in
  let (sigma, thm) = AllScheme.generate_all_theorem env sigma kn kn_nested focus u mib strpos in
  (* universe *)
  let sigma = UnivVariances.register_universe_variances_of env sigma thm in
  let uctx = Evd.ustate sigma in
  let uctx = UState.collapse_sort_variables ~only_above_prop:true uctx in
  let uctx = UState.normalize_variables uctx in
  let uctx = UState.minimize ~partial:false uctx in
  let sigma = Evd.set_ustate sigma uctx in
  let thm = UState.nf_universes uctx (EConstr.to_constr sigma thm) in
  let uctx = UState.restrict uctx (Vars.universes_of_constr thm) in
  let sigma = Evd.set_ustate sigma uctx in
  (* declare it *)
  let poly_flag = PolyFlags.make ~univ_poly:true ~collapse_sort_variables:true ~cumulative:true in
  let info = Declare.Info.make ~poly:poly_flag () in
  let fth_name = Nameops.add_suffix mib.mind_packets.(focus).mind_typename sAllThm in
  let cinfo = Declare.CInfo.make ~name:fth_name ~typ:(None : (Evd.econstr option)) () in
  let fth_ref = Declare.declare_definition ~info:info ~cinfo:cinfo ~opaque:false ~body:(EConstr.of_constr thm) sigma in
  (* register it *)
  let () = DeclareScheme.declare_scheme SuperGlobal keyAllThm (GlobRef.IndRef (kn,focus), fth_ref) in
  ()

let do_all_forall ?(user_call_scheme=false) ?all_depth ~declare_mind kn strpos =
  let env = Global.env () in
  let mib = Environ.lookup_mind kn env in
  let isPrimRecord = Array.exists (fun ind -> match ind.mind_record with PrimRecord _ -> true | _ -> false) mib.mind_packets in
  if not isPrimRecord then begin
    let (strpos, (sAll, sAllThm), (keyAll, keyAllThm)) =
          AllScheme.compute_positive_uparams_and_suffix env kn mib strpos in
    if List.exists (fun b -> b) strpos then
    let kn_nested = do_scheme_all_predicate ?all_depth ~declare_mind kn mib strpos sAll keyAll in
    Array.iteri (fun focus _ -> do_scheme_all_theorem kn mib kn_nested focus strpos sAllThm keyAllThm) mib.mind_packets
    end
  else
    if user_call_scheme then
      CErrors.user_err Pp.(str "Not implemented for primitive records.")


(**********************************************************************)

let map_inductive_block ?(locmap=Locmap.default None) f kn n =
  for i=0 to n-1 do
    let loc = Ind_tables.Locmap.lookup ~locmap (kn,i) in
    f ?loc (kn,i)
  done

type declare_mind_function = ?all_depth:int ->
  Entries.mutual_inductive_entry ->
  UState.named_universes_entry ->
  MutInd.t

(** Depth Generation of all predicate at definition of a new inductive type *)
let { Goptions.get = default_all_depth } =
  Goptions.declare_int_option_and_ref ~key:["Depth";"Scheme";"All"] ~value:0 ()

let default_all_depth kn mib =
  let env = Global.env () in
  let mib = Environ.lookup_mind kn env in
  if Inductiveops.mis_is_nested env kn mib
  then default_all_depth () -1
  else default_all_depth ()

let declare_default_schemes ?locmap ?all_depth ~(declare_mind:declare_mind_function) kn =
  let mib = Global.lookup_mind kn in
  let all_depth = Option.default (default_all_depth kn mib) all_depth in
  let n = Array.length mib.mind_packets in
  if !elim_flag && (mib.mind_finite <> Declarations.BiFinite || !bifinite_elim_flag)
     && mib.mind_typing_flags.check_positive then
    declare_induction_schemes kn ?locmap;
  if all_depth > 0 && mib.mind_finite <> CoFinite then
    do_all_forall ~all_depth:(all_depth-1) ~declare_mind:declare_mind kn None;
  if !case_flag then map_inductive_block ?locmap declare_one_case_analysis_scheme kn n;
  if is_eq_flag() then try_declare_beq_scheme kn ?locmap;
  if !eq_dec_flag then try_declare_eq_decidability kn ?locmap;
  if !rewriting_flag then map_inductive_block ?locmap declare_congr_scheme kn n;
  if !rewriting_flag then map_inductive_block ?locmap declare_rewriting_schemes kn n

module Internal = struct
  let do_scheme_all ~user_call_scheme ~declare_mind id strpos =
    let kn,_ = smart_ind id in
    do_all_forall ~user_call_scheme ~declare_mind kn strpos
end
