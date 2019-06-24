(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
open CErrors
open Util
open Names
open Declarations
open Term
open Constr
open Inductive
open Decl_kinds
open Indrec
open Declare
open Libnames
open Globnames
open Goptions
open Nameops
open Termops
open Smartlocate
open Vernacexpr
open Ind_tables
open Auto_ind_decl
open Eqschemes
open Elimschemes
open Context.Rel.Declaration

(* Flags governing automatic synthesis of schemes *)

let elim_flag = ref true
let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "automatic declaration of induction schemes";
      optkey   = ["Elimination";"Schemes"];
      optread  = (fun () -> !elim_flag) ;
      optwrite = (fun b -> elim_flag := b) }

let bifinite_elim_flag = ref false
let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "automatic declaration of induction schemes for non-recursive types";
      optkey   = ["Nonrecursive";"Elimination";"Schemes"];
      optread  = (fun () -> !bifinite_elim_flag) ;
      optwrite = (fun b -> bifinite_elim_flag := b) }

let case_flag = ref false
let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "automatic declaration of case analysis schemes";
      optkey   = ["Case";"Analysis";"Schemes"];
      optread  = (fun () -> !case_flag) ;
      optwrite = (fun b -> case_flag := b) }

let eq_flag = ref false
let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "automatic declaration of boolean equality";
      optkey   = ["Boolean";"Equality";"Schemes"];
      optread  = (fun () -> !eq_flag) ;
      optwrite = (fun b -> eq_flag := b) }

let is_eq_flag () = !eq_flag

let eq_dec_flag = ref false
let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "automatic declaration of decidable equality";
      optkey   = ["Decidable";"Equality";"Schemes"];
      optread  = (fun () -> !eq_dec_flag) ;
      optwrite = (fun b -> eq_dec_flag := b) }

let rewriting_flag = ref false
let () =
  declare_bool_option
    { optdepr  = false;
      optname  ="automatic declaration of rewriting schemes for equality types";
      optkey   = ["Rewriting";"Schemes"];
      optread  = (fun () -> !rewriting_flag) ;
      optwrite = (fun b -> rewriting_flag := b) }

(* Util *)

let define ~poly id sigma c t =
  let f = declare_constant in
  let univs = Evd.univ_entry ~poly sigma in
  let open Proof_global in
  let kn = f id
    (DefinitionEntry
      { proof_entry_body = c;
        proof_entry_secctx = None;
        proof_entry_type = t;
        proof_entry_universes = univs;
        proof_entry_opaque = false;
        proof_entry_inline_code = false;
        proof_entry_feedback = None;
      },
      Decl_kinds.IsDefinition Scheme) in
  definition_message id;
  kn

(* Boolean equality *)

let declare_beq_scheme_gen internal names kn =
  ignore (define_mutual_scheme beq_scheme_kind internal names kn)

let alarm what internal msg =
  let debug = false in
  match internal with
  | UserAutomaticRequest
  | InternalTacticRequest ->
    (if debug then
      Feedback.msg_debug
	(hov 0 msg ++ fnl () ++ what ++ str " not defined.")); None
  | _ -> Some msg

let try_declare_scheme what f internal names kn =
  try f internal names kn
  with e ->
  let e = CErrors.push e in
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
    | EqNotFound (ind',ind) ->
	alarm what internal
	  (str "Boolean equality on " ++
	   quote (Printer.pr_inductive (Global.env()) ind') ++
	   strbrk " is missing.")
    | UndefinedCst s ->
	alarm what internal
	  (strbrk "Required constant " ++ str s ++ str " undefined.")
    | AlreadyDeclared msg ->
        alarm what internal (msg ++ str ".")
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
           (str "Inductive types with annotations not supported.")
    | ConstructorWithNonParametricInductiveType ind ->
         alarm what internal
           (strbrk "Unsupported constructor with an argument whose type is a non-parametric inductive type." ++
            strbrk " Type " ++ quote (Printer.pr_inductive (Global.env()) ind) ++
            str " is applied to an argument which is not a variable.")
    | e when CErrors.noncritical e ->
        alarm what internal
	  (str "Unexpected error during scheme creation: " ++ CErrors.print e)
    | _ -> iraise e
  in
  match msg with
  | None -> ()
  | Some msg -> iraise (UserError (None, msg), snd e)

let beq_scheme_msg mind =
  let mib = Global.lookup_mind mind in
  (* TODO: mutual inductive case *)
  str "Boolean equality on " ++
    pr_enum (fun ind -> quote (Printer.pr_inductive (Global.env()) ind))
    (List.init (Array.length mib.mind_packets) (fun i -> (mind,i)))

let declare_beq_scheme_with l kn =
  try_declare_scheme (beq_scheme_msg kn) declare_beq_scheme_gen UserIndividualRequest l kn

let try_declare_beq_scheme kn =
  (* TODO: handle Fix, eventually handle
      proof-irrelevance; improve decidability by depending on decidability
      for the parameters rather than on the bl and lb properties *)
  try_declare_scheme (beq_scheme_msg kn) declare_beq_scheme_gen UserAutomaticRequest [] kn

let declare_beq_scheme = declare_beq_scheme_with []

(* Case analysis schemes *)
let declare_one_case_analysis_scheme ind =
  let (mib,mip) = Global.lookup_inductive ind in
  let kind = inductive_sort_family mip in
  let dep =
    if kind == InProp then case_scheme_kind_from_prop
    else if not (Inductiveops.has_dependent_elim mib) then
      case_scheme_kind_from_type
    else case_dep_scheme_kind_from_type in
  let kelim = elim_sort (mib,mip) in
    (* in case the inductive has a type elimination, generates only one
       induction scheme, the other ones share the same code with the
       appropriate type *)
  if Sorts.family_leq InType kelim then
    ignore (define_individual_scheme dep UserAutomaticRequest None ind)

(* Induction/recursion schemes *)

let kinds_from_prop =
  [InType,rect_scheme_kind_from_prop;
   InProp,ind_scheme_kind_from_prop;
   InSet,rec_scheme_kind_from_prop;
   InSProp,sind_scheme_kind_from_prop]

let kinds_from_type =
  [InType,rect_dep_scheme_kind_from_type;
   InProp,ind_dep_scheme_kind_from_type;
   InSet,rec_dep_scheme_kind_from_type;
   InSProp,sind_dep_scheme_kind_from_type]

let nondep_kinds_from_type =
  [InType,rect_scheme_kind_from_type;
   InProp,ind_scheme_kind_from_type;
   InSet,rec_scheme_kind_from_type;
   InSProp,sind_scheme_kind_from_type]

let declare_one_induction_scheme ind =
  let (mib,mip) = Global.lookup_inductive ind in
  let kind = inductive_sort_family mip in
  let from_prop = kind == InProp in
  let depelim = Inductiveops.has_dependent_elim mib in
  let kelim = Inductiveops.sorts_below (elim_sort (mib,mip)) in
  let kelim = if Global.sprop_allowed () then kelim
    else List.filter (fun s -> s <> InSProp) kelim
  in
  let elims =
    List.map_filter (fun (sort,kind) ->
        if List.mem_f Sorts.family_equal sort kelim then Some kind else None)
      (if from_prop then kinds_from_prop
       else if depelim then kinds_from_type
       else nondep_kinds_from_type)
  in
  List.iter (fun kind -> ignore (define_individual_scheme kind UserAutomaticRequest None ind))
    elims

let declare_induction_schemes kn =
  let mib = Global.lookup_mind kn in
  if mib.mind_finite <> Declarations.CoFinite then begin
    for i = 0 to Array.length mib.mind_packets - 1 do
      declare_one_induction_scheme (kn,i);
    done;
  end

(* Decidable equality *)

let declare_eq_decidability_gen internal names kn =
  let mib = Global.lookup_mind kn in
  if mib.mind_finite <> Declarations.CoFinite then
    ignore (define_mutual_scheme eq_dec_scheme_kind internal names kn)

let eq_dec_scheme_msg ind = (* TODO: mutual inductive case *)
  str "Decidable equality on " ++ quote (Printer.pr_inductive (Global.env()) ind)

let declare_eq_decidability_scheme_with l kn =
  try_declare_scheme (eq_dec_scheme_msg (kn,0))
    declare_eq_decidability_gen UserIndividualRequest l kn

let try_declare_eq_decidability kn =
  try_declare_scheme (eq_dec_scheme_msg (kn,0))
    declare_eq_decidability_gen UserAutomaticRequest [] kn

let declare_eq_decidability = declare_eq_decidability_scheme_with []

let ignore_error f x =
  try ignore (f x) with e when CErrors.noncritical e -> ()

let declare_rewriting_schemes ind =
  if Hipattern.is_inductive_equality ind then begin
    ignore (define_individual_scheme rew_r2l_scheme_kind UserAutomaticRequest None ind);
    ignore (define_individual_scheme rew_r2l_dep_scheme_kind UserAutomaticRequest None ind);
    ignore (define_individual_scheme rew_r2l_forward_dep_scheme_kind
      UserAutomaticRequest None ind);
    (* These ones expect the equality to be symmetric; the first one also *)
    (* needs eq *)
    ignore_error (define_individual_scheme rew_l2r_scheme_kind UserAutomaticRequest None) ind;
    ignore_error
      (define_individual_scheme rew_l2r_dep_scheme_kind UserAutomaticRequest None) ind;
    ignore_error
      (define_individual_scheme rew_l2r_forward_dep_scheme_kind UserAutomaticRequest None) ind
  end

let warn_cannot_build_congruence =
  CWarnings.create ~name:"cannot-build-congruence" ~category:"schemes"
         (fun () ->
          strbrk "Cannot build congruence scheme because eq is not found")

let declare_congr_scheme ind =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  if Hipattern.is_equality_type env sigma (EConstr.of_constr (mkInd ind)) (* FIXME *) then begin
    if
      try Coqlib.check_required_library Coqlib.logic_module_name; true
      with e when CErrors.noncritical e -> false
    then
      ignore (define_individual_scheme congr_scheme_kind UserAutomaticRequest None ind)
    else
      warn_cannot_build_congruence ()
  end

let declare_sym_scheme ind =
  if Hipattern.is_inductive_equality ind then
    (* Expect the equality to be symmetric *)
    ignore_error (define_individual_scheme sym_scheme_kind UserAutomaticRequest None) ind

(* Scheme command *)

let smart_global_inductive y = smart_global_inductive y
let rec split_scheme env l =
 match l with
  | [] -> [],[]
  | (Some id,t)::q -> let l1,l2 = split_scheme env q in
    ( match t with
      | InductionScheme (x,y,z) -> ((id,x,smart_global_inductive y,z)::l1),l2
      | CaseScheme (x,y,z) -> ((id,x,smart_global_inductive y,z)::l1),l2
      | EqualityScheme  x -> l1,((Some id,smart_global_inductive x)::l2)
    )
(*
 if no name has been provided, we build one from the types of the ind
requested
*)
  | (None,t)::q ->
      let l1,l2 = split_scheme env q in
      let names inds recs isdep y z =
        let ind = smart_global_inductive y in
        let sort_of_ind = inductive_sort_family (snd (lookup_mind_specif env ind)) in
        let suffix = (
          match sort_of_ind with
          | InProp ->
              if isdep then (match z with
              | InSProp -> inds ^ "s_dep"
              | InProp -> inds ^ "_dep"
              | InSet  -> recs ^ "_dep"
              | InType -> recs ^ "t_dep")
              else ( match z with
              | InSProp -> inds ^ "s"
              | InProp -> inds
              | InSet -> recs
              | InType -> recs ^ "t" )
          | _ ->
              if isdep then (match z with
              | InSProp -> inds ^ "s"
              | InProp -> inds
              | InSet -> recs
              | InType -> recs ^ "t" )
              else (match z with
              | InSProp -> inds ^ "s_nodep"
              | InProp -> inds ^ "_nodep"
              | InSet -> recs ^ "_nodep"
              | InType -> recs ^ "t_nodep")
        ) in
        let newid = add_suffix (Nametab.basename_of_global (IndRef ind)) suffix in
        let newref = CAst.make newid in
          ((newref,isdep,ind,z)::l1),l2
      in
	match t with
	| CaseScheme (x,y,z) -> names "_case" "_case" x y z
	| InductionScheme (x,y,z) -> names "_ind" "_rec" x y z
	| EqualityScheme  x -> l1,((None,smart_global_inductive x)::l2)

let do_mutual_induction_scheme ?(force_mutual=false) lnamedepindsort =
  let lrecnames = List.map (fun ({CAst.v},_,_,_) -> v) lnamedepindsort
  and env0 = Global.env() in
  let sigma, lrecspec, _ =
    List.fold_right
      (fun (_,dep,ind,sort) (evd, l, inst) ->
       let evd, indu, inst =
	 match inst with
	 | None ->
            let _, ctx = Typeops.type_of_global_in_context env0 (IndRef ind) in
            let u, ctx = UnivGen.fresh_instance_from ctx None in
            let evd = Evd.from_ctx (UState.of_context_set ctx) in
	      evd, (ind,u), Some u
	 | Some ui -> evd, (ind, ui), inst
       in
          (evd, (indu,dep,sort) :: l, inst))
    lnamedepindsort (Evd.from_env env0,[],None)
  in
  let sigma, listdecl = Indrec.build_mutual_induction_scheme env0 sigma ~force_mutual lrecspec in
  let poly =
    (* NB: build_mutual_induction_scheme forces nonempty list of mutual inductives
       (force_mutual is about the generated schemes) *)
    let _,_,ind,_ = List.hd lnamedepindsort in
    Global.is_polymorphic (IndRef ind)
  in
  let declare decl fi lrecref =
    let decltype = Retyping.get_type_of env0 sigma (EConstr.of_constr decl) in
    let decltype = EConstr.to_constr sigma decltype in
    let proof_output = Future.from_val ((decl,Univ.ContextSet.empty),Evd.empty_side_effects) in
    let cst = define ~poly fi sigma proof_output (Some decltype) in
    ConstRef cst :: lrecref
  in
  let _ = List.fold_right2 declare listdecl lrecnames [] in
  fixpoint_message None lrecnames

let get_common_underlying_mutual_inductive env = function
  | [] -> assert false
  | (id,(mind,i as ind))::l as all ->
      match List.filter (fun (_,(mind',_)) -> not (MutInd.equal mind mind')) l with
      | (_,ind')::_ ->
          raise (RecursionSchemeError (env, NotMutualInScheme (ind,ind')))
      | [] ->
	  if not (List.distinct_f Int.compare (List.map snd (List.map snd all)))
          then user_err Pp.(str "A type occurs twice");
	  mind,
	  List.map_filter
            (function (Some id,(_,i)) -> Some (i,id.CAst.v) | (None,_) -> None) all

let do_scheme l =
  let env = Global.env() in
  let ischeme,escheme = split_scheme env l in
(* we want 1 kind of scheme at a time so we check if the user
tried to declare different schemes at once *)
    if not (List.is_empty ischeme) && not (List.is_empty escheme)
    then
      user_err Pp.(str "Do not declare equality and induction scheme at the same time.")
    else (
      if not (List.is_empty ischeme) then do_mutual_induction_scheme ischeme
      else
        let mind,l = get_common_underlying_mutual_inductive env escheme in
	declare_beq_scheme_with l mind;
	declare_eq_decidability_scheme_with l mind
    )

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

let mk_coq_and sigma = Evarutil.new_global sigma (Coqlib.lib_ref "core.and.type")
let mk_coq_conj sigma = Evarutil.new_global sigma (Coqlib.lib_ref "core.and.conj")

let mk_coq_prod sigma = Evarutil.new_global sigma (Coqlib.lib_ref "core.prod.type")
let mk_coq_pair sigma = Evarutil.new_global sigma (Coqlib.lib_ref "core.prod.intro")

let build_combined_scheme env schemes =
  let sigma = Evd.from_env env in
  let sigma, defs = List.fold_left_map (fun sigma cst ->
    let sigma, c = Evd.fresh_constant_instance env sigma cst in
    sigma, (c, Typeops.type_of_constant_in env c)) sigma schemes in
  let find_inductive ty =
    let (ctx, arity) = decompose_prod ty in
    let (_, last) = List.hd ctx in
      match Constr.kind last with
	| App (ind, args) ->
	    let ind = destInd ind in
	    let (_,spec) = Inductive.lookup_mind_specif env (fst ind) in
	      ctx, ind, spec.mind_nrealargs
	| _ -> ctx, destInd last, 0
  in
  let (c, t) = List.hd defs in
  let ctx, ind, nargs = find_inductive t in
  (* We check if ALL the predicates are in Prop, if so we use propositional
     conjunction '/\', otherwise we use the simple product '*'.
  *)
  let inprop =
    let inprop (_,t) =
      Retyping.get_sort_family_of env sigma (EConstr.of_constr t)
      == Sorts.InProp
    in
    List.for_all inprop defs
  in
  let mk_and, mk_conj =
    if inprop
    then (mk_coq_and, mk_coq_conj)
    else (mk_coq_prod, mk_coq_pair)
  in
  (* Number of clauses, including the predicates quantification *)
  let prods = nb_prod sigma (EConstr.of_constr t) - (nargs + 1) in
  let sigma, coqand  = mk_and sigma in
  let sigma, coqconj = mk_conj sigma in
  let relargs = rel_vect 0 prods in
  let concls = List.rev_map
    (fun (cst, t) ->
      mkApp(mkConstU cst, relargs),
      snd (decompose_prod_n prods t)) defs in
  let concl_bod, concl_typ =
    fold_left'
      (fun (accb, acct) (cst, x) ->
        mkApp (EConstr.to_constr sigma coqconj, [| x; acct; cst; accb |]),
        mkApp (EConstr.to_constr sigma coqand, [| x; acct |])) concls
  in
  let ctx, _ =
    list_split_rev_at prods
      (List.rev_map (fun (x, y) -> LocalAssum (x, y)) ctx) in
  let typ = List.fold_left (fun d c -> Term.mkProd_wo_LetIn c d) concl_typ ctx in
  let body = it_mkLambda_or_LetIn concl_bod ctx in
  let sigma = Typing.check env sigma (EConstr.of_constr body) (EConstr.of_constr typ) in
  (sigma, body, typ)

let do_combined_scheme name schemes =
  let open CAst in
  let csts =
    List.map (fun {CAst.loc;v} ->
        let qualid = qualid_of_ident v in
        try Nametab.locate_constant qualid
        with Not_found -> user_err ?loc Pp.(pr_qualid qualid ++ str " is not declared."))
      schemes
  in
  let sigma,body,typ = build_combined_scheme (Global.env ()) csts in
  let proof_output = Future.from_val ((body,Univ.ContextSet.empty),Evd.empty_side_effects) in
  (* It is possible for the constants to have different universe
     polymorphism from each other, however that is only when the user
     manually defined at least one of them (as Scheme would pick the
     polymorphism of the inductive block). In that case if they want
     some other polymorphism they can also manually define the
     combined scheme. *)
  let poly = Global.is_polymorphic (ConstRef (List.hd csts)) in
  ignore (define ~poly name.v sigma proof_output (Some typ));
  fixpoint_message None [name.v]

(**********************************************************************)

let map_inductive_block f kn n = for i=0 to n-1 do f (kn,i) done

let declare_default_schemes kn =
  let mib = Global.lookup_mind kn in
  let n = Array.length mib.mind_packets in
  if !elim_flag && (mib.mind_finite <> Declarations.BiFinite || !bifinite_elim_flag)
     && mib.mind_typing_flags.check_guarded then
    declare_induction_schemes kn;
  if !case_flag then map_inductive_block declare_one_case_analysis_scheme kn n;
  if is_eq_flag() then try_declare_beq_scheme kn;
  if !eq_dec_flag then try_declare_eq_decidability kn;
  if !rewriting_flag then map_inductive_block declare_congr_scheme kn n;
  if !rewriting_flag then map_inductive_block declare_sym_scheme kn n;
  if !rewriting_flag then map_inductive_block declare_rewriting_schemes kn n
