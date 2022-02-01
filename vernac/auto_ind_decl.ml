(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is about the automatic generation of schemes about
   decidable equality, created by Vincent Siles, Oct 2007 *)

open CErrors
open Util
open Pp
open Term
open Constr
open Context
open Vars
open Termops
open Declarations
open Names
open Inductiveops
open Tactics
open Ind_tables
open Namegen
open Tactypes
open Proofview.Notations

module RelDecl = Context.Rel.Declaration

(**********************************************************************)
(* Generic synthesis of boolean equality *)

let quick_chop n l =
  let rec kick_last = function
    | t::[] -> []
    | t::q -> t::(kick_last q)
    | [] -> failwith "kick_last"
and aux = function
    | (0,l') -> l'
    | (n,h::t) -> aux (n-1,t)
    | _ -> failwith "quick_chop"
  in
  if n > (List.length l) then failwith "quick_chop args"
  else kick_last (aux (n,l) )

let deconstruct_type t =
  let l,r = decompose_prod t in
  (List.rev_map snd l)@[r]

exception EqNotFound of inductive * inductive
exception EqUnknown of string
exception UndefinedCst of string
exception InductiveWithProduct
exception InductiveWithSort
exception ParameterWithoutEquality of GlobRef.t
exception NonSingletonProp of inductive
exception DecidabilityMutualNotSupported
exception NoDecidabilityCoInductive
exception ConstructorWithNonParametricInductiveType of inductive
exception DecidabilityIndicesNotSupported

(* Some pre declaration of constant we are going to use *)
let andb_prop = fun _ -> UnivGen.constr_of_monomorphic_global (Global.env ()) (Coqlib.lib_ref "core.bool.andb_prop")

let andb_true_intro = fun _ ->
  UnivGen.constr_of_monomorphic_global (Global.env ())
    (Coqlib.lib_ref "core.bool.andb_true_intro")

(* We avoid to use lazy as the binding of constants can change *)
let bb () = UnivGen.constr_of_monomorphic_global (Global.env ()) (Coqlib.lib_ref "core.bool.type")
let tt () = UnivGen.constr_of_monomorphic_global (Global.env ()) (Coqlib.lib_ref "core.bool.true")
let ff () = UnivGen.constr_of_monomorphic_global (Global.env ()) (Coqlib.lib_ref "core.bool.false")
let eq () = UnivGen.constr_of_monomorphic_global (Global.env ()) (Coqlib.lib_ref "core.eq.type")

let sumbool () = UnivGen.constr_of_monomorphic_global (Global.env ()) (Coqlib.lib_ref "core.sumbool.type")
let andb = fun _ -> UnivGen.constr_of_monomorphic_global (Global.env ()) (Coqlib.lib_ref "core.bool.andb")

let induct_on  c = induction false None c None None
let destruct_on c = destruct false None c None None

let destruct_on_using c id =
  destruct false None c
    (Some (CAst.make @@ IntroOrPattern [[CAst.make @@ IntroNaming IntroAnonymous];
               [CAst.make @@ IntroNaming (IntroIdentifier id)]]))
    None

let destruct_on_as c l =
  destruct false None c (Some (CAst.make l)) None

let inj_flags = Some {
    Equality.keep_proof_equalities = true; (* necessary *)
    Equality.injection_pattern_l2r_order = true; (* does not matter here *)
  }

let my_discr_tac = Equality.discr_tac false None
let my_inj_tac x = Equality.inj inj_flags None false None (EConstr.mkVar x,NoBindings)

(* reconstruct the inductive with the correct de Bruijn indexes *)
let mkFullInd env (ind,u) n =
  let mib = Environ.lookup_mind (fst ind) env in
  let nparrec = mib.mind_nparams_rec in
  (* params context divided *)
  let lnonparrec,lnamesparrec =
    Inductive.inductive_nonrec_rec_paramdecls (mib,u) in
  if nparrec > 0
    then mkApp (mkIndU (ind,u),
      Array.of_list(Context.Rel.instance_list mkRel (nparrec+n) lnamesparrec))
    else mkIndU (ind,u)

let check_bool_is_defined () =
  if not (Coqlib.has_ref "core.bool.type")
  then raise (UndefinedCst "bool")

let check_no_indices mib =
  if Array.exists (fun mip -> mip.mind_nrealargs <> 0) mib.mind_packets then
    raise DecidabilityIndicesNotSupported

let get_scheme handle k ind = match local_lookup_scheme handle k ind with
| None -> assert false
| Some c -> c

let beq_scheme_kind_aux = ref (fun _ -> failwith "Undefined")

let get_inductive_deps env kn =
  (* fetching the mutual inductive body *)
  let mib = Environ.lookup_mind kn env in
  (* number of inductives in the mutual *)
  let nb_ind = Array.length mib.mind_packets in
  (* number of params in the type *)
  let nparrec = mib.mind_nparams_rec in
  check_no_indices mib;
  let make_one_eq accu i =
    (* This function is only trying to recursively compute the inductive types
       appearing as arguments of the constructors. This is done to support
       equality decision over hereditarily first-order types. It could be
       performed in a much cleaner way, e.g. using the kernel normal form of
       constructor types and kernel whd_all for the argument types. *)
    let rec aux accu c =
      let (c,a) = Reductionops.whd_betaiota_stack env Evd.empty EConstr.(of_constr c) in
      let (c,a) = EConstr.Unsafe.(to_constr c, List.map to_constr a) in
      match Constr.kind c with
      | Cast (x,_,_) -> aux accu (Term.applist (x,a))
      | App _ -> assert false
      | Ind ((kn', _), _) ->
          if Environ.QMutInd.equal env kn kn' then accu
          else
            List.fold_left aux (kn' :: accu) a
      | Const (kn, u) ->
        (match Environ.constant_opt_value_in env (kn, u) with
        | Some c -> aux accu (Term.applist (c,a))
        | None -> accu)
      | Rel _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | Proj _
      | Construct _ | Case _ | CoFix _ | Fix _ | Meta _ | Evar _ | Int _
      | Float _ | Array _ -> accu
    in
    let u = Univ.Instance.empty in
    let constrs n = get_constructors env (make_ind_family (((kn, i), u),
      Context.Rel.instance_list mkRel (n+nb_ind-1) mib.mind_params_ctxt)) in
    let constrsi = constrs (3+nparrec) in
    let fold i accu arg =
      let fold accu c = aux accu (RelDecl.get_type c) in
      List.fold_left fold accu arg.cs_args
    in
    Array.fold_left_i fold accu constrsi
  in
  Array.fold_left_i (fun i accu _ -> make_one_eq accu i) [] mib.mind_packets

let build_beq_scheme_deps env kn =
  let inds = get_inductive_deps env kn in
  List.map (fun ind -> SchemeMutualDep (ind, !beq_scheme_kind_aux ())) inds

let build_beq_scheme env handle kn =
  check_bool_is_defined ();
  (* fetching the mutual inductive body *)
  let mib = Environ.lookup_mind kn env in

  let auctx = Declareops.universes_context mib.mind_universes in
  let u, uctx = UnivGen.fresh_instance_from auctx None in
  let uctx = UState.of_context_set uctx in

  (* number of inductives in the mutual *)
  let nb_ind = Array.length mib.mind_packets in
  (* number of params in the type *)
  let nparrec = mib.mind_nparams_rec in
  check_no_indices mib;
  (* params context divided *)
  let lnonparrec,lnamesparrec =
    Inductive.inductive_nonrec_rec_paramdecls (mib,u) in
  (* predef coq's boolean type *)
  (* rec name *)
  let rec_name i =(Id.to_string (Array.get mib.mind_packets i).mind_typename)^
                    "_eqrec"
  in
  (* construct the "fun A B ... N, eqA eqB eqC ... N => fixpoint" part *)
  let create_input c =
    let myArrow u v = mkArrow u Sorts.Relevant (lift 1 v)
    and eqName = function
      | Name s -> Id.of_string ("eq_"^(Id.to_string s))
      | Anonymous -> Id.of_string "eq_A"
    in
    let ext_rel_list = Context.Rel.instance_list mkRel 0 lnamesparrec in
    let lift_cnt = ref 0 in
    let eqs_typ = List.map (fun aa ->
                      let a = lift !lift_cnt aa in
                      incr lift_cnt;
                      myArrow a (myArrow a (bb ()))
                    ) ext_rel_list in

    let eq_input = List.fold_left2
                     ( fun a b decl -> (* mkLambda(n,b,a) ) *)
                       (* here I leave the Naming thingy so that the type of
                  the function is more readable for the user *)
                       mkNamedLambda (map_annot eqName (RelDecl.get_annot decl)) b a )
                     c (List.rev eqs_typ) lnamesparrec
    in
    List.fold_left (fun a decl ->(* mkLambda(n,t,a)) eq_input rel_list *)
        (* Same here , hoping the auto renaming will do something good ;)  *)
        let x = map_annot
                  (function Name s -> s | Anonymous -> Id.of_string "A")
                  (RelDecl.get_annot decl)
        in
        mkNamedLambda x (RelDecl.get_type decl)  a) eq_input lnamesparrec
  in
  let make_one_eq cur =
    let ind = (kn,cur) in
    let indu = (ind,u) in
    (* current inductive we are working on *)
    let cur_packet = mib.mind_packets.(cur) in
    (* Inductive toto : [rettyp] := *)
    let rettyp = Inductive.type_of_inductive ((mib,cur_packet),u) in
    (* split rettyp in a list without the non rec params and the last ->
  e.g. Inductive vec (A:Set) : nat -> Set := ... will do [nat] *)
    let rettyp_l = quick_chop nparrec (deconstruct_type rettyp) in
    (* give a type A, this function tries to find the equality on A declared
       previously *)
    (*  nlist = the number of args (A , B , ... )
        eqA   = the de Bruijn index of the first eq param
        ndx   = how much to translate due to the 2nd Case
     *)
    let compute_A_equality rel_list nlist eqA ndx t =
      let lifti = ndx in
      let rec aux c =
        let (c,a) = Reductionops.whd_betaiota_stack env Evd.empty EConstr.(of_constr c) in
        let (c,a) = EConstr.Unsafe.(to_constr c, List.map to_constr a) in
        match Constr.kind c with
        | Rel x -> mkRel (x-nlist+ndx)
        | Var x ->
           (* Support for working in a context with "eq_x : x -> x -> bool" *)
           let eid = Id.of_string ("eq_"^(Id.to_string x)) in
           let () =
             try ignore (Environ.lookup_named eid env)
             with Not_found -> raise (ParameterWithoutEquality (GlobRef.VarRef x))
           in
           mkVar eid
        | Cast (x,_,_) -> aux (Term.applist (x,a))
        | App _ -> assert false
        | Ind ((kn',i as ind'),u) ->
           if Environ.QMutInd.equal env kn kn' then mkRel(eqA-nlist-i+nb_ind-1)
           else begin
               try
                 let c = get_scheme handle (!beq_scheme_kind_aux()) ind' in
                 let eq = mkConstU (c,u) in
                 let eqa = Array.of_list @@ List.map aux a in
                 let args =
                   Array.append
                     (Array.of_list (List.map (fun x -> lift lifti x) a)) eqa in
                 if Int.equal (Array.length args) 0 then eq
                 else mkApp (eq, args)
               with Not_found -> raise(EqNotFound (ind', ind))
             end
        | Sort _  -> raise InductiveWithSort
        | Prod _ -> raise InductiveWithProduct
        | Lambda _-> raise (EqUnknown "abstraction")
        | LetIn _ -> raise (EqUnknown "let-in")
        | Const (kn, u) ->
           (match Environ.constant_opt_value_in env (kn, u) with
            | Some c -> aux (Term.applist (c,a))
            | None ->
               (* Support for working in a context with "eq_x : x -> x -> bool" *)
               (* Needs Hints, see test suite *)
               let eq_lbl = Label.make ("eq_" ^ Label.to_string (Constant.label kn)) in
               let kneq = Constant.change_label kn eq_lbl in
               if Environ.mem_constant kneq env then
                 let _ = Environ.constant_opt_value_in env (kneq, u) in
                 Term.applist (mkConstU (kneq,u),a)
               else raise (ParameterWithoutEquality (GlobRef.ConstRef kn)))
        | Proj _ -> raise (EqUnknown "projection")
        | Construct _ -> raise (EqUnknown "constructor")
        | Case _ -> raise (EqUnknown "match")
        | CoFix _ -> raise (EqUnknown "cofix")
        | Fix _   -> raise (EqUnknown "fix")
        | Meta _  -> raise (EqUnknown "meta-variable")
        | Evar _  -> raise (EqUnknown "existential variable")
        | Int _ -> raise (EqUnknown "int")
        | Float _ -> raise (EqUnknown "float")
        | Array _ -> raise (EqUnknown "array")
      in
      aux t
    in
    (* construct the predicate for the Case part*)
    let do_predicate rel_list n =
      List.fold_left (fun a b -> mkLambda(make_annot Anonymous Sorts.Relevant,b,a))
        (mkLambda (make_annot Anonymous Sorts.Relevant,
                   mkFullInd env indu (n+3+(List.length rettyp_l)+nb_ind-1),
                   (bb ())))
        (List.rev rettyp_l) in
    (* make_one_eq *)
    (* do the [| C1 ... =>  match Y with ... end
               ...
               Cn => match Y with ... end |]  part *)
    let rci = Sorts.Relevant in (* TODO relevance *)
    let ci = make_case_info env ind rci MatchStyle in
    let constrs n =
      let params = Context.Rel.instance_list mkRel (n+nb_ind-1) mib.mind_params_ctxt in
      get_constructors env (make_ind_family (indu, params))
    in
    let constrsi = constrs (3+nparrec) in
    let n = Array.length constrsi in
    let ar = Array.init n (fun i ->
      let nb_cstr_args = List.length constrsi.(i).cs_args in
      let constrsj = constrs (3+nparrec+nb_cstr_args) in
      let ar2 = Array.init n (fun j ->
        if Int.equal i j then
          let cc = match nb_cstr_args with
            | 0 -> tt ()
            | _ ->
               let eqs = Array.init nb_cstr_args (fun ndx ->
                 let cc = RelDecl.get_type (List.nth constrsi.(i).cs_args ndx) in
                 let eqA = compute_A_equality rel_list
                             nparrec
                             (nparrec+3+2*nb_cstr_args)
                             (nb_cstr_args+ndx+1)
                             cc
                 in
                 mkApp (eqA, [|mkRel (ndx+1+nb_cstr_args);mkRel (ndx+1)|]))
               in
               Array.fold_left
                 (fun a b -> mkApp (andb(),[|b;a|]))
                 eqs.(0)
                 (Array.sub eqs 1 (nb_cstr_args - 1))
          in
          List.fold_left (fun a decl ->
              mkLambda (RelDecl.get_annot decl, RelDecl.get_type decl, a))
            cc
            constrsj.(j).cs_args
        else
          List.fold_left (fun a decl ->
              mkLambda (RelDecl.get_annot decl, RelDecl.get_type decl, a))
            (ff ())
            (constrsj.(j).cs_args))
      in
      let pred = EConstr.of_constr (do_predicate rel_list nb_cstr_args) in
      let case =
        simple_make_case_or_project env (Evd.from_env env)
          ci pred NoInvert (EConstr.mkVar (Id.of_string "Y"))
          (EConstr.of_constr_array ar2)
      in
      List.fold_left (fun a decl -> mkLambda (RelDecl.get_annot decl, RelDecl.get_type decl, a))
        (EConstr.Unsafe.to_constr case)
        (constrsi.(i).cs_args))
    in
    let pred = EConstr.of_constr (do_predicate rel_list 0) in
    let case =
      simple_make_case_or_project env (Evd.from_env env)
        ci pred NoInvert (EConstr.mkVar (Id.of_string "X"))
        (EConstr.of_constr_array ar)
    in
    mkNamedLambda (make_annot (Id.of_string "X") Sorts.Relevant) (mkFullInd env indu (nb_ind-1+1))  (
        mkNamedLambda (make_annot (Id.of_string "Y") Sorts.Relevant) (mkFullInd env indu (nb_ind-1+2))  (
            (EConstr.Unsafe.to_constr case)))
  in (* build_beq_scheme *)

  let names = Array.make nb_ind (make_annot Anonymous Sorts.Relevant) and
      types = Array.make nb_ind mkSet and
      cores = Array.make nb_ind mkSet in
  for i=0 to (nb_ind-1) do
    names.(i) <- make_annot (Name (Id.of_string (rec_name i))) Sorts.Relevant;
    types.(i) <- mkArrow (mkFullInd env ((kn,i),u) 0) Sorts.Relevant
                  (mkArrow (mkFullInd env ((kn,i),u) 1) Sorts.Relevant (bb ()));
    let c = make_one_eq i in
    cores.(i) <- c;
  done;
  let res = Array.init nb_ind (fun i ->
    let kelim = Inductive.elim_sort (mib,mib.mind_packets.(i)) in
    if not (Sorts.family_leq InSet kelim) then
      raise (NonSingletonProp (kn,i));
    let fix = match mib.mind_finite with
      | CoFinite ->
         raise NoDecidabilityCoInductive;
      | Finite ->
         mkFix (((Array.make nb_ind 0),i),(names,types,cores))
      | BiFinite ->
         (* If the inductive type is not recursive, the fixpoint is
             not used, so let's replace it with garbage *)
         let subst = List.init nb_ind (fun _ -> mkProp) in
         Vars.substl subst cores.(i)
    in
    create_input fix)
  in
  res, uctx

let beq_scheme_kind =
  declare_mutual_scheme_object "_beq"
  ~deps:build_beq_scheme_deps
  build_beq_scheme

let _ = beq_scheme_kind_aux := fun () -> beq_scheme_kind

(* This function tryies to get the [inductive] between a constr
  the constr should be Ind i or App(Ind i,[|args|])
*)
let destruct_ind env sigma c =
  let open EConstr in
  let (c,v) = Reductionops.whd_all_stack env sigma c in
  destInd sigma c, Array.of_list v

let bl_scheme_kind_aux = ref (fun () -> failwith "Undefined")
let lb_scheme_kind_aux = ref (fun () -> failwith "Undefined")

(*
  In the following, avoid is the list of names to avoid.
  If the args of the Inductive type are A1 ... An
  then avoid should be
 [| lb_An ... lb _A1  (resp. bl_An ... bl_A1)
    eq_An .... eq_A1 An ... A1 |]
so from Ai we can find the correct eq_Ai bl_ai or lb_ai
*)
(* used in the leib -> bool side*)
let do_replace_lb handle aavoid narg p q =
  let open EConstr in
  let avoid = Array.of_list aavoid in
  let do_arg env sigma hd v offset =
    match kind sigma v with
    | Var s ->
    let x = narg*offset in
    let n = Array.length avoid in
    let rec find i =
      if Id.equal avoid.(n-i) s then avoid.(n-i-x)
      else (if i<n then find (i+1)
            else user_err
                   (str "Var " ++ Id.print s ++ str " seems unknown.")
      )
    in mkVar (find 1)
    | Const (cst,u) ->
      (* Works in specific situations where the args have to be already declared as a
         Parameter (see example "J" in test file SchemeEquality.v);
         We assume the parameter to have the same polymorphic arity as cst *)
        let lbl = Label.to_string (Constant.label cst) in
        let newlbl = if Int.equal offset 1 then ("eq_" ^ lbl) else (lbl ^ "_lb") in
        let newcst = Constant.change_label cst (Label.make newlbl) in
        if Environ.mem_constant newcst env then mkConstU (newcst,u)
        else raise (ConstructorWithNonParametricInductiveType (fst hd))
    | _ -> raise (ConstructorWithNonParametricInductiveType (fst hd))

  in
  Proofview.Goal.enter begin fun gl ->
    let type_of_pq = Tacmach.pf_get_type_of gl p in
    let sigma = Tacmach.project gl in
    let env = Tacmach.pf_env gl in
    let (ind,u as indu),v = destruct_ind env sigma type_of_pq in
    let c = get_scheme handle (!lb_scheme_kind_aux ()) ind in
    let lb_type_of_p = mkConstU (c,u) in
       Proofview.tclEVARMAP >>= fun sigma ->
       let lb_args = Array.append (Array.append
                          v
                          (Array.Smart.map (fun x -> do_arg env sigma indu x 1) v))
                          (Array.Smart.map (fun x -> do_arg env sigma indu x 2) v)
        in let app =  if Array.is_empty lb_args
                       then lb_type_of_p else mkApp (lb_type_of_p,lb_args)
           in
           Tacticals.tclTHENLIST [
             Equality.replace p q ; apply app ; Auto.default_auto]
  end

(* used in the bool -> leb side *)
let do_replace_bl handle (ind,u as indu) aavoid narg lft rgt =
  let open EConstr in
  let avoid = Array.of_list aavoid in
  let do_arg env sigma hd v offset =
    match kind sigma v with
    | Var s ->
    let x = narg*offset in
    let n = Array.length avoid in
    let rec find i =
      if Id.equal avoid.(n-i) s then avoid.(n-i-x)
      else (if i<n then find (i+1)
            else user_err
                   (str "Var " ++ Id.print s ++ str " seems unknown.")
      )
    in mkVar (find 1)
    | Const (cst,u) ->
      (* Works in specific situations where the args have to be already declared as a
         Parameter (see example "J" in test file SchemeEquality.v)
         We assume the parameter to have the same polymorphic arith as cst *)
        let lbl = Label.to_string (Constant.label cst) in
        let newlbl = if Int.equal offset 1 then ("eq_" ^ lbl) else (lbl ^ "_bl") in
        let newcst = Constant.change_label cst (Label.make newlbl) in
        if Environ.mem_constant newcst env then mkConstU (newcst,u)
        else raise (ConstructorWithNonParametricInductiveType (fst hd))
    | _ -> raise (ConstructorWithNonParametricInductiveType (fst hd))
  in

  let rec aux l1 l2 =
    match (l1,l2) with
    | (t1::q1,t2::q2) ->
        Proofview.Goal.enter begin fun gl ->
        let sigma = Tacmach.project gl in
        let env = Tacmach.pf_env gl in
        if EConstr.eq_constr sigma t1 t2 then aux q1 q2
        else (
          let tt1 = Tacmach.pf_get_type_of gl t1 in
          let (ind',u as indu),v = try destruct_ind env sigma tt1
          (* trick so that the good sequence is returned*)
                with e when CErrors.noncritical e -> indu,[||]
          in if Ind.CanOrd.equal ind' ind
             then Tacticals.tclTHENLIST [Equality.replace t1 t2; Auto.default_auto ; aux q1 q2 ]
             else (
               let c = get_scheme handle (!bl_scheme_kind_aux ()) ind' in
               let bl_t1 = mkConstU (c,u) in
               let bl_args =
                        Array.append (Array.append
                          v
                          (Array.Smart.map (fun x -> do_arg env sigma indu x 1) v))
                          (Array.Smart.map (fun x -> do_arg env sigma indu x 2) v )
                in
                let app =  if Array.is_empty bl_args
                           then bl_t1 else mkApp (bl_t1,bl_args)
                in
                Tacticals.tclTHENLIST [
                  Equality.replace_by t1 t2
                    (Tacticals.tclTHEN (apply app) (Auto.default_auto)) ;
                  aux q1 q2 ]
              )
        )
        end
    | ([],[]) -> Proofview.tclUNIT ()
    | _ -> Tacticals.tclZEROMSG (str "Both side of the equality must have the same arity.")
  in
  Proofview.tclEVARMAP >>= fun sigma ->
  begin try Proofview.tclUNIT (destApp sigma lft)
    with DestKO -> Tacticals.tclZEROMSG (str "replace failed.")
  end >>= fun (ind1,ca1) ->
  begin try Proofview.tclUNIT (destApp sigma rgt)
    with DestKO -> Tacticals.tclZEROMSG (str "replace failed.")
  end >>= fun (ind2,ca2) ->
  begin try Proofview.tclUNIT (fst (destInd sigma ind1))
    with DestKO ->
      begin try Proofview.tclUNIT (fst (fst (destConstruct sigma ind1)))
        with DestKO -> Tacticals.tclZEROMSG (str "The expected type is an inductive one.")
      end
  end >>= fun (sp1,i1) ->
  begin try Proofview.tclUNIT (fst (destInd sigma ind2))
    with DestKO ->
      begin try Proofview.tclUNIT (fst (fst (destConstruct sigma ind2)))
        with DestKO -> Tacticals.tclZEROMSG (str "The expected type is an inductive one.")
      end
  end >>= fun (sp2,i2) ->
  Proofview.tclENV >>= fun env ->
  if not (Environ.QMutInd.equal env sp1 sp2) || not (Int.equal i1 i2)
  then Tacticals.tclZEROMSG (str "Eq should be on the same type")
  else aux (Array.to_list ca1) (Array.to_list ca2)

(*
  create, from a list of ids [i1,i2,...,in] the list
  [(in,eq_in,in_bl,in_al),,...,(i1,eq_i1,i1_bl_i1_al  )]
*)
let list_id l = List.fold_left ( fun a decl -> let s' =
      match RelDecl.get_name decl with
        Name s -> Id.to_string s
      | Anonymous -> "A" in
          (Id.of_string s',Id.of_string ("eq_"^s'),
              Id.of_string (s'^"_bl"),
              Id.of_string (s'^"_lb"))
            ::a
    ) [] l

let avoid_of_list_id list_id =
  List.fold_left (fun avoid (s,seq,sbl,slb) ->
      List.fold_left (fun avoid id -> Id.Set.add id avoid)
        avoid [s;seq;sbl;slb])
    Id.Set.empty list_id

(*
  build the right eq_I A B.. N eq_A .. eq_N
*)
let eqI handle (ind,u) list_id =
  let eA = Array.of_list((List.map (fun (s,_,_,_) -> mkVar s) list_id)@
                           (List.map (fun (_,seq,_,_)-> mkVar seq) list_id ))
  and e = mkConstU (get_scheme handle beq_scheme_kind ind,u)
  in mkApp(e,eA)

(**********************************************************************)
(* Boolean->Leibniz *)

open Namegen

let compute_bl_goal env handle (ind,u) lnamesparrec nparrec =
  let list_id = list_id lnamesparrec in
  let eqI = eqI handle (ind,u) list_id in
  let avoid = avoid_of_list_id list_id in
  let x = next_ident_away (Id.of_string "x") avoid in
  let y = next_ident_away (Id.of_string "y") (Id.Set.add x avoid) in
  let create_input c =
      let bl_typ = List.map (fun (s,seq,_,_) ->
        mkNamedProd (make_annot x Sorts.Relevant) (mkVar s) (
            mkNamedProd (make_annot y Sorts.Relevant) (mkVar s) (
              mkArrow
               ( mkApp(eq (),[|bb (); mkApp(mkVar seq,[|mkVar x;mkVar y|]);tt () |]))
               Sorts.Relevant
               ( mkApp(eq (),[|mkVar s;mkVar x;mkVar y|]))
          ))
        ) list_id in
      let bl_input = List.fold_left2 ( fun a (s,_,sbl,_) b ->
        mkNamedProd (make_annot sbl Sorts.Relevant) b a
      ) c (List.rev list_id) (List.rev bl_typ) in
      let eqs_typ = List.map (fun (s,_,_,_) ->
          mkProd(make_annot Anonymous Sorts.Relevant,mkVar s,mkProd(make_annot Anonymous Sorts.Relevant,mkVar s,(bb ())))
          ) list_id in
      let eq_input = List.fold_left2 ( fun a (s,seq,_,_) b ->
        mkNamedProd (make_annot seq Sorts.Relevant) b a
      ) bl_input (List.rev list_id) (List.rev eqs_typ) in
    List.fold_left (fun a decl ->
        let x = map_annot
            (function Name s -> s | Anonymous -> next_ident_away (Id.of_string "A") avoid)
            (RelDecl.get_annot decl)
        in
        mkNamedProd x (RelDecl.get_type decl) a) eq_input lnamesparrec
    in
     create_input (
        mkNamedProd (make_annot x Sorts.Relevant) (mkFullInd env (ind,u) nparrec) (
          mkNamedProd (make_annot y Sorts.Relevant) (mkFullInd env (ind,u) (nparrec+1)) (
            mkArrow
              (mkApp(eq (),[|bb ();mkApp(eqI,[|mkVar x;mkVar y|]);tt ()|]))
              Sorts.Relevant
              (mkApp(eq (),[|mkFullInd env (ind,u) (nparrec+3);mkVar x;mkVar y|]))
        )))

let compute_bl_tact handle ind lnamesparrec nparrec =
  let list_id = list_id lnamesparrec in
  let first_intros =
    ( List.map (fun (s,_,_,_) -> s ) list_id )
    @ ( List.map (fun (_,seq,_,_ ) -> seq) list_id )
    @ ( List.map (fun (_,_,sbl,_ ) -> sbl) list_id )
  in
  intros_using_then first_intros begin fun fresh_first_intros ->
    Tacticals.tclTHENLIST [
        intro_using_then (Id.of_string "x") (fun freshn -> induct_on (EConstr.mkVar freshn));
        intro_using_then (Id.of_string "y") (fun freshm -> destruct_on (EConstr.mkVar freshm));
        intro_using_then (Id.of_string "Z") begin fun freshz ->
          Tacticals.tclTHENLIST [
              intros;
              Tacticals.tclTRY (
                  Tacticals.tclORELSE reflexivity my_discr_tac
                );
              simpl_in_hyp (freshz,Locus.InHyp);
              (*
repeat ( apply andb_prop in z;let z1:= fresh "Z" in destruct z as [z1 z]).
               *)
              Tacticals.tclREPEAT (
                  Tacticals.tclTHENLIST [
                      Simple.apply_in freshz (EConstr.of_constr (andb_prop()));
                      destruct_on_as (EConstr.mkVar freshz)
                        (IntroOrPattern [[CAst.make @@ IntroNaming (IntroFresh (Id.of_string "Z"));
                                          CAst.make @@ IntroNaming (IntroIdentifier freshz)]])
                ]);
              (*
  Ci a1 ... an = Ci b1 ... bn
 replace bi with ai; auto || replace bi with ai by  apply typeofbi_prod ; auto
               *)
              Proofview.Goal.enter begin fun gl ->
                let concl = Proofview.Goal.concl gl in
                let sigma = Tacmach.project gl in
                match EConstr.kind sigma concl with
                | App (c,ca) -> (
                  match EConstr.kind sigma c with
                  | Ind (indeq, u) ->
                     if GlobRef.equal (GlobRef.IndRef indeq) Coqlib.(lib_ref "core.eq.type")
                     then
                       Tacticals.tclTHEN
                         (do_replace_bl handle ind
                            (List.rev fresh_first_intros)
                            nparrec (ca.(2))
                            (ca.(1)))
                         Auto.default_auto
                     else
                       Tacticals.tclZEROMSG (str "Failure while solving Boolean->Leibniz.")
                  | _ -> Tacticals.tclZEROMSG (str" Failure while solving Boolean->Leibniz.")
                )
                | _ -> Tacticals.tclZEROMSG (str "Failure while solving Boolean->Leibniz.")
                end

            ]
          end
      ]
    end

let make_bl_scheme env handle mind =
  let mib = Environ.lookup_mind mind env in
  if not (Int.equal (Array.length mib.mind_packets) 1) then
    user_err
      (str "Automatic building of boolean->Leibniz lemmas not supported");

  (* Setting universes *)
  let auctx = Declareops.universes_context mib.mind_universes in
  let u, uctx = UnivGen.fresh_instance_from auctx None in
  let uctx = UState.merge ~sideff:false UState.univ_rigid (UState.from_env env) uctx in

  let ind = (mind,0) in
  let nparrec = mib.mind_nparams_rec in
  let lnonparrec,lnamesparrec =
    Inductive.inductive_nonrec_rec_paramdecls (mib,u) in
  let bl_goal = compute_bl_goal env handle (ind,u) lnamesparrec nparrec in
  let bl_goal = EConstr.of_constr bl_goal in
  let poly = Declareops.inductive_is_polymorphic mib in
  let (ans, _, _, _, uctx) = Declare.build_by_tactic ~poly ~side_eff:false env ~uctx ~typ:bl_goal
    (compute_bl_tact handle (ind, EConstr.EInstance.make u) lnamesparrec nparrec)
  in
  ([|ans|], uctx)

let make_bl_scheme_deps env ind =
  let inds = get_inductive_deps env ind in
  let map ind = SchemeMutualDep (ind, !bl_scheme_kind_aux ()) in
  SchemeMutualDep (ind, beq_scheme_kind) :: List.map map inds

let bl_scheme_kind =
  declare_mutual_scheme_object "_dec_bl"
  ~deps:make_bl_scheme_deps
  make_bl_scheme

let _ = bl_scheme_kind_aux := fun () -> bl_scheme_kind

(**********************************************************************)
(* Leibniz->Boolean *)

let compute_lb_goal env handle (ind,u) lnamesparrec nparrec =
  let list_id = list_id lnamesparrec in
  let eq = eq () and tt = tt () and bb = bb () in
  let avoid = avoid_of_list_id list_id in
  let eqI = eqI handle (ind,u) list_id in
  let x = next_ident_away (Id.of_string "x") avoid in
  let y = next_ident_away (Id.of_string "y") (Id.Set.add x avoid) in
    let create_input c =
      let lb_typ = List.map (fun (s,seq,_,_) ->
        mkNamedProd (make_annot x Sorts.Relevant) (mkVar s) (
            mkNamedProd (make_annot y Sorts.Relevant) (mkVar s) (
              mkArrow
                ( mkApp(eq,[|mkVar s;mkVar x;mkVar y|]))
                Sorts.Relevant
                ( mkApp(eq,[|bb;mkApp(mkVar seq,[|mkVar x;mkVar y|]);tt|]))
          ))
        ) list_id in
      let lb_input = List.fold_left2 ( fun a (s,_,_,slb) b ->
        mkNamedProd (make_annot slb Sorts.Relevant) b a
      ) c (List.rev list_id) (List.rev lb_typ) in
      let eqs_typ = List.map (fun (s,_,_,_) ->
          mkProd(make_annot Anonymous Sorts.Relevant,mkVar s,
                 mkProd(make_annot Anonymous Sorts.Relevant,mkVar s,bb))
          ) list_id in
      let eq_input = List.fold_left2 ( fun a (s,seq,_,_) b ->
        mkNamedProd (make_annot seq Sorts.Relevant) b a
      ) lb_input (List.rev list_id) (List.rev eqs_typ) in
      List.fold_left (fun a decl ->
          let x = map_annot
              (function Name s -> s | Anonymous -> Id.of_string "A")
              (RelDecl.get_annot decl)
          in
          mkNamedProd x (RelDecl.get_type decl)  a) eq_input lnamesparrec
    in
      create_input (
        mkNamedProd (make_annot x Sorts.Relevant) (mkFullInd env (ind,u) nparrec) (
          mkNamedProd (make_annot y Sorts.Relevant) (mkFullInd env (ind,u) (nparrec+1)) (
            mkArrow
              (mkApp(eq,[|mkFullInd env (ind,u) (nparrec+2);mkVar x;mkVar y|]))
              Sorts.Relevant
              (mkApp(eq,[|bb;mkApp(eqI,[|mkVar x;mkVar y|]);tt|]))
        )))

let compute_lb_tact handle ind lnamesparrec nparrec =
  let list_id = list_id lnamesparrec in
  let first_intros =
    ( List.map (fun (s,_,_,_) -> s ) list_id )
    @ ( List.map (fun (_,seq,_,_) -> seq) list_id )
    @ ( List.map (fun (_,_,_,slb) -> slb) list_id )
  in
  intros_using_then first_intros begin fun fresh_first_intros ->
    Tacticals.tclTHENLIST [
        intro_using_then (Id.of_string "x") (fun freshn -> induct_on (EConstr.mkVar freshn));
        intro_using_then (Id.of_string "y") (fun freshm -> destruct_on (EConstr.mkVar freshm));
        intro_using_then (Id.of_string "Z") begin fun freshz ->
          Tacticals.tclTHENLIST [
              intros;
              Tacticals.tclTRY (
                  Tacticals.tclORELSE reflexivity my_discr_tac
                );
              my_inj_tac freshz;
              intros; simpl_in_concl;
              Auto.default_auto;
              Tacticals.tclREPEAT (
                  Tacticals.tclTHENLIST [apply (EConstr.of_constr (andb_true_intro()));
                                             simplest_split ;Auto.default_auto ]
                );
              Proofview.Goal.enter begin fun gls ->
                let concl = Proofview.Goal.concl gls in
                let sigma = Tacmach.project gls in
                (* assume the goal to be eq (eq_type ...) = true *)
                match EConstr.kind sigma concl with
                | App(c,ca) -> (match (EConstr.kind sigma ca.(1)) with
                                | App(c',ca') ->
                                   let n = Array.length ca' in
                                   do_replace_lb handle
                                     (List.rev fresh_first_intros)
                                     nparrec
                                     ca'.(n-2) ca'.(n-1)
                                | _ ->
                                   Tacticals.tclZEROMSG (str "Failure while solving Leibniz->Boolean.")
                               )
                | _ ->
                   Tacticals.tclZEROMSG (str "Failure while solving Leibniz->Boolean.")
                end
            ]
          end
      ]
    end

let make_lb_scheme env handle mind =
  let mib = Environ.lookup_mind mind env in
  if not (Int.equal (Array.length mib.mind_packets) 1) then
    user_err
      (str "Automatic building of Leibniz->boolean lemmas not supported");
  let ind = (mind,0) in

  (* Setting universes *)
  let auctx = Declareops.universes_context mib.mind_universes in
  let u, uctx = UnivGen.fresh_instance_from auctx None in
  let uctx = UState.merge ~sideff:false UState.univ_rigid (UState.from_env env) uctx in

  let nparrec = mib.mind_nparams_rec in
  let lnonparrec,lnamesparrec =
    Inductive.inductive_nonrec_rec_paramdecls (mib,u) in
  let lb_goal = compute_lb_goal env handle (ind,u) lnamesparrec nparrec in
  let lb_goal = EConstr.of_constr lb_goal in
  let poly = Declareops.inductive_is_polymorphic mib in
  let (ans, _, _, _, ctx) = Declare.build_by_tactic ~poly ~side_eff:false env ~uctx ~typ:lb_goal
    (compute_lb_tact handle ind lnamesparrec nparrec)
  in
  ([|ans|], ctx)

let make_lb_scheme_deps env ind =
  let inds = get_inductive_deps env ind in
  let map ind = SchemeMutualDep (ind, !lb_scheme_kind_aux ()) in
  SchemeMutualDep (ind, beq_scheme_kind) :: List.map map inds

let lb_scheme_kind =
  declare_mutual_scheme_object "_dec_lb"
  ~deps:make_lb_scheme_deps
  make_lb_scheme

let _ = lb_scheme_kind_aux := fun () -> lb_scheme_kind

(**********************************************************************)
(* Decidable equality *)

let check_not_is_defined () =
  if not (Coqlib.has_ref "core.not.type")
  then raise (UndefinedCst "not")

(* {n=m}+{n<>m}  part  *)
let compute_dec_goal env ind lnamesparrec nparrec =
  check_not_is_defined ();
  let eq = eq () and tt = tt () and bb = bb () in
  let list_id = list_id lnamesparrec in
  let avoid = avoid_of_list_id list_id in
  let x = next_ident_away (Id.of_string "x") avoid in
  let y = next_ident_away (Id.of_string "y") (Id.Set.add x avoid) in
    let create_input c =
      let lb_typ = List.map (fun (s,seq,_,_) ->
        mkNamedProd (make_annot x Sorts.Relevant) (mkVar s) (
            mkNamedProd (make_annot y Sorts.Relevant) (mkVar s) (
              mkArrow
                ( mkApp(eq,[|mkVar s;mkVar x;mkVar y|]))
                Sorts.Relevant
                ( mkApp(eq,[|bb;mkApp(mkVar seq,[|mkVar x;mkVar y|]);tt|]))
          ))
        ) list_id in
      let bl_typ = List.map (fun (s,seq,_,_) ->
        mkNamedProd (make_annot x Sorts.Relevant) (mkVar s) (
            mkNamedProd (make_annot y Sorts.Relevant) (mkVar s) (
              mkArrow
                ( mkApp(eq,[|bb;mkApp(mkVar seq,[|mkVar x;mkVar y|]);tt|]))
                Sorts.Relevant
                ( mkApp(eq,[|mkVar s;mkVar x;mkVar y|]))
          ))
        ) list_id in

      let lb_input = List.fold_left2 ( fun a (s,_,_,slb) b ->
        mkNamedProd (make_annot slb Sorts.Relevant) b a
      ) c (List.rev list_id) (List.rev lb_typ) in
      let bl_input = List.fold_left2 ( fun a (s,_,sbl,_) b ->
        mkNamedProd (make_annot sbl Sorts.Relevant) b a
      ) lb_input (List.rev list_id) (List.rev bl_typ) in

      let eqs_typ = List.map (fun (s,_,_,_) ->
          mkProd(make_annot Anonymous Sorts.Relevant,mkVar s,
                 mkProd(make_annot Anonymous Sorts.Relevant,mkVar s,bb))
          ) list_id in
      let eq_input = List.fold_left2 ( fun a (s,seq,_,_) b ->
        mkNamedProd (make_annot seq Sorts.Relevant) b a
      ) bl_input (List.rev list_id) (List.rev eqs_typ) in
      List.fold_left (fun a decl ->
          let x = map_annot
              (function Name s -> s | Anonymous -> Id.of_string "A")
              (RelDecl.get_annot decl)
          in
          mkNamedProd x (RelDecl.get_type decl) a) eq_input lnamesparrec
    in
        let eqnm = mkApp(eq,[|mkFullInd env ind (2*nparrec+2);mkVar x;mkVar y|]) in
        create_input (
          mkNamedProd (make_annot x Sorts.Relevant) (mkFullInd env ind (2*nparrec)) (
            mkNamedProd (make_annot y Sorts.Relevant) (mkFullInd env ind (2*nparrec+1)) (
              mkApp(sumbool(),[|eqnm;mkApp (UnivGen.constr_of_monomorphic_global (Global.env ()) @@ Coqlib.lib_ref "core.not.type",[|eqnm|])|])
          )
        )
      )

let compute_dec_tact handle (ind,u) lnamesparrec nparrec =
  let eq = eq () and tt = tt ()
      and ff = ff () and bb = bb () in
  let list_id = list_id lnamesparrec in
  let _ = get_scheme handle beq_scheme_kind ind in (* This is just an assertion? *)
  let _non_fresh_eqI = eqI handle (ind,u) list_id in
  let eqtrue x = mkApp(eq,[|bb;x;tt|]) in
  let eqfalse x = mkApp(eq,[|bb;x;ff|]) in
  let first_intros =
    ( List.map (fun (s,_,_,_) -> s ) list_id )
    @ ( List.map (fun (_,seq,_,_) -> seq) list_id )
    @ ( List.map (fun (_,_,sbl,_) -> sbl) list_id )
    @ ( List.map (fun (_,_,_,slb) -> slb) list_id )
  in
  let fresh_id s gl = fresh_id_in_env (Id.Set.empty) s (Proofview.Goal.env gl) in
  intros_using_then first_intros begin fun fresh_first_intros ->
    let eqI =
      let a = Array.of_list fresh_first_intros in
      let n = List.length list_id in
      assert (Int.equal (Array.length a) (4 * n));
      let fresh_list_id =
        List.init n (fun i -> (Array.get a i, Array.get a (i+n),
                               Array.get a (i+2*n), Array.get a (i+3*n))) in
      eqI handle (ind,u) fresh_list_id
    in
    intro_using_then (Id.of_string "x") begin fun freshn ->
      intro_using_then (Id.of_string "y") begin fun freshm ->
        Proofview.Goal.enter begin fun gl ->
          let freshH = fresh_id (Id.of_string "H") gl in
          let eqbnm = mkApp(eqI,[|mkVar freshn;mkVar freshm|]) in
          let arfresh = Array.of_list fresh_first_intros in
          let xargs = Array.sub arfresh 0 (2*nparrec) in
          let c = get_scheme handle bl_scheme_kind ind in
          let blI = mkConstU (c,u) in
          let c = get_scheme handle lb_scheme_kind ind in
          let lbI = mkConstU (c,u) in
          Tacticals.tclTHENLIST [
              (*we do this so we don't have to prove the same goal twice *)
              assert_by (Name freshH) (EConstr.of_constr (
                                           mkApp(sumbool(),[|eqtrue eqbnm; eqfalse eqbnm|])
                ))
                (Tacticals.tclTHEN (destruct_on (EConstr.of_constr eqbnm)) Auto.default_auto);

              Proofview.Goal.enter begin fun gl ->
                let freshH2 = fresh_id (Id.of_string "H") gl in
                Tacticals.tclTHENS (destruct_on_using (EConstr.mkVar freshH) freshH2) [
                    (* left *)
                    Tacticals.tclTHENLIST [
                        simplest_left;
                        apply (EConstr.of_constr (mkApp(blI,Array.map mkVar xargs)));
                        Auto.default_auto
                      ]
                  ;

                    (*right *)
                    Proofview.Goal.enter begin fun gl ->
                      let freshH3 = fresh_id (Id.of_string "H") gl in
                      Tacticals.tclTHENLIST [
                          simplest_right ;
                          unfold_constr (Coqlib.lib_ref "core.not.type");
                          intro;
                          Equality.subst_all ();
                          assert_by (Name freshH3)
                            (EConstr.of_constr (mkApp(eq,[|bb;mkApp(eqI,[|mkVar freshm;mkVar freshm|]);tt|])))
                            (Tacticals.tclTHENLIST [
                                 apply (EConstr.of_constr (mkApp(lbI,Array.map mkVar xargs)));
                                 Auto.default_auto
                            ]);
                          Equality.general_rewrite ~where:(Some freshH3) ~l2r:true
                            Locus.AllOccurrences ~freeze:true ~dep:false ~with_evars:true
                            ((EConstr.mkVar freshH2),
                             NoBindings
                            )
                            ;
                          my_discr_tac
                        ]
                      end
                  ]
                end
            ]
          end
        end
      end
    end

let make_eq_decidability env handle mind =
  let mib = Environ.lookup_mind mind env in
  if not (Int.equal (Array.length mib.mind_packets) 1) then
    raise DecidabilityMutualNotSupported;
  let ind = (mind,0) in
  let nparrec = mib.mind_nparams_rec in

  (* Setting universes *)
  let auctx = Declareops.universes_context mib.mind_universes in
  let u, uctx = UnivGen.fresh_instance_from auctx None in
  let uctx = UState.merge ~sideff:false UState.univ_rigid (UState.from_env env) uctx in

  let lnonparrec,lnamesparrec =
    Inductive.inductive_nonrec_rec_paramdecls (mib,u) in
  let poly = Declareops.inductive_is_polymorphic mib in
  let (ans, _, _, _, ctx) = Declare.build_by_tactic ~poly ~side_eff:false env ~uctx
      ~typ:(EConstr.of_constr (compute_dec_goal env (ind,u) lnamesparrec nparrec))
      (compute_dec_tact handle (ind,u) lnamesparrec nparrec)
  in
  ([|ans|], ctx)

let eq_dec_scheme_kind =
  declare_mutual_scheme_object "_eq_dec"
  ~deps:(fun _ ind -> [SchemeMutualDep (ind, bl_scheme_kind); SchemeMutualDep (ind, lb_scheme_kind)])
  make_eq_decidability

(* The eq_dec_scheme proofs depend on the equality and discr tactics
   but the inj tactics, that comes with discr, depends on the
   eq_dec_scheme... *)

let _ = Equality.set_eq_dec_scheme_kind eq_dec_scheme_kind
