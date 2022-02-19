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

exception EqNotFound of inductive
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
exception InternalDependencies

let named_hd env t na = named_hd env (Evd.from_env env) (EConstr.of_constr t) na
let name_assumption env = function
| RelDecl.LocalAssum (na,t) -> RelDecl.LocalAssum (map_annot (named_hd env t) na, t)
| RelDecl.LocalDef (na,c,t) -> RelDecl.LocalDef (map_annot (named_hd env c) na, c, t)
let name_context env ctxt =
  snd
    (List.fold_left
       (fun (env,hyps) d ->
          let d' = name_assumption env d in (Environ.push_rel d' env, d' :: hyps))
       (env,[]) (List.rev ctxt))

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
let int63_eqb () = UnivGen.constr_of_monomorphic_global (Global.env ()) (Coqlib.lib_ref "num.int63.eqb")
let float64_eqb () = UnivGen.constr_of_monomorphic_global (Global.env ()) (Coqlib.lib_ref "num.float.leibniz.eqb")

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
  mkApp (mkIndU (ind,u), Context.Rel.instance mkRel n mib.mind_params_ctxt)

let mkPartialInd env (ind,u) n =
  let mib = Environ.lookup_mind (fst ind) env in
  let _, recparams_ctx = Inductive.inductive_nonrec_rec_paramdecls (mib,u) in
  mkApp (mkIndU (ind,u), Context.Rel.instance mkRel n recparams_ctx)

let name_X = make_annot (Name (Id.of_string "X")) Sorts.Relevant
let name_Y = make_annot (Name (Id.of_string "Y")) Sorts.Relevant
let mk_eqb_over u = mkProd (name_X, u, (mkProd (name_Y, lift 1 u, bb ())))

let check_bool_is_defined () =
  if not (Coqlib.has_ref "core.bool.type")
  then raise (UndefinedCst "bool")

let check_no_indices mib =
  if Array.exists (fun mip -> mip.mind_nrealargs <> 0) mib.mind_packets then
    raise DecidabilityIndicesNotSupported

let is_irrelevant env c =
  match kind (EConstr.Unsafe.to_constr (Retyping.get_type_of env (Evd.from_env env) (EConstr.of_constr c))) with
  | Sort SProp -> true
  | _ -> false

let get_scheme handle k ind = match local_lookup_scheme handle k ind with
| None -> assert false
| Some c -> c

let beq_scheme_kind_aux = ref (fun _ -> failwith "Undefined")

let get_inductive_deps ~noprop env kn =
  (* fetching the mutual inductive body *)
  let mib = Environ.lookup_mind kn env in
  (* number of params in the type *)
  check_no_indices mib;
  let env = Environ.push_rel_context mib.mind_params_ctxt env in
  let sigma = Evd.from_env env in
  let get_deps_one accu i mip =
    (* This function is only trying to recursively compute the inductive types
       appearing as arguments of the constructors. This is done to support
       equality decision over hereditarily first-order types. It could be
       performed in a much cleaner way, e.g. using the kernel normal form of
       constructor types and kernel whd_all for the argument types. *)
    let rec aux env accu c =
      let (c,a) = Reductionops.whd_all_stack env sigma c in
      match EConstr.kind sigma c with
      | Cast (x,_,_) -> aux env accu (EConstr.applist (x,a))
      | App _ -> assert false
      | Ind ((kn', _ as ind), _) ->
          if Environ.QMutInd.equal env kn kn' then
            (* Example: Inductive T A := C : T (option A) -> T A. *)
            List.fold_left (aux env) accu a
          else
            let _,mip = Inductive.lookup_mind_specif env ind in
            (* Types in SProp have trivial equality and are skipped *)
            if match mip.mind_arity with RegularArity {mind_sort = SProp} -> true | _ -> false then
              List.fold_left (aux env) accu a
            else
              List.fold_left (aux env) (kn' :: accu) a
      | Const (kn, u) ->
        (match Environ.constant_opt_value_in env (kn, EConstr.EInstance.kind sigma u) with
        | Some c -> aux env accu (EConstr.applist (EConstr.of_constr c,a))
        | None -> accu)
      | Rel _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | Proj _
      | Construct _ | Case _ | CoFix _ | Fix _ | Meta _ | Evar _ | Int _
      | Float _ | Array _ -> Termops.fold_constr_with_full_binders env sigma EConstr.push_rel aux env (List.fold_left (aux env) accu a) c
    in
    let fold i accu (constr_ctx,_) =
      let constr_ctx, _ = List.chop mip.mind_consnrealdecls.(i) constr_ctx in
      let rec fold env accu = function
        | [] -> env, accu
        | decl::ctx ->
           let env, accu = fold env accu ctx in
           let t = Context.Rel.Declaration.get_type decl in
           Environ.push_rel decl env,
           (if noprop && is_irrelevant env t then accu else aux env accu (EConstr.of_constr t))
      in
      snd (fold env accu constr_ctx)
    in
    Array.fold_left_i fold accu mip.mind_nf_lc
  in
  Array.fold_left_i (fun i accu mip -> get_deps_one accu i mip) [] mib.mind_packets

(** A compact data structure to remember for each declaration of the
    context if it is a type and comes with a Boolean equality; if it
    comes with an equality we remember the integer to subtract to the
    de Bruijn indices of the binder to get the equality *)

type eq_status =
  | End
  (* int is the number of consecutive declarations without an equality *)
  | WithoutEq of int * eq_status
  (* list is the list of shifts for consecutive declarations with an equality *)
  | WithEq of int list * eq_status

let add_eq_status_no = function
  | WithEq _ | End as s -> WithoutEq (1, s)
  | WithoutEq (n, s) -> WithoutEq (n+1, s)

let set_eq_status_yes n q s =
  let rec aux n = function
    | WithoutEq (p,End) when Int.equal n p -> WithoutEq (p-1, WithEq ([q],End))
    | WithoutEq (p,WithEq (l,s)) when Int.equal n p -> WithoutEq (p-1, WithEq (q::l,s))
    | WithoutEq (p,s) when n < p -> WithoutEq (n-1, WithEq ([q], WithoutEq (p-n, s)))
    | WithoutEq (p,s) when Int.equal n 1 -> WithEq ([q], WithoutEq (p-1, s))
    | WithoutEq (p,s) -> WithoutEq (p, aux (n-p) s)
    | WithEq (l,s) -> WithEq (l,aux (n-List.length l) s)
    | End -> assert false in
  aux n s

let rec has_decl_equality n status =
  match n, status with
  | p, WithEq (l,s) when p <= List.length l -> Some (List.nth l (p-1))
  | p, WithEq (l,s) -> has_decl_equality (p-List.length l) s
  | p, WithoutEq (n,s) when p <= n -> None
  | p, WithoutEq (n,s) -> has_decl_equality (p-n) s
  | _, End -> assert false

(** The reallocation of variables to be done during the translation:
    [env] is the current env at the corresponding step of the translation
    [lift] is the lift for the original variables
    [eq_status] tells how to get the equality associated with a variable if any
    [ind_pos] tells the position of recursive calls (it could have
      been avoided by replacing the recursive occurrences of ind in an
      inductive definition by variables *)

type env_lift = {
  env : Environ.env; (* Gamma *)
  lift : Esubst.lift; (* lift : Gamma + Gamma_eq |- Gamma *)
  eq_status : eq_status;
  ind_pos : ((MutInd.t * int * rel_context * int) * int) option;
  }

let lift_ind_pos n =
  Option.map (fun (ind,k) -> (ind,k+n))

let empty_env_lift env = {
  env = env;
  lift = Esubst.el_id;
  eq_status = End;
  ind_pos = None;
  }

let push_env_lift decl env_lift = {
    env = Environ.push_rel decl env_lift.env;
    lift = Esubst.el_lift env_lift.lift;
    eq_status = add_eq_status_no env_lift.eq_status;
    ind_pos = lift_ind_pos 1 env_lift.ind_pos;
  }

let set_replicate n q env_lift = {
    env = env_lift.env;
    lift = env_lift.lift;
    eq_status = set_eq_status_yes n q env_lift.eq_status;
    ind_pos = env_lift.ind_pos;
  }

let shiftn_env_lift n env_lift =
  { env_lift with lift = Esubst.el_shft n (Esubst.el_liftn n env_lift.lift);
    ind_pos = lift_ind_pos n env_lift.ind_pos; }

let find_ind_env_lift env_lift (mind,i) =
  match env_lift.ind_pos with
  | Some ((mind',nrecparams,recparamsctx,nb_ind),n) when Environ.QMutInd.equal env_lift.env mind mind' ->
    Some (nrecparams,recparamsctx,n+nb_ind-i)
  | _ -> None

let shift_fix_env_lift ind nrecparams recparamsctx nb_ind env_lift = {
    env = env_lift.env;
    lift = Esubst.el_shft nb_ind env_lift.lift;
    eq_status = env_lift.eq_status;
    ind_pos = Some ((ind,nrecparams,recparamsctx,nb_ind),0)
    }

let push_rec_env_lift recdef env_lift =
  let n = Array.length (pi1 recdef) in {
    env = Environ.push_rec_types recdef env_lift.env;
    lift = Esubst.el_liftn n env_lift.lift;
    eq_status = add_eq_status_no env_lift.eq_status;
    ind_pos = lift_ind_pos n env_lift.ind_pos;
  }

let dest_lam_assum_expand env c =
  let ctx, c = Reduction.dest_lam_assum env c in
  if List.is_empty ctx then ctx, c
  else
    let t = EConstr.Unsafe.to_constr (Retyping.get_type_of (Environ.push_rel_context ctx env) (Evd.from_env env) (EConstr.of_constr c)) in
    let ctx', _ = Reduction.dest_prod_assum env t in
    ctx'@ctx, mkApp (lift (Context.Rel.length ctx') c, Context.Rel.instance mkRel 0 ctx')

let pred_context env ci params u nas =
  let mib, mip = Inductive.lookup_mind_specif env ci.ci_ind in
  let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
  let paramsubst = Vars.subst_of_rel_context_instance paramdecl params in
  let realdecls, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
  let self =
    let args = Context.Rel.instance mkRel 0 mip.mind_arity_ctxt in
    let inst = Univ.(Instance.of_array (Array.init (Instance.length u) Level.var)) in
    mkApp (mkIndU (ci.ci_ind, inst), args)
  in
  let realdecls = RelDecl.LocalAssum (Context.anonR, self) :: realdecls in
  Inductive.instantiate_context u paramsubst nas realdecls

let branch_context env ci params u nas i =
  let mib, mip = Inductive.lookup_mind_specif env ci.ci_ind in
  let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
  let paramsubst = Vars.subst_of_rel_context_instance paramdecl params in
  let ctx, _ = List.chop mip.mind_consnrealdecls.(i) (fst mip.mind_nf_lc.(i)) in
  Inductive.instantiate_context u paramsubst nas ctx

let build_beq_scheme_deps env kn =
  let inds = get_inductive_deps ~noprop:true env kn in
  List.map (fun ind -> SchemeMutualDep (ind, !beq_scheme_kind_aux ())) inds

let build_beq_scheme env handle kn =
  check_bool_is_defined ();
  (* predef coq's boolean type *)
  (* here I leave the Naming thingy so that the type of
     the function is more readable for the user *)
  let eqName = map_annot (function
    | Name s -> Name (Id.of_string ("eq_"^(Id.to_string s)))
    | Anonymous -> Name (Id.of_string "eq_A"))
  in

  (* The Boolean equality translation is a parametricity translation
     where each type T is interpreted as the pair of:
     - a (possibly degenerate) predicate T_R in Type over T (i.e. T_R : T->Type)
     - when T is decidable, a Boolean equality T_E over (i.e. T_E :
       option (T->T->bool) where None means not decidable, that is, at
       worst, unknown to be decidable)

     This generalizes into an interpretation of each term M:T as:
     - an inhabitant [|M|] of T_R M
     by setting for sort s:
     - s_R := \T:s.{R:T->s ; E:option (T->T->bool)} and
     - s_E := None
     so that types T:s are indeed interpreted as a pair, namely by:
     - [|T|] := {R:=T_R; E:=T_E} : s_R T
     and, in particular:
     - [|Type(n)|] := {R:=Type(n)_R; E:=Type(n)_E) : Type(n+1)_R Type(n)

     In practice, to have simpler schemes, we won't support here the
     full hierarchy of sorts. That is, we assume that type parameters
     of a type will be instantiated only by small types (i.e. not
     containing sorts). This makes sense since equality on large types
     is anyway not decidable in the general case [*].

     Now, it happens that several parts of the translation are
     degenerate. For instance, if T is a small type (not containing
     sorts), then T_R M, which expresses that M realizes T, is a
     singleton for all M (we assume functional extensionality to treat
     the case of dependent product types). Therefore, M_T does not
     need to be defined in this case. Conversely, if T is not small,
     it is not decidable and T_E will be None.

     This means that at least T_R is degenerate or T_E is None and
     this also means that for M:T with degenerate T_R, we don't need
     to compute [|M|].R

     This further means that when translating a variable x:T with T
     small, it can just be translated to x:T without requiring the
     trivial information that T_R x is inhabited.

     Similarly for types T of the form [forall X, (forall Y ...) ... Y args]
     based on the assumption [*] that Y is instantiated only by small
     functorial types for which (Y args)_R would be degenerate.

     Similarly, based on the restriction above [*] that parameters are
     instantiated by small types, when translating a variable x:T with
     T an arity, i.e. of the form [... -> Type] (or at worst
     [... -> Type*Type] etc.), we can assume x to be instantiated by a
     small functorial type whose R translation is degenerate.

     It remains the declarations of the form X:T for T of the form
     [forall X, ... X args] where X is in negative position of a
     dependent product. If such X is instantiated by a large type in
     the definition, as in
     [Inductive I (F:forall X:Type, X->X) (B:F Type nat) := C : B -> I F B],
     we give up. Otherwise said, we support only the case when `X`is
     instantiated by a small type.

     Eventually, we thus need two translations:
     - T_R when T is large and it does not need to go under
       applicative subterms since subterms [X args] are considered
       small by assumption [*]
     - T_E when T is small which needs to go under subterms and which
       thus needs to be generalized into a translation M_E : T_R.E
       whenever T is detected as decidable (in which case, T_R.E is
       typically of the form T->T->bool or of the form
       (T.1->T.1->bool)*(T.2->T.2->bool), etc.)

     Below, the first translation is called [translate_type_eq] and
     the second [translate_term_eq]. Additionally, there is a copy-cat
     translation called "translate_term" that lifts M in the typing context
     of M_R.

     The function [translate_type_eq] takes as input a type T and a
     term M of type T and it returns T_R M.

     For M of type T, the function [translate_term_eq M] returns an
     object of type term T_R M, that is, when M is itself some type U,
     an object of type U->U->bool.

     Note that we don't use an option type for non-decidable types but
     instead raises an exception whenever a type is not detected as
     decidable.

     Future work might support:
     - exotic types such as
       [Inductive I (F:forall X:Type, X->X) (B:F Type nat) := C : B -> I F B]
     - types with invertible indices like listn
     - dependent products over finite types (e.g. over bool->bool), and
       more generally compact types whose equality is decidable (see Escardo-Oliva)
  *)

  let rec translate_type_eq env_lift na c t =
    let ctx, t = Reduction.dest_prod_assum env t in
    let env_lift', ctx_eq = translate_context_eq env_lift ctx in
    let inst = Array.map (translate_term env_lift') (Context.Rel.instance mkRel 0 ctx) in
    let env_lift'' = shiftn_env_lift (Context.Rel.length ctx_eq) env_lift in
    let c = mkApp (translate_term env_lift'' c, inst) in
    let c = match kind t with
    | Sort _ -> Some (mk_eqb_over c)

    | Prod _ | LetIn _ -> assert false

    (* [s] is necessaritly a sort *)
    | Cast (t,k,s) ->
      begin
        match translate_type_eq env_lift' na c t with
        | None -> None
        | Some t -> Some (mkCast (t, k, mkProd (na, t, c)))
      end

    (* TODO: take into account situations like (P:Type * Type) which
       could be translated into (fst P->fst P>bool)*(snd P->snd
       P->bool); to be done in parallel with preserving the types in
       Proj/Construct/CoFix *)
    | Ind _ -> None
    | Array _ -> None

    (* We assume references to be references to small types and thus
       to types with singleton realizability predicate; to support
       references to large types, see comments above for the full
       translation *)
    | App _ | Rel _ | Var _ | Const _ -> None

    (* The restricted translation translates only types *)
    | Lambda _ | Construct _ -> assert false

    | Case (ci, u, pms, (pnames,p), iv, tm, lbr) ->
      let env_lift_pred = shiftn_env_lift (Array.length pnames) env_lift in
      let t =
        mkCase (ci, u,
          Array.map (translate_term env_lift_pred) pms,
          translate_term_with_binders env_lift_pred (pnames,p),
          Constr.map_invert (translate_term env_lift_pred) iv,
          mkRel 1,
          Array.map (translate_term_with_binders env_lift_pred) lbr) in
      (* in the restricted translation, only types are translated and
         the return predicate is necessarily a type *)
      let p = mkProd (anonR, t, p) in
      let lbr = Array.mapi (fun i (names, t) ->
        let ctx = branch_context env ci pms u names i in
        let env_lift' = List.fold_right push_env_lift ctx env_lift in
        match translate_type_eq env_lift' na (mkRel 1) t with
        | None -> None
        | Some t_eq -> Some (names, mkLambda (na, t, t_eq))) lbr in
      if Array.for_all Option.has_some lbr then
        let lbr = Array.map Option.get lbr in
        let case = mkCase (ci, u, pms, (pnames, p), iv, translate_term env_lift tm, lbr) in
        Some (mkApp (case, [|c|]))
      else
        None

    (* TODO: in parallel with traversing Fix in translate_term_eq to
       look for types, traverse Fix to look for Type here *)
    | Fix _ -> None

    (* Not building a type *)
    | Proj _ | CoFix _ | Int _ | Float _ -> None

    | Meta _ | Evar _ -> assert false (* kernel terms *)
    in
    Option.map (fun c -> Term.it_mkProd_or_LetIn c ctx_eq) c

  and translate_term_eq env_lift c =
    let ctx, c = dest_lam_assum_expand env_lift.env c in
    let env_lift, ctx = translate_context_eq env_lift ctx in
    let c = match Constr.kind c with
    | Rel x ->
        (match has_decl_equality x env_lift.eq_status with
        | Some n -> Some (mkRel (Esubst.reloc_rel x env_lift.lift - n))
        | None -> None)
    | Var x ->
        if Reduction.is_arity env (Typeops.type_of_variable env x) then
          (* Support for working in a context with "eq_x : x -> x -> bool" *)
          let eid = Id.of_string ("eq_"^(Id.to_string x)) in
          let () =
            try ignore (Environ.lookup_named eid env)
            with Not_found -> raise (ParameterWithoutEquality (GlobRef.VarRef x))
          in
          Some (mkVar eid)
        else
          None
    | Cast (c,k,t) ->
      begin
        match translate_term_eq env_lift c, translate_type_eq env_lift anonR c t with
        | Some c, Some t -> Some (mkCast (c,k,t))
        | None, None -> None
        | (None | Some _), _ -> assert false
      end
    | Lambda _ | LetIn _ -> assert false
    | App (f,args) ->
      begin
        let f, args =
          match kind f with
          | Ind (ind',_) ->
            (match find_ind_env_lift env_lift ind' with
            | Some (nrecparams,_,n) when Array.length args >= nrecparams ->
              Some (mkRel n), Array.sub args nrecparams (Array.length args - nrecparams)
            | _ -> translate_term_eq env_lift f, args)
          | Const (kn,u) ->
             (match Environ.constant_opt_value_in env (kn, u) with
              | Some c -> translate_term_eq env_lift (mkApp (c,args)), [||]
              | None -> translate_term_eq env_lift f, args)
          | _ -> translate_term_eq env_lift f, args
        in
        match f with
        | Some f -> Some (mkApp (f, translate_arguments_eq env_lift args))
        | None -> None
      end
    | Ind (ind',u) ->
      begin
        match find_ind_env_lift env_lift ind' with
        | Some (_,recparamsctx,n) -> Some (it_mkLambda_or_LetIn (mkRel n) (translate_context env_lift recparamsctx))
        | None ->
            try Some (mkConstU (get_scheme handle (!beq_scheme_kind_aux()) ind',u))
            with Not_found -> raise(EqNotFound ind')
      end
    | Const (kn,u as cst) ->
        if Environ.is_int63_type env kn then Some (int63_eqb ()) else
        if Environ.is_float64_type env kn then Some (float64_eqb ()) else
        if Environ.is_array_type env kn then (* TODO *) raise (ParameterWithoutEquality (GlobRef.ConstRef kn)) else
        (match Environ.constant_opt_value_in env (kn, u) with
        | Some c -> translate_term_eq env_lift c
        | None ->
        if Reduction.is_arity env (Typeops.type_of_constant_in env cst) then
          (* Support for working in a context with "eq_x : x -> x -> bool" *)
          (* Needs Hints, see test suite *)
          let eq_lbl = Label.make ("eq_" ^ Label.to_string (Constant.label kn)) in
          let kneq = Constant.change_label kn eq_lbl in
          if Environ.mem_constant kneq env then
            let _ = Environ.constant_opt_value_in env (kneq, u) in
            Some (mkConstU (kneq,u))
          else raise (ParameterWithoutEquality (GlobRef.ConstRef kn))
        else None)

    (* TODO: in parallel with preserving Type for Ind in
       translate_type_eq, preserve the types in Construct/CoFix *)
    | Proj _ | Construct _ | CoFix _ -> None

    | Case (ci, u, pms, (pnames,p), iv, tm, lbr) ->
      let pctx = pred_context env ci pms u pnames in
      let env_lift_pred = List.fold_right push_env_lift pctx env_lift in
      let n = Array.length pnames in
      let c =
        mkCase (ci, u,
          Array.map (lift n) pms,
          (pnames, liftn n (n+1) p),
          Constr.map_invert (lift n) iv,
          mkRel 1,
          Array.map (fun (names, br) -> (names, let q = Array.length names in liftn n (n+q+1) br)) lbr) in
      let p = translate_type_eq env_lift_pred anonR c p in
      let lbr = Array.mapi (fun i (names, t) ->
        let ctx = branch_context env ci pms u names i in
        let env_lift' = List.fold_right push_env_lift ctx env_lift in
        match translate_term_eq env_lift' t with
        | None -> None
        | Some t_eq -> Some (names, t_eq)) lbr in
      if Array.for_all Option.has_some lbr && Option.has_some p then
        let lbr = Array.map Option.get lbr in
        Some (mkCase (ci, u, pms, (pnames, Option.get p), iv, translate_term env_lift tm, lbr))
      else
        None

    | Fix ((recindxs,i),(names,typarray,bodies as recdef)) ->
      let _ =
        (* Almost work: would need:
           1. that the generated fix has an eq_status registration
              telling that an original recursive call should be
              interpreted as the pair of the whole fix and of the
              translated recursive call building the equality
           2. something to do around either packaging the type with
              its equality, or begin able for a match to have a return
              predicate different though convertible to itself, namely
              here a fix of match (see test-suite) *)
      let mkfix j = mkFix ((recindxs,j),recdef) in
      let typarray = Array.mapi (fun i -> translate_type_eq env_lift anonR (mkfix i)) typarray in
      let env_lift_types = push_rec_env_lift recdef env_lift in
      let bodies = Array.map (translate_term_eq env_lift_types) bodies in
      if Array.for_all Option.has_some bodies && Array.for_all Option.has_some typarray then
        let bodies = Array.map Option.get bodies in
        let typarray = Array.map Option.get typarray in
        Some (mkFix ((recindxs,i),(names,typarray,bodies)))
      else
        None
      in None

    | Sort _  -> raise InductiveWithSort (* would require a more sophisticated translation *)
    | Prod _ -> raise InductiveWithProduct (* loss of decidable if uncountable domain *)

    | Meta _ | Evar _ -> None (* assert false! *)
    | Int _ | Float _ | Array _ -> None
    in
    Option.map (fun c -> Term.it_mkLambda_or_LetIn c ctx) c

  (* Translate context by adding a context of Boolean equalities for each type argument

     Example of translated context:
     (F : (U -> U) -> nat -> U)
     (eq_F : forall G, (forall A, eq A -> eq (G A)) -> nat -> eq (F G)) *)

  and translate_context_eq env_lift ctx =
    let ctx = name_context env_lift.env ctx in
    let (env_lift_ctx,nctx_eq,ctx_with_eq) =
      List.fold_right (fun decl (env_lift,n,ctx) ->
        let env_lift = push_env_lift decl env_lift in
        let env_lift' = shiftn_env_lift (n-1) env_lift in
        match decl with
        | RelDecl.LocalDef (na,c,t) ->
          (match translate_term_eq env_lift' (lift 1 c), translate_type_eq env_lift' na (mkRel 1) (lift 1 t) with
          | Some eq_c, Some eq_typ ->
            (set_replicate 1 n env_lift, n, RelDecl.LocalDef (eqName na,eq_c,eq_typ) :: ctx)
          | None, None -> (env_lift, n-1, ctx)
          | (None | Some _), _ -> assert false)
        | RelDecl.LocalAssum (na,t) ->
           match translate_type_eq env_lift' na (mkRel 1) (lift 1 t) with
           | Some eq_typ -> (set_replicate 1 n env_lift, n, RelDecl.LocalAssum (eqName na,eq_typ) :: ctx)
           | None -> (env_lift, n-1, ctx)
      ) ctx (env_lift, Context.Rel.length ctx, ctx)
    in
    shiftn_env_lift nctx_eq env_lift_ctx, ctx_with_eq

  (* Translate arguments by adding Boolean equality when relevant

     Examples of translated applications:
     F (fun A => A) 0
     eq_F (fun A => A) (fun A eq_A => eq_A) 0

     F (fun A => list A) 0
     eq_F (fun A => list A) (fun A eq_A => eq_list A eq_A) 0 *)

  and translate_arguments_eq env_lift args =
    let args' = Array.map (translate_term env_lift) args in
    let eq_args = Array.of_list (List.map_filter (translate_term_eq env_lift) (Array.to_list args)) in
    Array.append args' eq_args

  (* Copy-cat translation with relocation *)

  and translate_term env_lift c =
    exliftn env_lift.lift c

  and translate_context env_lift ctx =
    Context.Rel.map_with_binders (fun i -> translate_term (shiftn_env_lift i env_lift)) ctx

  and translate_term_with_binders env_lift (names,c) =
    (names, translate_term (shiftn_env_lift (Array.length names) env_lift) c)

  in
  (* Starting translating the inductive block to Boolean equalities;
     Morally corresponds to the Ind case of translate_term_eq *)

  (* fetching the mutual inductive body *)
  let mib = Environ.lookup_mind kn env in

  (* Setting universes *)
  let auctx = Declareops.universes_context mib.mind_universes in
  let u, uctx = UnivGen.fresh_instance_from auctx None in
  let uctx = UState.of_context_set uctx in

  (* number of inductives in the mutual *)
  let nb_ind = Array.length mib.mind_packets in
  let truly_recursive =
    let open Declarations in
    let is_rec ra = match Declareops.dest_recarg ra with Mrec _ | Nested _ -> true | Norec -> false in
    Array.exists
      (fun mip -> Array.exists (List.exists is_rec) (Declareops.dest_subterms mip.mind_recargs))
      mib.mind_packets in
  (* params context divided *)
  let nonrecparams_ctx,recparams_ctx = Inductive.inductive_nonrec_rec_paramdecls (mib,u) in
  let params_ctx = nonrecparams_ctx @ recparams_ctx in
  let nparamsdecls = Context.Rel.length params_ctx in
  check_no_indices mib;

  let env_lift_recparams, recparams_ctx_with_eqs =
    translate_context_eq (empty_env_lift env) recparams_ctx in
  let env_lift_recparams_fix, fix_ctx, names, types =
    match mib.mind_finite with
    | CoFinite ->
      raise NoDecidabilityCoInductive
    | Finite when truly_recursive || nb_ind > 1 (* Hum, there exist non-recursive mutual types... *) ->
      (* rec name *)
      let rec_name i =
        (Id.to_string (Array.get mib.mind_packets i).mind_typename)^"_eqrec"
      in
      let names = Array.init nb_ind (fun i -> make_annot (Name (Id.of_string (rec_name i))) Sorts.Relevant) in
      let types = Array.init nb_ind (fun i -> Option.get (translate_type_eq env_lift_recparams anonR (mkPartialInd env ((kn,i),u) 0) (Term.it_mkProd_or_LetIn (*any sort:*) mkSet nonrecparams_ctx))) in
      let fix_ctx = List.rev (Array.to_list (Array.map2 (fun na t -> RelDecl.LocalAssum (na,t)) names types)) in
      shift_fix_env_lift kn mib.mind_nparams_rec recparams_ctx nb_ind env_lift_recparams, fix_ctx, names, types
    | Finite | BiFinite ->
      env_lift_recparams, [], [||], [||]
  in
  let env_lift_recparams_fix_nonrecparams, nonrecparams_ctx_with_eqs =
    translate_context_eq env_lift_recparams_fix nonrecparams_ctx in
  let make_one_eq cur =
    (* construct the "fun A B ... N, eqA eqB eqC ... N => fixpoint" part *)
    let ind = (kn,cur) in
    let indu = (ind,u) in
    let tomatch_ctx = RelDecl.[
        LocalAssum (name_Y,
                    translate_term (shiftn_env_lift 1 env_lift_recparams_fix_nonrecparams) (mkFullInd env indu 0));
        LocalAssum (name_X,
                    translate_term env_lift_recparams_fix_nonrecparams (mkFullInd env indu 0))
      ] in
    let env_lift_recparams_fix_nonrecparams_tomatch =
      shiftn_env_lift 2 env_lift_recparams_fix_nonrecparams in
    (* current inductive we are working on *)
    let pred =
      let cur_packet = mib.mind_packets.(cur) in
      (* Inductive toto : [rettyp] := *)
      let rettyp = Inductive.type_of_inductive ((mib,cur_packet),u) in
      (* split rettyp in a list without the non rec params and the last ->
         e.g. Inductive vec (A:Set) : nat -> Set := ... will do [nat] *)
      let _, rettyp = decompose_prod_n_assum nparamsdecls rettyp in
      let rettyp_l, _ = decompose_prod_assum rettyp in
      (* construct the predicate for the Case part*)
      it_mkLambda_or_LetIn
        (mkLambda (make_annot Anonymous Sorts.Relevant,
                   mkFullInd env indu (List.length rettyp_l),
                   (bb ())))
        rettyp_l in
    (* make_one_eq *)
    (* do the [| C1 ... =>  match Y with ... end
               ...
               Cn => match Y with ... end |]  part *)
    let rci = Sorts.Relevant in (* returning a boolean, hence relevant *)
    let constrs =
      let params = Context.Rel.instance_list mkRel 0 params_ctx in
      get_constructors env (make_ind_family (indu, params))
    in
    let make_andb_list = function
      | [] -> tt ()
      | eq :: eqs -> List.fold_left (fun eqs eq -> mkApp (andb(),[|eq;eqs|])) eq eqs
    in
    let body =
      match Environ.get_projections env ind with
      | Some projs ->
        (* A primitive record *)
        let nb_cstr_args = List.length constrs.(0).cs_args in
        let _,_,eqs = List.fold_right (fun decl (ndx,env_lift,l) ->
          let env_lift' = push_env_lift decl env_lift in
          match decl with
          | RelDecl.LocalDef (na,b,t) -> (ndx-1,env_lift',l)
          | RelDecl.LocalAssum (na,cc) ->
              if is_irrelevant env_lift.env cc then (ndx-1,env_lift',l)
              else
                if noccur_between 1 (nb_cstr_args-ndx) cc then
                  let cc = lift (ndx-nb_cstr_args) cc in
                  match translate_term_eq env_lift_recparams_fix_nonrecparams_tomatch cc with
                  | None -> raise (EqUnknown "type") (* A supported type should have an eq *)
                  | Some eqA ->
                     let proj = Projection.make projs.(nb_cstr_args-ndx) true in
                     (ndx-1,env_lift',mkApp (eqA, [|mkProj (proj,mkRel 2);mkProj (proj,mkRel 1)|])::l)
                else
                  raise InternalDependencies)
                        constrs.(0).cs_args (nb_cstr_args,env_lift_recparams_fix_nonrecparams_tomatch,[])
        in
        make_andb_list eqs
      | None ->
        (* An inductive type *)
        let ci = make_case_info env ind rci MatchStyle in
        let nconstr = Array.length constrs in
        let ar =
          Array.init nconstr (fun i ->
          let nb_cstr_args = List.length constrs.(i).cs_args in
          let env_lift_recparams_fix_nonrecparams_tomatch_csargsi = shiftn_env_lift nb_cstr_args env_lift_recparams_fix_nonrecparams_tomatch in
          let ar2 = Array.init nconstr (fun j ->
            let env_lift_recparams_fix_nonrecparams_tomatch_csargsij = shiftn_env_lift nb_cstr_args env_lift_recparams_fix_nonrecparams_tomatch_csargsi in
            let cc =
              if Int.equal i j then
                let _,_,eqs = List.fold_right (fun decl (ndx,env_lift,l) ->
                   let env_lift' = push_env_lift decl env_lift in
                   match decl with
                   | RelDecl.LocalDef (na,b,t) -> (ndx-1,env_lift',l)
                   | RelDecl.LocalAssum (na,cc) ->
                     if is_irrelevant env_lift.env cc then (ndx-1,env_lift',l)
                     else
                       if noccur_between 1 (nb_cstr_args-ndx) cc then
                         let cc = lift (ndx-nb_cstr_args) cc in
                         match translate_term_eq env_lift_recparams_fix_nonrecparams_tomatch_csargsij cc with
                         | None -> raise (EqUnknown "type") (* A supported type should have an eq *)
                         | Some eqA ->
                           (ndx-1,env_lift',mkApp (eqA, [|mkRel (ndx+nb_cstr_args);mkRel ndx|])::l)
                       else
                         raise InternalDependencies)
                                constrs.(j).cs_args (nb_cstr_args,env_lift_recparams_fix_nonrecparams_tomatch_csargsij,[])
                in
                make_andb_list eqs
              else
                ff ()
            in
            let cs_argsj = translate_context env_lift_recparams_fix_nonrecparams_tomatch_csargsi constrs.(j).cs_args in
            it_mkLambda_or_LetIn cc cs_argsj)
          in
          let predj = EConstr.of_constr (translate_term env_lift_recparams_fix_nonrecparams_tomatch_csargsi pred) in
          let case =
            simple_make_case_or_project env (Evd.from_env env)
              ci predj NoInvert (EConstr.mkRel (nb_cstr_args + 1))
              (EConstr.of_constr_array ar2)
          in
          let cs_argsi = translate_context env_lift_recparams_fix_nonrecparams_tomatch constrs.(i).cs_args in
          it_mkLambda_or_LetIn (EConstr.Unsafe.to_constr case) cs_argsi)
        in
        let predi = EConstr.of_constr (translate_term env_lift_recparams_fix_nonrecparams_tomatch pred) in
        let case =
          simple_make_case_or_project env (Evd.from_env env)
            ci predi NoInvert (EConstr.mkRel 2)
            (EConstr.of_constr_array ar) in
        EConstr.Unsafe.to_constr case
    in
    it_mkLambda_or_LetIn
      (it_mkLambda_or_LetIn body tomatch_ctx)
      nonrecparams_ctx_with_eqs
  in (* build_beq_scheme *)

  let res =
    match mib.mind_finite with
      | CoFinite ->
         raise NoDecidabilityCoInductive
      | Finite when truly_recursive || nb_ind > 1 (* Hum... *) ->
         let cores = Array.init nb_ind make_one_eq in
         Array.init nb_ind (fun i ->
            let kelim = Inductive.elim_sort (mib,mib.mind_packets.(i)) in
            if not (Sorts.family_leq InSet kelim) then
              raise (NonSingletonProp (kn,i));
            let decrArg = Context.Rel.length nonrecparams_ctx_with_eqs in
            let fix = mkFix (((Array.make nb_ind decrArg),i),(names,types,cores)) in
            it_mkLambda_or_LetIn fix recparams_ctx_with_eqs)
      | Finite | BiFinite ->
         assert (Int.equal nb_ind 1);
         (* If the inductive type is not recursive, the fixpoint is
             not used, so let's replace it with garbage *)
         let kelim = Inductive.elim_sort (mib,mib.mind_packets.(0)) in
         if not (Sorts.family_leq InSet kelim) then raise (NonSingletonProp (kn,0));
         [|it_mkLambda_or_LetIn (make_one_eq 0) recparams_ctx_with_eqs|]
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
        mkNamedProd (make_annot x Sorts.Relevant) (mkFullInd env (ind,u) (2*nparrec)) (
          mkNamedProd (make_annot y Sorts.Relevant) (mkFullInd env (ind,u) (2*nparrec+1)) (
            mkArrow
              (mkApp(eq (),[|bb ();mkApp(eqI,[|mkVar x;mkVar y|]);tt ()|]))
              Sorts.Relevant
              (mkApp(eq (),[|mkFullInd env (ind,u) (2*nparrec+3);mkVar x;mkVar y|]))
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
  let inds = get_inductive_deps ~noprop:false env ind in
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
        mkNamedProd (make_annot x Sorts.Relevant) (mkFullInd env (ind,u) (2*nparrec)) (
          mkNamedProd (make_annot y Sorts.Relevant) (mkFullInd env (ind,u) (2*nparrec+1)) (
            mkArrow
              (mkApp(eq,[|mkFullInd env (ind,u) (2*nparrec+2);mkVar x;mkVar y|]))
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
  let inds = get_inductive_deps ~noprop:false env ind in
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
        let eqnm = mkApp(eq,[|mkFullInd env ind (3*nparrec+2);mkVar x;mkVar y|]) in
        create_input (
          mkNamedProd (make_annot x Sorts.Relevant) (mkFullInd env ind (3*nparrec)) (
            mkNamedProd (make_annot y Sorts.Relevant) (mkFullInd env ind (3*nparrec+1)) (
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
