open GADT

  include AbstractTerm (struct
    type univ_instance = EConstr.EInstance.t

    include EConstr

    include Vars

    let exliftn el t =
      of_constr (Constr.exliftn el (Evd.MiniEConstr.unsafe_to_constr t))
  end)

  let mkIndU ((ind : 'ind InductiveDef.t), (instance : EConstr.EInstance.t)) : 'env t =
    Eq.(cast (sym ((InductiveDef.eq ^* Refl) ^-> eq)))
      EConstr.mkIndU (ind, instance)

  let whd_all (type env) (env : env Env.t) sigma (term : env t) =
    Eq.(cast (sym (Env.eq ^-> Refl ^-> eq ^-> eq)))
      Reductionops.whd_all env sigma term

  let nf_all (type env) (env : env Env.t) sigma (term : env t) =
    Eq.(cast (sym (Env.eq ^-> Refl ^-> eq ^-> eq)))
      Reductionops.nf_all env sigma term
  [@@ocaml.warning "-32"] (* can be unused *)

  let nf_zeta (type env) (env : env Env.t) sigma (term : env t) =
    Eq.(cast (sym (Env.eq ^-> Refl ^-> eq ^-> eq)))
      Reductionops.nf_all env sigma term
  [@@ocaml.warning "-32"] (* can be unused *)

(*
  let noccur_between sigma n m (term : 'env t) : bool =
    EConstr.Vars.noccur_between sigma n m (Eq.cast eq term)
*)

  let of_term (t : 'env Term.t) : 'env t =
    Eq.(cast (sym (Term.eq ^-> eq))) EConstr.of_constr t

  let mkSort (s : EConstr.ESorts.t) : 'env t =
    Eq.(cast (sym (Refl ^-> eq))) EConstr.mkSort s

  let print (env : 'env Env.t) sigma (term : 'env t) : Pp.t =
    Eq.(cast (sym (Env.eq ^-> Refl ^-> eq ^-> Refl)))
      Termops.Internal.print_constr_env env sigma term
  [@@ocaml.warning "-32"] (* can be unused *)

  let debug_print sigma (term : 'env t) : Pp.t =
    Termops.Internal.debug_print_constr sigma (Eq.cast eq term)
  [@@ocaml.warning "-32"] (* can be unused *)

  let retype_of (type env) (env : env Env.t) sigma (term : env t) : env t =
    Eq.(cast (sym (Env.eq ^-> Refl ^-> eq ^-> eq)))
      Retyping.get_type_of env sigma term

(*
  let get_type_of (type env) (env : env Env.t) (term : env t) : Evd.evar_map -> Evd.evar_map * env t =
    fun sigma ->
    Eq.(cast (sym (Env.eq ^-> Refl ^-> eq ^-> Refl ^* eq)))
      Typing.type_of env sigma term
*)

(*
  type 'env decompose_1 = {
      name : Names.Name.t Context.binder_annot;
      ty : 'env t;
      t : ('env Nat.succ) t;
    }

  let rec decompose_lam_1 : type env . Evd.evar_map -> env t ->
      env decompose_1 =
  fun sigma t ->
    match EConstr.kind sigma (Eq.cast eq t) with
    | Lambda (name, ty, t) ->
        { name; ty = Eq.(cast (sym eq)) ty; t = Eq.(cast (sym eq)) t }
    | Cast (c, _, _) -> decompose_lam_1 sigma (Eq.(cast (sym eq)) c)
    | _ -> failwith "decompose_lam_1: not an abstraction"

  let rec decompose_prod_1 : type env . Evd.evar_map -> env t ->
      env decompose_1 =
  fun sigma t ->
    match EConstr.kind sigma (Eq.cast eq t) with
    | Prod (name, ty, t) ->
        { name; ty = Eq.(cast (sym eq)) ty; t = Eq.(cast (sym eq)) t }
    | Cast (c, _, _) -> decompose_prod_1 sigma (Eq.(cast (sym eq)) c)
    | _ -> failwith "decompose_prod_1: not an assumption"
*)


  let destRel (type env) sigma (t : env t) : env Rel.t option =
    match EConstr.kind sigma (Eq.cast eq t) with
    | Rel p -> Some (Rel.unsafe_of_concrete p)
    | _ -> None

  let destApp (type env) sigma (t : env t) :
      (env t * env t array) option =
    match EConstr.kind sigma (Eq.cast eq t) with
    | App (c, u) -> Some ((Eq.(cast (sym (eq ^* array eq)))) (c, u))
    | _ -> None

  let destConstruct (type env) sigma (t : env t) :
      (Constructor.exists * EConstr.EInstance.t) option =
    match EConstr.kind sigma (Eq.cast eq t) with
    | Construct (c, u) -> Some (Exists (Eq.(cast (sym Constructor.eq) c)), u)
    | _ -> None

  let decompose_app sigma t =
    match destApp sigma t with
    | Some (f, cl) -> (f, Array.to_list cl)
    | None -> (t, [])

  type ('a, 'b) map = {
      f : 'n . 'n Height.t -> ('a * 'n) t -> ('b * 'n) t;
    }

  let map (type a b n) sigma (f : (a, b) map) :
      n Height.t -> (a * n) t -> (b * n) t =
    let f n term =
      Eq.(cast (Height.eq ^-> eq ^-> eq)) f.f n term in
    Eq.(cast (sym (Height.eq ^-> eq ^-> eq)))
      (EConstr.map_with_binders sigma succ f)

  type 'env subst = {
      f : 'n . 'n Height.t -> ('env * 'n) t -> ('env * 'n) t option
    }

  let rec subst_rec :
  type env n . Evd.evar_map -> env subst -> n Height.t -> (env * n) t ->
    (env * n) t =
  fun sigma f n term ->
    match f.f n term with
    | None ->
        map sigma { f = fun n term -> subst_rec sigma f n term } n term
    | Some term' -> term'

  let subst sigma f =
    let eq = morphism Env.zero_r in
    Eq.(cast (eq ^-> eq)) (subst_rec sigma f Height.zero)

  let mkConstructU constructor einstance =
    Eq.(cast (sym ((Constructor.eq ^* Refl) ^-> eq))) EConstr.mkConstructU
      (constructor, einstance)

  let mkApp (type env) (f : env t) (args : env t array) : env t =
    Eq.(cast (sym ((eq ^* array eq) ^-> eq))) EConstr.mkApp (f, args)

  let equal (type env) (sigma : Evd.evar_map) (a : env t) (b : env t) :
      bool =
    Eq.(cast (sym (eq ^-> eq ^-> Refl))) (EConstr.eq_constr sigma) a b

  let get_sort_of (type env) (env : env Env.t) sigma (t : env t) =
    Retyping.get_sort_of (Eq.cast Env.eq env) sigma (Eq.cast eq t)
(*
  let prod_applist (type env) sigma (t : env t) (list : env t list) : env t =
    Eq.(cast (sym (Refl ^-> eq ^-> Eq.list eq ^-> eq)))
      Termops.prod_applist sigma t list
*)
(*
  let nf_evar (type env) sigma (t : env t) : env t =
    Eq.(cast (sym (eq ^-> eq))) (Evarutil.nf_evar sigma) t
*)

let pr_eterm (env:Environ.env) sigma t = print Eq.(cast (sym Env.eq) env) sigma t
