open GADT

  include AbstractJudgment.Make (ETerm)

  let inh_conv_coerce_to (type env) ~program_mode ~resolve_tc ?use_coercions
        ?flags (env : env Env.t) (judgment : env t) (t : env ETerm.t) :
      (env t  * Coercion.coercion_trace option) EvarMapMonad.t =
    Eq.cast (EvarMapMonad.eq (Eq.pair (Eq.sym eq) Refl) Refl) (fun sigma ->
      let sigma, result, trace =
        Coercion.inh_conv_coerce_to ~program_mode ?flags ?use_coercions
          ~resolve_tc (Eq.cast Env.eq env)
          sigma (Eq.cast eq judgment) (Eq.cast ETerm.eq t) in
       (sigma, (result, trace)))

  let inh_conv_coerce_to_tycon (type env) ~program_mode (env : env Env.t)
      (judgment : env t) (tycon : env ETerm.t option) : env t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    match tycon with
    | Some p ->
        let* result, _trace =
          inh_conv_coerce_to ~program_mode ~resolve_tc:true env judgment p
            ~flags:(Evarconv.default_flags_of TransparentState.full) in
        return result
    | None -> return judgment
(*
  let unit (type env) (env : env Env.t) : env t Univ.in_universe_context_set EvarMapMonad.t =
    try
      Eq.(cast (sym (Env.eq ^-> eq ^* Refl))) Evarconv.coq_unit_judge env
    with _ ->
      make (ETerm.mkLambda Context.anonR (ETerm.mkProp ())
          (ETerm.mkLambda Context.anonR (ETerm.mkRel (Rel.zero ()))
            (ETerm.mkRel (Rel.zero ()))))
        (ETerm.mkProd Context.anonR (ETerm.mkProp ())
          (ETerm.mkProd Context.anonR (ETerm.mkRel (Rel.zero ()))
            (ETerm.mkRel (Rel.succ (Rel.zero ()))))), Univ.ContextSet.empty
*)

  let unit_m (type env) (env : env Env.t) : env t EvarMapMonad.t =
    fun sigma ->
    try
      Eq.(cast (sym (Env.eq ^-> Refl ^-> Refl ^* eq))) Evarconv.coq_unit_judge env
        sigma
    with _ ->
      sigma,
      make (ETerm.mkLambda Context.anonR (ETerm.mkProp ())
          (ETerm.mkLambda Context.anonR (ETerm.mkRel (Rel.zero ()))
            (ETerm.mkRel (Rel.zero ()))))
        (ETerm.mkProd Context.anonR (ETerm.mkProp ())
          (ETerm.mkProd Context.anonR (ETerm.mkRel (Rel.zero ()))
            (ETerm.mkRel (Rel.succ (Rel.zero ())))))

(*
  let new_evar env =
    let open EvarMapMonad.Ops in
    let* (ty, _) = EvarMapMonad.new_type_evar env Evd.univ_flexible_alg in
    let* v = EvarMapMonad.new_evar env ty in
    return (make v ty)
*)

  let of_term (type env) (env : env Env.t) sigma (term : env ETerm.t) : env t =
    make term (ETerm.retype_of env sigma term)

(*
  let of_term_via_typing (type env) (env : env Env.t) (term : env ETerm.t) : env t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let* ty = ETerm.get_type_of env term in
    return (make term ty)
*)

  let print env sigma j =
    Pp.(ETerm.print env sigma (uj_val j) ++ spc () ++ str ":" ++ spc () ++
      ETerm.print env sigma (uj_type j))
  [@@ocaml.warning "-32"] (* can be unused *)

  let debug_print sigma j =
    Pp.(ETerm.debug_print sigma (uj_val j) ++ spc () ++ str ":" ++ spc () ++
      ETerm.debug_print sigma (uj_type j))
  [@@ocaml.warning "-32"] (* can be unused *)

  let pr_judgement env sigma j = print Eq.(cast (sym Env.eq) env) sigma j
