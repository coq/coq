open GADT

  include Monad.State

  type 'a t = ('a, Evd.evar_map) Monad.State.t

  let new_type_evar (env : 'env Env.t)
        ?(filter : Evd.Filter.t option) rigid : ('env ETerm.t * EConstr.ESorts.t) t =
  fun sigma ->
    Eq.cast (Eq.pair Refl (Eq.pair (Eq.sym ETerm.eq) Refl))
      (Evarutil.new_type_evar ?filter (Eq.cast Env.eq env) sigma rigid)

  let new_evar (env : 'env Env.t)
        ?(filter : Evd.Filter.t option)
        ?(candidates : 'env ETerm.t list option)
        (ty : 'env ETerm.t) : 'env ETerm.t t =
  fun sigma ->
    Eq.cast (Eq.pair Refl (Eq.sym ETerm.eq))
      (Evarutil.new_evar (Eq.cast Env.eq env) sigma (Eq.cast ETerm.eq ty)
        ?filter
        ?candidates:(Eq.(cast (option (list ETerm.eq))) candidates))

(*
  let merge_context_set ?loc ?sideff rigid ctx : unit t =
    let open Ops in
    let* sigma = get in
    set (Evd.merge_context_set rigid sigma ctx)
*)
  let set_leq_sort env s s' =
    update (fun sigma -> Evd.set_leq_sort (Eq.cast Env.eq env) sigma s s')

(*
  let set_eq_sort env s s' =
    let open Ops in
    let* sigma = get in
    set (Evd.set_eq_sort (Eq.cast Env.eq env) sigma s s')
*)

  let fresh_inductive_instance env ind =
    fun sigma ->
      Eq.(cast (sym (Env.eq ^-> Refl ^-> InductiveDef.eq ^->
        (Refl ^* (InductiveDef.eq ^* Refl)))))
        Evd.fresh_inductive_instance env sigma ind
