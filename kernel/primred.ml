(* Reduction of native operators *)
open Names
open CPrimitives
open Retroknowledge
open Environ
open CErrors

let add_retroknowledge env action =
  match action with
  | Register_type(PT_int63,c) ->
    let retro = env.retroknowledge in
    let retro =
      match retro.retro_int63 with
      | None -> { retro with retro_int63 = Some c }
      | Some c' -> assert (Constant.equal c c'); retro in
    set_retroknowledge env retro
  | Register_ind(pit,ind) ->
    let retro = env.retroknowledge in
    let retro =
      match pit with
      | PIT_bool ->
        let r =
          match retro.retro_bool with
          | None -> ((ind,1), (ind,2))
          | Some (((ind',_),_) as t) -> assert (eq_ind ind ind'); t in
        { retro with retro_bool = Some r }
      | PIT_carry ->
        let r =
          match retro.retro_carry with
          | None -> ((ind,1), (ind,2))
          | Some (((ind',_),_) as t) -> assert (eq_ind ind ind'); t in
        { retro with retro_carry = Some r }
      | PIT_pair ->
        let r =
          match retro.retro_pair with
          | None -> (ind,1)
          | Some ((ind',_) as t) -> assert (eq_ind ind ind'); t in
        { retro with retro_pair = Some r }
      | PIT_cmp ->
        let r =
          match retro.retro_cmp with
          | None -> ((ind,1), (ind,2), (ind,3))
          | Some (((ind',_),_,_) as t) -> assert (eq_ind ind ind'); t in
        { retro with retro_cmp = Some r }
    in
    set_retroknowledge env retro
  | Register_inline(c) ->
    let (cb,r) = lookup_constant_key c env in
    let cb = {cb with Declarations.const_inline_code = true} in
    add_constant_key c cb !(fst r) env

let get_int_type env =
  match env.retroknowledge.retro_int63 with
  | Some c -> c
  | None -> anomaly Pp.(str"Reduction of primitive: int63 not registered")

let get_bool_constructors env =
  match env.retroknowledge.retro_bool with
  | Some r -> r
  | None -> anomaly Pp.(str"Reduction of primitive: bool not registered")

let get_carry_constructors env =
  match env.retroknowledge.retro_carry with
  | Some r -> r
  | None -> anomaly Pp.(str"Reduction of primitive: carry not registered")

let get_pair_constructor env =
  match env.retroknowledge.retro_pair with
  | Some c  -> c
  | None -> anomaly Pp.(str"Reduction of primitive: pair not registered")

let get_cmp_constructors env =
  match env.retroknowledge.retro_cmp with
  | Some r -> r
  | None -> anomaly Pp.(str"Reduction of primitive: cmp not registered")

exception NativeDestKO

module type RedNativeEntries =
  sig
    type elem
    type args
    type evd (* will be unit in kernel, evar_map outside *)

    val get : args -> int -> elem
    val get_int : evd -> elem -> Uint63.t
    val mkInt : env -> Uint63.t -> elem
    val mkBool : env -> bool -> elem
    val mkCarry : env -> bool -> elem -> elem (* true if carry *)
    val mkIntPair : env -> elem -> elem -> elem
    val mkLt : env -> elem
    val mkEq : env -> elem
    val mkGt : env -> elem

  end

module type RedNative =
 sig
   type elem
   type args
   type evd
   val red_prim : env -> evd -> CPrimitives.t -> args -> elem option
 end

module RedNative (E:RedNativeEntries) :
  RedNative with type elem = E.elem
  with type args = E.args
  with type evd = E.evd =
struct
  type elem = E.elem
  type args = E.args
  type evd = E.evd

  let get_int evd args i = E.get_int evd (E.get args i)

  let get_int1 evd args = get_int evd args 0

  let get_int2 evd args = get_int evd args 0, get_int evd args 1

  let get_int3 evd args =
    get_int evd args 0, get_int evd args 1, get_int evd args 2

  let red_prim_aux env evd op args =
    let open CPrimitives in
    match op with
    | Int63head0 ->
      let i = get_int1 evd args in E.mkInt env (Uint63.head0 i)
    | Int63tail0 ->
      let i = get_int1 evd args in E.mkInt env (Uint63.tail0 i)
    | Int63add ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.add i1 i2)
    | Int63sub ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.sub i1 i2)
    | Int63mul ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.mul i1 i2)
    | Int63div ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.div i1 i2)
    | Int63mod ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.rem i1 i2)
    | Int63lsr ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.l_sr i1 i2)
    | Int63lsl ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.l_sl i1 i2)
    | Int63land ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.l_and i1 i2)
    | Int63lor ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.l_or i1 i2)
    | Int63lxor ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.l_xor i1 i2)
    | Int63addc ->
      let i1, i2 = get_int2 evd args in
      let s = Uint63.add i1 i2 in
      E.mkCarry env (Uint63.lt s i1) (E.mkInt env s)
    | Int63subc ->
      let i1, i2 = get_int2 evd args in
      let s = Uint63.sub i1 i2 in
      E.mkCarry env (Uint63.lt i1 i2) (E.mkInt env s)
    | Int63addCarryC  ->
      let i1, i2 = get_int2 evd args in
      let s = Uint63.add (Uint63.add i1 i2) (Uint63.of_int 1) in
      E.mkCarry env (Uint63.le s i1) (E.mkInt env s)
    | Int63subCarryC  ->
      let i1, i2 = get_int2 evd args in
      let s = Uint63.sub (Uint63.sub i1 i2) (Uint63.of_int 1) in
      E.mkCarry env (Uint63.le i1 i2) (E.mkInt env s)
    | Int63mulc ->
      let i1, i2 = get_int2 evd args in
      let (h, l) = Uint63.mulc i1 i2 in
      E.mkIntPair env (E.mkInt env h) (E.mkInt env l)
    | Int63diveucl ->
      let i1, i2 = get_int2 evd args in
      let q,r = Uint63.div i1 i2, Uint63.rem i1 i2 in
      E.mkIntPair env (E.mkInt env q) (E.mkInt env r)
    | Int63div21 ->
      let i1, i2, i3 = get_int3 evd args in
      let q,r = Uint63.div21 i1 i2 i3 in
      E.mkIntPair env (E.mkInt env q) (E.mkInt env r)
    | Int63addMulDiv ->
      let p, i, j = get_int3 evd args in
      E.mkInt env
        (Uint63.l_or
           (Uint63.l_sl i p)
           (Uint63.l_sr j (Uint63.sub (Uint63.of_int Uint63.uint_size) p)))
    | Int63eq ->
      let i1, i2 = get_int2 evd args in
      E.mkBool env (Uint63.equal i1 i2)
    | Int63lt ->
      let i1, i2 = get_int2 evd args in
      E.mkBool env (Uint63.lt i1 i2)
    | Int63le ->
      let i1, i2 = get_int2 evd args in
      E.mkBool env (Uint63.le i1 i2)
    | Int63compare ->
      let i1, i2 = get_int2 evd args in
      begin match Uint63.compare i1 i2 with
        | x when x < 0 ->  E.mkLt env
        | 0 -> E.mkEq env
        | _ -> E.mkGt env
      end

  let red_prim env evd p args =
    try
      let r =
        red_prim_aux env evd p args
      in Some r
    with NativeDestKO -> None

end
