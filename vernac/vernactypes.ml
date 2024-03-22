
(** [('a,'b,'x) runner] means that any function taking ['a] and
    returning ['b] and some additional data can be interpreted as a
    function on a state ['x].

    The additional return data ['d] is useful when combining runners.
    We don't need an additional input data as it can just go in the closure.
*)
type ('a,'b,'x) runner = { run : 'd. 'x -> ('a -> 'b * 'd) -> 'x * 'd }


module Prog = struct

  type state = Declare.OblState.t
  type stack = state NeList.t

  type (_,_) t =
    | Ignore : (unit, unit) t
    | Modify : (state, state) t
    | Read : (state, unit) t
    | Push : (unit, unit) t
    | Pop : (state, unit) t

  let runner (type a b) (ty:(a,b) t) : (a,b,stack) runner =
    { run = fun pm f ->
      match ty with
      | Ignore -> let (), v = f () in pm, v
      | Modify ->
        let st, pm = NeList.repr pm in
        let st, v = f st in
        NeList.of_repr (st,pm), v
      | Read ->
        let (), v = f (NeList.head pm) in
        pm, v
      | Push ->
        let (), v = f () in
        NeList.push Declare.OblState.empty (Some pm), v
      | Pop ->
        let st, pm = NeList.repr pm in
        assert (not (CList.is_empty pm));
        let (), v = f st in
        NeList.of_list pm, v
    }

end

module Proof = struct
  module LStack = Vernacstate.LemmaStack

  type state = Declare.Proof.t
  type stack = LStack.t option

  type (_,_) t =
    | Ignore : (unit, unit) t
    | Modify : (state, state) t
    | Read : (state, unit) t
    | ReadOpt : (state option, unit) t
    | Reject : (unit, unit) t
    | Close : (state, unit) t
    | Open : (unit, state) t

  let use = function
    | None -> CErrors.user_err (Pp.str "Command not supported (No proof-editing in progress).")
    | Some stack -> LStack.pop stack

  let runner (type a b) (ty:(a,b) t) : (a,b,stack) runner =
    { run = fun stack f ->
      match ty with
      | Ignore -> let (), v = f () in stack, v
      | Modify ->
        let p, rest = use stack in
        let p, v = f p in
        Some (LStack.push rest p), v
      | Read ->
        let p, _ = use stack in
        let (), v = f p in
        stack, v
      | ReadOpt ->
        let p = Option.map LStack.get_top stack in
        let (), v = f p in
        stack, v
      | Reject ->
        let () = if Option.has_some stack
          then CErrors.user_err (Pp.str "Command not supported (Open proofs remain).")
        in
        let (), v = f () in
        stack, v
      | Close ->
        let p, rest = use stack in
        let (), v = f p in
        rest, v
      | Open ->
        let p, v = f () in
        Some (LStack.push stack p), v
    }

end

module OpaqueAccess = struct

  (* Modification of opaque tables (by Require registering foreign
     tables and Qed/abstract/etc adding entries to the local table)
     is currently not tracked by vernactypes.
  *)
  type _ t =
    | Ignore : unit t
    | Access : Global.indirect_accessor t

  let access = Library.indirect_accessor[@@warning "-3"]

  let runner (type a) (ty:a t) : (a,unit,unit) runner =
    { run = fun () f ->
      match ty with
      | Ignore -> let (), v = f () in (), v
      | Access -> let (), v = f access in (), v
    }

end

(* lots of messing with tuples in there, can we do better? *)
let combine_runners (type a b x c d y) (r1:(a,b,x) runner) (r2:(c,d,y) runner)
  : (a*c, b*d, x*y) runner
  = { run = fun (x,y) f ->
      match r1.run x @@ fun x ->
        match r2.run y @@ fun y ->
          match f (x,y)
          with ((b, d), o) -> (d, (b, o))
        with (y, (b, o)) -> (b, (y, o))
      with (x, (y, o)) -> ((x, y), o) }

type ('prog,'proof,'opaque_access) state_gen = {
  prog : 'prog;
  proof : 'proof;
  opaque_access : 'opaque_access;
}

let tuple { prog; proof; opaque_access } = (prog, proof), opaque_access
let untuple ((prog, proof), opaque_access) = { prog; proof; opaque_access }

type no_state = (unit, unit, unit) state_gen
let no_state = { prog = (); proof = (); opaque_access = (); }

let ignore_state = { prog = Prog.Ignore; proof = Proof.Ignore; opaque_access = OpaqueAccess.Ignore }

type 'r typed_vernac_gen =
    TypedVernac : {
      spec : (('inprog, 'outprog) Prog.t,
              ('inproof, 'outproof) Proof.t,
              'inaccess OpaqueAccess.t) state_gen;
      run : ('inprog, 'inproof, 'inaccess) state_gen -> ('outprog, 'outproof, unit) state_gen * 'r;
    } -> 'r typed_vernac_gen

let map_typed_vernac f (TypedVernac {spec; run}) =
  TypedVernac {spec; run = (fun st -> Util.on_snd f (run st)) }

type typed_vernac = unit typed_vernac_gen

type full_state = (Prog.stack,Vernacstate.LemmaStack.t option,unit) state_gen

let run (TypedVernac { spec = { prog; proof; opaque_access }; run }) (st:full_state) : full_state * _ =
  let ( * ) = combine_runners in
  let runner = Prog.runner prog * Proof.runner proof * OpaqueAccess.runner opaque_access in
  let st, v = runner.run (tuple st) @@ fun st ->
    let st, v= run @@ untuple st in tuple st, v
  in
  untuple st, v

let typed_vernac_gen spec run = TypedVernac { spec; run }

let typed_vernac spec run = TypedVernac { spec; run = (fun st -> run st, () ) }

let vtdefault f = typed_vernac ignore_state
    (fun (_:no_state) -> let () = f () in no_state)

let vtnoproof f = typed_vernac { ignore_state with proof = Reject }
    (fun (_:no_state) -> let () = f () in no_state)

let vtcloseproof f = typed_vernac { ignore_state with prog = Modify; proof = Close }
    (fun {prog; proof} -> let prog = f ~lemma:proof ~pm:prog in { no_state with prog })

let vtopenproof f = typed_vernac { ignore_state with proof = Open }
    (fun (_:no_state) -> let proof = f () in { no_state with proof })

let vtmodifyproof f = typed_vernac { ignore_state with proof = Modify }
    (fun {proof} -> let proof = f ~pstate:proof in { no_state with proof })

let vtreadproofopt f = typed_vernac { ignore_state with proof = ReadOpt }
    (fun {proof} -> let () = f ~pstate:proof in no_state)

let vtreadproof f = typed_vernac { ignore_state with proof = Read }
    (fun {proof} -> let () = f ~pstate:proof in no_state)

let vtreadprogram f = typed_vernac { ignore_state with prog = Read }
    (fun {prog} -> let () = f ~pm:prog in no_state)

let vtmodifyprogram f = typed_vernac { ignore_state with prog = Modify }
    (fun {prog} -> let prog = f ~pm:prog in { no_state with prog })

let vtdeclareprogram f = typed_vernac { ignore_state with prog = Read; proof = Open }
    (fun {prog} -> let proof = f ~pm:prog in { no_state with proof })

let vtopenproofprogram f = typed_vernac { ignore_state with prog = Modify; proof = Open }
    (fun {prog} -> let prog, proof = f ~pm:prog in { no_state with prog; proof; })

let vtopaqueaccess f = typed_vernac { ignore_state with opaque_access = Access }
    (fun {opaque_access} -> let () = f ~opaque_access in no_state)
