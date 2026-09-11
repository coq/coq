
(** [('a,'b,'x) runner] means that any function taking ['a] and
    returning ['b] and some additional data can be interpreted as a
    function on a state ['x].

    The additional return data ['d] is useful when combining runners.
    We don't need an additional input data as it can just go in the closure.
*)
type ('a,'b,'x) runner = { run : 'd. ?loc:Loc.t -> 'x -> ('a -> 'b * 'd) -> 'x * 'd }


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
    { run = fun ?loc pm f ->
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
    | Modify : { check_late_init : bool } -> (state, state) t
    | Read : (state, unit) t
    | ReadOpt : (state option, unit) t
    | Reject : (unit, unit) t
    | Close : { check_late_init : bool } -> (state, unit) t
    | Open : (unit, state) t

  let use = function
    | None -> CErrors.user_err (Pp.str "Command not supported (No proof-editing in progress).")
    | Some stack -> LStack.pop stack

  let quickfix_missing_proof ~loc _ =
    (* quickfix is purely additive so the loc is 0 characters long, at the beginning of the command. *)
    let loc = { loc with Loc.ep = loc.Loc.bp } in
    [Quickfix.make ~loc Pp.(str "Proof." ++ fnl())]

  let warn_missing_proof = CWarnings.create ~name:"missing-proof-command" ~category:CWarnings.CoreCategories.fragile
      ~quickfix:quickfix_missing_proof
      Pp.(fun default_using ->
          str "This interactive proof is not started by the \"Proof\" command." ++
          (match default_using with
           | None -> mt()
           | Some using ->
             spc() ++ str "Default Proof Using " ++ quote (Ppvernac.pr_using using) ++ str " will be ignored."))

  let check_late_init ?loc p =
    if Option.has_some @@ Declare.Proof.has_late_init p then p
    else begin
      let missing_using =
        if Global.sections_are_opened() then Proof_using.get_default_proof_using() else None
      in
      warn_missing_proof ?loc missing_using;
      Declare.Proof.finish_late_init p Implicit
    end

  let runner (type a b) (ty:(a,b) t) : (a,b,stack) runner =
    { run = fun ?loc stack f ->
      match ty with
      | Ignore -> let (), v = f () in stack, v
      | Modify o ->
        let p, rest = use stack in
        let p = if o.check_late_init then check_late_init ?loc p else p in
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
      | Close o ->
        let p, rest = use stack in
        let p = if o.check_late_init then check_late_init ?loc p else p in
        let (), v = f p in
        rest, v
      | Open ->
        let p, v = f () in
        Some (LStack.push stack p), v
    }

end

module Captured = struct
  type state = CapturedOutput.output list

  type _ t =
    | Ignore : unit t
    | Read : state t
    | Consume : state t

  let runner (type a) (ty:a t) : (a,unit,state) runner =
    { run = fun ?loc captured f ->
      match ty with
      | Ignore -> let (), v = f () in captured, v
      | Read -> let (), v = f captured in captured, v
      | Consume -> let (), v = f captured in [], v
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
    { run = fun ?loc () f ->
      match ty with
      | Ignore -> let (), v = f () in (), v
      | Access -> let (), v = f access in (), v
    }

end

(* lots of messing with tuples in there, can we do better? *)
let combine_runners (type a b x c d y) (r1:(a,b,x) runner) (r2:(c,d,y) runner)
  : (a*c, b*d, x*y) runner
  = { run = fun ?loc (x,y) f ->
      match r1.run ?loc x @@ fun x ->
        match r2.run ?loc y @@ fun y ->
          match f (x,y)
          with ((b, d), o) -> (d, (b, o))
        with (y, (b, o)) -> (b, (y, o))
      with (x, (y, o)) -> ((x, y), o) }

type ('prog,'proof,'captured,'opaque_access) state_gen = {
  prog : 'prog;
  proof : 'proof;
  captured : 'captured;
  opaque_access : 'opaque_access;
}

let tuple { prog; proof; captured; opaque_access } = prog, (proof, (captured, opaque_access))
let untuple (prog, (proof, (captured, opaque_access))) = { prog; proof; captured; opaque_access }

let tuple_explicit (st:Vernacstate.explicit_state) = st.prog, (st.proof, (st.captured_output, ()))
let untuple_explicit (prog, (proof, (captured_output, ()))) : Vernacstate.explicit_state =
  { prog; proof; captured_output }

type no_state = (unit, unit, unit, unit) state_gen
let no_state = { prog = (); proof = (); captured = (); opaque_access = (); }

let ignore_state = {
  prog = Prog.Ignore;
  proof = Proof.Ignore;
  captured = Captured.Ignore;
  opaque_access = OpaqueAccess.Ignore;
}

type 'r typed_vernac_gen =
    TypedVernac : {
      spec : (('inprog, 'outprog) Prog.t,
              ('inproof, 'outproof) Proof.t,
              'incaptured Captured.t,
              'inaccess OpaqueAccess.t) state_gen;
      run : ('inprog, 'inproof, 'incaptured, 'inaccess) state_gen ->
        ('outprog, 'outproof, unit, unit) state_gen * 'r;
    } -> 'r typed_vernac_gen

let map_typed_vernac f (TypedVernac {spec; run}) =
  TypedVernac {spec; run = (fun st -> Util.on_snd f (run st)) }

type typed_vernac = unit typed_vernac_gen

let run ?loc (TypedVernac { spec = { prog; proof; captured; opaque_access }; run })
    (st:Vernacstate.explicit_state) : Vernacstate.explicit_state * _ =
  (* NB: [@] is right associative *)
  let ( @ ) = combine_runners in
  let runner =
    Prog.runner prog
    @ Proof.runner proof
    @ Captured.runner captured
    @ OpaqueAccess.runner opaque_access
  in
  let st, v = runner.run ?loc (tuple_explicit st) @@ fun st ->
    let st, v = run @@ untuple st in tuple st, v
  in
  untuple_explicit st, v

let typed_vernac_gen spec run = TypedVernac { spec; run }

let typed_vernac spec run = TypedVernac { spec; run = (fun st -> run st, () ) }

let vtdefault f = typed_vernac ignore_state
    (fun (_:no_state) -> let () = f () in no_state)

let vtnoproof f = typed_vernac { ignore_state with proof = Reject }
    (fun (_:no_state) -> let () = f () in no_state)

let vtcloseproof ?(check_late_init=true) f =
  typed_vernac { ignore_state with prog = Modify; proof = Close { check_late_init } }
    (fun {prog; proof} -> let prog = f ~lemma:proof ~pm:prog in { no_state with prog })

let vtopenproof f = typed_vernac { ignore_state with proof = Open }
    (fun (_:no_state) -> let proof = f () in { no_state with proof })

let vtmodifyproof ?(check_late_init=true) f =
  typed_vernac { ignore_state with proof = Modify { check_late_init } }
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

let vtreadcapturedoutput f = typed_vernac { ignore_state with captured = Read }
    (fun {captured} -> let () = f ~captured in no_state)

let vtconsumecapturedoutput f = typed_vernac { ignore_state with captured = Consume }
    (fun {captured} -> let () = f ~captured in no_state)
