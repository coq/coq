
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

type typed_vernac =
    TypedVernac : {
      prog : ('in1, 'out1) Prog.t;
      proof : ('in2, 'out2) Proof.t;
      run : pm:'in1 -> proof:'in2 -> 'out1 * 'out2;
    } -> typed_vernac

let run (TypedVernac { prog; proof; run }) ~(pm:Prog.stack) ~(stack:Proof.stack) =
  let (pm, stack), () = (combine_runners (Prog.runner prog) (Proof.runner proof)).run (pm,stack)
      (fun (pm,proof) -> run ~pm ~proof, ())
  in
  stack, pm

let typed_vernac prog proof run = TypedVernac { prog; proof; run }

let vtdefault f = typed_vernac Prog.Ignore Proof.Ignore
    (fun ~pm:() ~proof:() -> let () = f () in (), ())

let vtnoproof f = typed_vernac Prog.Ignore Proof.Reject
    (fun ~pm:() ~proof:() -> let () = f () in (), ())

let vtcloseproof f = typed_vernac Prog.Modify Proof.Close
    (fun ~pm ~proof:lemma -> let pm = f ~lemma ~pm in pm, ())

let vtopenproof f = typed_vernac Prog.Ignore Proof.Open
    (fun ~pm:() ~proof:() -> let proof = f () in (), proof)

let vtmodifyproof f = typed_vernac Prog.Ignore Proof.Modify
    (fun ~pm:() ~proof:pstate -> let pstate = f ~pstate in (), pstate)

let vtreadproofopt f = typed_vernac Prog.Ignore Proof.ReadOpt
    (fun ~pm:() ~proof:pstate -> let () = f ~pstate in (), ())

let vtreadproof f = typed_vernac Prog.Ignore Proof.Read
    (fun ~pm:() ~proof:pstate -> let () = f ~pstate in (), ())

let vtreadprogram f = typed_vernac Prog.Read Proof.Ignore
    (fun ~pm ~proof:() -> let () = f ~pm in (), ())

let vtmodifyprogram f = typed_vernac Prog.Modify Proof.Ignore
    (fun ~pm ~proof:() -> let pm = f ~pm in pm, ())

let vtdeclareprogram f = typed_vernac Prog.Read Proof.Open
    (fun ~pm ~proof:() -> let proof = f ~pm in (), proof)

let vtopenproofprogram f = typed_vernac Prog.Modify Proof.Open
    (fun ~pm ~proof:() -> f ~pm)
