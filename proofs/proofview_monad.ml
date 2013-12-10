module NonLogical =
struct
type 'a t = unit -> 'a

type 'a ref = 'a Pervasives.ref

let ret = fun a -> (); fun () -> a

let bind = fun a k -> (); fun () -> k (a ()) ()

let ignore = fun a -> (); fun () -> ignore (a ())

let seq = fun a k -> (); fun () -> a (); k ()

let new_ref = fun a -> (); fun () -> Pervasives.ref a

let set = fun r a -> (); fun () -> Pervasives.(:=) r a

let get = fun r -> (); fun () -> Pervasives.(!) r

let raise = fun e -> (); fun () -> raise (Proof_errors.Exception e)

let catch = fun s h -> (); fun () ->
  try s ()
  with Proof_errors.Exception e ->
    let e = Errors.push e in
    h e ()

let read_line = fun () ->
  try Pervasives.read_line ()
  with e ->
    let e = Errors.push e in
    raise e ()

let print_char = fun c -> (); fun () -> print_char c

let print = fun s -> (); fun () ->
  try Pp.pp s; Pp.pp_flush ()
  with e ->
    let e = Errors.push e in
    raise e ()

let timeout = fun n t -> (); fun () ->
  let timeout_handler _ = Pervasives.raise (Proof_errors.Exception Proof_errors.Timeout) in
  let psh = Sys.signal Sys.sigalrm (Sys.Signal_handle timeout_handler) in
  Pervasives.ignore (Unix.alarm n);
  let restore_timeout () =
    Pervasives.ignore (Unix.alarm 0);
    Sys.set_signal Sys.sigalrm psh
  in
  try
    let res = t () in
    restore_timeout ();
    res
  with
  | e -> restore_timeout (); Pervasives.raise e

let run x =
  try x ()
  with Proof_errors.Exception e ->
    let e = Errors.push e in
    Pervasives.raise e

end


type ('a, 'b) list_view =
| Nil of exn
| Cons of 'a * 'b

type proofview = { initial : (Term.constr*Term.types) list; solution : Evd.evar_map; comb : Goal.goal list }

type logicalState = proofview

type logicalMessageType = bool * (Goal.goal list * Goal.goal list)

type logicalEnvironment = Environ.env

type message = logicalMessageType
type environment = logicalEnvironment
type state = logicalState

module Logical =
struct

type 'a ioT = 'a NonLogical.t

type 'a logicT = { logic : 'r. ('a -> (exn -> 'r ioT) -> 'r ioT) -> (exn -> 'r ioT) -> 'r ioT }

type 'a writerT = { writer : 'r. ('a -> message -> 'r logicT) -> 'r logicT }

type 'a readerT = { reader : 'r. ('a -> 'r writerT) -> environment -> 'r writerT }

type 'a stateT = { state : 'r. ('a -> state -> 'r readerT) -> state -> 'r readerT }

type 'a t = 'a stateT

let empty_message = (true, ([], []))

let ret x = { state = fun k s -> k x s }

let bind m f = { state = fun k s -> m.state (fun x s -> (f x).state k s) s }

let ignore m = { state = fun k s -> m.state (fun _ s -> k () s) s }

let seq m n =
  { state = fun k s -> m.state (fun () s -> n.state k s) s }

let set s =
  { state = fun k _ -> k () s }

let get = { state = fun k s -> k s s }

let current = { state = fun k s -> { reader = fun kr e -> (k e s).reader kr e } }

let join (b1, (l1, r1)) (b2, (l2, r2)) =
  (b1 && b2, (List.append l1 l2, List.append r1 r2))

let put msg =
  { state = fun k s ->
    let m = k () s in
    { reader = fun kr e ->
      let m = m.reader kr e in
      { writer = fun kw -> m.writer
        (fun x nmsg -> kw x (join msg nmsg))
      }
    }
  }

let zero err =
  { state = fun k s ->
    { reader = fun kr e ->
      { writer = fun kw ->
        { logic = fun sk fk -> fk err }
      }
    }
  }

let plus m f =
  { state = fun k s ->
    let m = m.state k s in
    { reader = fun kr e ->
      let m = m.reader kr e in
      { writer = fun kw ->
        let m = m.writer kw in
        { logic = fun sk fk ->
          let plus_fk err = ((((f err).state k s).reader kr e).writer kw).logic sk fk in
          m.logic sk plus_fk
        }
      }
    }
  }

let srun_state x s = { reader = fun kr _ -> kr (x, s) }
let srun_reader x = { writer = fun kw -> kw x empty_message }
let srun_writer x msg = { logic = fun sk fk -> sk (x, msg) fk }

let srun_logic_sk x fk =
  let next err =
    let ans = fk err in { logic = fun sk fk ->
    NonLogical.bind ans (function
    | Nil err -> fk err
    | Cons (y, n) -> sk x (fun err -> (n err).logic sk fk))
  } in
  let ans = Cons (x, next) in
  NonLogical.ret ans

let srun_logic_fk err = NonLogical.ret (Nil err)

let split_next k s kr e kw sk fk = (); function
| Nil _ as x ->
  let m = k x s in
  let m = m.reader kr e in
  let m = m.writer kw in
  m.logic sk fk
| Cons (((x, s), msg), next) ->
  let next err =
    let next = next err in {
    state = fun k s -> {
      reader = fun kr e -> {
        writer = fun kw -> {
          logic = fun sk fk ->
            let sk ((x, s), msg) fk =
              let kw x nmsg = kw x (join msg nmsg) in
              (((k x s).reader kr e).writer kw).logic sk fk
            in
            next.logic sk fk
        }
      }
    }
  } in
  let m = k (Cons (x, next)) s in
  let m = m.reader kr e in
  let m = m.writer (fun x nmsg -> kw x (join msg nmsg)) in
  m.logic sk fk

let split m =
  { state = fun k s ->
    let m = m.state srun_state s in
    { reader = fun kr e ->
      let m = m.reader srun_reader e in
      { writer = fun kw ->
        let m = m.writer srun_writer in
        { logic = fun sk fk ->
          let m = m.logic srun_logic_sk srun_logic_fk in
          NonLogical.bind m (split_next k s kr e kw sk fk)
        }
      }
    }
  }

let lift m =
  { state = fun k s ->
    { reader = fun kr e ->
      { writer = fun kw ->
        { logic = fun sk fk ->
          let lift x = (((k x s).reader kr e).writer kw).logic sk fk in
          NonLogical.bind m lift
        }
      }
    }
  }

let run m e s =
  let m = m.state srun_state s in
  let m = m.reader srun_reader e in
  let m = m.writer srun_writer in
  let run_fk err = NonLogical.raise (Proof_errors.TacticFailure err) in
  let run_sk x _ = NonLogical.ret x in
  m.logic run_sk run_fk

end
