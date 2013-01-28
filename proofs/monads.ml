module type Type = sig
  type t
end

module type S = sig
  type +'a t

  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val seq : unit t -> 'a t -> 'a t
  val ignore : 'a t -> unit t
(* spiwack: these will suffice for now, if we would use monads more
   globally, then I would add map/join/List.map and such functions,
   plus default implementations *)
end

module type State = sig
  type s (* type of the state *)
  include S

  val set : s -> unit t
  val get : s t
end

module Id : S with type 'a t = 'a = struct
  type 'a t = 'a

  let return x = x
  let bind x k = k x
  let ignore x = Pervasives.ignore x
  let seq () x = x
end

(* State monad transformer, adapted from Haskell's StateT *)
module State (X:Type) (T:S) : sig
  (* spiwack: it is not essential that both ['a result] and ['a t] be
     private (or either, for that matter). I just hope it will help
     catch more programming errors. *)
  type +'a result = private { result : 'a ; state : X.t }
  include State with type s = X.t and type +'a t = private X.t -> 'a result T.t
  (* a function version of the coercion from the private type ['a t].*)
  val run : 'a t -> s -> 'a result T.t
  val lift : 'a T.t -> 'a t
end = struct
  type s = X.t
  type 'a result = { result : 'a ; state : s }
  type 'a t = s -> 'a result T.t

  let run x = x
  (*spiwack: convenience notation, waiting for ocaml 3.12 *)
  let (>>=) = T.bind
  let return x s = T.return { result=x ; state=s }
  let bind x k s =
    x s >>= fun { result=a ; state=s } ->
    k a s
  let ignore x s =
    x s >>= fun x' ->
    T.return { x' with result=() }
  let seq x t s =
    (x s) >>= fun x' ->
    t x'.state
  let lift x s =
    x >>= fun a ->
    T.return { result=a ; state=s }

  let set s _ =
    T.return { result=() ; state=s }
  let get s =
    T.return { result=s ; state=s }
end

(* Double-continuation backtracking monads are reasonable folklore for
   "search" implementations (including Tac interactive prover's
   tactics). Yet it's quite hard to wrap your head around these.  I
   recommand reading a few times the "Backtracking, Interleaving, and
   Terminating Monad Transformers" paper by O. Kiselyov, C. Chen,
   D. Fridman.  The peculiar shape of the monadic type is reminiscent
   of that of the continuation monad transformer.

   The paper also contains the rational for the [split] abstraction.

   An explanation of how to derive such a monad from mathematical
   principle can be found in "Kan Extensions for Program Optimisation" by
   Ralf Hinze. *)
module type Logic = sig
  include S

  (* [zero] is usually argument free, but Coq likes to explain errors,
     hence error messages should be carried around. *)
  val zero : exn -> 'a t
  val plus : 'a t -> 'a t -> 'a t
(** Writing (+) for plus and (>>=) for bind, we shall require that

    zero+x = x

    x+zero = x

    (x+y)>>=k = (x>>=k)+(y>>=k) *)

  (** [split x] runs [x] until it either fails with [zero e] or finds
      a result [a].  In the former case it returns [Inr e], otherwise
      it returns [Inl (a,y)] where [y] can be run to get more results
      from [x]. It is a variant of prolog's cut. *)
  val split : 'a t -> ('a * 'a t , exn ) Util.union t
end
(* The [T] argument represents the "global" effect: it is not
   backtracked when backtracking occurs at a [plus]. *)
(* spiwack: hence, [T] will not be instanciated with a state monad
   representing the proofs, we will use a surrounding state transformer
   to that effect. In fact at the time I'm writing this comment, I have
   no immediate use for [T]. We might, however, consider instantiating it
   with a "writer" monad around [Pp] to implement [idtac "msg"] for
   instance. *)
module Logic (T:S) : sig
  include Logic

  (** [run x] raises [e] if [x] is [zero e]. *)
  val run : 'a t -> 'a T.t

  val lift : 'a T.t -> 'a t
end = struct
(* spiwack: the implementation is an adaptation of the aforementionned
   "Backtracking, Interleaving, and Terminating Monad Transformers"
   paper *)
  (* spiwack: [fk] stands for failure continuation, and [sk] for success
     continuation. *)
  type +'r fk = exn -> 'r
  type (-'a,'r) sk = 'a -> 'r fk -> 'r
  type 'a t = { go : 'r. ('a,'r T.t) sk -> 'r T.t fk -> 'r T.t }

  let return x = { go = fun sk fk ->
    sk x fk
                 }
  let bind x k = { go = fun sk fk ->
    x.go (fun a fk -> (k a).go sk fk) fk
                 }
  let ignore x = { go = fun sk fk ->
    x.go (fun _ fk -> sk () fk) fk
                 }
  let seq x t = { go = fun sk fk ->
    x.go (fun () fk -> t.go sk fk) fk
                }

  let zero e = { go = fun _ fk -> fk e }
  (* [plus x y] ignores any error raised by [x]. *)
  let plus x y = { go = fun sk fk ->
    x.go sk (fun _ -> y.go sk fk)
                 }

  let lift x = { go = fun sk fk ->
    T.bind x (fun a -> sk a fk)
               }

  let run x =
    let sk a _ = T.return a in
    let fk e = raise e in
    x.go sk fk

  (* For [reflect] and [split] see the "Backtracking, Interleaving,
     and Terminating Monad Transformers" paper *)
  let reflect : ('a*'a t , exn) Util.union -> 'a t = function
    | Util.Inr e -> zero e
    | Util.Inl (a,x) -> plus (return a) x

  let split x =
    (* spiwack: I cannot be sure right now, but [anomaly] shouldn't be
       reachable. If it is reachable there may be some redesign to be
       done around success continuations. *)
    let anomaly = Errors.make_anomaly ~label:"Monads.Logic(T).split"
      (Pp.str "[fk] should ignore this error")
    in
    let fk e = T.return (Util.Inr e) in
    let sk a fk = T.return (Util.Inl (a,bind (lift (fk anomaly)) reflect)) in
    lift (x.go sk fk)
end


(* [State(X)(T:Logic)] can be lifted to [Logic] by backtracking on state on [plus].*)
module StateLogic(X:Type)(T:Logic) : sig
  (* spiwack: some duplication from interfaces as we need ocaml 3.12
     to substitute inside signatures. *)
  type s = X.t
  type +'a result = private { result : 'a ; state : s }
  include Logic with type +'a t = private X.t -> 'a result T.t

  val set : s -> unit t
  val get : s t

  val run : 'a t -> s -> 'a result T.t
end = struct

  module S = State(X)(T)
  include S

  let zero e = lift (T.zero e)
  let plus x y =
    (* spiwack: convenience notation, waiting for ocaml 3.12 *)
    let (>>=) = bind in
    let (>>) = seq in
    get >>= fun initial ->
    lift begin
      (T.plus (run x initial) (run y initial)) 
    end >>= fun { result = a ; state = final } ->
    set final >>
    return a
  (* spiwack: the definition of [plus] is essentially [plus x y = fun s
     -> T.plus (run x s) (run y s)]. But the [private] annotation
     prevents us from writing that. Maybe I should remove [private]
     around [+'a t] (it would be unnecessary to remove that of ['a
     result]) after all. I'll leave it like that for now. *)

  let split x =
    (* spiwack: convenience notation, waiting for ocaml 3.12 *)
    let (>>=) = bind in
    let (>>) = seq in
    get >>= fun initial ->
    lift (T.split (run x initial)) >>= function
      | Util.Inr _ as e -> return e
      | Util.Inl (a,y) ->
          let y' =
            lift y >>= fun b ->
            set b.state >>
            return b.result
          in
          set a.state >>
          return (Util.Inl(a.result,y'))
end


