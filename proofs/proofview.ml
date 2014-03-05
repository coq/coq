(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* The proofview datastructure is a pure datastructure underlying the notion
   of proof (namely, a proof is a proofview which can evolve and has safety
   mechanisms attached).
   The general idea of the structure is that it is composed of a chemical
   solution: an unstructured bag of stuff which has some relations with 
   one another, which represents the various subnodes of the proof. Together
   with a comb: a datastructure that gives some order to some of these nodes, 
   namely the (focused) open goals. 
   The natural candidate for the solution is an {!Evd.evar_map}, that is
   a calculus of evars. The comb is then a list of goals (evars wrapped 
   with some extra information, like possible name anotations).
   There is also need of a list of the evars which initialised the proofview
   to be able to return information about the proofview. *)

open Util

(* Type of proofviews. *)
type proofview = Proofview_monad.proofview
open Proofview_monad

let proofview p =
  p.comb , p.solution

(* Initialises a proofview, the argument is a list of environement, 
   conclusion types, and optional names, creating that many initial goals. *)
let init sigma =
  let rec aux = function
  | [] ->  { initial = [] ; 
	     solution = sigma ;
             comb = [];
	   }
  | (env,typ)::l -> let { initial = ret ; solution = sol ; comb = comb } =
                           aux l
                         in
                         let ( new_defs , econstr ) = 
			   Evarutil.new_evar sol env typ
			 in
			 let (e,_) = Term.destEvar econstr in
			 let gl = Goal.build e in
			 { initial = (econstr,typ)::ret;
			   solution = new_defs ;
                           comb = gl::comb; }
  in
  fun l -> let v = aux l in
    (* Marks all the goal unresolvable for typeclasses. *)
    { v with solution = Typeclasses.mark_unresolvables v.solution }

type telescope =
  | TNil
  | TCons of Environ.env*Term.types*(Term.constr -> telescope)

let dependent_init =
  let rec aux sigma = function
  | TNil -> { initial = [] ;
	     solution = sigma ;
             comb = [];
	   }
  | TCons (env,typ,t) -> let ( sigma , econstr ) =
			  Evarutil.new_evar sigma env typ
			in
                        let { initial = ret ; solution = sol ; comb = comb } =
                          aux sigma (t econstr)
                        in
			let (e,_) = Term.destEvar econstr in
			let gl = Goal.build e in
			{ initial = (econstr,typ)::ret;
			   solution = sol ;
                           comb = gl::comb; }
  in
  fun sigma t -> let v = aux sigma t in
    (* Marks all the goal unresolvable for typeclasses. *)
    { v with solution = Typeclasses.mark_unresolvables v.solution }

let initial_goals { initial } = initial

(* Returns whether this proofview is finished or not. That is,
   if it has empty subgoals in the comb. There could still be unsolved
   subgoaled, but they would then be out of the view, focused out. *)
let finished = function
  | {comb = []} -> true
  | _  -> false

(* Returns the current value of the proofview partial proofs. *)
let return { solution=defs } = defs

let return_constr { solution = defs } c = Evarutil.nf_evar defs c

let partial_proof pv =
  List.map (return_constr pv) (List.map fst (initial_goals pv))

let emit_side_effects eff x =
  { x with solution = Evd.emit_side_effects eff x.solution }

(* spiwack: this function should probably go in the Util section,
    but I'd rather have Util (or a separate module for lists)
    raise proper exceptions before *)
(* [IndexOutOfRange] occurs in case of malformed indices
   with respect to list lengths. *)
exception IndexOutOfRange
(* no handler: should not be allowed to reach toplevel *)

(* [list_goto i l] returns a pair of lists [c,t] where
   [c] has length [i] and is the reversed of the [i] first
   elements of [l], and [t] is the rest of the list.
   The idea is to navigate through the list, [c] is then
   seen as the context of the current position. 
   Raises [IndexOutOfRange] if [i > length l]*)
let list_goto = 
  let rec aux acc index = function
    | l when Int.equal index 0-> (acc,l)
    | [] -> raise IndexOutOfRange
    | a::q -> aux (a::acc) (index-1) q
  in
  fun i l ->
    if i < 0 then
      raise IndexOutOfRange
    else
      aux [] i l

(* Type of the object which allow to unfocus a view.*)
(* First component is a reverse list of what comes before
   and second component is what goes after (in the expected
   order) *)
type focus_context = Goal.goal list * Goal.goal list

let focus_context f = f

(* This (internal) function extracts a sublist between two indices, and
   returns this sublist together with its context:
   if it returns [(a,(b,c))] then [a] is the sublist and (rev b)@a@c is the
   original list.
   The focused list has lenght [j-i-1] and contains the goals from
   number [i] to number [j] (both included) the first goal of the list
   being numbered [1].
   [focus_sublist i j l] raises [IndexOutOfRange] if
   [i > length l], or [j > length l] or [ j < i ].  *)
let focus_sublist i j l =
  let (left,sub_right) = list_goto (i-1) l in
  let (sub, right) = 
    try List.chop (j-i+1) sub_right
    with Failure _ -> raise IndexOutOfRange
  in
  (sub, (left,right))

(* Inverse operation to the previous one. *)
let unfocus_sublist (left,right) s =
  List.rev_append left (s@right)


(* [focus i j] focuses a proofview on the goals from index [i] to index [j] 
   (inclusive). (i.e. goals number [i] to [j] become the only goals of the
   returned proofview). The first goal has index 1.
   It returns the focus proof, and a context for the focus trace. *)
let focus i j sp =
  let (new_comb, context) = focus_sublist i j sp.comb in
  ( { sp with comb = new_comb } , context )

(* Unfocuses a proofview with respect to a context. *)
let undefined defs l =
  Option.List.flatten (List.map (Goal.advance defs) l)
let unfocus c sp =
  { sp with comb = undefined sp.solution (unfocus_sublist c sp.comb) }


(* The tactic monad:
   - Tactics are objects which apply a transformation to all
     the subgoals of the current view at the same time. By opposition
     to the old vision of applying it to a single goal. It allows 
     tactics such as [shelve_unifiable] or tactics to reorder
     the focused goals (not done yet).
     (* spiwack: the ordering of goals, though, is actually rather
        brittle. It would be much more interesting to find a more
        robust way to adress goals, I have no idea at this time 
        though*) 
     or global automation tactic for dependent subgoals (instantiating
     an evar has influences on the other goals of the proof in progress,
     not being able to take that into account causes the current eauto
     tactic to fail on some instances where it could succeed).
     Another benefit is that it is possible to write tactics that can
     be executed even if there are no focused goals.
   - Tactics form a monad ['a tactic], in a sense a tactic can be 
     seens as a function (without argument) which returns a value
     of type 'a and modifies the environement (in our case: the view).
     Tactics of course have arguments, but these are given at the 
     meta-level as OCaml functions.
     Most tactics in the sense we are used to return [()], that is
     no really interesting values. But some might pass information 
     around. 
     (* spiwack: as far as I'm aware this doesn't really relate to
        F. Kirchner and C. Muñoz.
     *)
     The tactics seen in Coq's Ltac are (for now at least) only 
     [unit tactic], the return values are kept for the OCaml toolkit.
     The operation or the monad are [Proofview.tclUNIT] (which is the 
     "return" of the tactic monad) [Proofview.tclBIND] (which is
     the "bind") and [Proofview.tclTHEN] (which is a specialized
     bind on unit-returning tactics).
*)

(* type of tactics:

   tactics can
   - access the environment,
   - report unsafe status, shelved goals and given up goals
   - access and change the current [proofview]
   - backtrack on previous changes of the proofview *)
module Proof = Proofview_monad.Logical
type +'a tactic = 'a Proof.t

(* Applies a tactic to the current proofview. *)
let apply env t sp =
  let (((next_r,next_state),status)) = Proofview_monad.NonLogical.run (Proof.run t env sp) in
  next_r , next_state , status

(*** tacticals ***)


let catchable_exception = function
  | Proof_errors.Exception _ -> false
  | e -> Errors.noncritical e


(* Unit of the tactic monad *)
let tclUNIT a = (Proof.ret a:'a Proof.t)

(* Bind operation of the tactic monad *)
let tclBIND = Proof.bind

(* Interpretes the ";" (semicolon) of Ltac.
   As a monadic operation, it's a specialized "bind"
   on unit-returning tactic (meaning "there is no value to bind") *)
let tclTHEN = Proof.seq

(* [tclIGNORE t] has the same operational content as [t],
   but drops the value at the end. *)
let tclIGNORE = Proof.ignore

(* [tclOR t1 t2 = t1] as long as [t1] succeeds. Whenever the successes
   of [t1] have been depleted and it failed with [e], then it behaves
   as [t2 e].  No interleaving at this point. *)
let tclOR t1 t2 =
  Proof.plus t1 t2

(* [tclZERO e] always fails with error message [e]*)
let tclZERO = Proof.zero

(* [tclORELSE t1 t2] behaves like [t1] if [t1] succeeds at least once
   or [t2] if [t1] fails. *)
let tclORELSE t1 t2 =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Proof.split t1 >>= function
    | Nil e -> t2 e
    | Cons (a,t1') -> Proof.plus (Proof.ret a) t1'

(* [tclIFCATCH a s f] is a generalisation of [tclORELSE]: if [a]
   succeeds at least once then it behaves as [tclBIND a s] otherwise, if [a]
   fails with [e], then it behaves as [f e]. *)
let tclIFCATCH a s f =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Proof.split a >>= function
    | Nil e -> f e
    | Cons (x,a') -> Proof.plus (s x) (fun e -> (a' e) >>= fun x' -> (s x'))

(* [tclONCE t] fails if [t] fails, otherwise it has exactly one
   success. *)
let tclONCE t =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Proof.split t >>= function
    | Nil e -> tclZERO e
    | Cons (x,_) -> tclUNIT x

exception MoreThanOneSuccess
let _ = Errors.register_handler begin function
  | MoreThanOneSuccess -> Errors.error "This tactic has more than one success."
  | _ -> raise Errors.Unhandled
end

(* [tclONCE e t] succeeds as [t] if [t] has exactly one
   success. Otherwise it fails.  It may behave differently than [t] as
   there may be extra non-logical effects used to discover that [t]
   does not have a second success. Moreover the second success may be
   conditional on the error recieved: [e] is used. *)
let tclEXACTLY_ONCE e t =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Proof.split t >>= function
    | Nil e -> tclZERO e
    | Cons (x,k) ->
        Proof.split (k e) >>= function
          | Nil _ -> tclUNIT x
          | _ -> tclZERO MoreThanOneSuccess


(* Focuses a tactic at a range of subgoals, found by their indices. *)
exception NoSuchGoals
let _ = Errors.register_handler begin function
  | NoSuchGoals -> Errors.error "No such goals."
  | _ -> raise Errors.Unhandled
end
let tclFOCUS_gen nosuchgoal i j t =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  let (>>) = Proof.seq in
  Proof.get >>= fun initial ->
  try
    let (focused,context) = focus i j initial in
    Proof.set focused >>
    t >>= fun result ->
    Proof.get >>= fun next ->
    Proof.set (unfocus context next) >>
    Proof.ret result
  with IndexOutOfRange -> nosuchgoal

let tclFOCUS i j t = tclFOCUS_gen (tclZERO NoSuchGoals) i j t
let tclTRYFOCUS i j t = tclFOCUS_gen (tclUNIT ()) i j t


(* Dispatch tacticals are used to apply a different tactic to each goal under
   consideration. They come in two flavours:
   [tclDISPATCH] takes a list of [unit tactic]-s and build a [unit tactic].
   [tclDISPATCHL] takes a list of ['a tactic] and returns an ['a list tactic].

   They both work by applying each of the tactic to the corresponding
   goal (starting with the first goal). In the case of [tclDISPATCHL],
   the tactic returns a list of the same size as the argument list (of
   tactics), each element being the result of the tactic executed in
   the corresponding goal. *)
exception SizeMismatch
let _ = Errors.register_handler begin function
  | SizeMismatch -> Errors.error "Incorrect number of goals."
  | _ -> raise Errors.Unhandled
end

(* A monadic list iteration function *)
(* spiwack: may be moved to a generic libray, or maybe as extracted
   code for extra efficiency? *)
(* val list_iter : 'a list -> 'b -> ('a -> 'b -> 'b tactic) -> 'b tactic *)
let rec list_iter l s i =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = tclBIND in
  match l with
  | [] -> tclUNIT s
  | [a] -> i a s
  | a::l ->
      i a s >>= fun r ->
      list_iter l r i

(* val list_iter : 'a list -> 'b list -> 'c -> ('a -> 'b -> 'c -> 'c tactic) -> 'c tactic *)
let rec list_iter2 l1 l2 s i =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = tclBIND in
  match l1 , l2 with
  | [] , [] -> tclUNIT s
  | [a] , [b] -> i a b s
  | a::l1 , b::l2 ->
      i a b s >>= fun r ->
      list_iter2 l1 l2 r i
  | _ , _ -> tclZERO SizeMismatch

(* A variant of [Proof.set] specialized on the comb. Doesn't change
   the underlying "solution" (i.e. [evar_map]) *)
let set_comb c =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Proof.get >>= fun step ->
  Proof.set { step with comb = c }

let on_advance g ~solved ~adv =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Proof.get >>= fun step ->
  match Goal.advance step.solution g with
  | None -> solved (* If [first] has been solved by side effect: do nothing. *)
  | Some g -> adv g

(* A variant of list_iter where we iter over the focused list of
   goals. The argument tactic is executed in a focus comprising only
   of the current goal, a goal which has been solved by side effect is
   skipped. The generated subgoals are concatenated in order.  *)
(* val list_iter_goal : 'a -> (Goal.goal -> 'a -> 'a tactic) -> 'a tactic *)
let list_iter_goal s i =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  let (>>) = Proof.seq in
  Proof.get >>= fun initial ->
  list_iter initial.comb (s,[]) begin fun goal ((r,subgoals) as cur) ->
    on_advance goal
      ~solved: ( Proof.ret cur )
      ~adv: begin fun goal ->
        set_comb [goal] >>
        i goal r >>= fun r ->
        Proof.get >>= fun step ->
        Proof.ret ( r , step.comb::subgoals )
      end
  end >>= fun (r,subgoals) ->
  set_comb (List.flatten (List.rev subgoals)) >>
  Proof.ret r

(* spiwack: essentially a copy/paste of the above… *)
(* val list_iter_goal : 'a list -> 'b -> (Goal.goal -> 'a -> 'b -> 'b tactic) -> 'b tactic *)
let list_iter_goal2 l s i =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  let (>>) = Proof.seq in
  Proof.get >>= fun initial ->
  list_iter2 initial.comb l (s,[]) begin fun goal a ((r,subgoals) as cur) ->
    on_advance goal
      ~solved: ( Proof.ret cur )
      ~adv: begin fun goal ->
        set_comb [goal] >>
        i goal a r >>= fun r ->
        Proof.get >>= fun step ->
        Proof.ret ( r , step.comb::subgoals )
      end
  end >>= fun (r,subgoals) ->
  set_comb (List.flatten (List.rev subgoals)) >>
  Proof.ret r

(* spiwack: we use an parametrised function to generate the dispatch
   tacticals.  [tclDISPATCHGEN] takes an argument [join] to reify the
   list of produced value into the final value. *)
let tclDISPATCHGEN f join tacs =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  match tacs with
  | [] ->
      begin 
        Proof.get >>= fun initial ->
        match initial.comb with
        | [] -> tclUNIT (join [])
        | _ -> tclZERO SizeMismatch
      end
  | [tac] ->
      begin
        Proof.get >>= fun initial ->
        match initial.comb with
        | [goal] ->
            on_advance goal
              ~solved:( tclUNIT (join []) )
              ~adv:begin fun _ ->
                f tac >>= fun res ->
                Proof.ret (join [res])
              end
        | _ -> tclZERO SizeMismatch
      end
  | _ ->
      list_iter_goal2 tacs [] begin fun _ t cur ->
        f t >>= fun y ->
        Proof.ret ( y :: cur )
      end >>= fun res ->
      Proof.ret (join res)

let tclDISPATCH tacs = tclDISPATCHGEN Util.identity ignore tacs

let tclDISPATCHL tacs =
  tclDISPATCHGEN Util.identity List.rev tacs

let extend_to_list startxs rx endxs l =
  (* spiwack: I use [l] essentially as a natural number *)
  let rec duplicate acc = function
    | [] -> acc
    | _::rest -> duplicate (rx::acc) rest
  in
  let rec tail to_match rest =
    match rest, to_match with
    | [] , _::_ -> raise SizeMismatch
    | _::rest , _::to_match -> tail to_match rest
    | _ , [] -> duplicate endxs rest
  in
  let rec copy pref rest =
    match rest,pref with
    | [] , _::_ -> raise SizeMismatch
    | _::rest, a::pref -> a::(copy pref rest)
    | _ , [] -> tail endxs rest
  in
  copy startxs l

let tclEXTEND tacs1 rtac tacs2 =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Proof.get >>= fun step ->
  try
    let tacs = extend_to_list tacs1 rtac tacs2 step.comb in
    tclDISPATCH tacs
  with SizeMismatch -> tclZERO SizeMismatch

let tclINDEPENDENT tac =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Proof.get >>= fun initial ->
  match initial.comb with
  | [] -> tclUNIT ()
  | [_] -> tac
  | _ -> list_iter_goal () (fun _ () -> tac)

(* No backtracking can happen here, hence, as opposed to the dispatch tacticals,
    everything is done in one step. *)
let sensitive_on_proofview s env step =
  let wrap g ((defs, partial_list) as partial_res) = 
    match Goal.advance defs g with
    | None -> partial_res
    | Some g ->
      let { Goal.subgoals = sg } , d' = Goal.eval s env defs g in
      (d', sg::partial_list)
  in
  let ( new_defs , combed_subgoals ) = 
    List.fold_right wrap step.comb (step.solution,[])
  in
  { step with
     solution = new_defs;
     comb = List.flatten combed_subgoals; }
let tclSENSITIVE s =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Proof.current >>= fun env ->
  Proof.get >>= fun step ->
  try
    let next = sensitive_on_proofview s env step in
    Proof.set next
  with e when catchable_exception e ->
    let e = Errors.push e in
    tclZERO e

let tclPROGRESS t =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Proof.get >>= fun initial ->
  t >>= fun res ->
  Proof.get >>= fun final ->
  let test =
    Evd.progress_evar_map initial.solution final.solution &&
    not (Util.List.for_all2eq (fun i f -> Goal.equal initial.solution i final.solution f) initial.comb final.comb)
  in
  if test then
    tclUNIT res
  else
    tclZERO (Errors.UserError ("Proofview.tclPROGRESS" , Pp.str"Failed to progress."))

let tclEVARMAP =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  Proof.get >>= fun initial ->
  Proof.ret (initial.solution)

let tclENV = Proof.current

exception Timeout
let _ = Errors.register_handler begin function
  | Timeout -> Errors.errorlabstrm "Proofview.tclTIMEOUT" (Pp.str"Tactic timeout!")
  | _ -> Pervasives.raise Errors.Unhandled
end

let tclTIMEOUT n t =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  let (>>) = Proof.seq in
  (* spiwack: as one of the monad is a continuation passing monad, it
     doesn't force the computation to be threaded inside the underlying
     (IO) monad. Hence I force it myself by asking for the evaluation of
     a dummy value first, lest [timeout] be called when everything has
     already been computed. *)
  let t = Proof.lift (Proofview_monad.NonLogical.ret ()) >> t in
  Proof.current >>= fun env ->
  Proof.get >>= fun initial ->
  Proof.lift begin
    Proofview_monad.NonLogical.catch
      begin
        Proofview_monad.NonLogical.bind
          (Proofview_monad.NonLogical.timeout n (Proof.run t env initial))
          (fun r -> Proofview_monad.NonLogical.ret (Util.Inl r))
      end
      begin function
        | Proof_errors.Timeout -> Proofview_monad.NonLogical.ret (Util.Inr Timeout)
        | Proof_errors.TacticFailure e as src ->
          let e = Backtrace.app_backtrace ~src ~dst:e in
          Proofview_monad.NonLogical.ret (Util.Inr e)
        | e -> Proofview_monad.NonLogical.raise e
      end
  end >>= function
    | Util.Inl ((res,s),m) ->
        Proof.set s >>
        Proof.put m >>
        Proof.ret res
    | Util.Inr e -> tclZERO e

let mark_as_unsafe =
  Proof.put (false,([],[]))

(* Shelves all the goals under focus. *)
let shelve =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  let (>>) = Proof.seq in
  Proof.get >>= fun initial ->
  Proof.set {initial with comb=[]} >>
  Proof.put (true,(initial.comb,[]))

(* Shelves the unifiable goals under focus, i.e. the goals which
   appear in other goals under focus (the unfocused goals are not
   considered). *)
let shelve_unifiable =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  let (>>) = Proof.seq in
  Proof.get >>= fun initial ->
  let (u,n) = Goal.partition_unifiable initial.solution initial.comb in
  Proof.set {initial with comb=n} >>
  Proof.put (true,(u,[]))

(* [unshelve l p] adds all the goals in [l] at the end of the focused
   goals of p *)
let unshelve l p =
  { p with comb = p.comb@l }

(* Gives up on the goal under focus. Reports an unsafe status. Proofs
   with given up goals cannot be closed. *)
let give_up =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Proof.bind in
  let (>>) = Proof.seq in
  Proof.get >>= fun initial ->
  Proof.set {initial with comb=[]} >>
  Proof.put (false,([],initial.comb))

(*** Commands ***)

let in_proofview p k =
  k p.solution



module Notations = struct
  let (>>=) = tclBIND
  let (<*>) = tclTHEN
  let (<+>) t1 t2 = tclOR t1 (fun _ -> t2)
end

open Notations

module Monad =
  Monad.Make(struct type +'a t = 'a tactic let return=tclUNIT let (>>=)=(>>=) end)


(*** Compatibility layer with <= 8.2 tactics ***)
module V82 = struct
  type tac = Goal.goal Evd.sigma -> Goal.goal list Evd.sigma

  let tactic tac =
    (* spiwack: we ignore the dependencies between goals here,
       expectingly preserving the semantics of <= 8.2 tactics *)
    (* spiwack: convenience notations, waiting for ocaml 3.12 *)
    let (>>=) = Proof.bind in
    Proof.get >>= fun ps ->
    try
      let tac gl evd = 
        let glsigma  =
          tac { Evd.it = gl ; sigma = evd; }  in
        let sigma = glsigma.Evd.sigma in
        let g = glsigma.Evd.it in
        ( g, sigma )
      in
        (* Old style tactics expect the goals normalized with respect to evars. *)
      let (initgoals,initevd) =
        Evd.Monad.List.map (fun g s -> Goal.V82.nf_evar s g) ps.comb ps.solution
      in
      let (goalss,evd) = Evd.Monad.List.map tac initgoals initevd in
      let sgs = List.flatten goalss in
      Proof.set { ps with solution=evd ; comb=sgs; }
    with e when catchable_exception e ->
      let e = Errors.push e in
      tclZERO e


  (* normalises the evars in the goals, and stores the result in
     solution. *)
  let nf_evar_goals =
    (* spiwack: convenience notations, waiting for ocaml 3.12 *)
    let (>>=) = Proof.bind in
    Proof.get >>= fun ps ->
    let (goals,evd) =
      Evd.Monad.List.map (fun g s -> Goal.V82.nf_evar s g) ps.comb ps.solution
    in
    Proof.set { ps with solution=evd ; comb=goals }

  (* A [Proofview.tactic] version of [Refiner.tclEVARS] *)
  let tclEVARS evd =
    (* spiwack: convenience notations, waiting for ocaml 3.12 *)
    let (>>=) = Proof.bind in
    Proof.get >>= fun ps ->
    Proof.set { ps with solution = evd }
    

  let has_unresolved_evar pv =
    Evd.has_undefined pv.solution

  (* Main function in the implementation of Grab Existential Variables.*)
  let grab pv =
    let undef = Evd.undefined_map pv.solution in
    let goals =
      List.map begin fun (e,_) ->
	Goal.build e
      end (Evar.Map.bindings undef)
    in
    { pv with comb = goals }
      
    

  (* Returns the open goals of the proofview together with the evar_map to 
     interprete them. *)
  let goals { comb = comb ; solution = solution; } =
   { Evd.it = comb ; sigma = solution }

  let top_goals { initial=initial ; solution=solution; } =
    let goals = List.map (fun (t,_) -> Goal.V82.build (fst (Term.destEvar t))) initial in
    { Evd.it = goals ; sigma=solution; }

  let top_evars { initial=initial } =
    let evars_of_initial (c,_) =
      Evar.Set.elements (Evarutil.evars_of_term c)
    in
    List.flatten (List.map evars_of_initial initial)

  let instantiate_evar n com pv =
    let (evk,_) =
      let evl = Evarutil.non_instantiated pv.solution in
      let evl = Evar.Map.bindings evl in
      if (n <= 0) then
	Errors.error "incorrect existential variable index"
      else if List.length evl < n then
	  Errors.error "not so many uninstantiated existential variables"
      else
	List.nth evl (n-1) 
    in
    { pv with
	solution = Evar_refiner.instantiate_pf_com evk com pv.solution }

  let of_tactic t gls =
    try
      let init = { solution = gls.Evd.sigma ; comb = [gls.Evd.it] ; initial = [] } in
      let (_,final,_) = apply (Goal.V82.env gls.Evd.sigma gls.Evd.it) t init in
      { Evd.sigma = final.solution ; it = final.comb }
    with Proof_errors.TacticFailure e ->
      let e = Errors.push e in
      raise e

  let put_status b =
    Proof.put (b,([],[]))

  let catchable_exception = catchable_exception

  let wrap_exceptions f =
    try f ()
    with e when catchable_exception e -> let e = Errors.push e in tclZERO e

end


module Goal = struct

  type t = {
    env : Environ.env;
    sigma : Evd.evar_map;
    hyps : Environ.named_context_val;
    concl : Term.constr ;
    self : Goal.goal ; (* for compatibility with old-style definitions *)
  }

  let env { env=env } = env
  let sigma { sigma=sigma } = sigma
  let hyps { hyps=hyps } = Environ.named_context_of_val hyps
  let concl { concl=concl } = concl

  let lift s k =
    (* spiwack: convenience notations, waiting for ocaml 3.12 *)
    let (>>=) = Proof.bind in
    let (>>) = Proof.seq in
    Proof.current >>= fun env ->
    Proof.get >>= fun step ->
    try
      let (ks,sigma) =
        Evd.Monad.List.map begin fun g sigma ->
          Util.on_fst k (Goal.eval s env sigma g)
        end step.comb step.solution
      in
      Proof.set { step with solution=sigma } >>
      tclDISPATCH ks
    with e when catchable_exception e ->
      let e = Errors.push e in
      tclZERO e

  let enter_t f = Goal.enter begin fun env sigma hyps concl self ->
    f {env=env;sigma=sigma;hyps=hyps;concl=concl;self=self}
  end
  let enter f =
    list_iter_goal () begin fun goal () ->
      Proof.current >>= fun env ->
      tclEVARMAP >>= fun sigma ->
      try
        (* enter_t cannot modify the sigma. *)
        let (t,_) = Goal.eval (enter_t f) env sigma goal in
        t
      with e when catchable_exception e ->
        let e = Errors.push e in
        tclZERO e
    end


  (* compatibility *)
  let goal { self=self } = self
  let refresh_sigma g =
    tclEVARMAP >>= fun sigma ->
    tclUNIT { g with sigma }

end

module NonLogical = Proofview_monad.NonLogical

let tclLIFT = Proofview_monad.Logical.lift


