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
   one another, which represents the various subnodes of the proof, together
   with a comb: a datastructure that gives order to some of these nodes, 
   namely the open goals. 
   The natural candidate for the solution is an {!Evd.evar_map}, that is
   a calculus of evars. The comb is then a list of goals (evars wrapped 
   with some extra information, like possible name anotations).
   There is also need of a list of the evars which initialised the proofview
   to be able to return information about the proofview. *)

(* Type of proofviews. *)
type proofview = {
     initial : (Term.constr * Term.types) list;
     solution : Evd.evar_map;
     comb : Goal.goal list
     }

let proofview p =
  p.comb , p.solution

(* Initialises a proofview, the argument is a list of environement, 
   conclusion types, and optional names, creating that many initial goals. *)
let init = 
  let rec aux = function
  | [] ->  { initial = [] ; 
	     solution = Evd.empty ;
	     comb = []
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
			   comb = gl::comb }
  in
  fun l -> let v = aux l in
    (* Marks all the goal unresolvable for typeclasses. *)
    { v with solution = Typeclasses.mark_unresolvables v.solution }

(* Returns whether this proofview is finished or not. That is,
   if it has empty subgoals in the comb. There could still be unsolved
   subgoaled, but they would then be out of the view, focused out. *)
let finished = function
  | {comb = []} -> true
  | _  -> false

(* Returns the current value of the proofview partial proofs. *)
let return { initial=init; solution=defs }  =
  List.map (fun (c,t) -> (Evarutil.nf_evar defs c , t)) init

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
    | l when index = 0-> (acc,l)
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
    try 
      Util.List.chop (j-i+1) sub_right 
    with Failure "list_chop" -> 
      Errors.errorlabstrm "nth_unproven" (Pp.str"No such unproven subgoal")
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
     the subgoals of the current view at the same time. By opposed
     to the old vision of applying it to a single goal. It mostly 
     allows to consider tactic like [reorder] to reorder the goals
     in the current view (which might be useful for the tactic designer)
     (* spiwack: the ordering of goals, though, is perhaps a bit
        brittle. It would be much more interesting to find a more
        robust way to adress goals, I have no idea at this time 
        though*) 
     or global automation tactic for dependent subgoals (instantiating
     an evar has influences on the other goals of the proof in progress,
     not being able to take that into account causes the current eauto
     tactic to fail on some instances where it could succeed).
   - Tactics are a monad ['a tactic], in a sense a tactic can be 
     seens as a function (without argument) which returns a value
     of type 'a and modifies the environement (in our case: the view).
     Tactics of course have arguments, but these are given at the 
     meta-level as OCaml functions.
     Most tactics, in the sense we are used to, return [ () ], that is
     no really interesting values. But some might pass information 
     around; the [(>>--)] and [(>>==)] bind-like construction are the
     main ingredients of this information passing. 
     (* spiwack: I don't know how much all this relates to F. Kirchner and 
        C. Muñoz. I wasn't able to understand how they used the monad
        structure in there developpement.
     *)
     The tactics seen in Coq's Ltac are (for now at least) only 
     [unit tactic], the return values are kept for the OCaml toolkit.
     The operation or the monad are [Proofview.tclUNIT] (which is the 
     "return" of the tactic monad) [Proofview.tclBIND] (which is
     the "bind", also noted [(>=)]) and [Proofview.tclTHEN] (which is a
     specialized bind on unit-returning tactics).
*)

(* type of tactics:

   tactics can
   - access the environment,
   - access and change the current [proofview]
   - backtrack on previous changes of the proofview *)
(* spiwack: it seems lighter, for now, to deal with the environment here rather than in [Monads]. *)

module LocalState = struct
  type t = proofview
end
module Backtrack = Monads.Logic(Monads.Id)
module Inner = Monads.StateLogic(LocalState)(Backtrack)

type +'a tactic = Environ.env -> 'a Inner.t

(* Applies a tactic to the current proofview. *)
let apply env t sp =
  let next = Backtrack.run (Inner.run (t env) sp) in
  next.Inner.state

(*** tacticals ***)


(* Unit of the tactic monad *)
let tclUNIT a _ = Inner.return a

(* Bind operation of the tactic monad *)
let tclBIND t k env =
  Inner.bind (t env) (fun a -> k a env)

(* Interpretes the ";" (semicolon) of Ltac.
   As a monadic operation, it's a specialized "bind"
   on unit-returning tactic (meaning "there is no value to bind") *)
let tclTHEN t1 t2 env =
  Inner.seq (t1 env) (t2 env)

(* [tclIGNORE t] has the same operational content as [t],
   but drops the value at the end. *)
let tclIGNORE tac env = Inner.ignore (tac env)

(* [tclOR t1 t2 = t1] as long as [t1] succeeds. Whenever the successes
   of [t1] have been depleted, then it behaves as [t2].  No
   interleaving at this point. *)
let tclOR t1 t2 env =
  Inner.plus (t1 env) (t2 env)

(* [tclZERO e] always fails with error message [e]*)
let tclZERO e _ = Inner.zero e

(* [tclORELSE t1 t2] behaves like [t1] if [t1] succeeds at least once
   or [t2] if [t1] fails. *)
let tclORELSE t1 t2 env =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Inner.bind in
  Inner.split (t1 env) >>= function
    | Util.Inr _ -> t2 env
    | Util.Inl (a,t1') -> Inner.plus (Inner.return a) t1'

(* Focuses a tactic at a range of subgoals, found by their indices. *)
(* arnaud: bug if 0 goals ! *)
let tclFOCUS i j t env =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Inner.bind in
  let (>>) = Inner.seq in
  Inner.get >>= fun initial ->
  let (focused,context) = focus i j initial in
  Inner.set focused >>
  t (env) >>= fun result ->
  Inner.get >>= fun next ->
  Inner.set (unfocus context next) >>
  Inner.return result

(* Dispatch tacticals are used to apply a different tactic to each goal under
    consideration. They come in two flavours:
    [tclDISPATCH] takes a list of [unit tactic]-s and build a [unit tactic].
    [tclDISPATCHS] takes a list of ['a sensitive tactic] and returns and returns
    and ['a sensitive tactic] where the ['a sensitive] interpreted in a goal [g]
    corresponds to that of the tactic which created [g].
    It is to be noted that the return value of [tclDISPATCHS ts] makes only
    sense in the goals immediatly built by it, and would cause an anomaly
    is used otherwise. *)
exception SizeMismatch
let _ = Errors.register_handler begin function
  | SizeMismatch -> Errors.error "Incorrect number of goals."
  | _ -> raise Errors.Unhandled
end
(* spiwack: we use an parametrised function to generate the dispatch tacticals.
    [tclDISPATCHGEN] takes a [null] argument to generate the return value
    if there are no goal under focus, and a [join] argument to explain how
    the return value at two given lists of subgoals are combined when
    both lists are being concatenated.
    [join] and [null] need be some sort of comutative monoid. *)
let rec tclDISPATCHGEN null join tacs env =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Inner.bind in
  let (>>) = Inner.seq in
  Inner.get >>= fun initial ->
  match tacs,initial.comb with
  | [], [] -> tclUNIT null env
  | t::tacs , first::goals ->
      Inner.set {initial with comb=goals} >>
      tclDISPATCHGEN null join tacs env >>= fun x ->
      Inner.get >>= fun step ->
      begin match Goal.advance step.solution first with
      | None -> Inner.return x (* If [first] has been solved by side effect: do nothing. *)
      | Some first ->
          Inner.set {step with comb=[first]} >>
          t env >>= fun y ->
          Inner.get >>= fun step' ->
          Inner.set {step' with comb=step'.comb@step.comb} >>
          Inner.return (join x y)
      end
  | _ , _ -> raise SizeMismatch

let unitK () () = ()
let tclDISPATCH = tclDISPATCHGEN () unitK

(* This is a helper function for the dispatching tactics (like [tclGOALBIND] and
    [tclDISPATCHS]). It takes an ['a sensitive] value, and returns a tactic
    whose return value is, again, ['a sensitive] but only has value in the
    (unmodified) goals under focus. *)
let here_s b env =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Inner.bind in
  Inner.get >>= fun step ->
  Inner.return (Goal.bind (Goal.here_list step.comb b) (fun b -> b))

(* see .mli for documentation. *)
let tclDISPATCHS tacs = 
  let tacs = 
    List.map begin fun tac -> 
      tclBIND tac here_s
    end tacs 
  in
  tclDISPATCHGEN Goal.null Goal.plus tacs

let extend_to_list =
  let rec copy n x l =
    if n < 0 then raise SizeMismatch
    else if n = 0 then l
    else copy (n-1) x (x::l)
  in
  fun startxs rx endxs l ->
    let ns = List.length startxs in
    let ne = List.length endxs in
    let n = List.length l in
    startxs@(copy (n-ne-ns) rx endxs)
let tclEXTEND tacs1 rtac tacs2 env =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Inner.bind in
  Inner.get >>= fun step ->
  let tacs = extend_to_list tacs1 rtac tacs2 step.comb in
  tclDISPATCH tacs env

(* spiwack: up to a few details, same errors are in the Logic module.
    this should be maintained synchronized, probably. *)
open Pretype_errors
let rec catchable_exception = function
  | Loc.Exc_located(_,e) -> catchable_exception e
  | Errors.UserError _
  | Type_errors.TypeError _ | PretypeError (_,_,TypingError _)
  | Indrec.RecursionSchemeError _
  | Nametab.GlobalizationError _ | PretypeError (_,_,VarNotFound _)
  (* unification errors *)
  | PretypeError(_,_,(CannotUnify _|CannotUnifyLocal _|CannotGeneralize _
		   |NoOccurrenceFound _|CannotUnifyBindingType _|NotClean _
		   |CannotFindWellTypedAbstraction _
		   |UnsolvableImplicit _)) -> true
  | Typeclasses_errors.TypeClassError 
      (_, Typeclasses_errors.UnsatisfiableConstraints _) -> true
  | _ -> false


(* [tclGOALBIND] and [tclGOALBINDU] are sorts of bind which take a
    [Goal.sensitive] as a first argument, the tactic then acts on each goal separately.
    Allows backtracking between goals. *)

(* [list_of_sensitive s k] where [s] is and ['a Goal.sensitive] [k]
   has type ['a -> 'b] returns the list of ['b] obtained by evualating
   [s] to each goal successively and applying [k] to each result. *)
let list_of_sensitive s k env step =
  Goal.list_map begin fun defs g ->
    let (a,defs) = Goal.eval s env defs g in
    (k a) , defs
  end step.comb step.solution
(* In form of a tactic *)
let list_of_sensitive s k env =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Inner.bind in
  let (>>) = Inner.seq in
  Inner.get >>= fun step ->
  try 
    let (tacs,defs) = list_of_sensitive s k env step in
    Inner.set { step with solution = defs } >>
    Inner.return tacs
  with e when catchable_exception e ->
    tclZERO e env

let tclGOALBIND s k =
  (* spiwack: the first line ensures that the value returned by the tactic [k] will
      not "escape its scope". *)
  let k a = tclBIND (k a) here_s in
  tclBIND (list_of_sensitive s k) begin fun tacs ->
    tclDISPATCHGEN Goal.null Goal.plus tacs
  end

let tclGOALBINDU s k =
  tclBIND (list_of_sensitive s k) begin fun tacs ->
    tclDISPATCHGEN () unitK tacs
  end

(* No backtracking can happen here, hence, as opposed to the dispatch tacticals,
    everything is done in one step. *)
let sensitive_on_proofview s env step =
  let wrap g ((defs, partial_list) as partial_res) = 
    match Goal.advance defs g with
    | None ->partial_res
    | Some g ->
      let {Goal.subgoals = sg } , d' = Goal.eval s env defs g in
      (d',sg::partial_list)
  in
  let ( new_defs , combed_subgoals ) = 
    List.fold_right wrap step.comb (step.solution,[])
  in
  { step with
     solution = new_defs;
     comb = List.flatten combed_subgoals }
let tclSENSITIVE s env =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Inner.bind in
  Inner.get >>= fun step ->
  try
    let next = sensitive_on_proofview s env step in
    Inner.set next
  with e when catchable_exception e ->
    tclZERO e env


(*** Commands ***)

let in_proofview p k =
  k p.solution

module Notations = struct
  let (>-) = Goal.bind
  let (>>-) = tclGOALBINDU
  let (>>--) = tclGOALBIND
  let (>=) = tclBIND
  let (>>=) t k = t >= fun s -> s >>- k
  let (>>==) t k = t >= fun s -> s >>-- k
  let (<*>) = tclTHEN
  let (<+>) = tclOR
end

(*** Compatibility layer with <= 8.2 tactics ***)
module V82 = struct
  type tac = Goal.goal Evd.sigma -> Goal.goal list Evd.sigma

  let tactic tac env =
    (* spiwack: we ignore the dependencies between goals here, expectingly
       preserving the semantics of <= 8.2 tactics *)
    (* spiwack: convenience notations, waiting for ocaml 3.12 *)
    let (>>=) = Inner.bind in
    Inner.get >>= fun ps ->
    try
      let tac evd gl = 
        let glsigma  = tac { Evd.it = gl ; Evd.sigma = evd }  in
        let sigma = glsigma.Evd.sigma in
        let g = glsigma.Evd.it in
        ( g , sigma )
      in
    (* Old style tactics expect the goals normalized with respect to evars. *)
      let (initgoals,initevd) = 
        Goal.list_map Goal.V82.nf_evar ps.comb ps.solution
      in
      let (goalss,evd) = Goal.list_map tac initgoals initevd in
      let sgs = List.flatten goalss in
      Inner.set { ps with solution=evd ; comb=sgs }
    with e when catchable_exception e ->
      tclZERO e env

  let has_unresolved_evar pv =
    Evd.has_undefined pv.solution

  (* Main function in the implementation of Grab Existential Variables.*)
  let grab pv =
    let goals =
      List.map begin fun (e,_) ->
	Goal.build e
      end (Evd.undefined_list pv.solution)
    in
    { pv with comb = goals }
      
    

  (* Returns the open goals of the proofview together with the evar_map to 
     interprete them. *)
  let goals { comb = comb ; solution = solution } = 
    { Evd.it = comb ; sigma = solution}

  let top_goals { initial=initial ; solution=solution } = 
    let goals = List.map (fun (t,_) -> Goal.V82.build (fst (Term.destEvar t))) initial in
    { Evd.it = goals ; sigma=solution }

  let top_evars { initial=initial } =
    let evars_of_initial (c,_) =
      Util.Intset.elements (Evarutil.evars_of_term c)
    in
    List.flatten (List.map evars_of_initial initial)

  let instantiate_evar n com pv =
    let (evk,_) = 
      let evl = Evarutil.non_instantiated pv.solution in
     if (n <= 0) then
	Errors.error "incorrect existential variable index"
      else if List.length evl < n then
	  Errors.error "not so many uninstantiated existential variables"
      else
	List.nth evl (n-1) 
    in
    { pv with
	solution = Evar_refiner.instantiate_pf_com evk com pv.solution }

end
