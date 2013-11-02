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

open Util

(* Type of proofviews. *)
type proofview = {
     initial : (Term.constr * Term.types) list;
     solution : Evd.evar_map;
     comb : Goal.goal list;
     }

let proofview p =
  p.comb , p.solution

(* Initialises a proofview, the argument is a list of environement, 
   conclusion types, and optional names, creating that many initial goals. *)
let init = 
  let rec aux = function
  | [] ->  { initial = [] ; 
	     solution = Evd.empty ;
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
module Backtrack = Monads.Logic(Monads.IO)
module Inner = Monads.StateLogic(LocalState)(Backtrack)

type +'a tactic = Environ.env -> 'a Inner.t

(* Applies a tactic to the current proofview. *)
let apply env t sp =
  let next = Monads.IO.run (Backtrack.run (Inner.run (t env) sp)) in
  next.Inner.result , next.Inner.state

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
   of [t1] have been depleted and it failed with [e], then it behaves
   as [t2 e].  No interleaving at this point. *)
let tclOR t1 t2 env =
  Inner.plus (t1 env) (fun e -> t2 e env)

(* [tclZERO e] always fails with error message [e]*)
let tclZERO e _ = Inner.zero e

(* [tclORELSE t1 t2] behaves like [t1] if [t1] succeeds at least once
   or [t2] if [t1] fails. *)
let tclORELSE t1 t2 env =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Inner.bind in
  Inner.split (t1 env) >>= function
    | Util.Inr e -> t2 e env
    | Util.Inl (a,t1') -> Inner.plus (Inner.return a) t1'

(* [tclIFCATCH a s f] is a generalisation of [tclORELSE]: if [a]
   succeeds at least once then it behaves as [tclBIND a s] otherwise, if [a]
   fails with [e], then it behaves as [f e]. *)
let tclIFCATCH a s f env =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Inner.bind in
  Inner.split (a env) >>= function
    | Util.Inr e -> f e env
    | Util.Inl (x,a') -> Inner.plus (s x env) (fun e -> (a' e) >>= fun x' -> (s x' env))

(* Focuses a tactic at a range of subgoals, found by their indices. *)
(* arnaud: bug if 0 goals ! *)
let tclFOCUS i j t env =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Inner.bind in
  let (>>) = Inner.seq in
  Inner.get >>= fun initial ->
  try
    let (focused,context) = focus i j initial in
    Inner.set focused >>
    t (env) >>= fun result ->
    Inner.get >>= fun next ->
    Inner.set (unfocus context next) >>
    Inner.return result
  with e ->
    (* spiwack: a priori the only possible exceptions are that of focus,
       of course I haven't made them algebraic yet. *)
    tclZERO e env

(* arnaud: vérifier les commentaires de dispatch vis-à-vis de l'ordre
   d'évaluation des buts. Ne pas oublier le mli *)
(* arnaud: commenter [tclDISPATCHL] *)
(* Dispatch tacticals are used to apply a different tactic to each goal under
   consideration. They come in two flavours:
   [tclDISPATCH] takes a list of [unit tactic]-s and build a [unit tactic]. *)
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
      begin match Goal.advance initial.solution first with
      | None -> Inner.return null (* If [first] has been solved by side effect: do nothing. *)
      | Some first ->
          Inner.set {initial with comb=[first]} >>
          t env
      end >>= fun y ->
      Inner.get >>= fun step ->
      Inner.set {step with comb=goals} >>
      tclDISPATCHGEN null join tacs env >>= fun x ->
      Inner.get >>= fun step' ->
      Inner.set {step' with comb=step.comb@step'.comb} >>
      Inner.return (join y x)
  | _ , _ -> tclZERO SizeMismatch env

let unitK () () = ()
let tclDISPATCH = tclDISPATCHGEN () unitK

let tclDISPATCHL tacs =
  let tacs =
    List.map begin fun tac ->
      tclBIND tac (fun a -> tclUNIT [a])
    end tacs
  in
  tclDISPATCHGEN [] (@) tacs

let extend_to_list =
  let rec copy n x l =
    if n < 0 then raise SizeMismatch
    else if Int.equal n 0 then l
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
  let tclSENSITIVE s env =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Inner.bind in
  Inner.get >>= fun step ->
  try
    let next = sensitive_on_proofview s env step in
    Inner.set next
  with e when Errors.noncritical e ->
    tclZERO e env

(* arnaud: on pourrait regarder la liste de buts aussi, mais je
   ne sais pas encore comment. Pour l'instant on fait au plus
   simple. *)
let tclPROGRESS t env =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Inner.bind in
  Inner.get >>= fun initial ->
  t env >>= fun res ->
  Inner.get >>= fun final ->
  let test =
    Evd.progress_evar_map initial.solution final.solution &&
    not (Util.List.for_all2eq (fun i f -> Goal.equal initial.solution i final.solution f) initial.comb final.comb)
  in
  if test then
    tclUNIT res env
  else
    tclZERO (Errors.UserError ("Proofview.tclPROGRESS" , Pp.str"Failed to progress.")) env

let tclEVARMAP _ =
  (* spiwack: convenience notations, waiting for ocaml 3.12 *)
  let (>>=) = Inner.bind in
  Inner.get >>= fun initial ->
  Inner.return (initial.solution)

let tclENV env =
  Inner.return env

let tclTIMEOUT n t env = Inner.timeout n (t env)

(*** Commands ***)

let in_proofview p k =
  k p.solution


(* spiwack: to help using `bind' like construct consistently. A glist
   is promissed to have exactly one element per goal when it is
   produced. *)
type 'a glist  = 'a list

module Notations = struct
  let (>-) = Goal.bind
  let (>=) = tclBIND
  let (>>-) t k =
    (* spiwack: the application of List.map may raise errors, as this
       combinator is mostly used in porting historical tactic code,
       where the error flow is somewhat hard to follow, hence the
       try/with *)
      t >= fun l ->
      try tclDISPATCH (List.map k l)
      with e when Errors.noncritical e -> tclZERO e
  let (>>--) t k =
    (* spiwack: the application of List.map may raise errors, as this
       combinator is mostly used in porting historical tactic code,
       where the error flow is somewhat hard to follow, hence the
       try/with *)
    begin
      t >= fun l ->
      try tclDISPATCHL (List.map k l)
      with e when Errors.noncritical e -> tclZERO e
    end >= fun l' ->
    tclUNIT (List.flatten l')
  let (>>=) = (>>-)
  let (>>==) = (>>--)
  let (<*>) = tclTHEN
  let (<+>) t1 t2 = tclOR t2 (fun _ -> t2)
end

open Notations
let rec list_map f = function
  | [] -> tclUNIT []
  | a::l ->
      f a >= fun a' ->
        list_map f l >= fun l' ->
          tclUNIT (a'::l')


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
        let glsigma  =
          tac { Evd.it = gl ; sigma = evd; }  in
        let sigma = glsigma.Evd.sigma in
        let g = glsigma.Evd.it in
        ( g, sigma )
      in
    (* Old style tactics expect the goals normalized with respect to evars. *)
      let (initgoals,initevd) =
        Goal.list_map Goal.V82.nf_evar ps.comb ps.solution
      in
      let (goalss,evd) = Goal.list_map tac initgoals initevd in
      let sgs = List.flatten goalss in
      Inner.set { ps with solution=evd ; comb=sgs; }
    with e when Errors.noncritical e ->
      tclZERO e env

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
    let init = { solution = gls.Evd.sigma ; comb = [gls.Evd.it] ; initial = [] } in
    let (_,final) = apply (Goal.V82.env gls.Evd.sigma gls.Evd.it) t init in
    { Evd.sigma = final.solution ; it = final.comb }

end


module Goal = struct

  type 'a u = 'a list

  let lift s env =
    (* spiwack: convenience notations, waiting for ocaml 3.12 *)
    let (>>=) = Inner.bind in
    let (>>) = Inner.seq in
    Inner.get >>= fun step ->
    try
      let (res,sigma) =
        Goal.list_map begin fun sigma g ->
          Goal.eval s env sigma g
        end step.comb step.solution
      in
      Inner.set { step with solution=sigma } >>
        Inner.return res
    with e when Errors.noncritical e ->
      tclZERO e env

  let return x = lift (Goal.return x)
  let concl = lift Goal.concl
  let hyps = lift Goal.hyps
  let env = lift Goal.env
end










