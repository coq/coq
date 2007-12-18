(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* The subproof datastructure is a pure datastructure underlying the notion
   of proof (namely, a proof is a subproof which can evolve and has safety
   mechanisms attached).
   The general idea of the structure is that it is composed of a chemical
   solution: an unstructured bag of stuff which has some relations with 
   one another, which represents the various subnodes of the proof, together
   with a comb: a datastructure that gives order to some of these nodes, 
   namely the open goals. 
   The natural candidate for the solution is an {!Evd.evar_defs}, that is
   a calculus of evars. The comb is then a list of goals (evars wrapped 
   with some extra information, like possible name anotations).
   There is also need of a list of the evars which initialised the subproof
   to be able to return information about the subproof. *)

type subproof = {
     initial : Term.constr list;
     solution : Evd.evar_defs;
     comb : Goal.goal list
     }

let rec init = function
  | [] ->  { initial = [] ; 
	     solution = Evd.create_evar_defs Evd.empty ;
	     comb = []
	   }
  | (env,typ,name)::l -> let { initial = ret ; solution = sol ; comb = comb } =
                           init l
                         in
                         let ( new_defs , econstr ) = 
			   Evarutil.new_evar sol env typ
			 in
			 let e = match Term.kind_of_term econstr with
			         | Term.Evar (e,_) -> e
				 | _ -> Util.anomaly 
				     "Subproof.init: new_evar failure"
				       (* the above error would mean
					  that [Evarutil.new_evar]
					  outputed a non-evar constr,
					  which it should not. *)
			 in
			 let gl = Goal.build ?name e in
			 { initial = econstr::ret;
			   solution = new_defs ;
			   comb = gl::comb }
		    
let rec start env l =
  init (List.map (fun x -> (env,x,None)) l)


(* Returns whether this subproof is finished or not. *)
let finished = function
  | {comb = []} -> true
  | _  -> false


(* Function which returns the current state of refinement of the required
   evars. *)
let return { initial=init; solution=defs } =
  List.map (Evarutil.nf_evar (Evd.evars_of defs)) init

(* arnaud: reporter certaines fonctions dans lib/ *)
(* [IndexOutOfRange] occurs in case of malformed indices
   with respect to list lengths. *)
exception IndexOutOfRange

(*arnaud: commenter*)
let list_goto i = 
  let rec aux acc index = function
    | [] -> raise IndexOutOfRange
    | a::q when index < i -> aux (a::acc) (index+1) q
    | l -> (acc,l)
  in
  fun l ->
    if i < 0 then
      raise IndexOutOfRange
    else
      aux [] 0 l

type focus_context = Goal.goal list * Goal.goal list

(* This (internal) function extracts a sublist between two indices, and
   returns this sublist together with its context :
   if it returns [(a,(b,c))] then [a] is the sublist and (rev b)@a@c is the
   original list.
   [focus_sublist i j l] raises [IndexOutOfRange(i, length l)] if
   [i >= length l], and [IndexOutOfRange(j,length l)] if 
   [j >= length l > i]. 
   It can also raise [NegativeIndex] if either [i] or [j-i] are negative. *)
(* arnaud: préciser "between to indices". *)
let focus_sublist i j l =
  let (left,sub_right) = list_goto i l in
  let (sub, right) = Util.list_chop (j-i+1) sub_right in
  (sub, (left,right))

(* Inverse operation to the previous one. *)
let unfocus_sublist (left,right) s =
  List.rev_append left (s@right)


(* [focus i j] focuses a subproof on the goals from index [i] to index [j] 
   (inclusive). (i.e. goals number [i] to [j] become the only goals of the
   returned subproof).
   It returns the focus proof, and a context for the focus trace. *)
let focus i j sp =
  let (new_comb, context) = focus_sublist i j sp.comb in
  ( { sp with comb = new_comb } , context )

(* Unfocuses a subproof with respect to a context. *)
let unfocus c sp =
  { sp with comb = unfocus_sublist c sp.comb }


(* Reoders the goals on the comb according to a permutation *)
let reorder p sp =
  { sp with comb = Array.to_list 
                  (Permutation.permute p 
		  (Array.of_list sp.comb)) 
  }

(* Returns the open goals of the subproof *)
let goals { comb = comb } = comb









(******************************************************************)
(***                                                            ***)
(***                Definition related to tactics               ***)
(***                                                            ***)
(******************************************************************)



(* type of tactics *)

type tactic = subproof -> subproof


(* Transforms a function of type 
   [Evd.evar_defs -> Goal.goal -> Goal.refinement] (i.e.
   a tactic that operates on a single goal) into an actual tactic.
   It operates by iterating the single-tactic from the last goal to 
   the first one. *)
let single_tactic f sp =
  let wrap g ((defs, partial_list) as partial_res) = 
    if Goal.is_defined (Evd.evars_of defs) g then 
      partial_res
    else
      let { Goal.new_defs = d' ; Goal.subgoals = sg } = f defs g in
      (d',sg::partial_list)
  in
  let ( new_defs , combed_subgoals ) = 
    List.fold_right wrap sp.comb (sp.solution,[])
  in
  { sp with solution = new_defs;
            comb = List.flatten combed_subgoals }


