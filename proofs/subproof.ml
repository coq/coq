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
				       (* arnaud:faire un nouveau new_evar 
					  ad hoc.
				          Chercher le pattern dans 
				          goal.ml aussi.*)
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

(* Returns the open goals of the subproof *)
let goals { comb = comb } = comb









(******************************************************************)
(***                                                            ***)
(***                Definition related to tactics               ***)
(***                                                            ***)
(******************************************************************)



(* type of tactics *)

type tactic = subproof -> subproof

(* exception which represent a failure in a command *)
exception TacticFailure of Pp.std_ppcmds

(* [fail s] raises [TacticFailure s].  *)
let fail msg = raise (TacticFailure msg)


(* Applies a tactic to the current subproof. *)
let apply t sp = t sp


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


(* Focuses a tactic at a single subgoal, found by it's index. *)
(* There could easily be such a tactical for a range of goals. *)
(* arnaud: bug if 0 goals ! *)
let choose_one i t sp =
  let (single,context) = focus i i sp in
  unfocus context (apply t single)

(* Makes a list of tactic into a tactic (interpretes the [ | ] construct).
   It applies the tactics from the last one to the first one.
   Fails on the proofs with a number of subgoals not matching the length
   of the list.*)
let rec list_of_tactics tac_list sp =
  match tac_list, sp.comb with
  | tac::list,goal::comb -> let rec_sp = { sp with comb = comb } in
                            let intermediate = list_of_tactics list rec_sp in
		            let this_sp = { intermediate with comb = [goal] } in
			    let almost = tac this_sp in
			    { almost with comb = almost.comb@intermediate.comb }
  | [],[] -> sp
  | _,_ -> fail (Pp.str "Not the right number of subgoals.")

(* arnaud: syntax de la construction ? *)
(* arnaud: catcher l'erreur en Failure, à faire après avoir retouché Util... *)
(* Interpretes the [ t1 | t2 | ... | t3 | t4 ] construct.
   That is it applies [t1] to the first goal, [t3] and [t4] to the 
   last two, and [t2] to the rest (this generalizes to two lists
   of tactics and a tactic to be repeated.
   As in the other constructions, the tactics are applied from the last
   goal to the first. *)
let rec extend_list_of_tactics begin_tac_list repeat_tac end_tac_list sp =
  let comb = sp.comb in
  let (b,m_e) = Util.list_chop (List.length begin_tac_list) comb in
  let (m,e) = Util.list_chop (List.length m_e - List.length end_tac_list) m_e in
  let end_sp = { sp with comb = e } in
  let intermediate_end_sp = list_of_tactics end_tac_list end_sp in
  let middle_sp = { intermediate_end_sp with comb = m } in
  let intermediate_middle_sp = apply repeat_tac middle_sp in
  let begin_sp = { intermediate_middle_sp with comb = b } in
  let almost = list_of_tactics begin_tac_list begin_sp in
  { almost with comb = almost.comb@(intermediate_middle_sp.comb
				  @ intermediate_end_sp.comb)
  }

(* Interpetes the ";" (semicolon) of Ltac. *)
let tac_then t1 t2 sp = t2 (t1 sp)



(* Reoders the goals on the comb according to a permutation *)
let reorder p sp =
  { sp with comb = Array.to_list 
                  (Permutation.permute p 
		  (Array.of_list sp.comb)) 
  }
