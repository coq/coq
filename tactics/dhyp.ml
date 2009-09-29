(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* Chet's comments about this tactic :

 Programmable destruction of hypotheses and conclusions.

   The idea here is that we are going to store patterns.  These
   patterns look like:

   TYP=<pattern>
   SORT=<pattern>

   and from these patterns, we will be able to decide which tactic to
   execute.

   For hypotheses, we have a vector of 4 patterns:

   HYP[TYP] HYP[SORT] CONCL[TYP] CONCL[SORT]

   and for conclusions, we have 2:

   CONCL[TYP] CONCL[SORT]

   If the user doesn't supply some of these, they are just replaced
   with empties.

   The process of matching goes like this:

   We use a discrimination net to look for matches between the pattern
   for HYP[TOP] (CONCL[TOP]) and the type of the chosen hypothesis.
   Then, we use this to look for the right tactic to apply, by
   matching the rest of the slots.  Each match is tried, and if there
   is more than one, this fact is reported, and the one with the
   lowest priority is taken.  The priority is a parameter of the
   tactic input.

   The tactic input is an expression to hand to the
   tactic-interpreter, and its priority.

   For most tactics, the priority should be the number of subgoals
   generated.

   Matching is compatible with second-order matching of sopattern.

   SYNTAX:

   Hint DHyp <hyp-pattern> pri <tac-pattern>.

   and

   Hint DConcl <concl-pattern> pri <tac-pattern>.

   The bindings at the end allow us to transfer information from the
   patterns on terms into the patterns on tactics in a safe way - we
   will perform second-order normalization and conversion to an AST
   before substitution into the tactic-expression.

   WARNING: The binding mechanism is NOT intended to facilitate the
   transfer of large amounts of information from the terms to the
   tactic.  This should be done in a special-purpose tactic.

 *)

(*

Example : The tactic "if there is a hypothesis saying that the
successor of some number is smaller than zero, then invert such
hypothesis" is defined in this way:

Require DHyp.
Hint Destruct Hypothesis less_than_zero (le (S ?) O) 1
  (:tactic:<Inversion $0>).

Then, the tactic is used like this:

Goal (le (S O) O) -> False.
Intro H.
DHyp  H.
Qed.

The name "$0" refers to the matching hypothesis --in this case the
hypothesis H.

Similarly for the conclusion :

Hint Destruct Conclusion equal_zero  (? = ?) 1 (:tactic:<Reflexivity>).

Goal (plus O O)=O.
DConcl.
Qed.

The "Discardable" option clears the hypothesis after using it.

Require DHyp.
Hint Destruct  Discardable Hypothesis less_than_zero (le (S ?) O) 1
  (:tactic:<Inversion $0>).

Goal (n:nat)(le (S n) O) -> False.
Intros n H.
DHyp  H.
Qed.
-- Eduardo (9/3/97 )

*)

open Pp
open Util
open Names
open Term
open Environ
open Reduction
open Proof_type
open Rawterm
open Tacmach
open Refiner
open Tactics
open Clenv
open Tactics
open Tacticals
open Libobject
open Library
open Pattern
open Matching
open Pcoq
open Tacexpr
open Termops
open Libnames

(* two patterns - one for the type, and one for the type of the type *)
type destructor_pattern = {
  d_typ: constr_pattern;
  d_sort: constr_pattern }

let subst_destructor_pattern subst { d_typ = t; d_sort = s } =
  { d_typ = subst_pattern subst t; d_sort = subst_pattern subst s }

(* hypothesis patterns might need to do matching on the conclusion, too.
 * conclusion-patterns only need to do matching on the hypothesis *)
type located_destructor_pattern =
   (* discardable, pattern for hyp, pattern for concl *)
   (bool * destructor_pattern * destructor_pattern,
   (* pattern for concl *)
   destructor_pattern) location

let subst_located_destructor_pattern subst = function
  | HypLocation (b,d,d') ->
      HypLocation
        (b,subst_destructor_pattern subst d, subst_destructor_pattern subst d')
  | ConclLocation d ->
      ConclLocation (subst_destructor_pattern subst d)

type destructor_data = {
  d_pat : located_destructor_pattern;
  d_pri : int;
  d_code : identifier option * glob_tactic_expr (* should be of phylum tactic *)
}

type t = (identifier,destructor_data) Nbtermdn.t
type frozen_t = (identifier,destructor_data) Nbtermdn.frozen_t

let tactab = (Nbtermdn.create () : t)

let lookup pat = Nbtermdn.lookup tactab pat

let init () = Nbtermdn.empty tactab

let freeze () = Nbtermdn.freeze tactab
let unfreeze fs = Nbtermdn.unfreeze fs tactab

let add (na,dd) =
  let pat = match dd.d_pat with
    | HypLocation(_,p,_) -> p.d_typ
    | ConclLocation p -> p.d_typ
  in
  if Nbtermdn.in_dn tactab na then begin
    msgnl (str "Warning [Overriding Destructor Entry " ++
             str (string_of_id na) ++ str"]");
    Nbtermdn.remap tactab na (pat,dd)
  end else
    Nbtermdn.add tactab (na,(pat,dd))

let _ =
  Summary.declare_summary "destruct-hyp-concl"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let forward_subst_tactic =
  ref (fun _ -> failwith "subst_tactic is not installed for DHyp")

let cache_dd (_,(_,na,dd)) =
  try
    add (na,dd)
  with _ ->
    anomalylabstrm "Dhyp.add"
      (str"The code which adds destructor hints broke;" ++ spc () ++
	 str"this is not supposed to happen")

let classify_dd (local,_,_ as o) =
  if local then Dispose else Substitute o

let subst_dd (_,subst,(local,na,dd)) =
  (local,na,
  { d_pat = subst_located_destructor_pattern subst dd.d_pat;
    d_pri = dd.d_pri;
    d_code = !forward_subst_tactic subst dd.d_code })

let (inDD,_) =
  declare_object {(default_object "DESTRUCT-HYP-CONCL-DATA") with
                    cache_function = cache_dd;
		    open_function = (fun i o -> if i=1 then cache_dd o);
                    subst_function = subst_dd;
		    classify_function = classify_dd }

let catch_all_sort_pattern = PMeta(Some (id_of_string "SORT"))
let catch_all_type_pattern = PMeta(Some (id_of_string "TYPE"))

let add_destructor_hint local na loc (_,pat) pri code =
  let code =
    begin match loc, code with
      | HypLocation _, TacFun ([id],body) -> (id,body)
      | ConclLocation _, _ -> (None, code)
      | _ ->
	  errorlabstrm "add_destructor_hint"
          (str "The tactic should be a function of the hypothesis name.") end
  in
  let pat = match loc with
    | HypLocation b ->
	HypLocation
	  (b,{d_typ=pat;d_sort=catch_all_sort_pattern},
	     {d_typ=catch_all_type_pattern;d_sort=catch_all_sort_pattern})
    | ConclLocation () ->
	ConclLocation({d_typ=pat;d_sort=catch_all_sort_pattern}) in
  Lib.add_anonymous_leaf
    (inDD (local,na,{ d_pat = pat; d_pri=pri; d_code=code }))

let match_dpat dp cls gls =
  let onconcl = cls.concl_occs <> no_occurrences_expr in
  match (cls,dp) with
    | ({onhyps=lo},HypLocation(_,hypd,concld)) when not onconcl ->
        let hl = match lo with
            Some l -> l
          | None -> List.map (fun id -> ((all_occurrences_expr,id),InHyp))
	              (pf_ids_of_hyps gls) in
        if not
          (List.for_all
            (fun ((_,id),hl) ->
              let cltyp = pf_get_hyp_typ gls id in
              let cl = pf_concl gls in
              (hl=InHyp) &
              (is_matching hypd.d_typ cltyp) &
              (is_matching hypd.d_sort (pf_type_of gls cltyp)) &
              (is_matching concld.d_typ cl) &
              (is_matching concld.d_sort (pf_type_of gls cl)))
            hl)
        then error "No match."
    | ({onhyps=Some[]},ConclLocation concld) when onconcl ->
        let cl = pf_concl gls in
        if not
          ((is_matching concld.d_typ cl) &
           (is_matching concld.d_sort (pf_type_of gls cl)))
        then error "No match."
    | _ -> error "ApplyDestructor"

let forward_interp_tactic =
  ref (fun _ -> failwith "interp_tactic is not installed for DHyp")

let set_extern_interp f = forward_interp_tactic := f

let applyDestructor cls discard dd gls =
  match_dpat dd.d_pat cls gls;
  let cll = simple_clause_of cls gls in
  let tacl =
    List.map (fun cl ->
      match cl, dd.d_code with
        | Some id, (Some x, tac) ->
	    let arg =
              ConstrMayEval(ConstrTerm (RRef(dummy_loc,VarRef id),None)) in
            TacLetIn (false, [(dummy_loc, x), arg], tac)
        | None, (None, tac) -> tac
        | _, (Some _,_) -> error "Destructor expects an hypothesis."
        | _, (None,_) -> error "Destructor is for conclusion.")
      cll in
  let discard_0 =
    List.map (fun cl ->
      match (cl,dd.d_pat) with
        | (Some id,HypLocation(discardable,_,_)) ->
            if discard & discardable then thin [id] else tclIDTAC
        | (None,ConclLocation _) -> tclIDTAC
        | _ -> error "ApplyDestructor" ) cll in
  tclTHEN (tclMAP !forward_interp_tactic tacl) (tclTHENLIST discard_0) gls


(* [DHyp id gls]

   will take an identifier, get its type, look it up in the
   discrimination net, get the destructors stored there, and then try
   them in order of priority. *)

let destructHyp discard id gls =
  let hyptyp = pf_get_hyp_typ gls id in
  let ddl = List.map snd (lookup hyptyp) in
  let sorted_ddl = Sort.list (fun dd1 dd2 -> dd1.d_pri > dd2.d_pri) ddl in
  tclFIRST (List.map (applyDestructor (onHyp id) discard) sorted_ddl) gls

let dHyp id gls = destructHyp false id gls

let h_destructHyp b id =
  abstract_tactic (TacDestructHyp (b,(dummy_loc,id))) (destructHyp b id)

(* [DConcl gls]

   will take a goal, get its concl, look it up in the
   discrimination net, get the destructors stored there, and then try
   them in order of priority. *)

let dConcl gls =
  let ddl = List.map snd (lookup (pf_concl gls)) in
  let sorted_ddl = Sort.list (fun dd1 dd2 -> dd1.d_pri > dd2.d_pri) ddl in
  tclFIRST (List.map (applyDestructor onConcl false) sorted_ddl) gls

let h_destructConcl = abstract_tactic TacDestructConcl dConcl

let rec search n =
  if n=0 then error "Search has reached zero.";
  tclFIRST
    [intros;
     assumption;
     (tclTHEN
        (Tacticals.tryAllHypsAndConcl
           (function
              | Some id -> (dHyp id)
              | None    ->  dConcl ))
        (search (n-1)))]

let auto_tdb n = tclTRY (tclCOMPLETE (search n))

let search_depth_tdb = ref(5)

let depth_tdb = function
  | None -> !search_depth_tdb
  | Some n -> n

let h_auto_tdb n = abstract_tactic (TacAutoTDB n) (auto_tdb (depth_tdb n))
