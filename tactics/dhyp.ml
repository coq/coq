
(* $Id$ *)

(* Chet's comments about this tactic :
 
 Programmable destruction of hypotheses and conclusions.

   The idea here is that we are going to store patterns.  These
   patterns look like:

   TYP=<patern>
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
  [<:tactic:<Inversion $0>>].

Then, the tactic is used like this:

Goal (le (S O) O) -> False.
Intro H.
DHyp  H.
Qed.

The name "$0" refers to the matching hypothesis --in this case the
hypothesis H.

Similarly for the conclusion :

Hint Destruct Conclusion equal_zero  (? = ?) 1 [<:tactic:<Reflexivity>>].

Goal (plus O O)=O.
DConcl.
Qed.

The "Discardable" option clears the hypothesis after using it.

Require DHyp.
Hint Destruct  Discardable Hypothesis less_than_zero (le (S ?) O) 1
  [<:tactic:<Inversion $0>>].

Goal (n:nat)(le (S n) O) -> False.
Intros n H.
DHyp  H.
Qed.
-- Eduardo (9/3/97 )

*)

open Pp
open Util
open Names
open Generic
open Term
open Environ
open Reduction
open Proof_trees
open Tacmach
open Tactics
open Clenv
open Tactics
open Tacticals
open Libobject
open Library
open Vernacinterp
open Pattern
open Coqast
open Ast
open Pcoq

(* two patterns - one for the type, and one for the type of the type *)
type destructor_pattern = {
  d_typ: constr; 
  d_sort: constr }
    
type ('a,'b) location = Hyp of 'a | Concl of 'b

(* hypothesis patterns might need to do matching on the conclusion, too.
 * conclusion-patterns only need to do matching on the hypothesis *)
type located_destructor_pattern =
   (* discadable , pattern for hyp, pattern for concl *)
   (bool * destructor_pattern * destructor_pattern,
   (* pattern for concl *)
   destructor_pattern) location

type destructor_data = {
  d_pat : located_destructor_pattern;
  d_pri : int;
  d_code : Ast.act } (* should be of phylum tactic *)

type t = (identifier,destructor_data) Nbtermdn.t
type frozen_t = (identifier,destructor_data) Nbtermdn.frozen_t

let tactab = (Nbtermdn.create () : t)

let lookup pat = Nbtermdn.lookup tactab pat

let init () = Nbtermdn.empty tactab

let freeze () = Nbtermdn.freeze tactab
let unfreeze fs = Nbtermdn.unfreeze fs tactab

let rollback f x =
  let fs = freeze() in 
  try f x with e -> (unfreeze fs; raise e)

let add (na,dd) =
  let pat = match dd.d_pat with
    | Hyp(_,p,_) -> p.d_typ
    | Concl p -> p.d_typ
  in 
  if Nbtermdn.in_dn tactab na then begin
    mSGNL [< 'sTR "Warning [Overriding Destructor Entry " ; 
             'sTR (string_of_id na) ; 'sTR"]" >];
    Nbtermdn.remap tactab na (pat,dd)
  end else 
    Nbtermdn.add tactab (na,(pat,dd))

let _ = 
  Summary.declare_summary "destruct-hyp-concl"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let cache_dd (_,(na,dd)) =
  try 
    add (na,dd)
  with _ -> 
    anomalylabstrm "Dhyp.add"
      [< 'sTR"The code which adds destructor hints broke;"; 'sPC; 
	 'sTR"this is not supposed to happen" >]

let specification_dd x = x

type destructor_data_object = identifier * destructor_data

let ((inDD:destructor_data_object->obj),
     (outDD:obj->destructor_data_object)) =
  declare_object ("DESTRUCT-HYP-CONCL-DATA",
                  { load_function = (fun _ -> ());
                    cache_function = cache_dd;
		    open_function = (fun _ -> ());
                    specification_function = specification_dd })
    
let add_destructor_hint na pat pri code =
  Lib.add_anonymous_leaf
    (inDD (na,{ d_pat = pat; d_pri=pri; d_code=code }))

let _ = 
  vinterp_add "HintDestruct"
    (function
       | [VARG_IDENTIFIER na; VARG_AST location; VARG_CONSTR patcom;
          VARG_NUMBER pri; VARG_AST tacexp] ->
	   let loc = match location with
             | Node(_,"CONCL",[]) -> Concl()
	     | Node(_,"DiscardableHYP",[]) -> Hyp true
	     | Node(_,"PreciousHYP",[]) -> Hyp false 
	     | _ -> assert false
	   in
	   fun () ->
	     let pat = raw_sopattern_of_compattern (Global.env()) patcom in
	     let code = Ast.to_act_check_vars ["$0",ETast] ETast tacexp in
	     add_destructor_hint na
               (match loc with
		  | Hyp b ->
		      Hyp(b,{d_typ=pat;d_sort=DOP0(Meta(new_meta()))},
			  { d_typ=DOP0(Meta(new_meta()));
		       	    d_sort=DOP0(Meta(new_meta())) })
		  | Concl () ->
		      Concl({d_typ=pat;d_sort=DOP0(Meta(new_meta()))}))
               pri code
       | _ -> bad_vernac_args "HintDestruct")

let match_dpat dp cls gls =
  let cltyp = clause_type cls gls in
  match (cls,dp) with
    | (Some id,Hyp(_,hypd,concld)) ->
        (somatch None hypd.d_typ cltyp)@
        (somatch None hypd.d_sort (pf_type_of gls cltyp))@
        (somatch None concld.d_typ (pf_concl gls))@
        (somatch None concld.d_sort (pf_type_of gls (pf_concl gls)))
    | (None,Concl concld) ->
        (somatch None concld.d_typ (pf_concl gls))@
        (somatch None concld.d_sort (pf_type_of gls (pf_concl gls)))
    | _ -> error "ApplyDestructor"

let applyDestructor cls discard dd gls =
  let mvb = match_dpat dd.d_pat cls gls in
  let astb = match cls with
    | Some id -> ["$0", Vast (nvar (string_of_id id))]
    | None -> ["$0", Vast (nvar "$0")] in
  (* TODO: find the real location *)
  let tcom = match Ast.eval_act dummy_loc astb dd.d_code with
    | Vast tcom -> tcom
    | _ -> assert false 
  in
  let discard_0 =
    match (cls,dd.d_pat) with
      | (Some id,Hyp(discardable,_,_)) ->
          if discard & discardable then thin [id] else tclIDTAC
      | (None,Concl _) -> tclIDTAC
      | _ -> error "ApplyDestructor" 
  in
  (tclTHEN (Tacinterp.interp tcom) discard_0) gls

(* [DHyp id gls]

   will take an identifier, get its type, look it up in the
   discrimination net, get the destructors stored there, and then try
   them in order of priority. *)

let destructHyp discard id gls =
  let hyptyp = clause_type (Some id) gls in
  let ddl = List.map snd (lookup hyptyp) in
  let sorted_ddl = Sort.list (fun dd1 dd2 -> dd1.d_pri > dd2.d_pri) ddl in
  tclFIRST (List.map (applyDestructor (Some id) discard) sorted_ddl) gls

let cDHyp id gls = destructHyp true id gls
let dHyp id gls = destructHyp false id gls

open Tacinterp

let _ = 
  tacinterp_add
    ("DHyp",(function
	       | [Identifier id] -> dHyp id
	       | _ -> bad_tactic_args "DHyp"))

let _ = 
  tacinterp_add
    ("CDHyp",(function
		| [Identifier id] -> cDHyp id
		| _ -> bad_tactic_args "CDHyp"))

(* [DConcl gls]

   will take a goal, get its concl, look it up in the
   discrimination net, get the destructors stored there, and then try
   them in order of priority. *)

let dConcl gls =
  let ddl = List.map snd (lookup (pf_concl gls)) in
  let sorted_ddl = Sort.list (fun dd1 dd2 -> dd1.d_pri > dd2.d_pri) ddl in
  tclFIRST (List.map (applyDestructor None false) sorted_ddl) gls

let _ = 
  tacinterp_add
    ("DConcl",(function
		 | [] -> dConcl
		 | _ -> bad_tactic_args "DConcl"))

let to2Lists (table:t) = Nbtermdn.to2lists table

let rec search n =
  if n=0 then error "Search has reached zero.";
  tclFIRST
    [intros;
     assumption;
     (tclTHEN  
        (Tacticals.tryAllClauses 
           (function 
              | Some id -> (dHyp id)
              | None    ->  dConcl ))
        (search (n-1)))]
    
let auto_tdb n = tclTRY (tclCOMPLETE (search n))
   
let sarch_depth_tdb = ref(5)
			
let dyn_auto_tdb = function 
  | [Integer n] -> auto_tdb n 
  | []          -> auto_tdb !sarch_depth_tdb
  | _           -> bad_tactic_args "AutoTDB"

let h_auto_tdb = hide_tactic "AutoTDB" dyn_auto_tdb
