(* This file contains an ml version of drag-and-drop. *)

(* #use "/net/home/bertot/experiments/pcoq/src/dad/dad.ml" *)

open Names;;
open Term;;
open Rawterm;;
open Util;;
open Environ;;
open Tactics;;
open Tacticals;;
open Pattern;;
open Matching;;
open Reduction;;
open Constrextern;;
open Constrintern;;
open Vernacinterp;;
open Libnames;;
open Nametab

open Proof_type;;
open Proof_trees;;
open Tacmach;;
open Typing;;
open Pp;;

open Paths;;

open Topconstr;;
open Genarg;;
open Tacexpr;;
open Rawterm;;

(* In a first approximation, drag-and-drop rules are like in CtCoq
   1/ a pattern,
   2,3/ Two paths: start and end positions,
   4/ the degree: the number of steps the algorithm should go up from the
      longest common prefix,
   5/ the tail path: the suffix of the longest common prefix of length the
      degree,
   6/ the command pattern, where meta variables are represented by objects
      of the form Node(_,"META"; [Num(_,i)])
*)


type dad_rule =
    constr_expr * int list * int list * int * int list
    * raw_atomic_tactic_expr;;

(* This value will be used systematically when constructing objects *)

let zz = Util.dummy_loc;;

(* This function receives a length n, a path p, and a term and returns a
   couple whose first component is the subterm designated by the prefix
   of p of length n, and the second component is the rest of the path *)

let rec get_subterm  (depth:int) (path: int list) (constr:constr) =
  match depth, path, kind_of_term constr with
    0, l, c -> (constr,l)
  | n, 2::a::tl, App(func,arr) -> 
      get_subterm (n - 2) tl arr.(a-1)
  | _,l,_ -> failwith (int_list_to_string 
                        "wrong path or wrong form of term"
                        l);;

(* This function maps a substitution on an abstract syntax tree.  The
   first argument, an object of type env, is necessary to
   transform constr terms into abstract syntax trees.  The second argument is
   the substitution, a list of pairs linking an integer and a constr term. *)

let rec map_subst (env :env) (subst:patvar_map) = function
  | CPatVar (_,(_,i)) ->
      let constr = List.assoc i subst in
      extern_constr false env constr
  | x -> map_constr_expr_with_binders (fun _ x -> x) (map_subst env) subst x;;

let map_subst_tactic env subst = function
  | TacExtend (loc,("Rewrite" as x),[b;cbl]) ->
      let c,bl = out_gen rawwit_constr_with_bindings cbl in
      assert (bl = NoBindings);
      let c = (map_subst env subst c,NoBindings) in
      TacExtend (loc,x,[b;in_gen rawwit_constr_with_bindings c])
  | _ -> failwith "map_subst_tactic: unsupported tactic"

(* This function is really the one that is important. *)
let rec find_cmd (l:(string * dad_rule) list) env constr p p1 p2 =
  match l with
    [] -> failwith "nothing happens"
  | (name, (pat, p_f, p_l, deg, p_r, cmd))::tl ->
     let length = List.length p in
     try
       if deg > length then
         failwith "internal"
       else
         let term_to_match, p_r = 
             try 
                get_subterm (length - deg) p constr
             with
                Failure s -> failwith "internal" in
         let _, constr_pat = 
            intern_constr_pattern Evd.empty (Global.env())
               ((*ct_to_ast*) pat) in
         let subst = matches constr_pat term_to_match in
         if (is_prefix p_f (p_r@p1)) & (is_prefix p_l (p_r@p2)) then
           TacAtom (zz, map_subst_tactic env subst cmd)
         else
	   failwith "internal"
     with
       Failure "internal" -> find_cmd tl env constr p p1 p2
     | PatternMatchingFailure -> find_cmd tl env constr p p1 p2;;


let dad_rule_list = ref ([]: (string * dad_rule) list);;

(*
(* \\ This function is also used in pbp. *)
let rec tactic_args_to_ints = function
    [] -> []
  | (Integer n)::l -> n::(tactic_args_to_ints l)
  | _ -> failwith "expecting only numbers";;

(* We assume that the two lists of integers for the tactic are simply
   given in one list, separated by a dummy tactic. *)
let rec part_tac_args l = function
    [] -> l,[]
  | (Tacexp a)::tl -> l, (tactic_args_to_ints tl)
  | (Integer n)::tl -> part_tac_args (n::l) tl
  | _ -> failwith "expecting only numbers and the word \"to\"";;


(* The dad_tac tactic takes a display_function as argument.  This makes
   it possible to use it in pcoq, but also in other contexts, just by
   changing the output routine. *)
let dad_tac display_function = function
   l -> let p1, p2 = part_tac_args [] l in
        (function g ->
           let (p_a, p1prime, p2prime) = decompose_path (List.rev p1,p2) in
           (display_function 
            (find_cmd (!dad_rule_list) (pf_env g)
	       (pf_concl g) p_a p1prime p2prime));
            tclIDTAC g);;
*)
let dad_tac display_function p1 p2 g =
  let (p_a, p1prime, p2prime) = decompose_path (p1,p2) in
  (display_function 
    (find_cmd (!dad_rule_list) (pf_env g) (pf_concl g) p_a p1prime p2prime));
  tclIDTAC g;;

(* Now we enter dad rule list management. *)

let add_dad_rule name patt p1 p2 depth pr command =
  dad_rule_list := (name, 
		    (patt, p1, p2, depth, pr, command))::!dad_rule_list;;

let rec remove_if_exists name = function
    [] -> false, []
  | ((a,b) as rule1)::tl -> if a = name then 
               let result1, l = (remove_if_exists name tl) in
               true, l
             else
               let result1, l = remove_if_exists name tl in
               result1, (rule1::l);;

let remove_dad_rule name =
  let result1, result2 = remove_if_exists name !dad_rule_list in
  if result1 then
    failwith("No such name among the drag and drop rules " ^ name)
  else
     dad_rule_list := result2;;

let dad_rule_names () =
    List.map (function (s,_) -> s) !dad_rule_list;;

(* this function is inspired from matches_core in pattern.ml *)
let constrain ((n : patvar),(pat : constr_pattern)) sigma =
  if List.mem_assoc n sigma then
    if pat = (List.assoc n sigma) then sigma
    else failwith "internal"
  else 
    (n,pat)::sigma
    
(* This function is inspired from matches_core in pattern.ml *)
let more_general_pat pat1 pat2 = 
  let rec match_rec sigma p1 p2 =
    match p1, p2 with
      | PMeta (Some n), m -> constrain (n,m) sigma

      | PMeta None, m -> sigma

      | PRef (VarRef sp1), PRef(VarRef sp2) when sp1 = sp2 -> sigma

      | PVar v1, PVar v2 when v1 = v2 -> sigma

      | PRef ref1, PRef ref2 when ref1 = ref2 -> sigma

      | PRel n1, PRel n2 when n1 = n2 -> sigma

      | PSort (RProp c1), PSort (RProp c2) when c1 = c2 -> sigma

      | PSort (RType _), PSort (RType _) -> sigma

      | PApp (c1,arg1), PApp (c2,arg2) ->
        (try array_fold_left2 match_rec (match_rec sigma c1 c2) arg1 arg2
         with Invalid_argument _ -> failwith "internal")
      | _ -> failwith "unexpected case in more_general_pat" in 
  try let _ = match_rec [] pat1 pat2 in true
  with Failure "internal" -> false;;

let more_general r1 r2 =
  match r1,r2 with
    (_,(patt1,p11,p12,_,_,_)),
    (_,(patt2,p21,p22,_,_,_)) ->
	(more_general_pat patt1 patt2) &
      (is_prefix p11 p21) & (is_prefix p12 p22);;

let not_less_general r1 r2 = 
  not (match r1,r2 with
    (_,(patt1,p11,p12,_,_,_)),
    (_,(patt2,p21,p22,_,_,_)) ->
	(more_general_pat patt1 patt2) &
      (is_prefix p21 p11) & (is_prefix p22 p12));;

let rec add_in_list_sorting rule1 = function
    [] -> [rule1]
  | (b::tl) as this_list ->
      if more_general rule1 b  then
	b::(add_in_list_sorting rule1 tl)
      else if not_less_general rule1 b then
	let tl2 = add_in_list_sorting_aux rule1 tl in
	(match tl2 with
	  [] -> rule1::this_list
	| _ -> b::tl2)
      else
	rule1::this_list
and add_in_list_sorting_aux rule1 = function
    [] -> []
  | b::tl -> 
      if more_general rule1 b then
      	b::(add_in_list_sorting rule1 tl)
      else
	let tl2 = add_in_list_sorting_aux rule1 tl in
	(match tl2 with
	  [] -> []
	| _ -> rule1::tl2);;

let rec sort_list = function
    [] -> [] 
  | a::l -> add_in_list_sorting a (sort_list l);;

let mk_dad_meta n = CPatVar (zz,(true,Nameops.make_ident "DAD" (Some n)));;
let mk_rewrite lr ast =
  let b = in_gen rawwit_bool lr in
  let cb = in_gen rawwit_constr_with_bindings (ast,NoBindings) in
  TacExtend (zz,"Rewrite",[b;cb])

open Vernacexpr

let dad_status = ref false;;

let start_dad () = dad_status := true;;

let add_dad_rule_fn name pat p1 p2 tac =
  let pr = match decompose_path (p1, p2) with pr, _, _ -> pr in
  add_dad_rule name pat p1 p2 (List.length pr) pr tac;;

(* To be parsed by camlp4

(*i camlp4deps: "parsing/grammar.cma" i*)

VERNAC COMMAND EXTEND AddDadRule
  [ "Add" "Dad" "Rule" string(name) constr(pat)
    "From" natural_list(p1) "To" natural_list(p2) tactic(tac) ] ->
  [ add_dad_rule_fn name pat p1 p2 tac ]
END

*)

let mk_id s = mkIdentC (id_of_string s);;
let mkMetaC = mk_dad_meta;;

add_dad_rule "distributivity-inv"
(mkAppC(mk_id("mult"),[mkAppC(mk_id("plus"),[mkMetaC(4);mkMetaC(3)]);mkMetaC(2)]))
[2; 2]
[2; 1]
1
[2]
(mk_rewrite true (mkAppC(mk_id( "mult_plus_distr"),[(mk_dad_meta 4) ;(mk_dad_meta 3) ;(mk_dad_meta 2) ])));

add_dad_rule "distributivity1-r"
(mkAppC(mk_id("plus"),[mkAppC(mk_id("mult"),[mkMetaC(4);mkMetaC(2)]);mkAppC(mk_id("mult"),[mkMetaC(3);mkMetaC(2)])]))
[2; 2; 2; 2]
[]
0
[]
(mk_rewrite false (mkAppC(mk_id("mult_plus_distr"),[(mk_dad_meta 4) ;(mk_dad_meta 3) ;(mk_dad_meta 2) ])));

add_dad_rule "distributivity1-l"
(mkAppC(mk_id("plus"),[mkAppC(mk_id("mult"),[mkMetaC(4);mkMetaC(2)]);mkAppC(mk_id("mult"),[mkMetaC(3);mkMetaC(2)])]))
[2; 1; 2; 2]
[]
0
[]
(mk_rewrite false (mkAppC(mk_id( "mult_plus_distr"),[(mk_dad_meta 4) ;(mk_dad_meta 3) ;(mk_dad_meta 2) ])));

add_dad_rule "associativity"
(mkAppC(mk_id("plus"),[mkAppC(mk_id("plus"),[mkMetaC(4);mkMetaC(3)]);mkMetaC(2)]))
[2; 1]
[]
0
[]
(mk_rewrite true (mkAppC(mk_id( "plus_assoc_r"),[(mk_dad_meta 4) ;(mk_dad_meta 3) ;(mk_dad_meta 2) ])));

add_dad_rule "minus-identity-lr"
(mkAppC(mk_id("minus"),[mkMetaC(2);mkMetaC(2)]))
[2; 1]
[2; 2]
1
[2]
(mk_rewrite false (mkAppC(mk_id( "minus_n_n"),[(mk_dad_meta 2) ])));

add_dad_rule "minus-identity-rl"
(mkAppC(mk_id("minus"),[mkMetaC(2);mkMetaC(2)]))
[2; 2]
[2; 1]
1
[2]
(mk_rewrite false (mkAppC(mk_id( "minus_n_n"),[(mk_dad_meta 2) ])));

add_dad_rule "plus-sym-rl"
(mkAppC(mk_id("plus"),[mkMetaC(3);mkMetaC(2)]))
[2; 2]
[2; 1]
1
[2]
(mk_rewrite true (mkAppC(mk_id( "plus_sym"),[(mk_dad_meta 3) ;(mk_dad_meta 2) ])));

add_dad_rule "plus-sym-lr"
(mkAppC(mk_id("plus"),[mkMetaC(3);mkMetaC(2)]))
[2; 1]
[2; 2]
1
[2]
(mk_rewrite true (mkAppC(mk_id( "plus_sym"),[(mk_dad_meta 3) ;(mk_dad_meta 2) ])));

add_dad_rule "absorb-0-r-rl"
(mkAppC(mk_id("plus"),[mkMetaC(2);mk_id("O")]))
[2; 2]
[1]
0
[]
(mk_rewrite false (mkAppC(mk_id( "plus_n_O"),[(mk_dad_meta 2) ])));

add_dad_rule "absorb-0-r-lr"
(mkAppC(mk_id("plus"),[mkMetaC(2);mk_id("O")]))
[1]
[2; 2]
0
[]
(mk_rewrite false (mkAppC(mk_id( "plus_n_O"),[(mk_dad_meta 2) ])));

add_dad_rule "plus-permute-lr"
(mkAppC(mk_id("plus"),[mkMetaC(4);mkAppC(mk_id("plus"),[mkMetaC(3);mkMetaC(2)])]))
[2; 1]
[2; 2; 2; 1]
1
[2]
(mk_rewrite true (mkAppC(mk_id( "plus_permute"),[(mk_dad_meta 4) ;(mk_dad_meta 3) ;(mk_dad_meta 2) ])));

add_dad_rule "plus-permute-rl"
(mkAppC(mk_id("plus"),[mkMetaC(4);mkAppC(mk_id("plus"),[mkMetaC(3);mkMetaC(2)])]))
[2; 2; 2; 1]
[2; 1]
1
[2]
(mk_rewrite true (mkAppC(mk_id( "plus_permute"),[(mk_dad_meta 4) ;(mk_dad_meta 3) ;(mk_dad_meta 2) ])));;

vinterp_add "StartDad"
   (function
     | [] ->
       (function () -> start_dad())
     | _ -> errorlabstrm "StartDad" (mt()));;
