(***************************************************************************

  This module provides parameterized functions to complete a rewriting
  system. They are intended to apply as well on terms and on words.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)
open Orderings_generalities

module type AbstractRewriting =
sig
  type symbol
  type signature
  type variables
  type t
  type rule
  type compiled_rules
    
  val smallest_constant : signature -> t ordering -> t
  val a_variable_of_the_term : t -> t

  val size :  signature  ->  t -> int
  val equals :  signature  ->  t ->  t -> bool
  val make_rule : signature  ->  t ->  t ->  rule
  val lhs_of_rule : rule ->  t
  val rhs_of_rule : rule ->  t
  val is_oriented : rule -> bool
      
  val compile : signature ->  rule list ->  compiled_rules
      
      (*
	
	[normalize sigma r t] returns the normal form of [t].
	[force_normalize] does the same but raises
	[Irreducible] if already in normal form. 
	
      *)
      
  val normalize : signature -> variables -> compiled_rules -> t ->  t
      
  exception Irreducible
    
  val force_normalize : signature -> variables -> compiled_rules -> t ->  t
      
      (*
	
	[self_critical_pairs sigma r] returns the list of
	critical pairs of [r] into itself.
	
      *)
      
  val self_critical_pairs : signature ->  rule -> ( t *  t) list
      
      (*
	
	[critical_pairs sigma r1 r2] returns the list of
	critical pairs between [r1] and [r2]. [r1] and [r2] are
	supposed to be different, use [self_critical_pairs] for
	computing critical pairs of a rule into itself.
	
      *)
      
  val critical_pairs : signature ->  rule ->  rule -> (t * t) list
      
      (*
	
	[is_encompassed_by sign p1 p2 t1 t2] returns true whenever
	there exists a context [C[]], and a substitution sigma such
	that [t1=C[p1 sigma]] and  [t2=C[p2 sigma]].
	
      *)
      
  val is_encompassed_by : signature  -> t -> t -> t -> t -> bool
      
      (*
	
	[regular_pair c t1 t2] returns the term [t2']
	such that all variables in [t2] which do not occur in the term 
	[t1] have been substituted by the constant term [c]. It raises 
	[Exit] whenever [t2'] is identical to [t2].
      
      *)
	
  val regular_pair : t -> t -> t -> t
      
      (*
	
	[canonize_pairs l] returns the list [l] where all pairs of
	terms have been put in a kind of canonical form with
	respect to name of variables. This is only for having a
	better printing of rules, it can be the identity
	function.
	
      *)
      
  val canonize_pairs : (t * t) list -> (t * t) list
  val print_t : signature  -> variables -> t -> unit
  val print_equation_set : signature  -> variables -> (t *  t) list -> unit
  val print_rewrite_rule : signature  -> variables ->  rule -> unit
end

open Gen_terms
open Orderings_generalities
open Substitution

module MakeStandardRewriting (Symbol : sig type t end) =
struct
  type symbol = Symbol.t
  type signature = symbol Signatures.signature
  type variables = Variables.user_variables 
  type t = symbol term
  type rule = symbol Rewrite_rules.rewrite_rule
  type compiled_rules = symbol Naive_dnet.dnet
  let smallest_constant sigma o = assert false
  let a_variable_of_the_term _ = assert false
  let size = Gen_terms.size 
  let equals sigma t1 t2 = t1=t2
  let make_rule = Rewrite_rules.make_rule 
  let lhs_of_rule rule = rule.Rewrite_rules.lhs 
  let rhs_of_rule rule = rule.Rewrite_rules.rhs
  let is_oriented rule = rule.Rewrite_rules.is_or
  let self_critical_pairs sigma r = 
    Standard_critical_pairs.self_critical_pairs sigma r
  let critical_pairs sigma r1 r2 = 
    Standard_critical_pairs.critical_pairs sigma r1 r2
  let compile = Naive_dnet.compile
  let normalize sigma vars compiled_rules t = 
    Standard_innermost.innermost_normalize sigma vars
      (Standard_rewriting.compiled_rewrite_at_top compiled_rules) t 
  exception Irreducible
  let force_normalize sigma vars compiled_rules t =
    try 
      Standard_innermost.force_innermost_normalize sigma vars
	(Standard_rewriting.compiled_rewrite_at_top compiled_rules) t 
    with Standard_innermost.Irreducible -> raise Irreducible
	
  let canonize_pairs l =
    List.map
      (function (s,t) -> 
	 let vars_of_s_and_t =
	   Variables.VarSet.union (set_of_variables s) 
	     (set_of_variables t) in
	 let sigma = 
	   Variables.VarMap.map 
	     (function v -> Var v)
	     (Variables.canonical_renaming vars_of_s_and_t) in
	   (apply_term s sigma, apply_term t sigma))
      l

  let is_encompassed_by _ _ _ _ _ = assert false
  let regular_pair _ _ _ = assert false

  let print_t = Gen_terms.print_term
  let print_equation_set = Gen_terms.print_equation_list
  let print_rewrite_rule = Rewrite_rules.print_rewrite_rule
end
  
module MakeACRewriting (Symbol : sig type t end) =
struct
  type symbol = Symbol.t
  type signature = symbol Signatures.signature
  type variables = Variables.user_variables 
  type t = symbol term
  type rule = symbol Rewrite_rules.rewrite_rule
  type compiled_rules = symbol Naive_dnet.dnet
  let smallest_constant sigma o = assert false
  let a_variable_of_the_term _ = assert false
  let size = Gen_terms.size
  let equals = Gen_terms.equals
  let make_rule = Rewrite_rules.make_rule
  let lhs_of_rule rule = rule.Rewrite_rules.lhs 
  let rhs_of_rule rule = rule.Rewrite_rules.rhs
  let is_oriented rule = rule.Rewrite_rules.is_or
  let self_critical_pairs sigma r = 
    Ac_critical_pairs.self_critical_pairs sigma r
  let critical_pairs sigma r1 r2 = 
    Ac_critical_pairs.critical_pairs sigma r1 r2
  let compile = Naive_dnet.compile
  let normalize sigma vars compiled_rules t = 
    Innermost.innermost_normalize sigma 
      (Rewriting.compiled_ac_rewrite_at_top sigma compiled_rules) t 
  exception Irreducible
  let force_normalize sigma vars compiled_rules t = 
    try 
      Innermost.force_innermost_normalize sigma
	(Rewriting.compiled_ac_rewrite_at_top sigma compiled_rules) t 
    with Innermost.Irreducible -> raise Irreducible
	
  let canonize_pairs l =
    List.map
      (function (s,t) -> 
	 let vars_of_s_and_t =
	   Variables.VarSet.union (set_of_variables s) 
	     (set_of_variables t) in
	 let sigma = 
	   Variables.VarMap.map 
	     (function v -> Var v)
	     (Variables.canonical_renaming vars_of_s_and_t) in
	   (apply_term s sigma, apply_term t sigma))
      l
      
  let is_encompassed_by _ _ _ _ _ = assert false
  let regular_pair _ _ _ = assert false

  let print_t = Gen_terms.print_term
  let print_equation_set = Gen_terms.print_equation_list
  let print_rewrite_rule = Rewrite_rules.print_rewrite_rule
end


module type TermOrdering =
sig
  type t 
  val o : t ordering
end

module MakeOrderedRewriting (Symbol : sig type t end) 
  (TO : TermOrdering with type t = Symbol.t Gen_terms.term) =
struct
  type symbol = Symbol.t
  type signature = Symbol.t Signatures.signature
  type variables = Variables.user_variables
  type t = Symbol.t Gen_terms.term
  type rule = Symbol.t Rewrite_rules.rewrite_rule
  type compiled_rules = Symbol.t Naive_dnet.dnet
			  
  let smallest_constant sigma o = 
    let precedence f g = o (Term (f,[])) (Term (g,[])) in
    let c = sigma#smallest_constant precedence in
      Term (c,[])

  let rec a_variable_of_the_term = function
      Var x as var_x -> var_x
    | Term (_,l) -> a_variable_of_the_list_of_term l
  
  and a_variable_of_the_list_of_term = function
      [] -> raise Not_found
    | t::l ->
	try 
	  a_variable_of_the_term t
	with 
	    Not_found -> a_variable_of_the_list_of_term l
	
  let size = Gen_terms.size 
  let equals sigma t1 t2 = t1=t2
  let make_rule sigma t1 t2 = 
    match TO.o t1 t2  with 
	Greater_than -> Rewrite_rules.make_rule sigma t1 t2
      | Less_than ->  Rewrite_rules.make_rule sigma t2 t1
      | _ ->  Rewrite_rules.make_non_oriented_rule sigma t1 t2
	    
  let lhs_of_rule rule = rule.Rewrite_rules.lhs 
  let rhs_of_rule rule = rule.Rewrite_rules.rhs
  let is_oriented rule = rule.Rewrite_rules.is_or

  let self_critical_pairs sigma rule = 
    Standard_critical_pairs.self_critical_pairs sigma rule
      
  let critical_pairs sigma r1 r2 = 
    Standard_critical_pairs.critical_pairs sigma r1 r2
      
  let compile = Naive_dnet.compile
		  
  let rec ordered_rewrite_at_top sign ruleset t =
    match ruleset with
	[] -> raise Not_found
      | r::s ->
	  try
	    let sigma = Standard_matching.matching r.Rewrite_rules.lhs t in
	    let t' = Substitution.apply_term r.Rewrite_rules.rhs sigma in
	      if r.Rewrite_rules.is_or or (TO.o t t' = Greater_than)
	      then (r.Rewrite_rules.rhs,sigma)
	      else ordered_rewrite_at_top sign s t
	  with Standard_matching.No_match -> ordered_rewrite_at_top sign s t 

  let normalize sign vars compiled_rules t = 
    let red t = 
      let ruleset = Naive_dnet.discriminate compiled_rules t in 
	ordered_rewrite_at_top sign ruleset t in
      Innermost.innermost_normalize sign red t 

  exception Irreducible
    
  let force_normalize sign vars compiled_rules t = 
    let red t = 
      let ruleset = Naive_dnet.discriminate compiled_rules t in 
	ordered_rewrite_at_top sign ruleset t in
      try
	Innermost.force_innermost_normalize sign red t 
      with Innermost.Irreducible -> raise Irreducible
	
  let canonize_pairs l =
    List.map
      (function (s,t) -> 
	 let vars_of_s_and_t =
	   Variables.VarSet.union (set_of_variables s) 
	     (set_of_variables t) in
	 let sigma = 
	   Variables.VarMap.map 
	     (function v -> Var v)
	     (Variables.canonical_renaming vars_of_s_and_t) in
	   (apply_term s sigma, apply_term t sigma))
      l
      
  let is_encompassed_by _ p1 p2 t1 t2 =
    let is_an_instance_of_p1_p2 s1 s2 =
      try
	let sigma1 = Standard_matching.matching p1 t1 
	and sigma2 = Standard_matching.matching p2 t2 in
	let _ = Substitution.merge_substs sigma1 sigma2 in
	  true
      with 
	  Substitution.Conflict 
	| Standard_matching.No_match -> false in
    let rec is_comp_rec s1 s2 =
      if is_an_instance_of_p1_p2 s1 s2
      then true
      else 
	match s1,s2 with
	    Term(f1,l1), Term(f2,l2) ->
	      if f1 <> f2
	      then false
	      else 
		begin
		  try
		    List.for_all2 
		      (fun u1 u2 -> u1=u2 or is_comp_rec u1 u2) l1 l2
		  with Invalid_argument _ -> false
		end
	  | _,_ -> false in
      is_comp_rec t1 t2

  let regular_pair = Gen_terms.build_a_term_for_a_right_regular_pair 

  let print_t = Gen_terms.print_term
  let print_equation_set = Gen_terms.print_equation_list
  let print_rewrite_rule = Rewrite_rules.print_rewrite_rule
end
  
module MakeOrderedACRewriting (Symbol : sig type t end) 
  (TO : TermOrdering with type t = Symbol.t Gen_terms.term) =
struct
  type symbol = Symbol.t
  type signature = symbol Signatures.signature
  type variables = Variables.user_variables
  type t = symbol Gen_terms.term
  type rule = symbol Rewrite_rules.rewrite_rule
  type compiled_rules = symbol Naive_dnet.dnet
			  
  let smallest_constant sigma o = 
    let precedence f g = o (Term (f,[])) (Term (g,[])) in
    let c = sigma#smallest_constant precedence in
      Term (c,[])

  let rec a_variable_of_the_term = function
      Var x as var_x -> var_x
    | Term (_,l) -> a_variable_of_the_list_of_term l
  
  and a_variable_of_the_list_of_term = function
      [] -> raise Not_found
    | t::l ->
	try 
	  a_variable_of_the_term t
	with 
	    Not_found -> a_variable_of_the_list_of_term l

  let size = Gen_terms.size 
  let equals = Gen_terms.equals
  let make_rule sigma t1 t2 = 
    match TO.o t1 t2  with 
	Greater_than -> Rewrite_rules.make_rule sigma t1 t2
      | Less_than ->  Rewrite_rules.make_rule sigma t2 t1
      | _ ->  Rewrite_rules.make_non_oriented_rule sigma t1 t2
	    
  let lhs_of_rule rule = rule.Rewrite_rules.lhs 
  let rhs_of_rule rule = rule.Rewrite_rules.rhs
  let is_oriented rule = rule.Rewrite_rules.is_or

  let self_critical_pairs sigma rule = 
    Ac_critical_pairs.self_critical_pairs sigma rule
      
  let critical_pairs sigma r1 r2 = 
    Ac_critical_pairs.critical_pairs sigma r1 r2
      
  let compile = Naive_dnet.compile
		  
  let rec ordered_ac_rewrite_at_top sign ruleset t =
    match ruleset with
	[] -> raise Not_found
      | r::s ->
	  try
	    let sigma = Matching.matching sign r.Rewrite_rules.lhs t in
	    let t' = Substitution.apply_term r.Rewrite_rules.rhs sigma in
	      if r.Rewrite_rules.is_or or (TO.o t t' = Greater_than)
	      then (r.Rewrite_rules.rhs,sigma)
	      else raise Matching.No_match
	  with Matching.No_match -> 
	    begin
	      match r.Rewrite_rules.ext with 
		  None -> ordered_ac_rewrite_at_top sign s t 
		| Some (lhs,rhs) ->
		    try
		      let sigma = Matching.matching sign lhs t in
		      let t' = Substitution.apply_term rhs sigma in
			if r.Rewrite_rules.is_or or 
			  (TO.o t t' = Greater_than)
			then (rhs,sigma)
			else raise Matching.No_match
		    with Matching.No_match -> 
		      ordered_ac_rewrite_at_top sign s t
	    end

  let normalize sign vars compiled_rules t =
    let red t = 
      let ruleset = Naive_dnet.discriminate compiled_rules t in 
	ordered_ac_rewrite_at_top sign ruleset t in
      Innermost.innermost_normalize sign red t 

  exception Irreducible
    
  let force_normalize sign vars compiled_rules t = 
    let red t = 
      let ruleset = Naive_dnet.discriminate compiled_rules t in 
	ordered_ac_rewrite_at_top sign ruleset t in
      try
	Innermost.force_innermost_normalize sign red t 
      with Innermost.Irreducible -> raise Irreducible
	
  let canonize_pairs l =
    List.map
      (function (s,t) -> 
	 let vars_of_s_and_t =
	   Variables.VarSet.union (set_of_variables s) 
	     (set_of_variables t) in
	 let sigma = 
	   Variables.VarMap.map 
	     (function v -> Var v)
	     (Variables.canonical_renaming vars_of_s_and_t) in
	   (apply_term s sigma, apply_term t sigma))
      l
      
  let is_encompassed_by sign p1 p2 t1 t2 =
    let is_an_instance_of p1 p2 s1 s2 =
      try
	let sigma1 = Matching.matching sign p1 t1 
	and sigma2 = Matching.matching sign p2 t2 in
	let _ = Substitution.merge_substs sigma1 sigma2 in
	  true
      with 
	  Substitution.Conflict 
	| Matching.No_match -> false in
    let rec remove_term s = function
	[] -> raise Not_found
      | u::l -> 
	  if Gen_terms.equals sign s u 
	  then l 
	  else u :: (remove_term s l) in
    let rec remove_common_terms = function
	([],_) as res -> res
      | (_,[]) as res -> res
      | (s1::l1), l2 ->
	  try
	    let l2' = remove_term s1 l2 in
	      remove_common_terms (l1,l2')
	  with Not_found ->
	    let (l1',l2') = remove_common_terms (l1,l2) in
	      (s1::l1',l2') in
    let rec is_comp_rec s1 s2 =
      if is_an_instance_of p1 p2 s1 s2
      then true
      else 
	match s1,s2 with
	    Term(f1,l1), Term(f2,l2) ->
	      if f1 <> f2
	      then false
	      else 
		begin
		  if sign#is_ac f1
		  then 
		    let vars_of_p1_p2 = 
		      Variables.VarSet.union (Gen_terms.set_of_variables p1)
			(Gen_terms.set_of_variables p2) in
		    let x = Var(Variables.var_outside_set (vars_of_p1_p2)) in
		    let p1_plus_x = 
		      Gen_terms. head_flatten_term sign 
			(Gen_terms.Term(f1,[x;p1]))
		    and p2_plus_x = 
		      Gen_terms. head_flatten_term sign 
			(Gen_terms.Term(f1,[x;p2])) in
		    if is_an_instance_of p1_plus_x p2_plus_x s1 s2
		    then true
		    else
		      begin
			match remove_common_terms (l1,l2) with
			    [u1],[u2] -> is_comp_rec u1 u2
			  | _,_ -> false
		      end
		  else
		    match remove_common_terms (l1,l2) with
			[u1],[u2] -> is_comp_rec u1 u2
		      | _,_ -> false
		end
	  | _,_ -> false in
      is_comp_rec t1 t2

  let regular_pair = Gen_terms.build_a_term_for_a_right_regular_pair

  let print_t = Gen_terms.print_term
  let print_equation_set = Gen_terms.print_equation_list
  let print_rewrite_rule = Rewrite_rules.print_rewrite_rule
end
  
module MakeWordRewriting (Symbol : sig type t end) =
struct
  type symbol = Symbol.t
  type signature = symbol String_signatures.word_signature
  type variables = unit 
  type t = symbol Words.word
  type rule = symbol String_rewriting.rewrite_rule
  type compiled_rules = symbol String_rewriting.compiled_srs
  let smallest_constant sigma o = assert false
  let a_variable_of_the_term _ = assert false
  let size sigma t = Words.length t
  let equals sigma = (=)
  let make_rule sigma s t = (s,t)
  let lhs_of_rule = fst
  let rhs_of_rule = snd
  let is_oriented rule = assert false
  let self_critical_pairs sigma r = 
    String_unification.superpose r r
  let critical_pairs sigma r1 r2 = 
    (String_unification.superpose r1 r2) @
    (String_unification.superpose r2 r1)
    
  let compile sigma = String_rewriting.compile_srs
  let normalize sigma vars compiled_rules t = 
    String_rewriting.compiled_normalize compiled_rules t 
  exception Irreducible
  let force_normalize sigma vars compiled_rules t = 
    let t' = String_rewriting.compiled_normalize compiled_rules t in
      if t = t'
      then raise Irreducible
      else t'
	
  let canonize_pairs l = l
			   
  let is_encompassed_by _ _ _ _ _ = assert false
  let regular_pair _ _ _ = assert false

  let print_t sigma () t = Words.pretty_print sigma t
  let print_equation_set sigma () = 
    let print_equation (s,t) =
      Printf.printf "@[<hov>";
      Words.pretty_print sigma s;
      Printf.printf "@ =@ ";
      Words.pretty_print sigma t;
      Printf.printf "@]" in
	
    let print_equation_list = function
	[]   -> (print_string "{}")
      | r::l ->
	  let rec print_end_list n = function
	      [] -> 
		begin
		  print_string " }";
		  Format.print_break 1 0;
		  print_string "(";
		  print_int n;
		  print_string " equation(s))"                 
		end
	    | (r::l) -> 
		begin
		  print_string  ",";
		  Format.force_newline ();
		  print_equation r;
		  print_end_list (succ n) l
		end
	  in 
	    begin
	      print_string "{ ";
	      Format.open_hovbox 0;
	      print_equation r;
	      print_end_list 1 l;
	      Format.close_box ()
	    end in
      print_equation_list
	
  let print_rewrite_rule sigma () r = 
    String_rewriting.pretty_print sigma [r]
      
    let print_t sigma () t = Words.pretty_print sigma t
        let print_equation_set sigma () = 
      let print_equation (s,t) =
	Printf.printf "@[<hov>";
	Words.pretty_print sigma s;
	Printf.printf "@ =@ ";
	Words.pretty_print sigma t;
	Printf.printf "@]" in
	
      let print_equation_list = function
	  []   -> (print_string "{}")
	| r::l ->
	    let rec print_end_list n = function
		[] -> 
		  begin
		    print_string " }";
		    Format.print_break 1 0;
		    print_string "(";
		    print_int n;
		    print_string " equation(s))"                 
		  end
	      | (r::l) -> 
		  begin
		    print_string  ",";
		    Format.force_newline ();
		    print_equation r;
		    print_end_list (succ n) l
		  end
	    in 
	      begin
		print_string "{ ";
		Format.open_hovbox 0;
		print_equation r;
		print_end_list 1 l;
		Format.close_box ()
	      end in
	print_equation_list

	let print_rewrite_rule sigma () r = 
	  String_rewriting.pretty_print sigma [r]

  end

module MakePWordRewriting =
  struct
    type symbol = unit
    type signature = Parameterized_signatures.parameterized_signature
    type variables = unit
    type t = Parameterized_words.word
    type rule = Parameterized_rewriting.rewrite_rule
    type compiled_rules = Parameterized_rewriting.srs
    let size sigma t = 1
    let equals sigma = Parameterized_similitude.test_weak_similitude 
    let make_rule sigma s t = match (s,t) with 
	 { Parameterized_words.env = e1;
	   Parameterized_words.letters = l1 ;
	   Parameterized_words.constr = c1
	 },
	 { Parameterized_words.env = e2;
	   Parameterized_words.letters = l2 ;
	   Parameterized_words.constr = c2
	 } -> {Parameterized_rewriting.rrule = (l1,l2); 
	       Parameterized_rewriting.rconstr = Linear_constraints.conj c1 c2;
	       Parameterized_rewriting.renv = e1@e2}
	 
    let lhs_of_rule r = 
      { Parameterized_words.env = r.Parameterized_rewriting.renv;
	Parameterized_words.letters = fst r.Parameterized_rewriting.rrule ;
	Parameterized_words.constr = r.Parameterized_rewriting.rconstr
      }
    let rhs_of_rule r=
      { Parameterized_words.env = r.Parameterized_rewriting.renv;
	Parameterized_words.letters = snd r.Parameterized_rewriting.rrule ;
	Parameterized_words.constr = r.Parameterized_rewriting.rconstr
      }

    let self_critical_pairs sigma r = 
      Parameterized_rewriting.critical_pairs r r

    let critical_pairs sigma r1 r2 = 
      (Parameterized_rewriting.critical_pairs r1 r2)@
      (Parameterized_rewriting.critical_pairs r2 r1)

    let compile sigma x = x

    let normalize sigma var compiled_rules t = 
      Parameterized_rewriting.normalize compiled_rules t 

    exception Irreducible

    let force_normalize sigma var compiled_rules t = 
      if Parameterized_rewriting.is_nf compiled_rules t then raise Irreducible
      else Parameterized_rewriting.normalize compiled_rules t


    let canonize_pairs l = l
      
    let print_t sigma () t = User_parameterized_words.pretty_print t
    let print_equation_set sigma v eqs = 
      Format.printf "@[{@ ";
      List.iter (function (l,r) -> 
		   Format.printf "@[";
		   print_t () () l ; 
		   Format.printf "@ =@ ";
		   print_t () () r ; 
		   Format.printf "@ ;@]";
		) eqs;
      Format.printf "@ }@]@."
    let print_equation_list l = 
      print_equation_set () () l
    let print_rewrite_rule sigma () r =
      Parameterized_rewriting.pretty_print [r]

  let smallest_constant sigma o = assert false
  let a_variable_of_the_term _ = assert false
  let is_encompassed_by _ _ _ _ _ = assert false
  let regular_pair _ _ _ = assert false
  let is_oriented rule = assert false
  end

(*i
Local Variables:
compile-command: "make -C .. opt"
End:
i*)
