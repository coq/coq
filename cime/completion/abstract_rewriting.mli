(***************************************************************************

  This module provides parameterized functions to complete a rewriting
  system. They are intended to apply as well on terms and on words.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Orderings_generalities

module type TermOrdering =
  sig
    type t 
    val o : t ordering
  end


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

    val size : signature  -> t -> int
    val equals : signature  -> t -> t -> bool
    val make_rule : signature  -> t -> t -> rule
    val lhs_of_rule : rule -> t
    val rhs_of_rule : rule -> t
    val is_oriented : rule -> bool

    val compile : signature -> rule list -> compiled_rules

	  (*
	    
	    [normalize sigma r t] returns the normal form of [t].
	    [force_normalize] does the same but raises
	    [Irreducible] if already in normal form. 

	  *)

    val normalize : signature -> variables -> compiled_rules -> t -> t

    exception Irreducible

    val force_normalize : signature -> variables -> compiled_rules -> t -> t

	(*

	  [self_critical_pairs sigma r] returns the list of
	  critical pairs of [r] into itself.

	*)

    val self_critical_pairs : signature -> rule -> (t * t) list

	(*

	  [critical_pairs sigma r1 r2] returns the list of
	  critical pairs between [r1] and [r2]. [r1] and [r2] are
	  supposed to be different, use [self_critical_pairs] for
	  computing critical pairs of a rule into itself.

	*)

    val critical_pairs : signature ->  rule ->  rule -> ( t *  t) list

	(*
	  [is_encompassed_by sign p1 p2 t1 t2] returns true whenever
	  there exists a context [C[]], and a substitution sigma such
	  that [t1=C[p1 sigma]] and  [t2=C[p2 sigma]].
	  
	*)

    val is_encompassed_by : signature -> t -> t -> t -> t -> bool
	
	(*
	  [regular_pair c t1 t2] returns the term [t2']
	  such that all variables in [t2] which do not occur in the term 
	  [t1] have been substituted by the constant term [c]. It raises 
	[Not_found] whenever [t2'] is identical to [t2].
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
    val print_t :signature  -> variables ->  t -> unit
    val print_equation_set : signature  -> variables -> ( t *  t) list -> unit
    val print_rewrite_rule : signature  -> variables ->  rule -> unit
  end


module MakeStandardRewriting : functor (Symbol : sig type t end) ->
  (AbstractRewriting
   with type symbol =  Symbol.t
   and type signature = Symbol.t Signatures.signature
   and type variables = Variables.user_variables
   and type t = Symbol.t Gen_terms.term
   and type rule = Symbol.t Rewrite_rules.rewrite_rule)

module MakeOrderedRewriting : functor (Symbol : sig type t end) ->
  functor (TO : TermOrdering 
	   with type t = Symbol.t Gen_terms.term) ->
  (AbstractRewriting
   with type symbol =  Symbol.t
   and type signature = Symbol.t Signatures.signature
   and type variables = Variables.user_variables
   and type t = Symbol.t Gen_terms.term
   and type rule = Symbol.t Rewrite_rules.rewrite_rule)

module MakeACRewriting : functor (Symbol : sig type t end) ->
  (AbstractRewriting
   with type symbol =  Symbol.t
   and type signature = Symbol.t Signatures.signature
   and type variables = Variables.user_variables
   and type t = Symbol.t Gen_terms.term
   and type rule = Symbol.t Rewrite_rules.rewrite_rule)
  
module MakeOrderedACRewriting : functor (Symbol : sig type t end) ->
  functor (TO : TermOrdering 
	   with type t = Symbol.t Gen_terms.term) ->
  (AbstractRewriting
   with type symbol =  Symbol.t
   and type signature = Symbol.t Signatures.signature
   and type variables = Variables.user_variables
   and type t = Symbol.t Gen_terms.term
   and type rule = Symbol.t Rewrite_rules.rewrite_rule)

module MakeWordRewriting : functor (Symbol : sig type t end) ->
  (AbstractRewriting
   with type symbol =  Symbol.t
   and type signature = Symbol.t String_signatures.word_signature
   and type variables = unit
   and type t = Symbol.t Words.word
   and type rule = Symbol.t String_rewriting.rewrite_rule)

module MakePWordRewriting : 
  (AbstractRewriting
   with 
     type signature = Parameterized_signatures.parameterized_signature
   and type variables = unit
   and type t = Parameterized_words.word
   and type rule = Parameterized_rewriting.rewrite_rule)

(*i
Local Variables:
compile-command: "make -C .. opt"
End:
i*)




	




