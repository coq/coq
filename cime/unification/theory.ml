(***************************************************************************

 Equational theories handled by unification and matching modulo

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Signatures

(*
There 3 kinds of unifications in \CiME{}:
\begin{itemize}
\item the [PLAIN] unification is the usual unification modulo;
\item the [AC_COMPLETE] unification provides a representation of the 
  unifiers modulo C and AC by a set of unifiers modulo all the current 
  theories (see \cite{boudet96rta} for more details);
\item the [AC] unification provides a complete set of unifiers modulo C 
  and AC, the others axioms of the theory being ignored.
\end{itemize}
*)

type unif_kind = 
    PLAIN
  | AC_COMPLETE
  | AC_ONLY

let unif_type = ref PLAIN

type 'symbol elem_theory = 
    Empty of 'symbol option
  | C of 'symbol
  | AC of 'symbol
  | ACU of 'symbol * 'symbol
  | ACI of 'symbol
  | AG of 'symbol * 'symbol * 'symbol
  | ACUN of 'symbol * 'symbol * int
  | BR of 'symbol * 'symbol * 'symbol * 'symbol 

exception No_theory

type 'symbol unif_elem_theory =
    'symbol option * 'symbol elem_theory

module OrderedElemTheory =
    struct
      type 'symbol t = 'symbol elem_theory
      let compare = compare
    end

module TheorySet = Ordered_sets.MakePoly (OrderedElemTheory)

module OrderedUnifElemTheory =
    struct
      type 'symbol t = 'symbol unif_elem_theory
      let compare = compare
    end

module UnifTheorySet = Ordered_sets.MakePoly (OrderedUnifElemTheory)

let additive_symbol_of_theory = function
    AC plus -> plus
  | ACU (plus,_) -> plus
  | ACI plus -> plus
  | ACUN (plus,_,_) -> plus
  | AG (plus,_,_) -> plus
  | BR (plus,_,_,_) -> plus
  | _ -> raise Not_found

let unit_symbol_of_theory = function
    ACU (_,one) -> one
  | ACUN (_,one,_) -> one
  | AG (_,one,_) -> one
  | BR (_,zero,_,_) -> zero
  | _ -> raise Not_found

let minus_symbol_of_theory = function
    AG(_,_,minus) -> minus
  | _ -> raise Not_found

(*
let is_the_elem_theory_of_symbol f = function
    Empty symb_set -> SymbolSet.mem f symb_set
  | C plus -> f = plus
  | AC plus -> f = plus
  | ACU (plus,zero) -> (f = plus) or (f = zero)
  | ACI plus -> f = plus
  | AG (plus,zero,minus) -> (f = plus) or (f = zero) or (f = minus)
  | ACUN (plus,zero,n) -> (f = plus) or (f = zero)
  | BR (plus,zero,times,one) -> 
      (f = plus) or (f = zero) or (f = times) or (f = one)

let rec elem_theory_of_symbol f = function
    [] -> raise No_theory
  | elem_th::list_of_elem_ths ->
      if is_the_elem_theory_of_symbol f elem_th
      then elem_th
      else elem_theory_of_symbol f list_of_elem_ths

let elem_theory_of_symbol f th_set = 
  let th_set_for_f = 
    TheorySet.filter (is_the_elem_theory_of_symbol f) th_set in

    if TheorySet.cardinal th_set_for_f = 1
    then TheorySet.choose th_set_for_f
    else assert false

*)
(*
let unif_elem_theory_of_symbol f unif_th_set = 
  let unif_th_set_for_f = 
    UnifTheorySet.filter
      (function
	   P elem_th -> is_the_elem_theory_of_symbol f elem_th 
	 | ACC (Dummy, Empty s) -> SymbolSet.mem f s
	 | ACC (Symbol g, elem_th) ->  f = g
	 | ACO elem_th -> is_the_elem_theory_of_symbol f elem_th
	 | _ -> assert false)
      unif_th_set in

    if UnifTheorySet.cardinal unif_th_set_for_f = 1
    then UnifTheorySet.choose unif_th_set_for_f
    else assert false
*)

(*
let build_plain_unif_theory_from_theory th_set = 
  TheorySet.fold 
    (fun elem_th unif_th_set -> UnifTheorySet.add (P elem_th) unif_th_set) 
    th_set UnifTheorySet.empty

let build_ac_complete_unif_theory_from_theory th_set =
  let (free_symb_set,unif_th_set) = 
    TheorySet.fold 
      (fun elem_th (fss,uts) -> 
       match elem_th with
	   Empty s -> (SymbolSet.union s fss, uts)

	 | C plus -> (fss, UnifTheorySet.add (ACC (Symbol plus,elem_th)) uts)

	 | AC plus -> (fss, UnifTheorySet.add (ACC(Symbol plus,elem_th)) uts)

	 | ACU (plus,zero) -> 
	     (SymbolSet.add zero fss,
	      UnifTheorySet.add (ACC(Symbol plus,elem_th)) uts)

	 | ACI plus -> (fss, UnifTheorySet.add (ACC(Symbol plus,elem_th)) uts)

	 | AG (plus,zero,minus) -> 
	     (SymbolSet.add zero (SymbolSet.add minus fss),
	      UnifTheorySet.add (ACC(Symbol plus,elem_th)) uts)

	 | ACUN (plus,zero,n) -> 
	     (SymbolSet.add zero fss,
	      UnifTheorySet.add (ACC(Symbol plus,elem_th)) uts)

	 | BR (plus,zero,times,one) ->
	     (SymbolSet.add zero (SymbolSet.add one fss),
	      UnifTheorySet.add (ACC(Symbol plus,elem_th))
		(UnifTheorySet.add (ACC(Symbol times,elem_th)) uts)))
 
     th_set (SymbolSet.empty, UnifTheorySet.empty) in

    if SymbolSet.is_empty free_symb_set
    then unif_th_set
    else UnifTheorySet.add (ACC(Dummy, Empty free_symb_set)) unif_th_set

let build_ac_only_unif_theory_from_theory th_set = 
  let (free_symb_set,unif_th_set) = 
    TheorySet.fold 
      (fun elem_th (fss,uts) -> 
       match elem_th with
	   Empty s -> (SymbolSet.union s fss), uts

	 | C plus -> fss, UnifTheorySet.add (ACO elem_th) uts

	 | AC plus -> fss, UnifTheorySet.add (ACO elem_th) uts

	 | ACU (plus,zero) -> 
	     SymbolSet.add zero fss,
	     UnifTheorySet.add (ACO (AC plus)) uts

	 | ACI plus -> fss, UnifTheorySet.add (ACO (AC plus)) uts

	 | AG (plus,zero,minus) -> 
	     SymbolSet.add zero (SymbolSet.add minus fss),
	     UnifTheorySet.add (ACO (AC plus)) uts

	 | ACUN (plus,zero,n) -> 
	     SymbolSet.add zero fss,
	     UnifTheorySet.add (ACO (AC plus)) uts

	 | BR (plus,zero,times,one) ->
	     SymbolSet.add zero (SymbolSet.add one fss),
	     UnifTheorySet.add (ACO (AC plus))
	       (UnifTheorySet.add (ACO (AC times)) uts))
 
     th_set (SymbolSet.empty, UnifTheorySet.empty) in

    if SymbolSet.is_empty free_symb_set
    then unif_th_set
    else UnifTheorySet.add (ACO (Empty free_symb_set)) unif_th_set


let build_unif_theory_from_theory th_set = 
  match !unif_type with 
      PLAIN -> build_plain_unif_theory_from_theory th_set
    | AC_COMPLETE -> build_ac_complete_unif_theory_from_theory th_set
    | AC_ONLY -> build_ac_only_unif_theory_from_theory th_set
*)
  
let elem_theory_from_unif_elem_theory (_,th) = th


let string_of_elem_theory sign = function
    Empty None -> "Empty"
  | Empty (Some f) -> String.concat "" ["Empty(";(sign#string_of_symbol f);")"]
  | C f -> String.concat "" ["C(";(sign#string_of_symbol f);")"]
  | AC f -> String.concat "" ["AC(";(sign#string_of_symbol f);")"]
  | ACU (f,u) -> 
      String.concat "" 
	[
	  "ACU(";
	  (sign#string_of_symbol f);
	  ",";
	  (sign#string_of_symbol u);
	  ")"
	]
  | ACI f -> String.concat "" ["ACI(";(sign#string_of_symbol f);")"]
  | AG (f,u,m) ->
      String.concat "" 
	[
	  "AG(";
	  (sign#string_of_symbol f);
	  ",";
	  (sign#string_of_symbol u);
	  ",";
	  (sign#string_of_symbol m);
	  ")"
	]
  | ACUN (f,u,n) ->
      String.concat "" 
	[
	  "ACUN(";
	  (sign#string_of_symbol f);
	  ",";
	  (sign#string_of_symbol u);
	  ",";
	  (string_of_int n);
	  ")"
	]
  | BR (f,g,h,i) ->
      String.concat ""
	[
	  "BR(";
	  (sign#string_of_symbol f);
	  ",";
	  (sign#string_of_symbol g);
	  ",";
	  (sign#string_of_symbol h);
	  ",";
	  (sign#string_of_symbol i);
	  ")"
	]
   


let string_of_unif_elem_theory sign = function
    None, th -> string_of_elem_theory sign th
  | (Some f), th ->
      String.concat "" 
	["(" ;
	 (sign#string_of_symbol f);
	 ",";
	 (string_of_elem_theory sign th);
	 ")"]


let print_theory sign t = 
  Format.print_string "<theory>";
  Format.print_newline ();
  TheorySet.iter 
    (fun th -> 
       Format.print_string (string_of_elem_theory sign th);
       Format.print_newline ())
    t
    

exception Syntax_error of string

let theory_check sigma = function
    ACU(f,u) as th -> 
      if (sigma#is_ac f) & (sigma#arity u) = 0
      then th
      else 
	raise 
	    (Syntax_error 
	       ("The first symbol " ^ 
		(sigma#string_of_symbol f) ^ 
		" of ACU should be AC and the second symbol " ^ 
		(sigma#string_of_symbol u) ^ 
		" should be of arity 0."))

  | ACI(f) as th ->
      if sigma#is_ac f
      then th
      else 
	raise 
	    (Syntax_error 
	       ("The symbol " ^ 
		(sigma#string_of_symbol f) ^ 
		" of ACI should be AC."))

  | AG(f,u,minus) as th ->
      if (sigma#is_ac f) & (sigma#arity u) = 0 & (sigma#arity minus) = 1
      then th
      else 
	raise 
	  (Syntax_error 
	     ("The first symbol " ^ 
	      (sigma#string_of_symbol f) ^ 
	      " of AG should be AC, the second symbol " ^ 
	      (sigma#string_of_symbol u) ^ 
	      " should be of arity 0 and the third symbol " ^
	      (sigma#string_of_symbol minus) ^
	      " should be of arity 1."))

  | ACUN(f,u,_) as th ->
      if (sigma#is_ac f) & (sigma#arity u) = 0
      then th
      else 
	raise 
	  (Syntax_error 
	     ("The first symbol " ^ 
	      (sigma#string_of_symbol f) ^ 
	      " of ACUN should be AC and the second symbol " ^ 
	      (sigma#string_of_symbol u) ^ 
	      " should be of arity 0."))

  | BR(f,u,g,o) as th ->
      if (sigma#is_ac f) & ((sigma#arity u) = 0) & 
	(sigma#is_ac g) & (sigma#arity o) = 0
      then th
      else 
	raise 
	  (Syntax_error 
	     ("The first symbol " ^ 
	      (sigma#string_of_symbol f) ^ 
	      " of BR should be AC, the second symbol " ^ 
	      (sigma#string_of_symbol u) ^ 
	      " should be of arity 0, the third symbol " ^
	      (sigma#string_of_symbol g) ^
	      " should be of AC and the fourth symbol " ^
	      " should be of arity 0."))
  | _ -> assert false


