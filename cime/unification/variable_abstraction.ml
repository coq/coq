(***************************************************************************

 Variable abstraction.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


open Signatures
open Variables
open Gen_terms
open Theory
open Controle

(*===================================================================

               Abstraction of alien subterms by variables 
                     in order to get pure equations

====================================================================*)

(*

  [(purify_term find_th (t, bindings))] recursively purifies the
  term [t] bottom-up, {\em i.e.} replaces the alien\footnote{An alien
  subterm of [t] is a subterm [u] the head of which does not belong to
  the same elementary theory as [t].} subterms $u_i$s of [t] by some
  variables.

  The elementary theories of the symbols are given by [find_th].
  Be aware of the fact that this list should be compatible with the
  unification type [PLAIN], [AC_ONLY] or [AC_COMPLETE] (see the module
  Theory).


  If there is already a binding $u_i=x_i$ in the [bindings],
  $u_i$ is replaced by $x_i$.

  Otherwise $x_i$ is a new variable, and the equation $u_i=x_i$ is
  added to the [bindings].

  [(purify_list_of_terms find_th (list_of_terms, bindings))] does the 
  same for a [list_of_terms].

*)

module OrderedTerms = 
  struct
    type 'symbol t = 'symbol term
    let compare = compare
  end

module TermsMap = Ordered_maps.MakePoly (OrderedTerms)


let rec purify_term find_th = function
    (Var _), _, _ as final_result -> final_result

  | (Term (f,l), bindings_as_a_map, bindings_as_a_list) ->
      let uth_of_f = find_th f in
      let (lt',bm',bl') = 
	purify_list_of_terms find_th (l, bindings_as_a_map, bindings_as_a_list) in
      let (lt'',bm'',bl'') = 
	List.fold_left 
	  (fun (lt,bm,bl) t -> 
	     match t with
		 Var _ -> (t::lt,bm,bl)
	       | Term (g,_) ->
		   if find_th g = uth_of_f
		   then ((t::lt),bm,bl)
		   else 
		     try
		       ((TermsMap.find t bm)::lt, bm,bl)
		     with Not_found ->
		       let x = fresh_var_for_unif () in
		       let v = Var x in
			 (v::lt, (TermsMap.add t v bm), (v,t)::bl)
	  )
	  ([],bm',bl') lt' in
	(Term (f,List.rev lt''), bm'',bl'')
	

and purify_list_of_terms find_th = function
    [], _, _ as final_res -> final_res

  | t::list_of_terms, bindings, list_of_pure_eqs ->
      let (t',b',le') = 
	purify_term find_th (t,bindings,list_of_pure_eqs) in
      let (list_of_terms',b'',le'') = 
	purify_list_of_terms find_th (list_of_terms,b',le') in
	(t'::list_of_terms',b'',le'')



let purify_list_of_equations unif_k find_th list_of_eqs = 
  let (list_of_pure_eqs,_) = 
    List.fold_left
      (fun (lpe, b) e ->
	 match e with
	     Var _, Var _ -> (e::lpe, b)

	   | Var _ as v, t ->
	       let t',b',lpe' = purify_term find_th (t,b,lpe) in
		 ((v,t')::lpe',b')
	   
	   | t, (Var _ as v) -> 
	       let t',b',lpe' = purify_term find_th (t,b,lpe) in
		 ((v,t')::lpe',b')
	   
	   | (Term (f1,l1) as t1), (Term (f2,l2) as t2) ->
	       let _,th_of_f1 = find_th f1
	       and _,th_of_f2 = find_th f2 in
		 if (unif_k <> PLAIN) or 
		   begin
		     match th_of_f1, th_of_f2 with
			 (Empty _), (Empty _) -> true
		       | _ , _ -> false
		   end
		 then 
		   if f1 = f2
		   then
		     let (t1',b',lpe') = purify_term find_th (t1,b,lpe) in
		     let (t2',b'',lpe'') = purify_term find_th (t2,b',lpe') in
		       (t1',t2')::lpe'', b''
		   else raise No_solution
		 else
		   let (t1',b',lpe') = purify_term find_th (t1,b,lpe) in
		   let (t2',b'',lpe'') = purify_term find_th (t2,b',lpe') in
		     if th_of_f1 = th_of_f2
		     then (t1',t2')::lpe'', b''
		     else 
		       try
			 let v = TermsMap.find t1' b'' in
			   (v,t2') :: lpe'',
			   TermsMap.add t2' v b''
		       with Not_found ->
			 try
			   let v = TermsMap.find t2' b'' in
			     (v,t1') :: lpe'',
			     TermsMap.add t1' v b''
			 with Not_found ->
			   let x = fresh_var_for_unif () in
			   let v = Var x in
			     (v,t1')::(v,t2')::lpe'', 
			     TermsMap.add t1' v (TermsMap.add t2' v b'')
      )
      ([],TermsMap.empty) list_of_eqs in
    list_of_pure_eqs



