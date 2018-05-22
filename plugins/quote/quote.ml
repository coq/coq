(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* The `Quote' tactic *)

(* The basic idea is to automatize the inversion of interpretation functions
   in 2-level approach

   Examples are given in \texttt{theories/DEMOS/DemoQuote.v}

   Suppose you have a langage \texttt{L} of 'abstract terms'
   and a type \texttt{A} of 'concrete terms'
   and a function \texttt{f : L -> (varmap A L) -> A}.

   Then, the tactic \texttt{quote f} will replace an
   expression \texttt{e} of type \texttt{A} by \texttt{(f vm t)}
   such that \texttt{e} and \texttt{(f vm t)} are convertible.

   The problem is then inverting the function \texttt{f}.

   The tactic works when:

   \begin{itemize}
   \item L is a simple inductive datatype. The constructors of L may
     have one of the three following forms:

     \begin{enumerate}
     \item ordinary recursive constructors like: \verb|Cplus : L -> L -> L|
     \item variable leaf like: \verb|Cvar : index -> L|
     \item constant leaf like \verb|Cconst : A -> L|
     \end{enumerate}

     The definition of \texttt{L} must contain at most one variable
     leaf and at most one constant leaf.

     When there are both a variable leaf and a constant leaf, there is
     an ambiguity on inversion. The term t can be either the
     interpretation of \texttt{(Cconst t)} or the interpretation of
     (\texttt{Cvar}~$i$) in a variable map containing the binding $i
     \rightarrow$~\texttt{t}. How to discriminate between these
     choices?

     To solve the dilemma, one gives to \texttt{quote} a list of
     \emph{constant constructors}: a term will be considered as a
     constant if it is either a constant constructor or the
     application of a constant constructor to constants. For example
     the list \verb+[S, O]+ defines the closed natural
     numbers. \texttt{(S (S O))} is a constant when \texttt{(S x)} is
     not.

     The definition of constants vary for each application of the
     tactic, so it can even be different for two applications of
     \texttt{quote} with the same function.

   \item \texttt{f} is a quite simple fixpoint on
     \texttt{L}. In particular, \texttt{f} must verify:

\begin{verbatim}
     (f (Cvar i)) = (varmap_find vm default_value i)
\end{verbatim}
\begin{verbatim}
     (f (Cconst c)) = c
\end{verbatim}

     where \texttt{index} and \texttt{varmap\_find} are those defined
     the \texttt{Quote} module. \emph{The tactic won't work with
     user's own variables map!!}  It is mandatory to use the
     variable map defined in module \texttt{Quote}.

   \end{itemize}

   The method to proceed is then clear:

   \begin{itemize}
   \item Start with an empty hashtable of "registed leafs"
      that maps constr to integers and a "variable counter" equal to 0.
    \item Try to match the term with every right hand side of the
      definition of \texttt{f}.

      If there is one match, returns the correponding left hand
      side and call yourself recursively to get the arguments of this
      left hand side.

      If there is no match, we are at a leaf. That is the
      interpretation of either a variable or a constant.

      If it is a constant, return \texttt{Cconst} applied to that
      constant.

      If not, it is a variable. Look in the hashtable
      if this leaf has been already encountered. If not, increment
      the variable counter and add an entry to the hashtable; then
      return \texttt{(Cvar !variables\_counter)}
   \end{itemize}
*)


(*i*)
open CErrors
open Util
open Names
open Constr
open EConstr
open Pattern
open Patternops
open Constr_matching
open Tacmach
open Proofview.Notations
(*i*)

(*s First, we need to access some Coq constants
  We do that lazily, because this code can be linked before
  the constants are loaded in the environment *)

let constant dir s =
  EConstr.of_constr @@ UnivGen.constr_of_global @@
    Coqlib.coq_reference "Quote" ("quote"::dir) s

let coq_Empty_vm = lazy (constant ["Quote"] "Empty_vm")
let coq_Node_vm = lazy (constant ["Quote"] "Node_vm")
let coq_varmap_find = lazy (constant ["Quote"] "varmap_find")
let coq_Right_idx = lazy (constant ["Quote"] "Right_idx")
let coq_Left_idx = lazy (constant ["Quote"] "Left_idx")
let coq_End_idx = lazy (constant ["Quote"] "End_idx")

(*s Then comes the stuff to decompose the body of interpetation function
  and pre-compute the inversion data.

For a function like:

\begin{verbatim}
  Fixpoint interp (vm:varmap Prop) (f:form) :=
     match f with
       | f_and f1 f1 f2 => (interp f1) /\ (interp f2)
       | f_or f1 f1 f2 => (interp f1) \/ (interp f2)
       | f_var i => varmap_find Prop default_v i vm
       | f_const c => c
     end.
\end{verbatim}

With the constant constructors \texttt{C1}, \dots, \texttt{Cn}, the
corresponding scheme will be:

\begin{verbatim}
  {normal_lhs_rhs =
     [ "(f_and ?1 ?2)", "?1 /\ ?2";
       "(f_or ?1 ?2)", " ?1 \/ ?2";];
   return_type = "Prop";
   constants = Some [C1,...Cn];
   variable_lhs = Some "(f_var ?1)";
   constant_lhs = Some "(f_const ?1)"
  }
\end{verbatim}

If there is no constructor for variables in the type \texttt{form},
then [variable_lhs] is [None]. Idem for constants and
[constant_lhs]. Both cannot be equal to [None].

The metas in the RHS must correspond to those in the LHS (one cannot
exchange ?1 and ?2 in the example above)

*)

module ConstrSet = Set.Make(Constr)

type inversion_scheme = {
  normal_lhs_rhs : (constr * constr_pattern) list;
  variable_lhs : constr option;
  return_type : constr;
  constants : ConstrSet.t;
  constant_lhs : constr option }

(*s [compute_ivs gl f cs] computes the inversion scheme associated to
  [f:constr] with constants list [cs:constr list] in the context of
  goal [gl]. This function uses the auxiliary functions
  [i_can't_do_that], [decomp_term], [compute_lhs] and [compute_rhs]. *)

let i_can't_do_that () = user_err Pp.(str "Quote: not a simple fixpoint")

let decomp_term sigma c = EConstr.kind sigma (Termops.strip_outer_cast sigma c)

(*s [compute_lhs typ i nargsi] builds the term \texttt{(C ?nargsi ...
  ?2 ?1)}, where \texttt{C} is the [i]-th constructor of inductive
  type [typ] *)

let coerce_meta_out id =
  let s = Id.to_string id in
  int_of_string (String.sub s 1 (String.length s - 1))
let coerce_meta_in n =
  Id.of_string ("M" ^ string_of_int n)

let compute_lhs sigma typ i nargsi =
  match EConstr.kind sigma typ with
    | Ind((sp,0),u) ->
        let argsi = Array.init nargsi (fun j -> mkMeta (nargsi - j)) in
        mkApp (mkConstructU (((sp,0),i+1),u), argsi)
    | _ -> i_can't_do_that ()

(*s This function builds the pattern from the RHS. Recursive calls are
  replaced by meta-variables ?i corresponding to those in the LHS *)

let compute_rhs env sigma bodyi index_of_f =
  let rec aux c =
    match EConstr.kind sigma c with
      | App (j, args) when isRel sigma j && Int.equal (destRel sigma j) index_of_f (* recursive call *) ->
          let i = destRel sigma (Array.last args) in
	  PMeta (Some (coerce_meta_in i))
      | App (f,args) ->
          PApp (pattern_of_constr env sigma (EConstr.to_constr sigma f), Array.map aux args)
      | Cast (c,_,_) -> aux c
      | _ -> pattern_of_constr env sigma (EConstr.to_constr sigma c)
  in
  aux bodyi

(*s Now the function [compute_ivs] itself *)

let compute_ivs f cs gl =
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.New.project gl in
  let (cst, u) = try destConst sigma f with DestKO -> i_can't_do_that () in
  let u = EInstance.kind sigma u in
  let body = Environ.constant_value_in (Global.env()) (cst, u) in
  let body = EConstr.of_constr body in
  match decomp_term sigma body with
    | Fix(([| len |], 0), ([| name |], [| typ |], [| body2 |])) ->
        let (args3, body3) = decompose_lam sigma body2 in
        let nargs3 = List.length args3 in
        let is_conv = Reductionops.is_conv env sigma in
          begin match decomp_term sigma body3 with
          | Case(_,p,c,lci) -> (* <p> Case c of c1 ... cn end *)
              let n_lhs_rhs = ref []
              and v_lhs = ref (None : constr option)
              and c_lhs = ref (None : constr option) in
              Array.iteri
                (fun i ci ->
                   let argsi, bodyi = decompose_lam sigma ci in
                   let nargsi = List.length argsi in
           (* REL (narg3 + nargsi + 1) is f *)
           (* REL nargsi+1 to REL nargsi + nargs3 are arguments of f *)
           (* REL 1 to REL nargsi are argsi (reverse order) *)
           (* First we test if the RHS is the RHS for constants *)
                   if isRel sigma bodyi && Int.equal (destRel sigma bodyi) 1 then
                     c_lhs := Some (compute_lhs sigma (snd (List.hd args3))
                                      i nargsi)
           (* Then we test if the RHS is the RHS for variables *)
                   else begin match decompose_app sigma bodyi with
                     | vmf, [_; _; a3; a4 ]
                         when isRel sigma a3 && isRel sigma a4 && is_conv vmf
                           (Lazy.force coq_varmap_find) ->
                             v_lhs := Some (compute_lhs sigma
                                              (snd (List.hd args3))
                                              i nargsi)
           (* Third case: this is a normal LHS-RHS *)
                     | _ ->
                         n_lhs_rhs :=
                         (compute_lhs sigma (snd (List.hd args3)) i nargsi,
                          compute_rhs env sigma bodyi (nargs3 + nargsi + 1))
                         :: !n_lhs_rhs
                   end)
                lci;

              if Option.is_empty !c_lhs && Option.is_empty !v_lhs then i_can't_do_that ();

	      (* The Cases predicate is a lambda; we assume no dependency *)
	      let p = match EConstr.kind sigma p with
		| Lambda (_,_,p) -> Termops.pop p
		| _ -> p
	      in

              { normal_lhs_rhs = List.rev !n_lhs_rhs;
                variable_lhs = !v_lhs;
                return_type = p;
                constants = List.fold_right ConstrSet.add cs ConstrSet.empty;
                constant_lhs = !c_lhs }

          | _ -> i_can't_do_that ()
        end
    |_ -> i_can't_do_that ()

(* TODO for that function:
\begin{itemize}
\item handle the case where the return type is an argument of the
  function
\item handle the case of simple mutual inductive (for example terms
  and lists of terms) formulas with the corresponding mutual
  recursvive interpretation functions.
\end{itemize}
*)

(*s Stuff to build variables map, currently implemented as complete
binary search trees (see file \texttt{Quote.v}) *)

(* First the function to distinghish between constants (closed terms)
   and variables (open terms) *)

let rec closed_under sigma cset t =
  (ConstrSet.mem (EConstr.Unsafe.to_constr t) cset) ||
  (match EConstr.kind sigma t with
     | Cast(c,_,_) -> closed_under sigma cset c
     | App(f,l) -> closed_under sigma cset f && Array.for_all (closed_under sigma cset) l
     | _ -> false)

(*s [btree_of_array [| c1; c2; c3; c4; c5 |]] builds the complete
   binary search tree containing the [ci], that is:

\begin{verbatim}
                  c1
                 /  \
               c2    c3
              /  \
             c4  c5
\end{verbatim}

The second argument is a constr (the common type of the [ci])
*)

let btree_of_array a ty =
  let size_of_a = Array.length a in
  let semi_size_of_a = size_of_a lsr 1 in
  let node = Lazy.force coq_Node_vm
  and empty = mkApp (Lazy.force coq_Empty_vm, [| ty |]) in
  let rec aux n =
    if n > size_of_a
    then empty
    else if  n > semi_size_of_a
    then mkApp (node, [| ty; a.(n-1); empty; empty |])
    else mkApp (node, [| ty; a.(n-1); aux (2*n); aux (2*n+1) |])
  in
  aux 1

(*s [btree_of_array] and [path_of_int] verify the following invariant:\\
   {\tt (varmap\_find A dv }[(path_of_int n)] [(btree_of_array a ty)]
  = [a.(n)]\\
  [n] must be [> 0] *)

let path_of_int n =
  (* returns the list of digits of n in reverse order with
     initial 1 removed *)
  let rec digits_of_int n =
    if Int.equal n 1 then []
    else (Int.equal (n mod 2) 1)::(digits_of_int (n lsr 1))
  in
  List.fold_right
    (fun b c -> mkApp ((if b then Lazy.force coq_Right_idx
                         else Lazy.force coq_Left_idx),
                         [| c |]))
    (List.rev (digits_of_int n))
    (Lazy.force coq_End_idx)

(*s The tactic works with a list of subterms sharing the same
  variables map. We need to sort terms in order to avoid than
  strange things happen during replacement of terms by their
  'abstract' counterparties. *)

(* [subterm t t'] tests if constr [t'] occurs in [t] *)
(* This function does not descend under binders (lambda and Cases) *)

let rec subterm gl (t : constr) (t' : constr) =
  (pf_conv_x gl t t') ||
  (match EConstr.kind (project gl) t with
     | App (f,args) -> Array.exists (fun t -> subterm gl t t') args
     | Cast(t,_,_) -> (subterm gl t t')
     | _ -> false)

(*s We want to sort the list according to reverse subterm order. *)
(* Since it's a partial order the algoritm of Sort.list won't work !! *)

let rec sort_subterm gl l =
  let sigma = project gl in
  let rec insert c = function
    | [] -> [c]
    | (h::t as l) when EConstr.eq_constr sigma c h -> l (* Avoid doing the same work twice *)
    | h::t -> if subterm gl c h then c::h::t else h::(insert c t)
  in
  match l with
    | [] -> []
    | h::t -> insert h (sort_subterm gl t)

module Constrhash = Hashtbl.Make(Constr)

let subst_meta subst c =
  let subst = List.map (fun (i, c) -> i, EConstr.Unsafe.to_constr c) subst in
  EConstr.of_constr (Termops.subst_meta subst (EConstr.Unsafe.to_constr c))

(*s Now we are able to do the inversion itself.
  We destructurate the term and use an imperative hashtable
  to store leafs that are already encountered.
  The type of arguments is:\\
  [ivs : inversion_scheme]\\
  [lc: constr list]\\
  [gl: goal sigma]\\ *)
let quote_terms env sigma ivs lc =
  Coqlib.check_required_library ["Coq";"quote";"Quote"];
  let varhash  = (Constrhash.create 17 : constr Constrhash.t) in
  let varlist = ref ([] : constr list) in (* list of variables *)
  let counter = ref 1 in (* number of variables created + 1 *)
  let rec aux c =
    let rec auxl l =
      match l with
        | (lhs, rhs)::tail ->
            begin try
              let s1 = Id.Map.bindings (matches env sigma rhs c) in
              let s2 = List.map (fun (i,c_i) -> (coerce_meta_out i,aux c_i)) s1
	      in
              subst_meta s2 lhs
            with PatternMatchingFailure -> auxl tail
            end
        |  [] ->
             begin match ivs.variable_lhs with
               | None ->
                   begin match ivs.constant_lhs with
                     | Some c_lhs -> subst_meta [1, c] c_lhs
                     | None -> anomaly (Pp.str "invalid inversion scheme for quote.")
                   end
               | Some var_lhs ->
                   begin match ivs.constant_lhs with
                     | Some c_lhs when closed_under sigma ivs.constants c ->
			 subst_meta [1, c] c_lhs
                     | _ ->
			 begin
                           try Constrhash.find varhash (EConstr.Unsafe.to_constr c)
                           with Not_found ->
                             let newvar =
                               subst_meta [1, (path_of_int !counter)]
				 var_lhs in
                             begin
                               incr counter;
                               varlist := c :: !varlist;
                               Constrhash.add varhash (EConstr.Unsafe.to_constr c) newvar;
                               newvar
                             end
			 end
                   end
             end
    in
    auxl ivs.normal_lhs_rhs
  in
  let lp = List.map aux lc in
    (lp, (btree_of_array (Array.of_list (List.rev !varlist))
            ivs.return_type ))

(*s actually we could "quote" a list of terms instead of a single
  term. Ring for example needs that, but Ring doesn't use Quote
  yet. *)

let pf_constrs_of_globals l =
  let rec aux l acc =
    match l with
      [] -> Proofview.tclUNIT (List.rev acc)
    | hd :: tl ->
       Tacticals.New.pf_constr_of_global hd >>= fun g -> aux tl (g :: acc)
  in aux l []

let quote f lid =
  Proofview.Goal.enter begin fun gl ->
    let fg = Tacmach.New.pf_global f gl in
    let clg = List.map (fun id -> Tacmach.New.pf_global id gl) lid in
    Tacticals.New.pf_constr_of_global fg >>= fun f ->
    pf_constrs_of_globals clg >>= fun cl ->
    Proofview.Goal.nf_enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Tacmach.New.project gl in
      let ivs = compute_ivs f (List.map (EConstr.to_constr sigma) cl) gl in
      let concl = Proofview.Goal.concl gl in
      let quoted_terms = quote_terms env sigma ivs [concl] in
      let (p, vm) = match quoted_terms with
      | [p], vm -> (p,vm)
      | _ -> assert false
      in
      match ivs.variable_lhs with
      | None -> Tactics.convert_concl (mkApp (f, [| p |])) DEFAULTcast
      | Some _ -> Tactics.convert_concl (mkApp (f, [| vm; p |])) DEFAULTcast
    end
  end

let gen_quote cont c f lid =
  Proofview.Goal.enter begin fun gl ->
    let fg = Tacmach.New.pf_global f gl in
    let clg = List.map (fun id -> Tacmach.New.pf_global id gl) lid in
    Tacticals.New.pf_constr_of_global fg >>= fun f ->
    pf_constrs_of_globals clg >>= fun cl ->
    Proofview.Goal.nf_enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Tacmach.New.project gl in
      let cl = List.map (EConstr.to_constr sigma) cl in
      let ivs = compute_ivs f cl gl in
      let quoted_terms = quote_terms env sigma ivs [c] in
      let (p, vm) = match quoted_terms with
        | [p], vm -> (p,vm)
        | _ -> assert false
      in
      match ivs.variable_lhs with
      | None -> cont (mkApp (f, [| p |]))
      | Some _ -> cont (mkApp (f, [| vm; p |]))
    end
  end

(*i

Just testing ...

#use "include.ml";;
open Quote;;

let r = glob_constr_of_string;;

let ivs = {
  normal_lhs_rhs =
   [ r "(f_and ?1 ?2)", r "?1/\?2";
     r "(f_not ?1)", r "~?1"];
  variable_lhs = Some (r "(f_atom ?1)");
  return_type = r "Prop";
  constants = ConstrSet.empty;
  constant_lhs = (r "nat")
};;

let t1 = r "True/\(True /\ ~False)";;
let t2 = r "True/\~~False";;

quote_term ivs () t1;;
quote_term ivs () t2;;

let ivs2 =
  normal_lhs_rhs =
   [ r "(f_and ?1 ?2)", r "?1/\?2";
     r "(f_not ?1)", r "~?1"
     r "True", r "f_true"];
  variable_lhs = Some (r "(f_atom ?1)");
  return_type = r "Prop";
  constants = ConstrSet.empty;
  constant_lhs = (r "nat")

i*)
