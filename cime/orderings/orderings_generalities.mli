(***************************************************************************

This module provides all general notions about orderings

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


(*

\subsubsection{Comparison results}

First, we define a type for given all different possible results of a
comparison. Usually, a comparaison may result in either $>$, $<$ or
$=$ ; but here the situation is a more complicated.

First, we are interested in what is called pre-orderings, or
quasi-orderings, that is two different objects may be
\emph{equivalent} w.r.t. an ordering. Moreover, we are also interested
in partial orderings, that is two objects may be \emph{uncomparable}
w.r.t to an ordering (neither $>$ nor $<$). That's why here an
ordering function over a type $t$ will be any function of type
$t\rightarrow t \rightarrow result$ where $result$ is either
\emph{equivalent}, \emph{greater\_than}, \emph{less\_than} or
\emph{uncomparable}. Such a ordering function defines in fact both a
(partial) quasi-ordering $\succeq$ and an associated (partial) strict
ordering $\succ$ :
\begin{itemize}

\item $x\succeq y$ if $order(x,y) = `>` or `=`$ ;

\item $x\succ y$ if $order(x,y) = `>` $.

\end{itemize}

The ordering function $order$ must be design in such a way that : 

\begin{itemize}

\item $\succeq$ is reflexive and transitive : for all $x$, $x\succeq
x$ ; and for all $x$, $y$ and $z$, $x\succeq y$ and $y\succeq z$ imply
$x\succeq z$ ;

\item $\succ$ is transitive : for all $x$, $y$ and $z$, $x\succ y$ and
$y\succ z$ imply $x\succ z$ ;

\item if $x\succeq y$ then $y\preceq x$ ;

\item if $x\succ y$ then $y\prec x$ ;

\item if $x\succ y$ then $x\succeq y$ ;

\item ...

\end{itemize}


Moreover, we will be interested mainly an \emph{term orderings}, that
is orderings defined over sets of terms with variables. In that case,
one is interested in having \emph{stable} orderings : if $s\succeq t$
then $s\sigma \succeq t\sigma$ for all substitutions $\sigma$ (and the
same for $\succ$). In that situation, more complicated things may
happen, for example let us assume that $a$ is the smallest constant of
a signature, then one would like to have $x\succeq a$ for any variable
$x$, but in fact for the substitution $\sigma=\{x\mapsto a\}$ we would
get $x\sigma\simeq a$ and for any other $x\sigma \succ a$. So what
should return the function $order$ on $(x,a)$ ? $`>`$ or $`=`$ would
be wrong so the only correct answer would be `uncomparable`. These is
not satisfactory at all, so we introduce two additional possible
answers for an ordering function : \emph{greater or equivalent} and
\emph{less or equivalent}.

Finally, the type of comparison is given by the following

*)

type comparison_result = 
  | Equivalent 
  | Greater_than
  | Less_than
  | Greater_or_equivalent
  | Less_or_equivalent
  | Uncomparable
;;


(*

  [(string_of_comparison_result r)] returns a string for displaying [r]

*)

val string_of_comparison_result : comparison_result -> string

type 'a ordering = 'a -> 'a -> comparison_result 


(*i
module type ORDERED_STRUCTURE =
   sig
     type t
     val cmp: t -> t -> comparison_result
   end
i*)

val is_greater_or_equal : comparison_result -> bool
    
val is_less_or_equal : comparison_result -> bool
    

(*

  [(greater_than_all o x l)] returns [true] if for all [y] in list [l],
  [x] is greater than [y] for [o]

*)

val greater_than_all :
  'a ordering -> 'a -> 'a list -> bool

(*

  [(exists_greater_or_equal o l y)] returns [true] if there exists [x]
  in list [l] such that [x] is greater than or equal to [y] for [o]

*)

val exists_greater_or_equal :
  'a ordering -> 'a list -> 'a -> bool
;;

val forall_exists_greater :
  'a ordering -> 'a list -> 'a list -> bool
;;


val remove_equivalent_elements :
  'a ordering -> 'a list -> 'a list -> ('a list * 'a list)
;;

(*

\subsubsection{General ordering functionals}

*)

(*

Products of orderings

*)

(*i
val produit_ordres :
      comparison_result * comparison_result -> comparison_result
i*)

(*

[(lexicographic_extension o)] where [o] is an ordering function over a
type $t$, is the ordering function [o'] over lists of $t$ by
lexicographic use of $o$, that is $(x_1,\ldots,x_n) \succ'
(y_1,\ldots,y_n)$ if there is a $k$ s.t. $x_1 \succeq y_1$, \ldots
$x_{k-1} \succeq y_{k-1}$ and $x_k \succ y_k$. Raises
[Invalid_argument] of the two lists do not have the same length.

[(lexicographic_extension_of_orderings l)] where [l] is a list of
ordering functions $o_1,\ldots,o_n$ all over the same type $t$, is the
ordering function over $t$ given by $x \succ y$ if there is a $k$
s.t. $x\succeq_1 y$, \ldots $x\succeq_{k-1} y$ and $x\succ_k y$

*)

val lexicographic_extension : ('a ordering) -> ('a list ordering)

val lexicographic_extension_of_orderings : ('a ordering) list -> ('a ordering)


(*

[(multiset_extension o)] where [o] is an ordering function over a
type $t$, is the ordering function [o'] over lists of $t$ by
multiset use of $o$.

*)

val multiset_extension :  ('a ordering) -> ('a list ordering)




