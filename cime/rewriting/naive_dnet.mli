(***************************************************************************

Discrimination nets in a naive way: non linearity is not handled,
subterms whose top is a non-free symbol are considered.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)



type 'symbol dnet ;;



(*

  [compile sigma r] compiles the TRS [r] on signature [sigma] into a
  discriminate net, to be used with the next function.

*)

val compile : 
  'symbol #Signatures.signature ->
    'symbol Rewrite_rules.rewrite_rule list -> 'symbol dnet

(*

  [discriminate d t] returns the list of rules of [d] which may match
  term [t]. One as to call a complete matching algorithm to each of
  the resulting rules, to take into account non-linearities and C or
  AC symbols.

  Examples:

  \begin{itemize}

  \item for any term headed by $f$, a non-linear rule of the form
  $f(x,x) \rightarrow r$ will be in the returned list.

  \item for any term headed by AC symbol $+$, a rule of the form
  $l_1+\cdots+l_n \rightarrow r$ will be in the returned list.

  \end{itemize}

*)


val discriminate :
  'symbol dnet -> 
    'symbol Gen_terms.term -> 'symbol Rewrite_rules.rewrite_rule list





val print : 'symbol #Signatures.signature -> 'symbol dnet -> unit


