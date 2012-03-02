type term_pp = Pp.std_ppcmds
type subtyping_error =
    UncoercibleInferType of Pp.loc * term_pp * term_pp
  | UncoercibleInferTerm of Pp.loc * term_pp * term_pp * term_pp * term_pp
  | UncoercibleRewrite of term_pp * term_pp
type typing_error =
    NonFunctionalApp of Pp.loc * term_pp * term_pp * term_pp
  | NonConvertible of Pp.loc * term_pp * term_pp
  | NonSigma of Pp.loc * term_pp
  | IllSorted of Pp.loc * term_pp
exception Subtyping_error of subtyping_error
exception Typing_error of typing_error
exception Debug_msg of string
val typing_error : typing_error -> 'a
val subtyping_error : subtyping_error -> 'a
