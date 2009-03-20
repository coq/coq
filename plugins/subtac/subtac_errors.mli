type term_pp = Pp.std_ppcmds
type subtyping_error =
    UncoercibleInferType of Util.loc * term_pp * term_pp
  | UncoercibleInferTerm of Util.loc * term_pp * term_pp * term_pp * term_pp
  | UncoercibleRewrite of term_pp * term_pp
type typing_error =
    NonFunctionalApp of Util.loc * term_pp * term_pp * term_pp
  | NonConvertible of Util.loc * term_pp * term_pp
  | NonSigma of Util.loc * term_pp
  | IllSorted of Util.loc * term_pp
exception Subtyping_error of subtyping_error
exception Typing_error of typing_error
exception Debug_msg of string
val typing_error : typing_error -> 'a
val subtyping_error : subtyping_error -> 'a
