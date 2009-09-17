open Util
open Pp
open Printer

type term_pp = Pp.std_ppcmds

type subtyping_error =
  | UncoercibleInferType of loc * term_pp * term_pp
  | UncoercibleInferTerm of loc * term_pp * term_pp * term_pp * term_pp
  | UncoercibleRewrite of term_pp * term_pp

type typing_error =
  | NonFunctionalApp of loc * term_pp * term_pp * term_pp
  | NonConvertible of loc * term_pp * term_pp
  | NonSigma of loc * term_pp
  | IllSorted of loc * term_pp

exception Subtyping_error of subtyping_error
exception Typing_error of typing_error

exception Debug_msg of string

let typing_error e = raise (Typing_error e)
let subtyping_error e = raise (Subtyping_error e)
