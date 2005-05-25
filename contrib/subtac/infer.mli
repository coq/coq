type term_pp = Pp.std_ppcmds

type subtyping_error = 
  | UncoercibleInferType of Util.loc * term_pp * term_pp
  | UncoercibleInferTerm of Util.loc * term_pp * term_pp * term_pp * term_pp
  | UncoercibleRewrite of term_pp * term_pp

type typing_error = 
  | NonFunctionalApp of Util.loc * term_pp * term_pp
  | NonConvertible of Util.loc * term_pp * term_pp
  | NonSigma of Util.loc * term_pp

exception Subtyping_error of subtyping_error
exception Typing_error of typing_error
exception Debug_msg of string

val subtyping_error : subtyping_error -> 'a
val typing_error : typing_error -> 'a

type sort = Term.sorts
type sort_loc = sort Util.located
type dterm =
    DRel of Natural.nat
  | DLambda of (Names.name Util.located * dtype_loc) * dterm_loc * dtype_loc
  | DApp of dterm_loc * dterm_loc * dtype_loc
  | DLetIn of Names.name Util.located * dterm_loc * dterm_loc * dtype_loc
  | DLetTuple of (Names.name Util.located * dtype_loc * dtype_loc) list *
      dterm_loc * dterm_loc * dtype_loc
  | DIfThenElse of dterm_loc * dterm_loc * dterm_loc * dtype_loc
  | DSum of (Names.name Util.located * dterm_loc) * (dterm_loc * dtype_loc) *
      dtype_loc
  | DCoq of Term.constr * dtype_loc
and dterm_loc = dterm Util.located
and dtype =
    DTApp of dtype_loc * dtype_loc * dtype_loc * sort_loc
  | DTPi of (Names.name Util.located * dtype_loc) * dtype_loc * sort_loc
  | DTSigma of (Names.name Util.located * dtype_loc) * dtype_loc * sort_loc
  | DTSubset of (Names.identifier Util.located * dtype_loc) * dtype_loc *
      sort_loc
  | DTRel of Natural.nat
  | DTTerm of dterm_loc * dtype_loc * sort_loc
  | DTSort of sort_loc
  | DTInd of Names.identifier Util.located * dtype_loc * Names.inductive *
      sort_loc
  | DTCoq of Term.types * dtype_loc * sort_loc
and dtype_loc = dtype Util.located

val print_dtype_loc :
  (Names.name * dtype_loc) list -> dtype_loc -> Pp.std_ppcmds
val print_dterm_loc :
  (Names.name * dtype_loc) list -> dterm_loc -> Pp.std_ppcmds

val sort_of_dtype_loc :
  (Names.name * dtype_loc) list -> dtype_loc -> sort_loc


val infer :
  (Names.name * dtype_loc) list -> Sast.term_loc -> dterm_loc * dtype_loc
val infer_type : (Names.name * dtype_loc) list -> Sast.type_loc -> dtype_loc
