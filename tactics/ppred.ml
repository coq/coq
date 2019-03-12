open Util
open Pp
open Locus
open Genredexpr
open Pputils

let pr_with_occurrences pr keyword (occs,c) =
  match occs with
    | AtLeastOneOccurrence -> hov 1 (pr c ++ spc () ++ keyword "at" ++ str" +")
    | AllOccurrences ->
      pr c
    | NoOccurrences ->
      failwith "pr_with_occurrences: no occurrences"
    | OnlyOccurrences nl ->
      hov 1 (pr c ++ spc () ++ keyword "at" ++ spc () ++
                hov 0 (prlist_with_sep spc (pr_or_var int) nl))
    | AllOccurrencesBut nl ->
      hov 1 (pr c ++ spc () ++ keyword "at" ++ str" - " ++
                hov 0 (prlist_with_sep spc (pr_or_var int) nl))

exception ComplexRedFlag

let pr_short_red_flag pr r =
  if not r.rBeta ||  not r.rMatch || not r.rFix || not r.rCofix || not r.rZeta then
    raise ComplexRedFlag
  else if List.is_empty r.rConst then
    if r.rDelta then mt () else raise ComplexRedFlag
  else (if r.rDelta then str "-" else mt ()) ++
          hov 0 (str "[" ++ prlist_with_sep spc pr r.rConst ++ str "]")

let pr_red_flag pr r =
  try pr_short_red_flag pr r
  with ComplexRedFlag ->
    (if r.rBeta then pr_arg str "beta" else mt ()) ++
      (if r.rMatch && r.rFix && r.rCofix then pr_arg str "iota" else
          (if r.rMatch then pr_arg str "match" else mt ()) ++
          (if r.rFix then pr_arg str "fix" else mt ()) ++
          (if r.rCofix then pr_arg str "cofix" else mt ())) ++
      (if r.rZeta then pr_arg str "zeta" else mt ()) ++
      (if List.is_empty r.rConst then
          if r.rDelta then pr_arg str "delta"
          else mt ()
        else
          pr_arg str "delta " ++ (if r.rDelta then str "-" else mt ()) ++
            hov 0 (str "[" ++ prlist_with_sep spc pr r.rConst ++ str "]"))

let pr_union pr1 pr2 = function
  | Inl a -> pr1 a
  | Inr b -> pr2 b

let pr_red_expr (pr_constr,pr_lconstr,pr_ref,pr_pattern) keyword = function
  | Red false -> keyword "red"
  | Hnf -> keyword "hnf"
  | Simpl (f,o) -> keyword "simpl" ++ (pr_short_red_flag pr_ref f)
                    ++ pr_opt (pr_with_occurrences (pr_union pr_ref pr_pattern) keyword) o
  | Cbv f ->
    if f.rBeta && f.rMatch && f.rFix && f.rCofix &&
          f.rZeta && f.rDelta && List.is_empty f.rConst then
      keyword "compute"
    else
      hov 1 (keyword "cbv" ++ pr_red_flag pr_ref f)
  | Lazy f ->
    hov 1 (keyword "lazy" ++ pr_red_flag pr_ref f)
  | Cbn f ->
    hov 1 (keyword "cbn" ++ pr_red_flag pr_ref f)
  | Unfold l ->
    hov 1 (keyword "unfold" ++ spc() ++
              prlist_with_sep pr_comma (pr_with_occurrences pr_ref keyword) l)
  | Fold l -> hov 1 (keyword "fold" ++ prlist (pr_arg pr_constr) l)
  | Pattern l ->
    hov 1 (keyword "pattern" ++
              pr_arg (prlist_with_sep pr_comma (pr_with_occurrences pr_constr keyword)) l)

  | Red true ->
    CErrors.user_err Pp.(str "Shouldn't be accessible from user.")
  | ExtraRedExpr s ->
    str s
  | CbvVm o ->
    keyword "vm_compute" ++ pr_opt (pr_with_occurrences (pr_union pr_ref pr_pattern) keyword) o
  | CbvNative o ->
    keyword "native_compute" ++ pr_opt (pr_with_occurrences (pr_union pr_ref pr_pattern) keyword) o

let pr_red_expr_env env sigma (pr_constr,pr_lconstr,pr_ref,pr_pattern) =
  pr_red_expr (pr_constr env sigma, pr_lconstr env sigma, pr_ref, pr_pattern env sigma)
