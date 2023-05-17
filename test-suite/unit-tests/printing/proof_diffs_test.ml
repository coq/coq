open OUnit
open Utest
open Pp_diff
open Proof_diffs

(* Needed to be able to set through goptions *)
let () =
  let open Names in
  Lib.start_compilation DirPath.dummy (ModPath.MPfile DirPath.dummy)

let tokenize_string = Proof_diffs.tokenize_string
let diff_pp = diff_pp ~tokenize_string
let diff_str = diff_str ~tokenize_string

let tests = ref []
let add_test name test = tests := (mk_test name (TestCase test)) :: !tests

let log_out_ch = open_log_out_ch __FILE__
let cfprintf oc = Printf.(kfprintf (fun oc -> fprintf oc "") oc)
let cprintf s = cfprintf log_out_ch s
let _ = Proof_diffs.log_out_ch := log_out_ch

let string_of_string s : string = "\"" ^ s ^ "\""

(* todo: OCaml: why can't the body of the test function be given in the add_test line? *)

let t () =
  let expected : diff_list = [] in
  let diffs = diff_str "" "   " in

  assert_equal ~msg:"empty" ~printer:string_of_diffs expected diffs;
  let (has_added, has_removed) = has_changes diffs in
  assert_equal ~msg:"has `Added" ~printer:string_of_bool false has_added;
  assert_equal ~msg:"has `Removed" ~printer:string_of_bool false has_removed
let _ = add_test "diff_str empty" t


let t () =
  let expected : diff_list =
    [ `Common (0, 0, "a"); `Common (1, 1, "b"); `Common (2, 2, "c")] in
  let diffs = diff_str "a b c" " a  b\t  c\n" in

  assert_equal ~msg:"white space" ~printer:string_of_diffs expected diffs;
  let (has_added, has_removed) = has_changes diffs in
  assert_equal ~msg:"no `Added" ~printer:string_of_bool false has_added;
  assert_equal ~msg:"no `Removed" ~printer:string_of_bool false has_removed
let _ = add_test "diff_str white space" t

let t () =
  let expected : diff_list = [ `Removed (0, "a"); `Added (0, "b")] in
  let diffs = diff_str "a" "b" in

  assert_equal ~msg:"add/remove" ~printer:string_of_diffs expected diffs;
  let (has_added, has_removed) = has_changes diffs in
  assert_equal ~msg:"has `Added" ~printer:string_of_bool true has_added;
  assert_equal ~msg:"has `Removed" ~printer:string_of_bool true has_removed
let _ = add_test "diff_str add/remove" t

(* lexer tweaks:
   comments are lexed as multiple tokens
   strings tokens include begin/end quotes and embedded ""
   single multibyte characters returned even if they're not keywords

   inputs that give a lexer failure (but no use case needs them yet):
     ".12"
     unterminated string
     invalid UTF-8 sequences
   *)
let t () =
  let str = "(* comment.field *) ?id () \"str\"\"ing\" \\ := Ж &gt; ∃ 'c' xx" in
  let toks = tokenize_string str in
  (*List.iter (fun x -> cprintf "'%s' " x) toks;*)
  (*cprintf "\n";*)
  let str_no_white = String.concat "" (String.split_on_char ' ' str) in
  assert_equal ~printer:(fun x -> x) str_no_white (String.concat "" toks);
  List.iter (fun s ->
    assert_equal ~msg:("'" ^ s ^ "' is a single token") ~printer:string_of_bool true (List.mem s toks))
    [ "(*"; "()"; ":="]

let _ = add_test "tokenize_string/diff_mode in lexer" t

open Pp

let rec flatten pp : Pp.t =
  match repr pp with
  | Ppcmd_glue l ->
    unrepr @@
    Ppcmd_glue
      (List.concat
         (List.map
            (fun x -> let x = flatten x in
              match repr x with
              | Ppcmd_glue l2 -> l2
              | _ -> [x])
            l))
  | Ppcmd_box (block, pp) -> unrepr @@ Ppcmd_box (block, flatten pp)
  | Ppcmd_tag (tag, pp) -> unrepr @@ Ppcmd_tag (tag, flatten pp)
  | _ -> pp

let write_diffs_option s =
  Goptions.set_string_option_value Proof_diffs.opt_name s

(* example that was failing from #8922 *)
let t () =
  write_diffs_option "removed";
  ignore (diff_str "X : ?Goal" "X : forall x : ?Goal0, ?Goal1");
  write_diffs_option "on"
let _ = add_test "shorten_diff_span failure from #8922" t

(* note pp_to_string concatenates adjacent strings, could become one token,
e.g. str " a" ++ str "b " will give a token "ab" *)
(* checks background is present and correct *)
let t () =
  let o_pp = str "a" ++ str "!" ++ str "c" in
  let n_pp = str "a" ++ str "?" ++ str "c" in
  let (o_exp, n_exp) = (wrap_in_bg "diff.removed" (str "a" ++ (tag "diff.removed" (str "!")) ++ str "c"),
                        wrap_in_bg "diff.added" (str "a" ++ (tag "diff.added" (str "?")) ++ str "c")) in
  let (o_diff, n_diff) = diff_pp o_pp n_pp in

  assert_equal ~msg:"removed" ~printer:db_string_of_pp o_exp o_diff;
  assert_equal ~msg:"added"   ~printer:db_string_of_pp n_exp n_diff
let _ = add_test "diff_pp/add_diff_tags add/remove" t

let t () =
  (*Printf.printf "%s\n" (string_of_diffs (diff_str "a d" "a b c d"));*)
  let o_pp = str "a" ++ str " d" in
  let n_pp = str "a" ++ str " b " ++ str " c " ++ str "d" ++ str " e " in
  let n_exp = flatten (wrap_in_bg "diff.added" (seq [
      str "a";
      str " "; (tag "start.diff.added" (str "b "));
      (tag "end.diff.added" (str " c")); str " ";
      (str "d");
      str " "; (tag "diff.added" (str "e")); str " "
      ])) in
  let (_, n_diff) = diff_pp o_pp n_pp in

  assert_equal ~msg:"added"   ~printer:db_string_of_pp n_exp (flatten n_diff)
let _ = add_test "diff_pp/add_diff_tags a span with spaces" t


let t () =
  let o_pp = str " " in
  let n_pp = tag "sometag" (str "a") in
  let n_exp = flatten (wrap_in_bg "diff.added" (tag "diff.added" (tag "sometag" (str "a")))) in
  let (_, n_diff) = diff_pp o_pp n_pp in

  assert_equal ~msg:"added"   ~printer:db_string_of_pp n_exp (flatten n_diff)
let _ = add_test "diff_pp/add_diff_tags diff tags outside existing tags" t

let t () =
  let o_pp = str " " in
  let n_pp = seq [(tag "sometag" (str " a ")); str "b"] in
  let n_exp = flatten (wrap_in_bg "diff.added"
      (seq [tag "sometag" (str " "); (tag "start.diff.added" (tag "sometag" (str "a ")));
          (tag "end.diff.added" (str "b"))]) ) in
  let (_, n_diff) = diff_pp o_pp n_pp in

  assert_equal ~msg:"added"   ~printer:db_string_of_pp n_exp (flatten n_diff)
let _ = add_test "diff_pp/add_diff_tags existing tagged values with spaces" t

let t () =
  let o_pp = str " " in
  let n_pp = str " a b " in
  let n_exp = flatten (wrap_in_bg "diff.added"
      (seq [str " "; tag "diff.added" (str "a b"); str " "])) in
  let (_, n_diff) = diff_pp o_pp n_pp in

  assert_equal ~msg:"added"   ~printer:db_string_of_pp n_exp (flatten n_diff)
let _ = add_test "diff_pp/add_diff_tags multiple tokens in pp" t

let t () =
  let o_pp = str "a d" in
  let n_pp = seq [str "a b"; str "c d"] in
  let n_exp = flatten (wrap_in_bg "diff.added"
      (seq [str "a "; tag "start.diff.added" (str "b");
            tag "end.diff.added" (str "c"); str " d"])) in
  let (_, n_diff) = diff_pp o_pp n_pp in

  assert_equal ~msg:"added"   ~printer:db_string_of_pp n_exp (flatten n_diff)
let _ = add_test "diff_pp/add_diff_tags token spanning multiple Ppcmd_strs" t

let t () =
  let o_pp = seq [str ""; str "a"] in
  let n_pp = seq [str ""; str "a b"] in
  let n_exp = flatten (wrap_in_bg "diff.added"
      (seq [str ""; str "a "; tag "diff.added" (str "b")])) in
  let (_, n_diff) = diff_pp o_pp n_pp in

  assert_equal ~msg:"added"   ~printer:db_string_of_pp n_exp (flatten n_diff)
let _ = add_test "diff_pp/add_diff_tags empty string preserved" t

(* todo: awaiting a change in the lexer to return the quotes of the string token *)
let t () =
  let s = "\"a b\"" in
  let o_pp = seq [str s] in
  let n_pp = seq [str "\"a b\" "] in
  cprintf "ppcmds: %s\n" (string_of_ppcmds n_pp);
  let n_exp = flatten (wrap_in_bg "diff.added"
      (seq [str ""; str "a "; tag "diff.added" (str "b")])) in
  let (_, n_diff) = diff_pp o_pp n_pp in

  assert_equal ~msg:"string" ~printer:string_of_string "a b" (List.hd (tokenize_string s));
  assert_equal ~msg:"added"   ~printer:db_string_of_pp n_exp (flatten n_diff)
let _ = if false then add_test "diff_pp/add_diff_tags token containing white space" t

let add_entries map idents rhs_pp =
  let make_entry() = { idents; rhs_pp } in
  List.iter (fun ident -> map := CString.Map.add ident (make_entry ()) !map) idents

let print_list hyps = List.iter (fun x -> cprintf "%s\n" (string_of_ppcmds (flatten x))) hyps
let db_print_list hyps = List.iter (fun x -> cprintf "%s\n" (db_string_of_pp (flatten x))) hyps


(* a : uint
   b : int car ->
   b : car
   a : uint int
DIFFS
   b : car   (remove int)
   b : car   (added bg only)
   a: uint int (add int)
*)
let t () =
  write_diffs_option "removed";   (* turn on "removed" option *)
  let o_line_idents = [ ["a"]; ["b"]] in
  let o_hyp_map = ref CString.Map.empty in
  add_entries o_hyp_map ["a"] (str " : uint");
  add_entries o_hyp_map ["b"] (str " : int car");
  let n_line_idents = [ ["b"]; ["a"]] in
  let n_hyp_map = ref CString.Map.empty in
  add_entries n_hyp_map ["b"] (str " : car");
  add_entries n_hyp_map ["a"] (str " : uint int");
  let expected = [flatten (wrap_in_bg "diff.removed" (seq [str "b"; str " : ";
                      (tag "diff.removed" (str "int")); str " car" ]));
                  flatten (wrap_in_bg "diff.added" (seq [str "b"; str " : car"]));
                  flatten (wrap_in_bg "diff.added" (seq [str "a";
                      str " : uint "; (tag "diff.added" (str "int")) ]))
  ] in

  let hyps_diff_list = diff_hyps o_line_idents !o_hyp_map n_line_idents !n_hyp_map in

  (*print_list hyps_diff_list;*)
  (*db_print_list hyps_diff_list;*)

  List.iter2 (fun exp act ->
      assert_equal ~msg:"added"   ~printer:db_string_of_pp exp (flatten act))
      expected hyps_diff_list
let _ = add_test "diff_hyps simple diffs" t

(* a : nat
  c, d : int ->
  a, b : nat
  d : int
DIFFS
 c, d : int (remove c,)
 a, b : nat (add ,b)
 d : int *)
let t () =
  write_diffs_option "removed";   (* turn on "removed" option *)
  let o_line_idents = [ ["a"]; ["c"; "d"]] in
  let o_hyp_map = ref CString.Map.empty in
  add_entries o_hyp_map ["a"] (str " : nat");
  add_entries o_hyp_map ["c"; "d"] (str " : int");
  let n_line_idents = [ ["a"; "b"]; ["d"]] in
  let n_hyp_map = ref CString.Map.empty in
  add_entries n_hyp_map ["a"; "b"] (str " : nat");
  add_entries n_hyp_map ["d"] (str " : int");
  let expected = [flatten (wrap_in_bg "diff.added" (seq [str "a"; (tag "start.diff.added"
                      (str ", ")); (tag "end.diff.added" (str "b")); str " : nat" ]));
                  flatten (wrap_in_bg "diff.removed" (seq [(tag "start.diff.removed"
                      (str "c")); (tag "end.diff.removed" (str ",")); str " "; str "d";  str " : int" ]));
                  flatten (seq [str "d"; str " : int" ])
  ] in

  let hyps_diff_list = diff_hyps o_line_idents !o_hyp_map n_line_idents !n_hyp_map in

  (*print_list hyps_diff_list;*)
  (*print_list expected;*)

  (*db_print_list hyps_diff_list;*)
  (*db_print_list expected;*)

  List.iter2 (fun exp act ->
      assert_equal ~msg:"added"   ~printer:db_string_of_pp exp (flatten act))
      expected hyps_diff_list
let _ = add_test "diff_hyps compacted" t

(* a : uint
   b : int
   c : nat ->
   b, a, c : nat
DIFFS
   a : uint (remove)
   b : int (remove)
   b, a, c : nat (add b, a,)
 is this a realistic use case?
*)
let t () =
  write_diffs_option "removed";   (* turn on "removed" option *)
  let o_line_idents = [ ["a"]; ["b"]; ["c"]] in
  let o_hyp_map = ref CString.Map.empty in
  add_entries o_hyp_map ["a"] (str " : uint");
  add_entries o_hyp_map ["b"] (str " : int");
  add_entries o_hyp_map ["c"] (str " : nat");
  let n_line_idents = [ ["b"; "a"; "c"] ] in
  let n_hyp_map = ref CString.Map.empty in
  add_entries n_hyp_map ["b"; "a"; "c"] (str " : nat");
  let expected = [flatten (wrap_in_bg "diff.removed" (seq [str "a"; str " : ";
                      (tag "diff.removed" (str "uint"))]));
                  flatten (wrap_in_bg "diff.removed" (seq [str "b"; str " : ";
                      (tag "diff.removed" (str "int"))]));
                  flatten (wrap_in_bg "diff.added" (seq [(tag "start.diff.added"
                      (str "b")); str ", "; str "a"; (tag "end.diff.added" (str ","));
                      str " "; str "c"; str " : nat"]))
  ] in

  let hyps_diff_list = diff_hyps o_line_idents !o_hyp_map n_line_idents !n_hyp_map in

  (*print_list hyps_diff_list;*)
  (*db_print_list hyps_diff_list;*)

  List.iter2 (fun exp act ->
      assert_equal ~msg:"added"   ~printer:db_string_of_pp exp (flatten act))
      expected hyps_diff_list
let _ = add_test "diff_hyps compacted with join" t

(* b, a, c : nat ->
   a : uint
   b : int
   c : nat
DIFFS
   b, a, c : nat (remove b,a,)
   a : uint (add uint)
   b : int (add int)
   c : nat
 is this a realistic use case? *)
let t () =
  write_diffs_option "removed";   (* turn on "removed" option *)
  let o_line_idents = [ ["b"; "a"; "c"] ] in
  let o_hyp_map = ref CString.Map.empty in
  add_entries o_hyp_map ["b"; "a"; "c"] (str " : nat");
  let n_line_idents = [ ["a"]; ["b"]; ["c"]] in
  let n_hyp_map = ref CString.Map.empty in
  add_entries n_hyp_map ["a"] (str " : uint");
  add_entries n_hyp_map ["b"] (str " : int");
  add_entries n_hyp_map ["c"] (str " : nat");
  let expected = [flatten (wrap_in_bg "diff.removed" (seq [(tag "start.diff.removed"
                      (str "b")); str ", "; str "a"; (tag "end.diff.removed" (str ","));
                      str " "; str "c"; str " : nat"]));
                  flatten (wrap_in_bg "diff.added" (seq [str "a"; str " : "; (tag "diff.added" (str "uint"))]));
                  flatten (wrap_in_bg "diff.added" (seq [str "b"; str " : "; (tag "diff.added" (str "int"))]));
                  flatten (seq [str "c"; str " : nat"])
  ] in

  let hyps_diff_list = diff_hyps o_line_idents !o_hyp_map n_line_idents !n_hyp_map in

  (*print_list hyps_diff_list;*)
  (*db_print_list hyps_diff_list;*)

  List.iter2 (fun exp act ->
      assert_equal ~msg:"added"   ~printer:db_string_of_pp exp (flatten act))
      expected hyps_diff_list
let _ = add_test "diff_hyps compacted with split" t

(* i : nat
   b : bool
   j : nat ->
   i, j : nat
DIFFS
   b : bool (removed)
   i, j : nat
*)
let t () =
  write_diffs_option "removed";   (* turn on "removed" option *)
  let o_line_idents = [ ["i"]; ["b"]; ["j"] ] in
  let o_hyp_map = ref CString.Map.empty in
  add_entries o_hyp_map ["i"] (str " : nat");
  add_entries o_hyp_map ["b"] (str " : bool");
  add_entries o_hyp_map ["j"] (str " : nat");
  let n_line_idents = [ ["i"; "j"]] in
  let n_hyp_map = ref CString.Map.empty in
  add_entries n_hyp_map ["i"; "j"] (str " : nat");
  let expected = [flatten (wrap_in_bg "diff.removed"
                      (seq [tag "start.diff.removed" (str "b"); tag "end.diff.removed" (str " : bool")]));
                  flatten (seq [str "i"; str ", "; str "j"; str " : nat"])
  ] in

  let hyps_diff_list = diff_hyps o_line_idents !o_hyp_map n_line_idents !n_hyp_map in

  (* print_list hyps_diff_list; *)
  (* db_print_list hyps_diff_list; *)

  List.iter2 (fun exp act ->
      assert_equal ~msg:"added"   ~printer:db_string_of_pp exp (flatten act))
      expected hyps_diff_list
let _ = add_test "diff_hyps removal causes compaction from #14577" t

(* other potential tests
coqtop/terminal formatting BLOCKED: CAN'T GET TAGS IN FORMATTER
  white space at end of line
  spanning diffs
shorten_diff_span

MAYBE NOT WORTH IT
diff_pp/add_diff_tags
  add/remove - show it preserves, recurs and processes:
    nested in boxes
    breaks, etc.  preserved
diff_pp_combined with/without removed
*)


let _ = run_tests __FILE__ log_out_ch (List.rev !tests)
