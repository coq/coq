open OUnit
open Utest
open CoqProject_file

let tests = ref []
let add_test name test = tests := (mk_test name (TestCase test)) :: !tests

let sourced_file x = { thing = x; source = ProjectFile }

(* Implicit argument for `read_project_file` *)
let warning_fn _ = ()

let t () =
  let project_file_contents = "" in
  bracket_tmpfile
  (fun (project_file_path, project_file_channel) ->
    output_string project_file_channel project_file_contents;
    flush project_file_channel;
    let expected : unit project = {
      project_file = Some project_file_path;
      makefile = None;
      native_compiler = None;
      docroot = None;

      files = [];
      cmd_line_files = [];
      meta_file = Absent;

      ml_includes = [];
      r_includes = [];
      q_includes = [];
      extra_args = [];
      defs = [];

      extra_data = ();
    } in
    assert_equal expected (read_project_file ~warning_fn project_file_path)
  ) ()
let _ = add_test "empty file" t

let t () =
  let project_file_contents = "-arg \"-w default\" -arg -w -arg foo -arg \"-set 'Default Goal Selector=!'\"" in
  bracket_tmpfile
  (fun (project_file_path, project_file_channel) ->
    output_string project_file_channel project_file_contents;
    flush project_file_channel;
    let expected : unit project = {
      project_file = Some project_file_path;
      makefile = None;
      native_compiler = None;
      docroot = None;

      files = [];
      cmd_line_files = [];
      meta_file = Absent;

      ml_includes = [];
      r_includes = [];
      q_includes = [];
      extra_args = List.map sourced_file ["-w"; "default"; "-w"; "foo"; "-set"; "Default Goal Selector=!"];
      defs = [];

      extra_data = ();
    } in
    assert_equal expected (read_project_file ~warning_fn project_file_path)
  ) ()
let _ = add_test "-arg separation" t

let _ = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
