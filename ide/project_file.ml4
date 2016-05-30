type target =
  | ML of string (* ML file : foo.ml -> (ML "foo.ml") *)
  | MLI of string (* MLI file : foo.mli -> (MLI "foo.mli") *)
  | ML4 of string (* ML4 file : foo.ml4 -> (ML4 "foo.ml4") *)
  | MLLIB of string (* MLLIB file : foo.mllib -> (MLLIB "foo.mllib") *)
  | MLPACK of string (* MLLIB file : foo.mlpack -> (MLLIB "foo.mlpack") *)
  | V of string  (* V file : foo.v -> (V "foo") *)
  | Arg of string
  | Special of string * string * bool * string
    (* file, dependencies, is_phony, command *)
  | Subdir of string
  | Def of string * string (* X=foo -> Def ("X","foo") *)
  | MLInclude of string (* -I physicalpath *)
  | Include of string * string (* -Q physicalpath logicalpath *)
  | RInclude of string * string (* -R physicalpath logicalpath *)

type install =
  | NoInstall
  | TraditionalInstall
  | UserInstall
  | UnspecInstall

exception Parsing_error
let rec parse_string = parser
  | [< '' ' | '\n' | '\t' >] -> ""
  | [< 'c; s >] -> (String.make 1 c)^(parse_string s)
  | [< >] -> ""
and parse_string2 = parser
  | [< ''"' >] -> ""
  | [< 'c; s >] -> (String.make 1 c)^(parse_string2 s)
  | [< >] -> raise Parsing_error
and parse_skip_comment = parser
  | [< ''\n'; s >] -> s
  | [< 'c; s >] -> parse_skip_comment s
  | [< >] -> [< >]
and parse_args = parser
  | [< '' ' | '\n' | '\t'; s >] -> parse_args s
  | [< ''#'; s >] -> parse_args (parse_skip_comment s)
  | [< ''"'; str = parse_string2; s >] -> ("" ^ str) :: parse_args s
  | [< 'c; str = parse_string; s >] -> ((String.make 1 c) ^ str) :: (parse_args s)
  | [< >] -> []


let parse f =
  let c = open_in f in
  let res = parse_args (Stream.of_channel c) in
    close_in c;
    res

let rec process_cmd_line orig_dir ((project_file,makefile,install,opt) as opts) l = function
  | [] -> opts, l
  | ("-h"|"--help") :: _ ->
    raise Parsing_error
  | ("-no-opt"|"-byte") :: r ->
    process_cmd_line orig_dir (project_file,makefile,install,false) l r
  | ("-full"|"-opt") :: r ->
    process_cmd_line orig_dir (project_file,makefile,install,true) l r
  | "-impredicative-set" :: r ->
    Feedback.msg_warning (Pp.str "Please now use \"-arg -impredicative-set\" instead of \"-impredicative-set\" alone to be more uniform.");
    process_cmd_line orig_dir opts (Arg "-impredicative-set" :: l) r
  | "-no-install" :: r ->
    Feedback.msg_warning (Pp.(++) (Pp.str "Option -no-install is deprecated.") (Pp.(++) (Pp.spc ()) (Pp.str "Use \"-install none\" instead")));
    process_cmd_line orig_dir (project_file,makefile,NoInstall,opt) l r
  | "-install" :: d :: r ->
    if install <> UnspecInstall then Feedback.msg_warning (Pp.str "-install sets more than once.");
    let install =
      match d with
	| "user" -> UserInstall
	| "none" -> NoInstall
	| "global" -> TraditionalInstall
	| _ -> Feedback.msg_warning (Pp.(++) (Pp.str "invalid option '") (Pp.(++) (Pp.str d) (Pp.str "' passed to -install.")));
          install
    in
    process_cmd_line orig_dir (project_file,makefile,install,opt) l r
  | "-custom" :: com :: dependencies :: file :: r ->
    Feedback.msg_warning (Pp.app
    (Pp.str "Please now use \"-extra[-phony] result deps command\" instead of \"-custom command deps result\".")
    (Pp.pr_arg Pp.str "It follows makefile target declaration order and has a clearer semantic.")
    );
    process_cmd_line orig_dir opts (Special (file,dependencies,false,com) :: l) r
  | "-extra" :: file :: dependencies :: com :: r ->
    process_cmd_line orig_dir opts (Special (file,dependencies,false,com) :: l) r
  | "-extra-phony" :: target :: dependencies :: com :: r ->
    process_cmd_line orig_dir opts (Special (target,dependencies,true,com) :: l) r
  | "-Q" :: d :: lp :: r ->
    process_cmd_line orig_dir opts ((Include (CUnix.correct_path d orig_dir, lp)) :: l) r
  | "-I" :: d :: r ->
    process_cmd_line orig_dir opts ((MLInclude (CUnix.correct_path d orig_dir)) :: l) r
  | "-R" :: p :: lp :: r ->
    process_cmd_line orig_dir opts (RInclude (CUnix.correct_path p orig_dir,lp) :: l) r
  | ("-Q"|"-R"|"-I"|"-custom"|"-extra"|"-extra-phony") :: _ ->
    raise Parsing_error
  | "-f" :: file :: r ->
    let file = CUnix.remove_path_dot (CUnix.correct_path file orig_dir) in
    let () = match project_file with
      | None -> ()
      | Some _ -> Feedback.msg_warning (Pp.str
	"Several features will not work with multiple project files.")
    in
    let (opts',l') = process_cmd_line (Filename.dirname file) (Some file,makefile,install,opt) l (parse file) in
      process_cmd_line orig_dir opts' l' r
  | ["-f"] ->
    raise Parsing_error
  | "-o" :: file :: r ->
      begin try
	let _ = String.index file '/' in
	  raise Parsing_error
      with Not_found ->
	let () = match makefile with
	  |None -> ()
	  |Some f ->
	     Feedback.msg_warning (Pp.(++) (Pp.str "Only one output file is genererated. ") (Pp.(++) (Pp.str f) (Pp.str " will not be.")))
	in process_cmd_line orig_dir (project_file,Some file,install,opt) l r
      end
  | v :: "=" :: def :: r ->
    process_cmd_line orig_dir opts (Def (v,def) :: l) r
  | "-arg" :: a :: r ->
    process_cmd_line orig_dir opts (Arg a :: l) r
  | f :: r ->
      let f = CUnix.correct_path f orig_dir in
	process_cmd_line orig_dir opts ((
          if Filename.check_suffix f ".v" then V f
	  else if (Filename.check_suffix f ".ml") then ML f
	  else if (Filename.check_suffix f ".ml4") then ML4 f
	  else if (Filename.check_suffix f ".mli") then MLI f
	  else if (Filename.check_suffix f ".mllib") then MLLIB f
	  else if (Filename.check_suffix f ".mlpack") then MLPACK f
	  else Subdir f) :: l) r

let process_cmd_line orig_dir opts l args =
  let (opts, l) = process_cmd_line orig_dir opts l args in
  opts, List.rev l

let rec post_canonize f =
  if Filename.basename f = Filename.current_dir_name
  then let dir = Filename.dirname f in
    if dir = Filename.current_dir_name then f else post_canonize dir
  else f

(* Return: ((v,(mli,ml4,ml,mllib,mlpack),special,subdir),(ml_inc,q_inc,r_inc),(args,defs)) *)
let split_arguments args =
  List.fold_right
    (fun a ((v,(mli,ml4,ml,mllib,mlpack as m),o,s as t),
            (ml_inc,q_inc,r_inc as i),(args,defs as d)) ->
     match a with
     | V n ->
        ((CUnix.remove_path_dot n::v,m,o,s),i,d)
     | ML n ->
        ((v,(mli,ml4,CUnix.remove_path_dot n::ml,mllib,mlpack),o,s),i,d)
     | MLI n ->
        ((v,(CUnix.remove_path_dot n::mli,ml4,ml,mllib,mlpack),o,s),i,d)
     | ML4 n ->
        ((v,(mli,CUnix.remove_path_dot n::ml4,ml,mllib,mlpack),o,s),i,d)
     | MLLIB n ->
        ((v,(mli,ml4,ml,CUnix.remove_path_dot n::mllib,mlpack),o,s),i,d)
     | MLPACK n ->
        ((v,(mli,ml4,ml,mllib,CUnix.remove_path_dot n::mlpack),o,s),i,d)
     | Special (n,dep,is_phony,c) ->
        ((v,m,(n,dep,is_phony,c)::o,s),i,d)
     | Subdir n ->
        ((v,m,o,n::s),i,d)
     | MLInclude p ->
        let ml_new = (CUnix.remove_path_dot (post_canonize p),
                      CUnix.canonical_path_name p) in
        (t,(ml_new::ml_inc,q_inc,r_inc),d)
     | Include (p,l) ->
        let q_new = (CUnix.remove_path_dot (post_canonize p),l,
		     CUnix.canonical_path_name p) in
        (t,(ml_inc,q_new::q_inc,r_inc),d)
     | RInclude (p,l) ->
        let r_new = (CUnix.remove_path_dot (post_canonize p),l,
		     CUnix.canonical_path_name p) in
        (t,(ml_inc,q_inc,r_new::r_inc),d)
     | Def (v,def) ->
        (t,i,(args,(v,def)::defs))
     | Arg a ->
        (t,i,(a::args,defs)))
    args (([],([],[],[],[],[]),[],[]),([],[],[]),([],[]))

let read_project_file f =
  split_arguments
    (snd (process_cmd_line (Filename.dirname f) (Some f, None, NoInstall, true) [] (parse f)))

let args_from_project file project_files default_name =
  let build_cmd_line ml_inc i_inc r_inc args =
    List.fold_right (fun (_,i) o -> "-I" :: i :: o) ml_inc
      (List.fold_right (fun (_,l,i) o -> "-Q" :: i :: l :: o) i_inc
        (List.fold_right (fun (_,l,p) o -> "-R" :: p :: l :: o) r_inc
	  (List.fold_right (fun a o -> parse_args (Stream.of_string a) @ o) args [])))
  in try
      let (fname,(_,(ml_inc,i_inc,r_inc),(args,_))) = List.hd project_files in
	fname, build_cmd_line ml_inc i_inc r_inc args
    with Failure _ ->
      let rec find_project_file dir = try
	let fname = Filename.concat dir default_name in
	let ((v_files,_,_,_),(ml_inc,i_inc,r_inc),(args,_)) =
          read_project_file fname in
	fname, build_cmd_line ml_inc i_inc r_inc args
      with Sys_error s ->
	let newdir = Filename.dirname dir in
	  if dir = newdir then "",[] else find_project_file newdir
      in find_project_file (Filename.dirname file)
