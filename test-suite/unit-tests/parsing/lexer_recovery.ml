(* The idea of this test is to have the lexer crash at a new line,
   with the ∀ symbol in line 2; then we test that we can recover correctly. *)
let doc =
"Definition map_union_weak `{β A, Insert K A (M A),
  ∀ A, Empty (M A),
   ∀ A, Lookup K A (M A),
    ∀ A, FinMapToList K A (M A)} {A} (m1 m2 : M A) :=
  map_imap (λ l v, Some (default v (m1 !! l))) m2."

let parse pa n =
  let entry = Pvernac.Vernac_.main_entry in
  let rec loop res n =
    if n = 0 then res else
      match Procq.Entry.parse entry pa with
      | None -> res
      | Some r -> loop (r :: res) (n-1)
  in
  loop [] n |> List.rev

let raw_pr_loc fmt (l : Loc.t) =
  let { Loc.fname=_; line_nb; bol_pos; line_nb_last; bol_pos_last; bp; ep } = l in
  Format.fprintf fmt "| line_nb: %d | bol_pos: %d | line_nb_last: %d | bol_pos_last: %d | bp: %d | ep: %d |"
    line_nb bol_pos line_nb_last bol_pos_last bp ep

let print_locs fmt { CAst.loc; _ } =
  Option.iter (Format.fprintf fmt "@[%a@]" raw_pr_loc) loc

let setup_pa () =
  let text = doc in
  Procq.Parsable.make (Gramlib.Stream.of_string text)

let parse_whole pa =
  parse pa 10

(* Use junk *)
let log_file = __FILE__ ^ ".log"

let main () =
  let pa = setup_pa () in
  let res, loc =
    try
      let _ = parse_whole pa in
      false, Procq.Parsable.loc pa
    with
    (* should be `E Undefined_token` but type is private *)
    | CLexer.Error.E _ ->
      (* We now consume a single token and check that the location is
         correct for "A" *)
      let () = Procq.Parsable.consume pa 1 in
      let loc = Procq.Parsable.loc pa in
      let res = (loc.line_nb = 2) && (loc.bol_pos = 52) && (loc.bp = 58) && (loc.ep = 59) in
      res, loc
    | _ -> false, Procq.Parsable.loc pa
  in
  let oc = Stdlib.open_out log_file in
  let outf = Format.formatter_of_out_channel oc in
  Format.fprintf outf "fail lexer test passed: %a@\n%!" raw_pr_loc loc;
  Format.pp_print_flush outf ();
  Stdlib.close_out oc;
  if res then exit 0 else exit 1

let () = main ()
