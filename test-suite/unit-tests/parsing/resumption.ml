let doc =
"Definition a := Type.
Definition b := Prop.
Definition c :=
    b.
Definition d :=
      c.
(* this is a comment *)
"

let parse pa n =
  let entry = Pvernac.Vernac_.main_entry in
  let rec loop res n =
    if n = 0 then res else
      match Pcoq.Entry.parse entry pa with
      | None -> res
      | Some r -> loop (r :: res) (n-1)
  in
  loop [] n |> List.rev

let raw_pr_loc fmt (l : Loc.t) =
  let { Loc.fname=_; line_nb; bol_pos; line_nb_last; bol_pos_last; bp; ep } = l in
  Format.fprintf fmt "| line_nb: %d | bol_pos: %d | line_nb_last: %d | bol_pos_last: %d | bp: %d | ep: %d |"
    line_nb bol_pos line_nb_last bol_pos_last bp ep

let _print_locs fmt { CAst.loc; _ } =
  Option.iter (Format.fprintf fmt "@[%a@]@\n" raw_pr_loc) loc

let parse_whole () =
  let text = doc in
  let pa = Pcoq.Parsable.make (Gramlib.Stream.of_string text) in
  parse pa 10

(* From clexer *)
let after loc =
  Loc.{ loc with
        line_nb = loc.line_nb_last;
        bol_pos = loc.bol_pos_last;
        bp      = loc.ep;
      }

let parse_n n =
  let pa = Pcoq.Parsable.make (Gramlib.Stream.of_string doc) in
  let res1 = parse pa n in
  let loc = Pcoq.Parsable.loc pa |> CLexer.after in
  (* Format.eprintf "@\nlast loc:@\n@[%a@]@\n@\n%!" raw_pr_loc loc; *)
  let str = Gramlib.Stream.of_string doc in
  Gramlib.Stream.njunk loc.ep str;
  let pa = Pcoq.Parsable.make ~loc str in
  let res2 = parse pa 10 in
  res1 @ res2

let log_file = __FILE__ ^ ".log"

let main () =
  let reference = parse_whole () in
  let test = [parse_n 1; parse_n 2; parse_n 3; parse_n 4] in
  let res = List.for_all (fun t -> t = reference) test in
  let oc = Stdlib.open_out log_file in
  let outf = Format.formatter_of_out_channel oc in
  Format.fprintf outf "split parsing test passed: %b@\n%!" res;
  Format.pp_print_flush outf ();
  Stdlib.close_out oc;
  if res then exit 0 else exit 1

let () = main ()
