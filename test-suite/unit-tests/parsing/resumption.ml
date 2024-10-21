let doc =
"Definition a := Type.
Definition b := Prop.
 Definition c :=
    b.
Definition d :=
      c.
(* this is a comment *)
  Definition m :=
 forall (x : Type), x.
"

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

let parse_whole () =
  let text = doc in
  let pa = Procq.Parsable.make (Gramlib.Stream.of_string text) in
  parse pa 10

(* Use junk *)
let parse_n n =
  let pa = Procq.Parsable.make (Gramlib.Stream.of_string doc) in
  let res1 = parse pa n in
  let loc = Procq.Parsable.loc pa |> CLexer.after in
  let str = Gramlib.Stream.of_string doc in
  Gramlib.Stream.njunk () loc.bp str;
  let pa = Procq.Parsable.make ~loc str in
  let res2 = parse pa 10 in
  res1 @ res2

(* Use offset to set count and avoid the junk *)
let parse_n_offset n =
  let pa = Procq.Parsable.make (Gramlib.Stream.of_string doc) in
  let res1 = parse pa n in
  let loc = Procq.Parsable.loc pa |> CLexer.after in
  let doc = String.sub doc loc.bp (String.length doc - loc.bp) in
  let str = Gramlib.Stream.of_string ~offset:loc.bp doc in
  let pa = Procq.Parsable.make ~loc str in
  let res2 = parse pa 10 in
  res1 @ res2

let log_file = __FILE__ ^ ".log"

let main () =
  let reference = parse_whole () in
  let test1 = [parse_n 1; parse_n 2; parse_n 3; parse_n 4; parse_n 5] in
  let test2 = [parse_n_offset 1; parse_n_offset 2; parse_n_offset 3; parse_n_offset 4; parse_n_offset 5] in
  let tests = test1 @ test2 in
  let res = List.for_all (fun t -> t = reference) tests in
  let oc = Stdlib.open_out log_file in
  let outf = Format.formatter_of_out_channel oc in
  Format.fprintf outf "split parsing test passed: %b@\n%!" res;
  List.iter (Format.fprintf outf "locs@\n@[<v>%a@]@\n@\n" (Format.pp_print_list print_locs)) tests;
  Format.pp_print_flush outf ();
  Stdlib.close_out oc;
  if res then exit 0 else exit 1

let () = main ()
