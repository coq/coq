(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "deprecated-info-tactical,profile-backtracking,extraction-logical-axiom") -*- *)

(* Test that mentioning a few warnings defined in plugins works. The failure
mode here is that these result in a warning about unknown warnings, since the
plugins are not known at command line parsing time. *)
