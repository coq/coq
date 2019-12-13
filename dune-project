(lang dune 2.0)
(name coq)
(using coq 0.1)

(formatting
 (enabled_for ocaml))

; We cannot set this to true until as long as the build is not
; properly bootstrapped [that is, we remove the voboot target]
;
; (generate_opam_files true)
