{ ocamlPackages }:

{
  buildInputs = with ocamlPackages; [ ocaml findlib menhir ];
  configure = "./configure -ignore-coq-version x86_64-linux";
  make = "make all check-proof";
}
