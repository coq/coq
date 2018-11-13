{ autoconf, ocamlPackages }:

{
  buildInputs = [ autoconf ] ++ (with ocamlPackages; [ ocaml findlib camlp5 ocamlgraph ]);
  configure = "autoconf && ./configure";
  make = "make all test-suite";
}
