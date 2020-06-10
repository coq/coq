{ autoconf, automake, ocaml, flocq }:

{
  buildInputs = [ autoconf automake ocaml ];
  coqBuildInputs = [ flocq ];
  configure = "autoreconf && ./configure";
  make = "./remake";
  clean = "./remake clean";
}
