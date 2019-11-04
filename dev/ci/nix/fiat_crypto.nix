{ ocamlPackages }:
{
  buildInputs = with ocamlPackages; [ ocaml findlib ];
  configure = "git submodule update --init --recursive && ulimit -s 32768";
  make = "make c-files printlite lite && make -j 1 coq";
}
