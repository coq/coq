{ autoconf, automake, ssreflect }:

{
  buildInputs = [ autoconf automake ];
  coqBuildInputs = [ ssreflect ];
  configure = "./autogen.sh && ./configure";
  make = "./remake";
  clean = "./remake clean";
}
