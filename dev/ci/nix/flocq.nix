{ autoconf, automake }:

{
  buildInputs = [ autoconf automake ];
  configure = "./autogen.sh && ./configure";
  make = "./remake";
}
