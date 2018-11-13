{ coqprime }:
{
  buildInputs = [ coqprime ];
  configure = "git submodule update --init --recursive && ulimit -s 32768";
  make = "make new-pipeline c-files";
}
