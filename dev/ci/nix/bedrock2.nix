{}:
{
  configure = "git submodule update --init --recursive";
  clean = "(cd deps/bbv && make clean); (cd deps/riscv-coq && make clean); (cd compiler && make clean); (cd bedrock2 && make clean)";
}
