{}:

rec {
  make = "make IGNORECOQVERSION=true";
  clean = "${make} clean";
}
