# Some developers don't want a pinned nix-shell by default.
# If you want to use the pin nix-shell or a more sophisticated set of arguments:
# $ nix-shell default.nix --arg shell true
import ./default.nix { pkgs = import <nixpkgs> {}; shell = true; }
