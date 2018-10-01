# If you want to use a more sophisticated set of arguments:
# $ nix-shell default.nix --arg shell true
import ./default.nix { shell = true; }
