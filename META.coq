# TODO: Move to META.in once coq_makefile2 is merged.
# We need to reuse:
# - The variable substitution mechanism.
# - Sourcing of "coq_install_path" and "coq_version" variables.
#
# With this rules, we would have:
#  version = ${coq_version}
# and
#  linkopts(byte)   = "-dllpath ${coq_install_path}/kernel/byterun/ -dllib -lcoqrun"

description = "The Coq Proof Assistant Plugin API"
version = "8.7"

directory = ""
requires = "camlp5"

package "config" (

  description = "Coq Configuration Variables"
  version     = "8.7"

  directory   = "config"

)

package "lib" (

  description = "Base Coq Library"
  version     = "8.7"

  directory   = "lib"

  requires         = "str, unix, threads, coq.config"

  archive(byte)    = "clib.cma"
  archive(byte)   += "lib.cma"

  archive(native)  = "clib.cmxa"
  archive(native) += "lib.cmxa"

)

package "vm" (

  description = "Coq VM"
  version     = "8.7"

  directory        = "kernel/byterun"

# We should generate this file at configure time for local byte builds
# to work properly.

# Enable this setting for local byte builds, disabling the one below.
#  linkopts(byte)   = "-dllpath path_to_coq/kernel/byterun/ -dllib -lcoqrun"

  linkopts(byte)   = "-dllib -lcoqrun"
  linkopts(native) = "-cclib -lcoqrun"

)

package "kernel" (

  description = "Coq's Kernel"
  version     = "8.7"

  directory   = "kernel"

  requires    = "dynlink, coq.lib, coq.vm"

  archive(byte)    = "kernel.cma"
  archive(native)  = "kernel.cmxa"

)

package "library" (

  description = "Coq Libraries (vo) support"
  version     = "8.7"

  requires    = "coq.kernel"

  directory   = "library"

  archive(byte)    = "library.cma"
  archive(native)  = "library.cmxa"

)

package "intf" (

  description = "Coq Public Data Types"
  version     = "8.7"

  requires    = "coq.library"

  directory   = "intf"

  archive(byte)    = "intf.cma"
  archive(native)  = "intf.cmxa"
)

package "engine" (

  description = "Coq Tactic Engine"
  version     = "8.7"

  requires    = "coq.library"
  directory   = "engine"

  archive(byte)    = "engine.cma"
  archive(native)  = "engine.cmxa"

)

package "pretyping" (

  description = "Coq Pretyper"
  version     = "8.7"

  requires    = "coq.engine"
  directory   = "pretyping"

  archive(byte)    = "pretyping.cma"
  archive(native)  = "pretyping.cmxa"

)

package "interp" (

  description = "Coq Term Interpretation"
  version     = "8.7"

  requires    = "coq.pretyping"
  directory   = "interp"

  archive(byte)    = "interp.cma"
  archive(native)  = "interp.cmxa"

)

package "grammar" (

  description = "Coq Base Grammar"
  version     = "8.7"

  requires    = "coq.interp"
  directory   = "grammar"

  archive(byte)   = "grammar.cma"
  archive(native) = "grammar.cmxa"
)

package "proofs" (

  description = "Coq Proof Engine"
  version     = "8.7"

  requires    = "coq.interp"
  directory   = "proofs"

  archive(byte)    = "proofs.cma"
  archive(native)  = "proofs.cmxa"

)

package "parsing" (

  description = "Coq Parsing Engine"
  version     = "8.7"

  requires    = "camlp5.gramlib, coq.proofs"
  directory   = "parsing"

  archive(byte)    = "parsing.cma"
  archive(native)  = "parsing.cmxa"

)

package "printing" (

  description = "Coq Printing Engine"
  version     = "8.7"

  requires    = "coq.parsing"
  directory   = "printing"

  archive(byte)    = "printing.cma"
  archive(native)  = "printing.cmxa"

)

package "tactics" (

  description = "Coq Basic Tactics"
  version     = "8.7"

  requires    = "coq.printing"
  directory   = "tactics"

  archive(byte)    = "tactics.cma"
  archive(native)  = "tactics.cmxa"

)

package "vernac" (

  description = "Coq Vernacular Interpreter"
  version     = "8.7"

  requires    = "coq.tactics"
  directory   = "vernac"

  archive(byte)    = "vernac.cma"
  archive(native)  = "vernac.cmxa"

)

package "stm" (

  description = "Coq State Transactional Machine"
  version     = "8.7"

  requires    = "coq.vernac"
  directory   = "stm"

  archive(byte)    = "stm.cma"
  archive(native)  = "stm.cmxa"

)

package "API" (

  description = "Coq API"
  version     = "8.7"

  requires    = "coq.stm"
  directory   = "API"

  archive(byte)    = "API.cma"
  archive(native)  = "API.cmxa"

)

package "ltac" (

  description = "Coq LTAC Plugin"
  version     = "8.7"

  requires    = "coq.API"
  directory   = "plugins/ltac"

  archive(byte)    = "ltac_plugin.cmo"
  archive(native)  = "ltac_plugin.cmx"

)

package "toplevel" (

  description = "Coq Toplevel"
  version     = "8.7"

  requires    = "coq.stm"
  directory   = "toplevel"

  archive(byte)    = "toplevel.cma"
  archive(native)  = "toplevel.cmxa"

)

package "idetop" (

  description = "Coq IDE Libraries"
  version     = "8.7"

  requires    = "coq.toplevel"
  directory   = "ide"

  archive(byte)    = "coqidetop.cma"
  archive(native)  = "coqidetop.cmxa"

)

# XXX Depends on way less than toplevel
package "ide" (

  description = "Coq IDE Libraries"
  version     = "8.7"

# XXX Add GTK
  requires    = "coq.toplevel"
  directory   = "ide"

  archive(byte)    = "ide.cma"
  archive(native)  = "ide.cmxa"

)
