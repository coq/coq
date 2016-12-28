description = "The Coq Proof Assistant Plugin API"
version = "8.6"

directory = ""
requires = "camlp5"

package "config" (

  description = "Coq Configuration Variables"
  version     = "8.6"

  directory   = "config"

)

package "lib" (

  description = "Base Coq Library"
  version     = "8.6"

  directory   = "lib"

  requires         = "coq.config"

  archive(byte)    = "clib.cma"
  archive(byte)   += "lib.cma"

  archive(native)  = "clib.cmxa"
  archive(native) += "lib.cmxa"

)

package "vm" (

  description = "Coq VM"

  version     = "8.6"

# EJGA FIXME: Unfortunately dllpath is dependent on the type of Coq
# install. In a local one we'll want kernel/byterun, in a non-local
# one we want to set it to coqlib. We should thus generate this file
# at configure time, but let's hear for some more feedback from
# experts.

# Enable for local native & byte builds
#  directory        = "kernel/byterun"

# Enable for local byte builds and set up properly
#  linkopts(byte)   = "-dllpath /path/to/coq/kernel/byterun/ -dllib -lcoqrun"

# Disable for local byte builds
  linkopts(byte)   = "-dllib -lcoqrun"
  linkopts(native) = "-cclib -lcoqrun"

)

package "kernel" (

  description = "The Coq's Kernel"
  version     = "8.6"

  directory   = "kernel"

  requires    = "coq.lib, coq.vm"

  archive(byte)    = "kernel.cma"
  archive(native)  = "kernel.cmxa"

)

package "library" (

  description = "Coq Libraries (vo) support"
  version     = "8.6"

  requires    = "coq.kernel"

  directory   = "library"

  archive(byte)    = "library.cma"
  archive(native)  = "library.cmxa"

)

package "intf" (

  description = "Coq Public Data Types"
  version     = "8.6"

  requires    = "coq.library"

  directory   = "intf"

)

package "engine" (

  description = "Coq Libraries (vo) support"
  version     = "8.6"

  requires    = "coq.library"
  directory   = "engine"

  archive(byte)    = "engine.cma"
  archive(native)  = "engine.cmxa"

)

package "pretyping" (

  description = "Coq Pretyper"
  version     = "8.6"

  requires    = "coq.engine"
  directory   = "pretyping"

  archive(byte)    = "pretyping.cma"
  archive(native)  = "pretyping.cmxa"

)

package "interp" (

  description = "Coq Term Interpretation"
  version     = "8.6"

  requires    = "coq.pretyping"
  directory   = "interp"

  archive(byte)    = "interp.cma"
  archive(native)  = "interp.cmxa"

)

package "grammar" (

  description = "Coq Base Grammar"
  version     = "8.6"

  requires    = "coq.interp"
  directory   = "grammar"

  archive(byte)   = "grammar.cma"
  archive(native) = "grammar.cmxa"
)

package "proofs" (

  description = "Coq Proof Engine"
  version     = "8.6"

  requires    = "coq.interp"
  directory   = "proofs"

  archive(byte)    = "proofs.cma"
  archive(native)  = "proofs.cmxa"

)

package "parsing" (

  description = "Coq Parsing Engine"
  version     = "8.6"

  requires    = "coq.proofs"
  directory   = "parsing"

  archive(byte)    = "parsing.cma"
  archive(native)  = "parsing.cmxa"

)

package "printing" (

  description = "Coq Printing Libraries"
  version     = "8.6"

  requires    = "coq.parsing"
  directory   = "printing"

  archive(byte)    = "printing.cma"
  archive(native)  = "printing.cmxa"

)

package "tactics" (

  description = "Coq Tactics"
  version     = "8.6"

  requires    = "coq.printing"
  directory   = "tactics"

  archive(byte)    = "tactics.cma"
  archive(native)  = "tactics.cmxa"

)

package "stm" (

  description = "Coq State Transactional Machine"
  version     = "8.6"

  requires    = "coq.tactics"
  directory   = "stm"

  archive(byte)    = "stm.cma"
  archive(native)  = "stm.cmxa"

)

package "toplevel" (

  description = "Coq Toplevel"
  version     = "8.6"

  requires    = "coq.stm"
  directory   = "toplevel"

  archive(byte)    = "toplevel.cma"
  archive(native)  = "toplevel.cmxa"

)

package "highparsing" (

  description = "Coq Extra Parsing"
  version     = "8.6"

  requires    = "coq.toplevel"
  directory   = "parsing"

  archive(byte)    = "highparsing.cma"
  archive(native)  = "highparsing.cmxa"

)

package "ltac" (

  description = "Coq LTAC Plugin"
  version     = "8.6"

  requires    = "coq.highparsing"
  directory   = "ltac"

  archive(byte)    = "ltac.cma"
  archive(native)  = "ltac.cmxa"

)
