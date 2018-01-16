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

package "clib" (
  description = "Base General Coq Library"
  version     = "8.7"

  directory   = "clib"
  requires    = "str, unix, threads"

  archive(byte)    = "clib.cma"
  archive(native)  = "clib.cmxa"
)

package "lib" (

  description = "Base Coq-Specific Library"
  version     = "8.7"

  directory   = "lib"

  requires    = "coq.clib, coq.config"

  archive(byte)   = "lib.cma"
  archive(native) = "lib.cmxa"

)

package "vm" (

  description = "Coq VM"
  version     = "8.7"

  directory        = "kernel/byterun"

# We could generate this file at configure time for the share byte
# build path to work properly.
#
# Enable this setting for local byte builds if you want dynamic linking:
#
#  linkopts(byte)   = "-dllpath path_to_coq/kernel/byterun/ -dllib -lcoqrun"

# We currently prefer static linking of the VM.
  archive(byte)    = "libcoqrun.a"
  linkopts(byte)   = "-custom"

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

package "ltac" (

  description = "Coq LTAC Plugin"
  version     = "8.7"

  requires    = "coq.stm"
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

package "plugins" (

  description = "Coq built-in plugins"
  version     = "8.7"

  requires    = ""
  directory   = "plugins"

  package "tauto" (

    description = "Coq tauto plugin"
    version     = "8.7"

    requires    = "coq.ltac"
    directory   = "ltac"

    archive(byte)    = "tauto_plugin.cmo"
    archive(native)  = "tauto_plugin.cmx"
  )

  package "omega" (

    description = "Coq omega plugin"
    version     = "8.7"

    requires    = "coq.ltac"
    directory   = "omega"

    archive(byte)    = "omega_plugin.cmo"
    archive(native)  = "omega_plugin.cmx"
  )

  package "romega" (

    description = "Coq romega plugin"
    version     = "8.7"

    requires    = "coq.plugins.omega"
    directory   = "romega"

    archive(byte)    = "romega_plugin.cmo"
    archive(native)  = "romega_plugin.cmx"
  )

  package "micromega" (

    description = "Coq micromega plugin"
    version     = "8.7"

    requires    = "num,coq.ltac"
    directory   = "micromega"

    archive(byte)    = "micromega_plugin.cmo"
    archive(native)  = "micromega_plugin.cmx"
  )

  package "quote" (

    description = "Coq quote plugin"
    version     = "8.7"

    requires    = "coq.ltac"
    directory   = "quote"

    archive(byte)    = "quote_plugin.cmo"
    archive(native)  = "quote_plugin.cmx"
  )

  package "newring" (

    description = "Coq newring plugin"
    version     = "8.7"

    requires    = "coq.plugins.quote"
    directory   = "setoid_ring"

    archive(byte)    = "newring_plugin.cmo"
    archive(native)  = "newring_plugin.cmx"
  )

  package "fourier" (

    description = "Coq fourier plugin"
    version     = "8.7"

    requires    = "coq.ltac"
    directory   = "fourier"

    archive(byte)    = "fourier_plugin.cmo"
    archive(native)  = "fourier_plugin.cmx"
  )

  package "extraction" (

    description = "Coq extraction plugin"
    version     = "8.7"

    requires    = "coq.ltac"
    directory   = "extraction"

    archive(byte)    = "extraction_plugin.cmo"
    archive(native)  = "extraction_plugin.cmx"
  )

  package "cc" (

    description = "Coq cc plugin"
    version     = "8.7"

    requires    = "coq.ltac"
    directory   = "cc"

    archive(byte)    = "cc_plugin.cmo"
    archive(native)  = "cc_plugin.cmx"
  )

  package "ground" (

    description = "Coq ground plugin"
    version     = "8.7"

    requires    = "coq.ltac"
    directory   = "firstorder"

    archive(byte)    = "ground_plugin.cmo"
    archive(native)  = "ground_plugin.cmx"
  )

  package "rtauto" (

    description = "Coq rtauto plugin"
    version     = "8.7"

    requires    = "coq.ltac"
    directory   = "rtauto"

    archive(byte)    = "rtauto_plugin.cmo"
    archive(native)  = "rtauto_plugin.cmx"
  )

  package "btauto" (

    description = "Coq btauto plugin"
    version     = "8.7"

    requires    = "coq.ltac"
    directory   = "btauto"

    archive(byte)    = "btauto_plugin.cmo"
    archive(native)  = "btauto_plugin.cmx"
  )

  package "recdef" (

    description = "Coq recdef plugin"
    version     = "8.7"

    requires    = "coq.plugins.extraction"
    directory   = "funind"

    archive(byte)    = "recdef_plugin.cmo"
    archive(native)  = "recdef_plugin.cmx"
  )

  package "nsatz" (

    description = "Coq nsatz plugin"
    version     = "8.7"

    requires    = "num,coq.ltac"
    directory   = "nsatz"

    archive(byte)    = "nsatz_plugin.cmo"
    archive(native)  = "nsatz_plugin.cmx"
  )

  package "natsyntax" (

    description = "Coq natsyntax plugin"
    version     = "8.7"

    requires    = ""
    directory   = "syntax"

    archive(byte)    = "nat_syntax_plugin.cmo"
    archive(native)  = "nat_syntax_plugin.cmx"
  )

  package "zsyntax" (

    description = "Coq zsyntax plugin"
    version     = "8.7"

    requires    = ""
    directory   = "syntax"

    archive(byte)    = "z_syntax_plugin.cmo"
    archive(native)  = "z_syntax_plugin.cmx"
  )

  package "rsyntax" (

    description = "Coq rsyntax plugin"
    version     = "8.7"

    requires    = ""
    directory   = "syntax"

    archive(byte)    = "r_syntax_plugin.cmo"
    archive(native)  = "r_syntax_plugin.cmx"
  )

  package "int31syntax" (

    description = "Coq int31syntax plugin"
    version     = "8.7"

    requires    = ""
    directory   = "syntax"

    archive(byte)    = "int31_syntax_plugin.cmo"
    archive(native)  = "int31_syntax_plugin.cmx"
  )

  package "asciisyntax" (

    description = "Coq asciisyntax plugin"
    version     = "8.7"

    requires    = ""
    directory   = "syntax"

    archive(byte)    = "ascii_syntax_plugin.cmo"
    archive(native)  = "ascii_syntax_plugin.cmx"
  )

  package "stringsyntax" (

    description = "Coq stringsyntax plugin"
    version     = "8.7"

    requires    = "coq.plugins.asciisyntax"
    directory   = "syntax"

    archive(byte)    = "string_syntax_plugin.cmo"
    archive(native)  = "string_syntax_plugin.cmx"
  )

  package "derive" (

    description = "Coq derive plugin"
    version     = "8.7"

    requires    = ""
    directory   = "derive"

    archive(byte)    = "derive_plugin.cmo"
    archive(native)  = "derive_plugin.cmx"
  )

  package "ssrmatching" (

    description = "Coq ssrmatching plugin"
    version     = "8.7"

    requires    = "coq.ltac"
    directory   = "ssrmatching"

    archive(byte)    = "ssrmatching_plugin.cmo"
    archive(native)  = "ssrmatching_plugin.cmx"
  )

  package "ssreflect" (

    description = "Coq ssreflect plugin"
    version     = "8.7"

    requires    = "coq.plugins.ssrmatching"
    directory   = "ssr"

    archive(byte)    = "ssreflect_plugin.cmo"
    archive(native)  = "ssreflect_plugin.cmx"
  )
)
