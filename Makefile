##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #   INRIA, CNRS and contributors - Copyright 1999-2019       ##
## <O___,, #       (see CREDITS file for the list of authors)           ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################

# The default build system is make-based one.
ifndef COQ_USE_DUNE
include Makefile.make
else
include Makefile.dune
endif
