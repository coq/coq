##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #   INRIA, CNRS and contributors - Copyright 1999-2018       ##
## <O___,, #       (see CREDITS file for the list of authors)           ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
from __future__ import print_function
import sys

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

def missing_dep(dep):
    eprint('Cannot find %s (needed to build documentation)' % dep)
    eprint('You can run `pip3 install %s` to install it.' % dep)
    sys.exit(1)

try:
    import sphinx_rtd_theme
except:
    missing_dep('sphinx_rtd_theme')

try:
    import pexpect
except:
    missing_dep('pexpect')

try:
    import antlr4
except:
    missing_dep('antlr4-python3-runtime')

try:
    import bs4
except:
    missing_dep('beautifulsoup4')
