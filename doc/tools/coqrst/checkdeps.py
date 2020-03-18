##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #         Copyright INRIA, CNRS and contributors             ##
## <O___,, # (see version control and CREDITS file for authors & dates) ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
from __future__ import print_function
import sys

missing_deps = []

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

def missing_dep(dep):
    missing_deps.append(dep)

def report_missing_deps():
    if len(missing_deps) > 0:
        deps = " ".join(missing_deps)
        eprint('Cannot find package(s) `%s` (needed to build documentation)' % deps)
        eprint('You can run `pip3 install %s` to install it/them.' % deps)
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

try:
    import sphinxcontrib.bibtex
except:
    missing_dep('sphinxcontrib-bibtex')

report_missing_deps()
