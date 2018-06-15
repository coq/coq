##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #   INRIA, CNRS and contributors - Copyright 1999-2018       ##
## <O___,, #       (see CREDITS file for the list of authors)           ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
"""
Use CoqDoc to highlight Coq snippets
====================================

Pygment's Coq parser isn't the best; instead, use coqdoc to highlight snippets.
Only works for full, syntactically valid sentences; on shorter snippets, coqdoc
swallows parts of the input.

Works by reparsing coqdoc's output into the output that Sphinx expects from a
lexer.
"""

import os
import platform
from tempfile import mkstemp
from subprocess import check_output

from bs4 import BeautifulSoup
from bs4.element import NavigableString

COQDOC_OPTIONS = ['--body-only', '--no-glob', '--no-index', '--no-externals',
                  '-s', '--html', '--stdout', '--utf8']

COQDOC_SYMBOLS = ["->", "<-", "<->", "=>", "<=", ">=", "<>", "~", "/\\", "\\/", "|-", "*", "forall", "exists"]
COQDOC_HEADER = "".join("(** remove printing {} *)".format(s) for s in COQDOC_SYMBOLS)

def coqdoc(coq_code, coqdoc_bin=None):
    """Get the output of coqdoc on coq_code."""
    coqdoc_bin = coqdoc_bin or os.path.join(os.getenv("COQBIN"), "coqdoc")
    fd, filename = mkstemp(prefix="coqdoc-", suffix=".v")
    if platform.system().startswith("CYGWIN"):
        # coqdoc currently doesn't accept cygwin style paths in the form "/cygdrive/c/..."
        filename = check_output(["cygpath", "-w", filename]).decode("utf-8").strip()
    try:
        os.write(fd, COQDOC_HEADER.encode("utf-8"))
        os.write(fd, coq_code.encode("utf-8"))
        os.close(fd)
        return check_output([coqdoc_bin] + COQDOC_OPTIONS + [filename], timeout = 10).decode("utf-8")
    finally:
        os.remove(filename)

def is_whitespace_string(elem):
    return isinstance(elem, NavigableString) and elem.strip() == ""

def strip_soup(soup, pred):
    """Strip elements maching pred from front and tail of soup."""
    while soup.contents and pred(soup.contents[-1]):
        soup.contents.pop()

    skip = 0
    for elem in soup.contents:
        if not pred(elem):
            break
        skip += 1

    soup.contents[:] = soup.contents[skip:]

def lex(source):
    """Convert source into a stream of (css_classes, token_string)."""
    coqdoc_output = coqdoc(source)
    soup = BeautifulSoup(coqdoc_output, "html.parser")
    root = soup.find(class_='code')
    strip_soup(root, is_whitespace_string)
    for elem in root.children:
        if isinstance(elem, NavigableString):
            yield [], elem
        elif elem.name == "span":
            cls = "coqdoc-{}".format(elem['title'])
            yield [cls], elem.string
        elif elem.name == 'br':
            pass
        else:
            raise ValueError(elem)

def main():
    """Lex stdin (for testing purposes)"""
    import sys
    for classes, text in lex(sys.stdin.read()):
        print(repr(text) + "\t" ' '.join(classes))

if __name__ == '__main__':
    main()
