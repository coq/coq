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
Drive coqtop with Python!
=========================

This module is a simple pexpect-based driver for coqtop, based on the old
REPL interface.
"""

import os
import re

import pexpect

class CoqTop:
    """Create an instance of coqtop.

    Use this as a context manager: no instance of coqtop is created until
    you call `__enter__`.  coqtop is terminated when you `__exit__` the
    context manager.

    Sentence parsing is very basic for now (a "." in a quoted string will
    confuse it).
    """

    COQTOP_PROMPT = re.compile("\r\n[^< ]+ < ")

    def __init__(self, coqtop_bin=None, color=False, args=None) -> str:
        """Configure a coqtop instance (but don't start it yet).

        :param coqtop_bin: The path to coqtop; uses $COQBIN by default, falling back to "coqtop"
        :param color:      When True, tell coqtop to produce ANSI color codes (see
                           the ansicolors module)
        :param args:       Additional arugments to coqtop.
        """
        BOOT = True
        if os.getenv('COQBOOT') == "no":
            BOOT = False
        self.coqtop_bin = coqtop_bin or os.path.join(os.getenv('COQBIN', ""), "coqtop")
        if not pexpect.utils.which(self.coqtop_bin):
            raise ValueError("coqtop binary not found: '{}'".format(self.coqtop_bin))
        self.args = (args or []) + ["-boot"] * BOOT + ["-color", "on"] * color
        self.coqtop = None

    def __enter__(self):
        if self.coqtop:
            raise ValueError("This module isn't re-entrant")
        self.coqtop = pexpect.spawn(self.coqtop_bin, args=self.args, echo=False, encoding="utf-8")
        # Disable delays (http://pexpect.readthedocs.io/en/stable/commonissues.html?highlight=delaybeforesend)
        self.coqtop.delaybeforesend = 0
        self.next_prompt()
        return self

    def __exit__(self, type, value, traceback):
        self.coqtop.kill(9)

    def next_prompt(self):
        "Wait for the next coqtop prompt, and return the output preceeding it."
        self.coqtop.expect(CoqTop.COQTOP_PROMPT, timeout = 10)
        return self.coqtop.before

    def sendone(self, sentence):
        """Send a single sentence to coqtop.

        :sentence: One Coq sentence (otherwise, Coqtop will produce multiple
                   prompts and we'll get confused)
        """
        # Suppress newlines, but not spaces: they are significant in notations
        sentence = re.sub(r"[\r\n]+", " ", sentence).strip()
        self.coqtop.sendline(sentence)
        try:
            output = self.next_prompt()
        except:
            print("Error while sending the following sentence to coqtop: {}".format(sentence))
            raise
        # print("Got {}".format(repr(output)))
        return output

def sendmany(*sentences):
    """A small demo: send each sentence in sentences and print the output"""
    with CoqTop() as coqtop:
        for sentence in sentences:
            print("=====================================")
            print(sentence)
            print("-------------------------------------")
            response = coqtop.sendone(sentence)
            print(response)

def main():
    """Run a simple performance test and demo `sendmany`"""
    with CoqTop() as coqtop:
        for _ in range(200):
            print(repr(coqtop.sendone("Check nat.")))
        sendmany("Goal False -> True.", "Proof.", "intros H.",
                 "Check H.", "Chchc.", "apply I.", "Qed.")

if __name__ == '__main__':
    main()
