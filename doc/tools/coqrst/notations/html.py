##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #   INRIA, CNRS and contributors - Copyright 1999-2018       ##
## <O___,, #       (see CREDITS file for the list of authors)           ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
"""A visitor for ANTLR notation ASTs, producing raw HTML.

Uses the dominate package.
"""

from dominate import tags

from .parsing import parse
from .TacticNotationsParser import TacticNotationsParser
from .TacticNotationsVisitor import TacticNotationsVisitor

class TacticNotationsToHTMLVisitor(TacticNotationsVisitor):
    def visitRepeat(self, ctx:TacticNotationsParser.RepeatContext):
        with tags.span(_class="repeat-wrapper"):
            with tags.span(_class="repeat"):
                self.visitChildren(ctx)
            repeat_marker = ctx.LGROUP().getText()[1]
            separator = ctx.ATOM()
            tags.sup(repeat_marker)
            if separator:
                tags.sub(separator.getText())

    def visitCurlies(self, ctx:TacticNotationsParser.CurliesContext):
        sp = tags.span(_class="curlies")
        sp.add("{")
        with sp:
            self.visitChildren(ctx)
        sp.add("}")

    def visitAtomic(self, ctx:TacticNotationsParser.AtomicContext):
        tags.span(ctx.ATOM().getText())

    def visitHole(self, ctx:TacticNotationsParser.HoleContext):
        tags.span(ctx.ID().getText()[1:], _class="hole")
        sub = ctx.SUB()
        if sub:
            tags.sub(sub.getText()[1:])

    def visitMeta(self, ctx:TacticNotationsParser.MetaContext):
        txt = ctx.METACHAR().getText()[1:]
        if (txt == "{") or (txt == "}"):
            tags.span(txt)
        else:
            tags.span(txt, _class="meta")

    def visitWhitespace(self, ctx:TacticNotationsParser.WhitespaceContext):
        tags.span(" ")          # TODO: no need for a <span> here

def htmlize(notation):
    """Translate notation to a dominate HTML tree"""
    top = tags.span(_class='notation')
    with top:
        TacticNotationsToHTMLVisitor().visit(parse(notation))
    return top

def htmlize_str(notation):
    """Translate notation to a raw HTML document"""
    # ‘pretty=True’ introduces spurious spaces
    return htmlize(notation).render(pretty=False)

def htmlize_p(notation):
    """Like `htmlize`, wrapped in a ‘p’.
    Does not return: instead, must be run in a dominate context.
    """
    with tags.p():
        htmlize(notation)
