##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #   INRIA, CNRS and contributors - Copyright 1999-2019       ##
## <O___,, #       (see CREDITS file for the list of authors)           ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
"""A visitor for ANTLR notation ASTs, producing Sphinx nodes.

Unlike the HTML visitor, this produces Sphinx-friendly nodes that can be used by
all backends. If you just want HTML output, use the HTML visitor.
"""

from .parsing import parse
from .TacticNotationsParser import TacticNotationsParser
from .TacticNotationsVisitor import TacticNotationsVisitor

from docutils import nodes
from sphinx import addnodes

class TacticNotationsToSphinxVisitor(TacticNotationsVisitor):
    def defaultResult(self):
        return []

    def aggregateResult(self, aggregate, nextResult):
        if nextResult:
            aggregate.extend(nextResult)
        return aggregate

    def visitAlternative(self, ctx:TacticNotationsParser.AlternativeContext):
        return [nodes.inline('', '', *self.visitChildren(ctx), classes=['alternative'])]

    def visitAltblock(self, ctx:TacticNotationsParser.AltblockContext):
        return [nodes.inline('', '', *self.visitChildren(ctx), classes=['alternative-block'])]

    def visitAltsep(self, ctx:TacticNotationsParser.AltsepContext):
        return [nodes.inline('|', '\u200b', classes=['alternative-separator'])]

    @staticmethod
    def is_alternative(node):
        return isinstance(node, nodes.inline) and node['classes'] == ['alternative']

    def visitRepeat(self, ctx:TacticNotationsParser.RepeatContext):
        # Uses inline nodes instead of subscript and superscript to ensure that
        # we get the right customization hooks at the LaTeX level
        wrapper = nodes.inline('', '', classes=['repeat-wrapper'])

        children = self.visitChildren(ctx)
        if len(children) == 1 and self.is_alternative(children[0]):
            # Use a custom style if an alternative is nested in a repeat.
            # (We could detect this in CSS, but it's much harder in LaTeX.)

            children[0]['classes'] = ['repeated-alternative']
        wrapper += nodes.inline('', '', *children, classes=["repeat"])

        repeat_marker = ctx.LGROUP().getText()[1]
        wrapper += nodes.inline(repeat_marker, repeat_marker, classes=['notation-sup'])

        separator = ctx.ATOM() or ctx.PIPE()
        if separator:
            sep = separator.getText()
            wrapper += nodes.inline(sep, sep, classes=['notation-sub'])

        return [wrapper]

    def visitCurlies(self, ctx:TacticNotationsParser.CurliesContext):
        sp = nodes.inline('', '', classes=["curlies"])
        sp += nodes.Text("{")
        sp.extend(self.visitChildren(ctx))
        sp += nodes.Text("}")
        return [sp]

    def visitAtomic(self, ctx:TacticNotationsParser.AtomicContext):
        atom = ctx.ATOM().getText()
        sub = ctx.SUB()
        node = nodes.inline(atom, atom)

        if sub:
            sub_index = sub.getText()[2:]
            node += nodes.subscript(sub_index, sub_index)

        return [node]

    def visitPipe(self, ctx:TacticNotationsParser.PipeContext):
        return [nodes.Text("|")]

    def visitHole(self, ctx:TacticNotationsParser.HoleContext):
        hole = ctx.ID().getText()
        token_name = hole[1:]
        node = nodes.inline(hole, token_name, classes=["hole"])

        sub = ctx.SUB()
        if sub:
            sub_index = sub.getText()[2:]
            node += nodes.subscript(sub_index, sub_index)

        return [addnodes.pending_xref(token_name, node, reftype='token',
                                 refdomain='std', reftarget=token_name)]

    def visitEscaped(self, ctx:TacticNotationsParser.EscapedContext):
        escaped = ctx.ESCAPED().getText()
        return [nodes.inline(escaped, escaped[1:])]

    def visitWhitespace(self, ctx:TacticNotationsParser.WhitespaceContext):
        return [nodes.Text(" ")]

def sphinxify(notation):
    """Translate a notation into a Sphinx document tree."""
    vs = TacticNotationsToSphinxVisitor()
    return vs.visit(parse(notation))

def main():
    print(sphinxify("a := {+, b {+ c}}"))

if __name__ == '__main__':
    main()
