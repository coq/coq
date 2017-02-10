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
Parse Coq's ANSI output.
========================

Translated to Python from Coq's terminal.ml.
"""

# pylint: disable=too-many-return-statements, too-many-branches

def parse_color(style, offset):
    color = style[offset] % 10
    if color == 0:
        return ("black", 1)
    elif color == 1:
        return ("red", 1)
    elif color == 2:
        return ("green", 1)
    elif color == 3:
        return ("yellow", 1)
    elif color == 4:
        return ("blue", 1)
    elif color == 5:
        return ("magenta", 1)
    elif color == 6:
        return ("cyan", 1)
    elif color == 7:
        return ("white", 1)
    elif color == 9:
        return ("default", 1)
    elif color == 8:
        nxt = style[offset + 1]
        if nxt == 5:
            return ("index-{}".format(style[offset + 1]), 2)
        elif nxt == 2:
            return ("rgb-{}-{}-{}".format(*style[offset+1:offset+4]), 4)
        else:
            raise ValueError("{}, {}".format(style, offset))
    else:
        raise ValueError()

def parse_style(style, offset, acc):
    offset = 0
    while offset < len(style):
        head = style[offset]

        if head == 0:
            acc.append("reset")
        elif head == 1:
            acc.append("bold")
        elif head == 3:
            acc.append("italic")
        elif head == 4:
            acc.append("underline")
        elif head == 7:
            acc.append("negative")
        elif head == 22:
            acc.append("no-bold")
        elif head == 23:
            acc.append("no-italic")
        elif head == 24:
            acc.append("no-underline")
        elif head == 27:
            acc.append("no-negative")
        else:
            color, suboffset = parse_color(style, offset)
            offset += suboffset - 1
            if 30 <= head < 40:
                acc.append("fg-{}".format(color))
            elif 40 <= head < 50:
                acc.append("bg-{}".format(color))
            elif 90 <= head < 100:
                acc.append("fg-light-{}".format(color))
            elif 100 <= head < 110:
                acc.append("bg-light-{}".format(color))

        offset += 1

def parse_ansi(code):
    """Parse an ansi code into a collection of CSS classes.

    :param code: A sequence of ‘;’-separated ANSI codes.  Do not include the
                 leading ‘^[[’ or the final ‘m’
    """
    classes = []
    parse_style([int(c) for c in code.split(';')], 0, classes)
    return ["ansi-" + cls for cls in classes]

if __name__ == '__main__':
    # As produced by Coq with ‘Check nat.’
    print(parse_ansi("92;49;22;23;24;27"))
