#!/usr/bin/env python
import sys
from TimeFileMaker import *

if __name__ == '__main__':
    USAGE = 'Usage: %s FILE_NAME [OUTPUT_FILE_NAME ..]' % sys.argv[0]
    HELP_STRING = r'''Formats timing information from the output of `make TIMED=1` into a sorted table.

The input is expected to contain lines in the format:
FILE_NAME (...user: NUMBER_IN_SECONDS...)
'''
    if len(sys.argv) < 2 or '--help' in sys.argv[1:] or '-h' in sys.argv[1:]:
        print(USAGE)
        if '--help' in sys.argv[1:] or '-h' in sys.argv[1:]:
            print(HELP_STRING)
            if len(sys.argv) == 2: sys.exit(0)
        sys.exit(1)
    else:
        times_dict = get_times(sys.argv[1])
        table = make_table_string(times_dict)
        print_or_write_table(table, sys.argv[2:])
