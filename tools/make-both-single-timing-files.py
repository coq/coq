#!/usr/bin/env python
import sys
from TimeFileMaker import *

if __name__ == '__main__':
    USAGE = 'Usage: %s AFTER_FILE_NAME BEFORE_FILE_NAME [OUTPUT_FILE_NAME ..]' % sys.argv[0]
    HELP_STRING = r'''Formats timing information from the output of two invocations of `coqc -time` into a sorted table'''
    if len(sys.argv) < 3 or '--help' in sys.argv[1:] or '-h' in sys.argv[1:]:
        print(USAGE)
        if '--help' in sys.argv[1:] or '-h' in sys.argv[1:]:
            print(HELP_STRING)
            if len(sys.argv) == 2: sys.exit(0)
        sys.exit(1)
    else:
        left_dict = get_single_file_times(sys.argv[1])
        right_dict = get_single_file_times(sys.argv[2])
        table = make_diff_table_string(left_dict, right_dict, tag="Code")
        print_or_write_table(table, sys.argv[3:])
