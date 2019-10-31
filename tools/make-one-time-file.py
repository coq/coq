#!/usr/bin/env python3
import sys
from TimeFileMaker import *

if __name__ == '__main__':
    USAGE = 'Usage: %s FILE_NAME [--real] [OUTPUT_FILE_NAME ..]' % sys.argv[0]
    HELP_STRING = r'''Formats timing information from the output of `make TIMED=1` into a sorted table.

The input is expected to contain lines in the format:
FILE_NAME (...user: NUMBER_IN_SECONDS...)
If --real is passed, then the lines are instead expected in the format:
FILE_NAME (...real: NUMBER_IN_SECONDS...)
'''
    use_real, args = parse_args(sys.argv, USAGE, HELP_STRING, allow_sort_by=False, min_arg_count=2)
    times_dict = get_times(args[1], use_real=use_real)
    table = make_table_string(times_dict)
    print_or_write_table(table, args[2:])
