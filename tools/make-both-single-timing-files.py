#!/usr/bin/env python
import sys
from TimeFileMaker import *

if __name__ == '__main__':
    USAGE = 'Usage: %s [--sort-by=auto|absolute|diff] AFTER_FILE_NAME BEFORE_FILE_NAME [OUTPUT_FILE_NAME ..]' % sys.argv[0]
    HELP_STRING = r'''Formats timing information from the output of two invocations of `coqc -time` into a sorted table'''
    sort_by, args = parse_args(sys.argv, USAGE, HELP_STRING)
    left_dict = get_single_file_times(args[1])
    right_dict = get_single_file_times(args[2])
    table = make_diff_table_string(left_dict, right_dict, tag="Code", sort_by=sort_by)
    print_or_write_table(table, args[3:])
