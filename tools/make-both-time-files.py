#!/usr/bin/env python3
from TimeFileMaker import *

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=r'''Formats timing information from the output of two invocations of `make TIMED=1` into a sorted table.''')
    add_sort_by(parser)
    add_real(parser)
    add_after_file_name(parser)
    add_before_file_name(parser)
    add_output_file_name(parser)
    args = parser.parse_args()
    left_dict = get_times(args.AFTER_FILE_NAME, use_real=args.real)
    right_dict = get_times(args.BEFORE_FILE_NAME, use_real=args.real)
    table = make_diff_table_string(left_dict, right_dict, sort_by=args.sort_by)
    print_or_write_table(table, args.OUTPUT_FILE_NAME)
