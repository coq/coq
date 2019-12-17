#!/usr/bin/env python3
from TimeFileMaker import *

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=r'''Formats timing information from the output of two invocations of `coqc -time` into a sorted table''')
    add_sort_by(parser)
    add_user(parser, single_timing=True)
    add_fuzz(parser)
    add_after_file_name(parser)
    add_before_file_name(parser)
    add_output_file_name(parser)
    args = parser.parse_args()
    left_dict = get_single_file_times(args.AFTER_FILE_NAME, use_real=args.real)
    right_dict = get_single_file_times(args.BEFORE_FILE_NAME, use_real=args.real)
    left_dict, right_dict = adjust_fuzz(left_dict, right_dict, fuzz=args.fuzz)
    table = make_diff_table_string(left_dict, right_dict, tag="Code", sort_by=args.sort_by)
    print_or_write_table(table, args.OUTPUT_FILE_NAME)
