#!/usr/bin/env python3
import sys
from TimeFileMaker import *

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=r'''Formats timing information from the output of `make TIMED=1` into a sorted table.''')
    add_real(parser)
    add_file_name(parser)
    add_output_file_name(parser)
    add_include_mem(parser)
    add_sort_by_mem(parser)
    args = parser.parse_args()
    stats_dict = get_times_and_mems(args.FILE_NAME, use_real=args.real, include_mem=args.include_mem)
    table = make_table_string(stats_dict, include_mem=args.include_mem, sort_by_mem=args.sort_by_mem)
    print_or_write_table(table, args.OUTPUT_FILE_NAME)
