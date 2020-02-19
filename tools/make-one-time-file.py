#!/usr/bin/env python3
import sys
from TimeFileMaker import *

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=r'''Formats timing information from the output of `make TIMED=1` into a sorted table.''')
    add_real(parser)
    add_file_name(parser)
    add_output_file_name(parser)
    args = parser.parse_args()
    times_dict = get_times(args.FILE_NAME, use_real=args.real)
    table = make_table_string(times_dict)
    print_or_write_table(table, args.OUTPUT_FILE_NAME)
