#!/usr/bin/env python
from __future__ import with_statement
import os, sys, re

# This script parses the output of `make TIMED=1` into a dictionary
# mapping names of compiled files to the number of minutes and seconds
# that they took to compile.

STRIP_REG = re.compile('^(coq/|contrib/|)(?:theories/|src/)?')
STRIP_REP = r'\1'
INFINITY  = '\xe2\x88\x9e'

def reformat_time_string(time):
    seconds, milliseconds = time.split('.')
    seconds = int(seconds)
    minutes, seconds = int(seconds / 60), seconds % 60
    return '%dm%02d.%ss' % (minutes, seconds, milliseconds)

def get_times(file_name):
    '''
    Reads the contents of file_name, which should be the output of
    'make TIMED=1', and parses it to construct a dict mapping file
    names to compile durations, as strings.  Removes common prefixes
    using STRIP_REG and STRIP_REP.
    '''
    if file_name == '-':
        lines = sys.stdin.read()
    else:
        with open(file_name, 'r') as f:
            lines = f.read()
    reg = re.compile(r'^([^\s]+) \([^\)]*?user: ([0-9\.]+)[^\)]*?\)\s*$', re.MULTILINE)
    times = reg.findall(lines)
    if all(time in ('0.00', '0.01') for name, time in times):
        reg = re.compile(r'^([^\s]*) \([^\)]*?real: ([0-9\.]+)[^\)]*?\)\s*$', re.MULTILINE)
        times = reg.findall(lines)
    if all(STRIP_REG.search(name.strip()) for name, time in times):
        times = tuple((STRIP_REG.sub(STRIP_REP, name.strip()), time) for name, time in times)
    return dict((name, reformat_time_string(time)) for name, time in times)

def get_single_file_times(file_name):
    '''
    Reads the contents of file_name, which should be the output of
    'coqc -time', and parses it to construct a dict mapping lines to
    to compile durations, as strings.
    '''
    if file_name == '-':
        lines = sys.stdin.read()
    else:
        with open(file_name, 'r') as f:
            lines = f.read()
    reg = re.compile(r'^Chars ([0-9]+) - ([0-9]+) ([^ ]+) ([0-9\.]+) secs (.*)$', re.MULTILINE)
    times = reg.findall(lines)
    if len(times) == 0: return dict()
    longest = max(max((len(start), len(stop))) for start, stop, name, time, extra in times)
    FORMAT = 'Chars %%0%dd - %%0%dd %%s' % (longest, longest)
    return dict((FORMAT % (int(start), int(stop), name), reformat_time_string(time)) for start, stop, name, time, extra in times)

def make_sorting_key(times_dict, descending=True):
    def get_key(name):
        minutes, seconds = times_dict[name].replace('s', '').split('m')
        def fix_sign(num):
            return -num if descending else num
        return (fix_sign(int(minutes)), fix_sign(float(seconds)), name)
    return get_key

def get_sorted_file_list_from_times_dict(times_dict, descending=True):
    '''
    Takes the output dict of get_times and returns the list of keys,
    sorted by duration.
    '''
    return sorted(times_dict.keys(), key=make_sorting_key(times_dict, descending=descending))

def to_seconds(time):
    '''
    Converts a string time into a number of seconds.
    '''
    minutes, seconds = time.replace('s', '').split('m')
    sign = -1 if time[0] == '-' else 1
    return sign * (abs(int(minutes)) * 60 + float(seconds))

def from_seconds(seconds, signed=False):
    '''
    Converts a number of seconds into a string time.
    '''
    sign = ('-' if seconds < 0 else '+') if signed else ''
    seconds = abs(seconds)
    minutes = int(seconds) / 60
    seconds -= minutes * 60
    full_seconds = int(seconds)
    partial_seconds = int(100 * (seconds - full_seconds))
    return sign + '%dm%02d.%02ds' % (minutes, full_seconds, partial_seconds)

def sum_times(times, signed=False):
    '''
    Takes the values of an output from get_times, parses the time
    strings, and returns their sum, in the same string format.
    '''
    return from_seconds(sum(map(to_seconds, times)), signed=signed)

def format_percentage(num, signed=True):
    sign = ('-' if num < 0 else '+') if signed else ''
    num = abs(num)
    whole_part = int(num * 100)
    frac_part = int(100 * (num * 100 - whole_part))
    return sign + '%d.%02d%%' % (whole_part, frac_part)

def make_diff_table_string(left_times_dict, right_times_dict,
                           descending=True,
                           left_tag="After", tag="File Name", right_tag="Before", with_percent=True,
                           change_tag="Change", percent_change_tag="% Change"):
    # We first get the names of all of the compiled files: all files
    # that were compiled either before or after.
    all_names_dict = dict()
    all_names_dict.update(right_times_dict)
    all_names_dict.update(left_times_dict) # do the left (after) last, so that we give precedence to those ones
    if len(all_names_dict.keys()) == 0: return 'No timing data'
    prediff_times = tuple((name, to_seconds(left_times_dict.get(name,'0m0.0s')), to_seconds(right_times_dict.get(name,'0m0.0s')))
                          for name in all_names_dict.keys())
    diff_times_dict = dict((name, from_seconds(lseconds - rseconds, signed=True))
                           for name, lseconds, rseconds in prediff_times)
    percent_diff_times_dict = dict((name, ((format_percentage((lseconds - rseconds) / rseconds))
                                           if rseconds != 0 else (INFINITY if lseconds > 0 else 'N/A')))
                                   for name, lseconds, rseconds in prediff_times)
    # update to sort by approximate difference, first
    get_key = make_sorting_key(all_names_dict, descending=descending)
    all_names_dict = dict((name, (abs(int(to_seconds(diff_times_dict[name]))), get_key(name)))
                          for name in all_names_dict.keys())
    names = sorted(all_names_dict.keys(), key=all_names_dict.get)
    #names = get_sorted_file_list_from_times_dict(all_names_dict, descending=descending)
    # set the widths of each of the columns by the longest thing to go in that column
    left_sum = sum_times(left_times_dict.values())
    right_sum = sum_times(right_times_dict.values())
    left_sum_float = sum(map(to_seconds, left_times_dict.values()))
    right_sum_float = sum(map(to_seconds, right_times_dict.values()))
    diff_sum = from_seconds(left_sum_float - right_sum_float, signed=True)
    percent_diff_sum = (format_percentage((left_sum_float - right_sum_float) / right_sum_float)
                        if right_sum_float > 0 else 'N/A')
    left_width = max(max(map(len, ['N/A'] + list(left_times_dict.values()))), len(left_sum))
    right_width = max(max(map(len, ['N/A'] + list(right_times_dict.values()))), len(right_sum))
    far_right_width = max(max(map(len, ['N/A', change_tag] + list(diff_times_dict.values()))), len(diff_sum))
    far_far_right_width = max(max(map(len, ['N/A', percent_change_tag] + list(percent_diff_times_dict.values()))), len(percent_diff_sum))
    middle_width = max(map(len, names + [tag, "Total"]))
    format_string = ("%%(left)-%ds | %%(middle)-%ds | %%(right)-%ds || %%(far_right)-%ds"
                     % (left_width, middle_width, right_width, far_right_width))
    if with_percent:
        format_string += " | %%(far_far_right)-%ds" % far_far_right_width
    header = format_string % {'left': left_tag, 'middle': tag, 'right': right_tag, 'far_right': change_tag, 'far_far_right': percent_change_tag}
    total = format_string % {'left': left_sum, 'middle': "Total", 'right': right_sum, 'far_right': diff_sum, 'far_far_right': percent_diff_sum}
    # separator to go between headers and body
    sep = '-' * len(header)
    # the representation of the default value (0), to get replaced by N/A
    left_rep, right_rep, far_right_rep, far_far_right_rep = ("%%-%ds | " % left_width) % 0, (" | %%-%ds || " % right_width) % 0, ("|| %%-%ds" % far_right_width) % 0, ("| %%-%ds" % far_far_right_width) % 0
    return '\n'.join([header, sep, total, sep] +
                     [format_string % {'left': left_times_dict.get(name, 0),
                                       'middle': name,
                                       'right': right_times_dict.get(name, 0),
                                       'far_right': diff_times_dict.get(name, 0),
                                       'far_far_right': percent_diff_times_dict.get(name, 0)}
                      for name in names]).replace(left_rep, 'N/A'.center(len(left_rep) - 3) + ' | ').replace(right_rep, ' | ' + 'N/A'.center(len(right_rep) - 7) + ' || ').replace(far_right_rep, '|| ' + 'N/A'.center(len(far_right_rep) - 3)).replace(far_far_right_rep, '| ' + 'N/A'.center(len(far_far_right_rep) - 2))

def make_table_string(times_dict,
                      descending=True,
                      tag="Time"):
    if len(times_dict.keys()) == 0: return 'No timing data'
    # We first get the names of all of the compiled files, sorted by
    # duration
    names = get_sorted_file_list_from_times_dict(times_dict, descending=descending)
    # compute the widths of the columns
    times_width = max(max(map(len, times_dict.values())), len(sum_times(times_dict.values())))
    names_width = max(map(len, names + ["File Name", "Total"]))
    format_string = "%%-%ds | %%-%ds" % (times_width, names_width)
    header = format_string % (tag, "File Name")
    total = format_string % (sum_times(times_dict.values()),
                             "Total")
    sep = '-' * len(header)
    return '\n'.join([header, sep, total, sep] +
                     [format_string % (times_dict[name],
                                       name)
                      for name in names])

def print_or_write_table(table, files):
    if len(files) == 0 or '-' in files:
        print(table)
    for file_name in files:
        if file_name != '-':
            with open(file_name, 'w') as f:
                f.write(table)
