from __future__ import with_statement
from __future__ import division
from __future__ import unicode_literals
from __future__ import print_function
import sys
import re
import argparse
import os
import math
from io import open

# This script parses the output of `make TIMED=1` into a dictionary
# mapping names of compiled files to the number of minutes and seconds
# that they took to compile.

STRIP_REG = re.compile('^(?:%s/)?(coq/|contrib/|)(?:theories/|src/)?' % re.escape(os.getcwd()))
STRIP_REP = r'\1'
INFINITY  = '\u221e'

TIME_KEY = 'time'
MEM_KEY = 'mem'

def nonnegative(arg):
    v = int(arg)
    if v < 0: raise argparse.ArgumentTypeError("%s is an invalid non-negative int value" % arg)
    return v

def add_sort_by(parser):
    return parser.add_argument(
        '--sort-by', type=str, dest='sort_by', choices=('auto', 'absolute', 'diff'),
        default='auto',
        help=('How to sort the table entries.\n' +
              'The "auto" method sorts by absolute time differences ' +
              'rounded towards zero to a whole-number of seconds, then ' +
              'by times in the "after" column, and finally ' +
              'lexicographically by file name. This will put the ' +
              'biggest changes in either direction first, and will ' +
              'prefer sorting by build-time over subsecond changes in ' +
              'build time (which are frequently noise); lexicographic ' +
              'sorting forces an order on files which take effectively ' +
              'no time to compile.\n' +
              'The "absolute" method sorts by the total time taken.\n' +
              'The "diff" method sorts by the signed difference in time.'))

def add_sort_by_mem(parser):
    return parser.add_argument(
        '--sort-by-mem', action='store_true', dest='sort_by_mem',
        help=('Sort the table entries by memory rather than time.'))

def add_fuzz(parser):
    return parser.add_argument(
        '--fuzz', dest='fuzz', metavar='N', type=nonnegative, default=0,
        help=('By default, two lines are only considered the same if ' +
              'the character offsets and initial code strings match.  '
              'This option relaxes this constraint by allowing the ' +
              'character offsets to differ by up to N characters, as long ' +
              'as the total number of characters and initial code strings ' +
              'continue to match.  This is useful when there are small changes ' +
              'to a file, and you want to match later lines that have not ' +
              'changed even though the character offsets have changed.'))

def add_real(parser, single_timing=False):
    return parser.add_argument(
        '--real', action='store_true',
        help=(r'''Use real times rather than user times.

''' + ('''By default, the input is expected to contain lines in the format:
FILE_NAME (...user: NUMBER_IN_SECONDS...mem: NUMBER ko...)
If --real is passed, then the lines are instead expected in the format:
FILE_NAME (...real: NUMBER_IN_SECONDS...mem: NUMBER ko...)''' if not single_timing else
'''The input is expected to contain lines in the format:
Chars START - END COMMAND NUMBER secs (NUMBERu...)''')))

def add_user(parser, single_timing=False):
    return parser.add_argument(
        '--user', dest='real', action='store_false',
        help=(r'''Use user times rather than real times.

''' + ('''By default, the input is expected to contain lines in the format:
FILE_NAME (...real: NUMBER_IN_SECONDS...mem: NUMBER ko...)
If --user is passed, then the lines are instead expected in the format:
FILE_NAME (...user: NUMBER_IN_SECONDS...mem: NUMBER ko...)''' if not single_timing else
'''The input is expected to contain lines in the format:
Chars START - END COMMAND NUMBER secs (NUMBERu...)''')))

def add_include_mem(parser):
    return parser.add_argument(
        '--no-include-mem', dest='include_mem', default=True, action='store_false',
        help=(r'''Don't include memory in the table.'''))

# N.B. We need to include default=None for nargs='*', c.f., https://bugs.python.org/issue28609#msg280180
def add_file_name_gen(parser, prefix='', descr='file containing the build log', stddir='in', defaults=None, **kwargs):
    extra = ('' if defaults is None else ' (defaults to %s if no argument is passed)' % defaults)
    return parser.add_argument(
        prefix + 'FILE_NAME', type=str,
        help=('The name of the %s (use "-" for std%s)%s.' % (descr, stddir, extra)),
        **kwargs)

def add_file_name(parser): return add_file_name_gen(parser)
def add_after_file_name(parser): return add_file_name_gen(parser, 'AFTER_', 'file containing the "after" build log')
def add_before_file_name(parser): return add_file_name_gen(parser, 'BEFORE_', 'file containing the "before" build log')
def add_output_file_name(parser): return add_file_name_gen(parser, 'OUTPUT_', 'file to write the output table to', stddir='out', defaults='-', nargs='*', default=None)


def reformat_time_string(time):
    try:
        seconds, milliseconds = time.split('.')
    except ValueError:
        print('WARNING: Invalid time string: not the right number of dots (.); expected one: %s' % repr(time), file=sys.stderr)
        seconds, milliseconds = (time + '.').split('.')[:2]
        if seconds == '': seconds = 0
    seconds = int(seconds)
    minutes, seconds = divmod(seconds, 60)
    return '%dm%02d.%ss' % (minutes, seconds, milliseconds)

def get_file_lines(file_name):
    if file_name == '-':
        if hasattr(sys.stdin, 'buffer'):
            lines = sys.stdin.buffer.readlines()
        else:
            lines = sys.stdin.readlines()
    else:
        with open(file_name, 'rb') as f:
            lines = f.readlines()
    for line in lines:
        try:
            # Since we read the files in binary mode, we have to
            # normalize Windows line endings from \r\n to \n
            yield line.decode('utf-8').replace('\r\n', '\n')
        except UnicodeDecodeError: # invalid utf-8
            pass

def get_file(file_name):
    return ''.join(get_file_lines(file_name))

def merge_dicts(d1, d2):
    if d2 is None: return d1
    if d1 is None: return d2
    assert(isinstance(d1, dict))
    assert(isinstance(d2, dict))
    ret = {}
    for k in set(list(d1.keys()) + list(d2.keys())):
        ret[k] = merge_dicts(d1.get(k), d2.get(k))
    return ret

def get_mems_of_lines(lines):
    reg = re.compile(r'^([^\s]+) \([^\)]*?mem: ([0-9]+) ko[^\)]*?\)\s*$', re.MULTILINE)
    mems = reg.findall(lines)
    if all(STRIP_REG.search(name.strip()) for name, mem in mems):
        mems = tuple((STRIP_REG.sub(STRIP_REP, name.strip()), mem) for name, mem in mems)
    return dict((name, {MEM_KEY:int(mem)}) for name, mem in mems)

def get_times_of_lines(lines, use_real=False):
    reg_user = re.compile(r'^([^\s]+) \([^\)]*?user: ([0-9\.]+)[^\)]*?\)\s*$', re.MULTILINE)
    reg_real = re.compile(r'^([^\s]+) \([^\)]*?real: ([0-9\.]+)[^\)]*?\)\s*$', re.MULTILINE)
    reg = reg_real if use_real else reg_user
    times = reg.findall(lines)
    if all(time in ('0.00', '0.01') for name, time in times):
        reg = reg_real
        times = reg.findall(lines)
    if all(STRIP_REG.search(name.strip()) for name, time in times):
        times = tuple((STRIP_REG.sub(STRIP_REP, name.strip()), time) for name, time in times)
    return dict((name, {TIME_KEY:reformat_time_string(time)}) for name, time in times)

def get_times_and_mems(file_name, use_real=False, include_mem=True):
    # we only get the file once, in case it is a stream like stdin
    lines = get_file(file_name)
    return merge_dicts(get_times_of_lines(lines, use_real=use_real),
                       (get_mems_of_lines(lines) if include_mem else None))

def get_mems(file_name):
    '''
    Reads the contents of file_name, which should be the output of
    'make TIMED=1', and parses it to construct a dict mapping file
    names to peak memory usage, as integers.  Removes common prefixes
    using STRIP_REG and STRIP_REP.
    '''
    return get_mems_of_lines(get_file(file_name))

def get_times(file_name, use_real=False):
    '''
    Reads the contents of file_name, which should be the output of
    'make TIMED=1', and parses it to construct a dict mapping file
    names to compile durations, as strings.  Removes common prefixes
    using STRIP_REG and STRIP_REP.
    '''
    return get_times_of_lines(get_file(file_name))

def get_single_file_times(file_name, use_real=False):
    '''
    Reads the contents of file_name, which should be the output of
    'coqc -time', and parses it to construct a dict mapping lines to
    to compile durations, as strings.
    '''
    lines = get_file(file_name)
    reg = re.compile(r'^Chars ([0-9]+) - ([0-9]+) ([^ ]+) ([0-9\.]+) secs \(([0-9\.]+)u(.*)\)$', re.MULTILINE)
    times = reg.findall(lines)
    if len(times) == 0: return dict()
    longest = max(max((len(start), len(stop))) for start, stop, name, real, user, extra in times)
    FORMAT = 'Chars %%0%dd - %%0%dd %%s' % (longest, longest)
    return dict((FORMAT % (int(start), int(stop), name), {TIME_KEY:reformat_time_string(real if use_real else user)}) for start, stop, name, real, user, extra in times)

def fuzz_merge(l1, l2, fuzz):
    '''Takes two iterables of ((start, end, code), times) and a fuzz
    parameter, and yields a single iterable of ((start, stop, code),
    times1, times2)

    We only give both left and right if (a) the codes are the same,
    (b) the number of characters (stop - start) is the same, and (c)
    the difference between left and right code locations is <= fuzz.

    We keep a current guess at the overall offset, and prefer drawing
    from whichever list is earliest after correcting for current
    offset.

    '''
    assert(fuzz >= 0)
    cur_fuzz = 0
    l1 = list(l1)
    l2 = list(l2)
    cur1, cur2 = None, None
    while (len(l1) > 0 or cur1 is not None) and (len(l2) > 0 or cur2 is not None):
        if cur1 is None: cur1 = l1.pop(0)
        if cur2 is None: cur2 = l2.pop(0)
        ((s1, e1, c1), t1), ((s2, e2, c2), t2) = cur1, cur2
        assert(t1 is not None)
        assert(t2 is not None)
        s2_adjusted, e2_adjusted = s2 + cur_fuzz, e2 + cur_fuzz
        if cur1[0] == cur2[0]:
            yield (cur1, cur2)
            cur1, cur2 = None, None
            cur_fuzz = 0
        elif c1 == c2 and e1-s1 == e2-s2 and abs(s1 - s2) <= fuzz:
            yield (((s1, e1, c1), t1), ((s2, e2, c2), t2))
            cur1, cur2 = None, None
            cur_fuzz = s1 - s2
        elif s1 < s2_adjusted or (s1 == s2_adjusted and e1 <= e2):
            yield (((s1, e1, c1), t1), ((s1 - cur_fuzz, e1 - cur_fuzz, c1), None))
            cur1 = None
        else:
            yield (((s2 + cur_fuzz, e2 + cur_fuzz, c2), None), ((s2, e2, c2), t2))
            cur2 = None
    if len(l1) > 0:
        for i in l1: yield (i, (i[0], None))
    elif len(l2) > 0:
        for i in l2: yield ((i[0], None), i)

def adjust_fuzz(left_dict, right_dict, fuzz):
    reg = re.compile(r'Chars ([0-9]+) - ([0-9]+) (.*)$')
    left_dict_list = sorted(((int(s), int(e), c), v) for ((s, e, c), v) in ((reg.match(k).groups(), v) for k, v in left_dict.items()))
    right_dict_list = sorted(((int(s), int(e), c), v) for ((s, e, c), v) in ((reg.match(k).groups(), v) for k, v in right_dict.items()))
    merged = list(fuzz_merge(left_dict_list, right_dict_list, fuzz))
    if len(merged) == 0:
        # assert that both left and right dicts are empty
        assert(not left_dict)
        assert(not right_dict)
        return left_dict, right_dict
    longest = max(max((len(str(start1)), len(str(stop1)), len(str(start2)), len(str(stop2)))) for ((start1, stop1, code1), t1), ((start2, stop2, code2), t2) in merged)
    FORMAT1 = 'Chars %%0%dd - %%0%dd %%s' % (longest, longest)
    FORMAT2 = 'Chars %%0%dd-%%0%dd ~ %%0%dd-%%0%dd %%s' % (longest, longest, longest, longest)
    if fuzz == 0:
        left_dict = dict((FORMAT1 % k, t1) for (k, t1), _ in merged if t1 is not None)
        right_dict = dict((FORMAT1 % k, t2) for _, (k, t2) in merged if t2 is not None)
    else:
        left_dict = dict((FORMAT2 % (s1, e1, s2, e2, c1), t1) for ((s1, e1, c1), t1), ((s2, e2, c2), t2) in merged if t1 is not None)
        right_dict = dict((FORMAT2 % (s1, e1, s2, e2, c1), t2) for ((s1, e1, c1), t1), ((s2, e2, c2), t2) in merged if t2 is not None)
    return left_dict, right_dict

def fix_sign_for_sorting(num, descending=True):
    return -num if descending else num

def make_sorting_key(stats_dict, descending=True, sort_by_mem=False):
    if sort_by_mem:
        def get_key(name):
            if MEM_KEY not in stats_dict[name].keys():
                print('WARNING: %s has no mem key: %s' % (name, repr(stats_dict[name])), file=sys.stderr)
            mem = stats_dict[name].get(MEM_KEY, '0')
            return (fix_sign_for_sorting(int(mem), descending=descending),
                    name)
    else:
        def get_key(name):
            if TIME_KEY not in stats_dict[name].keys():
                print('WARNING: %s has no time key: %s' % (name, repr(stats_dict[name])), file=sys.stderr)
            minutes, seconds = stats_dict[name].get(TIME_KEY, '0m00s').replace('s', '').split('m')
            return (fix_sign_for_sorting(int(minutes), descending=descending),
                    fix_sign_for_sorting(float(seconds), descending=descending),
                    name)
    return get_key

def get_sorted_file_list_from_stats_dict(stats_dict, descending=True, sort_by_mem=False):
    '''
    Takes the output dict of get_times and returns the list of keys,
    sorted by duration.
    '''
    return sorted(stats_dict.keys(), key=make_sorting_key(stats_dict, descending=descending, sort_by_mem=sort_by_mem))

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
    full_centiseconds = round(abs(seconds) * 100)
    seconds = int(full_centiseconds) // 100
    centiseconds = full_centiseconds - (seconds * 100)
    minutes = int(seconds) // 60
    seconds -= minutes * 60
    return sign + '%dm%02d.%02ds' % (minutes, seconds, centiseconds)

def sum_times(times, signed=False):
    '''
    Takes the values of an output from get_times, parses the time
    strings, and returns their sum, in the same string format.
    '''
    # sort the times before summing because floating point addition is not associative
    return from_seconds(math.fsum(sorted(map(to_seconds, times))), signed=signed)

def format_percentage(num, signed=True):
    sign = ('-' if num < 0 else '+') if signed else ''
    num = abs(num)
    whole_part = int(num * 100)
    frac_part = int(100 * (num * 100 - whole_part))
    return sign + '%d.%02d%%' % (whole_part, frac_part)

def make_diff_table_string(left_dict, right_dict,
                           sort_by='auto',
                           descending=True, sort_by_mem=False,
                           left_tag='After', tag='File Name', right_tag='Before', with_percent=True,
                           left_mem_tag='Peak Mem', right_mem_tag='Peak Mem',
                           include_mem=False,
                           change_tag='Change', percent_change_tag='% Change',
                           change_mem_tag='Change (mem)', percent_change_mem_tag='% Change (mem)',
                           mem_fmt='%d ko'):
    # We first get the names of all of the compiled files: all files
    # that were compiled either before or after.
    all_names_dict = dict()
    all_names_dict.update(right_dict)
    all_names_dict.update(left_dict) # do the left (after) last, so that we give precedence to those ones
    if len(all_names_dict.keys()) == 0: return 'No timing data'
    get_time = (lambda d, name: to_seconds(d.get(name, {}).get(TIME_KEY, '0m0.0s')))
    prediff_times = tuple((name, get_time(left_dict, name), get_time(right_dict, name))
                          for name in all_names_dict.keys())
    diff_times_dict = dict((name, from_seconds(lseconds - rseconds, signed=True))
                           for name, lseconds, rseconds in prediff_times)
    percent_diff_times_dict = dict((name, ((format_percentage((lseconds - rseconds) / rseconds))
                                           if rseconds != 0 else (INFINITY if lseconds > 0 else 'N/A')))
                                   for name, lseconds, rseconds in prediff_times)

    get_mem = (lambda d, name: d.get(name, {}).get(MEM_KEY, 0))
    prediff_mems = tuple((name, get_mem(left_dict, name), get_mem(right_dict, name))
                         for name in all_names_dict.keys())
    diff_mems_dict = dict((name, lmem - rmem) for name, lmem, rmem in prediff_mems)
    percent_diff_mems_dict = dict((name, ((format_percentage((lmem - rmem) / float(rmem)))
                                          if rmem != 0 else (INFINITY if lmem > 0 else 'N/A')))
                                  for name, lmem, rmem in prediff_mems)

    # update to sort by approximate difference, first
    if sort_by_mem:
        get_prekey = (lambda name: diff_mems_dict[name])
    else:
        get_prekey = (lambda name: to_seconds(diff_times_dict[name]))
    get_key_abs = make_sorting_key(all_names_dict, descending=descending, sort_by_mem=sort_by_mem)
    get_key_diff_float = (lambda name: fix_sign_for_sorting(get_prekey(name), descending=descending))
    get_key_diff_absint = (lambda name: fix_sign_for_sorting(int(abs(get_prekey(name))), descending=descending))
    get_key_with_name = (lambda get_key: lambda name: (get_key(name), name))
    if sort_by == 'absolute':
        get_key = get_key_with_name(get_key_abs)
    elif sort_by == 'diff':
        get_key = get_key_with_name(get_key_diff_float)
    else: # sort_by == 'auto'
        get_key = get_key_with_name((lambda name: (get_key_diff_absint(name), get_key_abs(name))))
    names = sorted(all_names_dict.keys(), key=get_key)
    #names = get_sorted_file_list_from_stats_dict(all_names_dict, descending=descending)
    # set the widths of each of the columns by the longest thing to go in that column
    left_sum = sum_times(v[TIME_KEY] for v in left_dict.values() if TIME_KEY in v.keys())
    right_sum = sum_times(v[TIME_KEY] for v in right_dict.values() if TIME_KEY in v.keys())
    left_sum_float = sum(sorted(to_seconds(v[TIME_KEY]) for v in left_dict.values() if TIME_KEY in v.keys()))
    right_sum_float = sum(sorted(to_seconds(v[TIME_KEY]) for v in right_dict.values() if TIME_KEY in v.keys()))
    diff_sum = from_seconds(left_sum_float - right_sum_float, signed=True)
    percent_diff_sum = (format_percentage((left_sum_float - right_sum_float) / right_sum_float)
                        if right_sum_float > 0 else 'N/A')

    left_width = max(max(map(len, ['N/A', left_tag] + [v[TIME_KEY] for v in left_dict.values() if TIME_KEY in v.keys()])), len(left_sum))
    right_width = max(max(map(len, ['N/A', right_tag] + [v[TIME_KEY] for v in right_dict.values() if TIME_KEY in v.keys()])), len(right_sum))
    far_right_width = max(max(map(len, ['N/A', change_tag] + list(diff_times_dict.values()))), len(diff_sum))
    far_far_right_width = max(max(map(len, ['N/A', percent_change_tag] + list(percent_diff_times_dict.values()))), len(percent_diff_sum))
    total_string = 'Total' if not include_mem else 'Total Time / Peak Mem'
    middle_width = max(map(len, names + [tag, total_string]))

    left_peak = max([0] + [v.get(MEM_KEY, 0) for v in left_dict.values()])
    right_peak = max([0] + [v.get(MEM_KEY, 0) for v in right_dict.values()])
    diff_peak = left_peak - right_peak
    percent_diff_peak = (format_percentage((left_peak - right_peak) / float(right_peak))
                         if right_peak != 0 else (INFINITY if left_peak > 0 else 'N/A'))

    left_mem_width = max(max(map(len, ['N/A', left_mem_tag] + [mem_fmt % v.get(MEM_KEY, 0) for v in left_dict.values()])), len(mem_fmt % left_peak))
    right_mem_width = max(max(map(len, ['N/A', right_mem_tag] + [mem_fmt % v.get(MEM_KEY, 0) for v in right_dict.values()])), len(mem_fmt % right_peak))
    far_right_mem_width = max(max(map(len, ['N/A', change_mem_tag] + [mem_fmt % v for v in diff_mems_dict.values()])), len(mem_fmt % diff_peak))
    far_far_right_mem_width = max(max(map(len, ['N/A', percent_change_mem_tag] + list(percent_diff_mems_dict.values()))), len(percent_diff_peak))

    if include_mem:
        format_string = ("%%(left)%ds | %%(left_mem)%ds | %%(middle)-%ds | %%(right)%ds | %%(right_mem)%ds || %%(far_right)%ds || %%(far_right_mem)%ds"
                         % (left_width, left_mem_width, middle_width, right_width, right_mem_width, far_right_width, far_right_mem_width))
    else:
        format_string = ("%%(left)%ds | %%(middle)-%ds | %%(right)%ds || %%(far_right)%ds"
                         % (left_width, middle_width, right_width, far_right_width))

    if with_percent:
        format_string += " | %%(far_far_right)%ds" % far_far_right_width
        if include_mem:
            format_string += " | %%(far_far_right_mem)%ds" % far_far_right_mem_width

    header = format_string % {'left': left_tag, 'left_mem': left_mem_tag,
                              'middle': tag,
                              'right': right_tag, 'right_mem': right_mem_tag,
                              'far_right': change_tag, 'far_right_mem': change_mem_tag,
                              'far_far_right': percent_change_tag, 'far_far_right_mem': percent_change_mem_tag}
    total = format_string % {'left': left_sum, 'left_mem': mem_fmt % left_peak,
                             'middle': total_string,
                             'right': right_sum, 'right_mem': mem_fmt % right_peak,
                             'far_right': diff_sum, 'far_right_mem': mem_fmt % diff_peak,
                             'far_far_right': percent_diff_sum, 'far_far_right_mem': percent_diff_peak}
    # separator to go between headers and body
    sep = '-' * len(header)
    # the representation of the default value (0), to get replaced by N/A
    left_rep, right_rep, far_right_rep, far_far_right_rep = ("%%%ds | " % left_width) % 'N/A', (" | %%%ds |" % right_width) % 'N/A', ("|| %%%ds" % far_right_width) % 'N/A', ("| %%%ds" % far_far_right_width) % 'N/A'
    left_mem_rep, right_mem_rep, far_right_mem_rep, far_far_right_mem_rep = ("%%%ds | " % left_mem_width) % 'N/A', (" | %%%ds |" % right_mem_width) % 'N/A', ("|| %%%ds" % far_right_mem_width) % 'N/A', ("| %%%ds" % far_far_right_mem_width) % 'N/A'
    get_formatted_mem = (lambda k, v: (mem_fmt % v[k]) if k in v.keys() else 'N/A')
    return '\n'.join([header, sep, total, sep] +
                     [format_string % {'left': left_dict.get(name, {}).get(TIME_KEY, 'N/A'),
                                       'left_mem': get_formatted_mem(MEM_KEY, left_dict.get(name, {})),
                                       'middle': name,
                                       'right': right_dict.get(name, {}).get(TIME_KEY, 'N/A'),
                                       'right_mem': get_formatted_mem(MEM_KEY, right_dict.get(name, {})),
                                       'far_right': diff_times_dict.get(name, 'N/A'),
                                       'far_right_mem': get_formatted_mem(name, diff_mems_dict),
                                       'far_far_right': percent_diff_times_dict.get(name, 'N/A'),
                                       'far_far_right_mem': percent_diff_mems_dict.get(name, 'N/A')}
                      for name in names]).replace(left_rep, 'N/A'.center(len(left_rep) - 3) + ' | ').replace(right_rep, ' | ' + 'N/A'.center(len(right_rep) - 5) + ' |').replace(far_right_rep, '|| ' + 'N/A'.center(len(far_right_rep) - 3)).replace(far_far_right_rep, '| ' + 'N/A'.center(len(far_far_right_rep) - 2)).replace(left_mem_rep, 'N/A'.center(len(left_mem_rep) - 3) + ' | ').replace(right_mem_rep, ' | ' + 'N/A'.center(len(right_mem_rep) - 5) + ' |').replace(far_right_mem_rep, '|| ' + 'N/A'.center(len(far_right_mem_rep) - 3)).replace(far_far_right_mem_rep, '| ' + 'N/A'.center(len(far_far_right_mem_rep) - 2))

def make_table_string(stats_dict,
                      descending=True, sort_by_mem=False,
                      tag="Time", mem_tag="Peak Mem", mem_fmt='%d ko',
                      include_mem=False):
    if len(stats_dict.keys()) == 0: return 'No timing data'
    # We first get the names of all of the compiled files, sorted by
    # duration
    names = get_sorted_file_list_from_stats_dict(stats_dict, descending=descending, sort_by_mem=sort_by_mem)
    # compute the widths of the columns
    times_width = max(len('N/A'), len(tag), max(len(v[TIME_KEY]) for v in stats_dict.values() if TIME_KEY in v.keys()), len(sum_times(v[TIME_KEY] for v in stats_dict.values() if TIME_KEY in v.keys())))
    mems_width = max(len('N/A'), len(mem_tag), max(len(mem_fmt % v.get(MEM_KEY, 0)) for v in stats_dict.values()), len(mem_fmt % (max(v.get(MEM_KEY, 0) for v in stats_dict.values()))))
    total_string = 'Total' if not include_mem else 'Total Time / Peak Mem'
    names_width = max(map(len, names + ["File Name", total_string]))
    if include_mem:
        format_string = "%%(time)%ds | %%(mem)%ds | %%(name)-%ds" % (times_width, mems_width, names_width)
    else:
        format_string = "%%(time)%ds | %%(name)-%ds" % (times_width, names_width)
    get_formatted_mem = (lambda k, v: (mem_fmt % v[k]) if k in v.keys() else 'N/A')
    header = format_string % {'time': tag, 'mem': mem_tag, 'name': 'File Name'}
    total = format_string % {'time': sum_times(v[TIME_KEY] for v in stats_dict.values() if TIME_KEY in v.keys()),
                             'mem': ((mem_fmt % max(v[MEM_KEY] for v in stats_dict.values() if MEM_KEY in v.keys())) if any(MEM_KEY in v.keys() for v in stats_dict.values()) else 'N/A'),
                             'name': total_string}
    sep = '-' * len(header)
    return '\n'.join([header, sep, total, sep] +
                     [format_string % {'time': stats_dict[name].get(TIME_KEY, 'N/A'),
                                       'mem': get_formatted_mem(MEM_KEY, stats_dict[name]),
                                       'name': name}
                      for name in names])

def print_or_write_table(table, files):
    if table[-1] != '\n': table += '\n'
    if len(files) == 0 or '-' in files:
        if hasattr(sys.stdout, 'buffer'):
            sys.stdout.buffer.write(table.encode("utf-8"))
        else:
            sys.stdout.write(table.encode("utf-8"))
    for file_name in files:
        if file_name != '-':
            with open(file_name, 'w', encoding="utf-8") as f:
                f.write(table)
