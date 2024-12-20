#!/usr/bin/env python3

import os
import gitlab
from tabulate import tabulate

gt = gitlab.Gitlab(url="https://gitlab.inria.fr", private_token=os.getenv("PIPELINE_STATS_TOKEN"), api_version="4")

prj = gt.projects.get("coq/coq")

pipeline_id=os.getenv("CI_PIPELINE_ID")
pipeline = prj.pipelines.get(pipeline_id)

def pptime(seconds):
    if seconds >= 60 * 60:
        hours = seconds / (60 * 60)
        minutes = (seconds % (60 * 60)) / 60
        return f"{hours:.0f}h {minutes:.0f}min"
    elif seconds >= 60:
        minutes = seconds / 60
        rest = seconds % 60
        return f"{minutes:.0f}min {rest:.0f}s"
    else:
        return f"{seconds:.0f}s"

def ppsize(size, decimal_places=2):
    for unit in ['B', 'KiB', 'MiB', 'GiB', 'TiB', 'PiB']:
        if size < 1024.0 or unit == 'PiB':
            break
        size /= 1024.0
    return f"{size:.{decimal_places}f} {unit}"

res=[]
total_time=0.0
total_size=0
total_log_size=0

for j in pipeline.jobs.list(iterator=True):
    if j.duration is None:
        continue # non-finished job, eg bench or pipeline stats
    size=0
    log_size=0
    if 'artifacts' in j.attributes:
        for art in j.attributes['artifacts']:
            if art['file_type'] == 'trace':
                log_size += art['size']
            else:
                size += art['size']
    res += [[j.name, j.duration, size, log_size, j.id]]
    total_time += j.duration
    total_size += size
    total_log_size += log_size

res += [['total', total_time, total_size, total_log_size, pipeline_id]]

def sortkey(v):
    return v[1]

ppres = [ [v[0], pptime(v[1]), ppsize(v[2]), ppsize(v[3]), v[4]]
          for v in sorted(res, key=sortkey) ]

print(tabulate(ppres, headers=['name', 'duration', 'artifacts size', 'log size', 'id'], tablefmt='orgtbl'))
