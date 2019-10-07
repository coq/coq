#!/usr/bin/python3

"""This python script retrieves CI job statistics from GITLAB
   and creates a .csv file with failure correlation statistics"""

import os
import sys
import time
import tempfile
import requests
import json
import collections
import csv

# ATTENTION: This uses SSL which is on Windows installed e.g. by using an Anaconda Python.
# If you use e.g. VSCode, make sure to start VSCode via Anaconda to get the correct path.
# Another option is to use a cygwin python.

# Discard tests with less than min_total test entries
min_total = 10

# Get API token from environment and create authorization header
api_token = os.getenv('GITLAB_API_TOKEN')
if not api_token:
    print("Error: please set environment variable GITLAB_API_TOKEN", file=sys.stderr)
    print("See https://docs.gitlab.com/ee/user/profile/personal_access_tokens.html", file=sys.stderr)
    exit()

headers = {'Content-Type': 'application/json', 'Authorization': 'Bearer {0}'.format(api_token)}

# Gitlab time restrictions
lasttime = time.time()-1

# Create output folder
outdir = os.path.join(tempfile.gettempdir(),"gitlab-stats")
if not os.path.exists(outdir):
    os.mkdir(outdir)

def api_delay():
    """ Gitlab API does not allow more than 10 accesses per second """
    global lasttime
    delta = time.time()-lasttime
    if delta < 0.12:
        print('delay={0}'.format(delta))
        time.sleep(delta)
    lasttime = time.time()

def get_gitlab_pipelinelist_page(perpage,page):
    """ Get one page of the list of piplines """
    api_delay()
    api_url = 'https://gitlab.com/api/v4/projects/coq%2Fcoq/pipelines?per_page={0}&page={1}'.format(perpage,page)
    response = requests.get(api_url, headers=headers)
    if response.status_code == 200:
        return json.loads(response.content.decode('utf-8'))
    else:
        return None

def get_gitlab_pipeline_joblist(pipelineId):
    """ Get the detailed list of all jobs for a pipeline (at most 100) """
    api_delay()
    api_url = 'https://gitlab.com/api/v4/projects/coq%2Fcoq/pipelines/{0}/jobs?per_page=100'.format(pipelineId)
    response = requests.get(api_url, headers=headers)
    if response.status_code == 200:
        return json.loads(response.content.decode('utf-8'))
    else:
        return None

def get_jobinfo(perpage,nPages):
    """ Get the detailed job lists for several pages of the pipeline list - return list of json files """
    assert(perpage>=1 and perpage<=100)
    filelist = []
    for iPage in range(1,nPages+1):
        pipelinelist = get_gitlab_pipelinelist_page(perpage,iPage)
        if pipelinelist:
            for pipeline in pipelinelist:
                pipelineId = pipeline['id']
                outfilename = os.path.join(outdir,'jobinfo_pipeline_{0}.json'.format(pipelineId))
                if not os.path.isfile(outfilename):
                    print('Getting Jobinfo for pipeline {0} = {1}'.format(pipelineId,outfilename))
                    joblist = get_gitlab_pipeline_joblist(pipelineId)
                    with open(outfilename, 'w') as jsonfile:
                        json.dump(joblist, jsonfile)
                filelist.append(outfilename)
    return filelist

def read_pipeline_jobinfo(filelist):
    jobinfolist = []
    for filename in filelist:
        with open(filename, 'r') as jsonfile:
            jobinfo = json.load(jsonfile)
            jobinfolist.append(jobinfo)
    return jobinfolist

def get_jobnames(pipeline_jobinfo):
    names=set()
    for pipeline in pipeline_jobinfo:
        for job in pipeline:
            names.add(job['name'])
    return names

def pipeline_is_finished(pipeline):
    """Check if a pipeline is finished (all jobs are success or fail)"""
    for job in pipeline:
        if not job['status'] in {'success','failed'}:
            return False
    return True

def pipeline_has_repeats(pipeline):
    """Check if a pipeline has multiple jobs with the same name"""
    jobs = set()
    for job in pipeline:
        if job['name'] in jobs:
            return True
        jobs.add(job['name'])
    return False

def get_jobcrosssuccess(pipeline_jobinfo, csvFilename):
    """Collect cross failure statistics from job info list and output as CSV"""
    jobnames = sorted(get_jobnames(pipeline_jobinfo))
    statSuccess = collections.defaultdict(lambda : 0)
    statFailure = collections.defaultdict(lambda : 0)
    statTotal = collections.defaultdict(lambda : 0)
    statCrossFailure = collections.defaultdict(lambda : collections.defaultdict(lambda : 0))
    for pipeline in pipeline_jobinfo:
        # Check if pipeline is sane
        if not pipeline_is_finished(pipeline):
            continue
        if pipeline_has_repeats(pipeline):
            continue
        assert(len(pipeline)<100)
        
        for job1 in pipeline:
            name1 = job1['name']
            stat1 = job1['status']=='success'
            statTotal[name1] += 1
            if stat1:
                statSuccess[name1] += 1
            else:
                statFailure[name1] += 1

            for job2 in pipeline:
                name2 = job2['name']
                stat2 = job2['status']=='success'
                if not stat1 and not stat2:
                    statCrossFailure[name1][name2] += 1
    
    # do some sanity checks
    for name1 in jobnames:
        assert(statCrossFailure[name1][name1] == statFailure[name1])
        for name2 in jobnames:
            assert(statCrossFailure[name1][name2] <= statFailure[name1])
            assert(statCrossFailure[name1][name2] <= statFailure[name2])

    # remove uninteresting jobs
    lowcountjobs = [name for name in jobnames if statTotal[name]<min_total]
    for name in lowcountjobs:
        jobnames.remove(name)

    # Output data as CSV
    with open(csvFilename, mode='w', newline='') as csv_file:
        csv_writer = csv.writer(csv_file, delimiter=',', quotechar='"', quoting=csv.QUOTE_MINIMAL)
        csv_writer.writerow(['name','total','success','failure'] + [name2 for name2 in jobnames])
        for name1 in jobnames:
            csv_writer.writerow(
                [name1,statTotal[name1],statSuccess[name1],statFailure[name1]] + 
                [statCrossFailure[name1][name2] for name2 in jobnames]
                )

filelist = get_jobinfo(100,30)
pipeline_jobinfo = read_pipeline_jobinfo(filelist)
get_jobcrosssuccess(pipeline_jobinfo, 'crossfail.csv')

