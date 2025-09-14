"""
Global configuration of Knuckledragger
"""

solver = None
admit_enabled = True
# timeout = 1000
admit_level = 50


# TODO: Someday, when it is annoyingly slow to check built in theories, we can add a flag to disable them
# check_lib = True
timing = False
perf_log = []


def perf_event(tag, data, time):
    if timing:
        perf_log.append((tag, data, time))
