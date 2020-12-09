__all__ = ['timer_start', 'timer_lap', 'timer_stop', 'timer_stop_all']

import sys
import time
import atexit
from .helpers import log

def seconds_to_most_relevant_unit(s):
	s *= 1e6
	if s < 1000:
		return '{:.3f}µs'.format(s)

	s /= 1000
	if s < 1000:
		return '{:.3f}ms'.format(s)

	s /= 1000
	if s < 60:
		return '{:.3f}s'.format(s)

	s /= 60
	return '{:d}m {:.3f}s'.format(int(s), s/60%60)

def timer_start(name=sys.argv[0]):
	now_wall, now_cpu = time.perf_counter(), time.process_time()
	timers[name] = (now_wall, now_cpu, now_wall, now_cpu, 1)

def timer_lap(name=sys.argv[0]):
	now_wall, now_cpu =  time.perf_counter(), time.process_time()
	*x, prev_wall, prev_cpu, lap = timers[name]

	dt_wall = seconds_to_most_relevant_unit(now_wall - prev_wall)
	dt_cpu  = seconds_to_most_relevant_unit(now_cpu  - prev_cpu )

	log('Timer {} lap #{}: {} wall, {} CPU\n'.format(name, lap, dt_wall, dt_cpu))

	timers[name] = (*x,  time.perf_counter(), time.process_time(), lap + 1)

def timer_stop(name=sys.argv[0]):
	now_wall, now_cpu = time.perf_counter(), time.process_time()
	prev_wall, prev_cpu, *_ = timers.pop(name)

	dt_wall = seconds_to_most_relevant_unit(now_wall - prev_wall)
	dt_cpu  = seconds_to_most_relevant_unit(now_cpu  - prev_cpu )

	log('Timer {}: {} wall, {} CPU\n'.format(name, dt_wall, dt_cpu))

def timer_stop_all():
	now_wall, now_cpu = time.perf_counter(), time.process_time()

	while timers:
		k, v = timers.popitem()
		prev_wall, prev_cpu, *_ = v
		dt_wall = seconds_to_most_relevant_unit(now_wall - prev_wall)
		dt_cpu  = seconds_to_most_relevant_unit(now_cpu  - prev_cpu )

		log('Timer {}: {} wall, {} CPU\n'.format(k, dt_wall, dt_cpu))

################################################################################

timers = {}
atexit.register(timer_stop_all)
