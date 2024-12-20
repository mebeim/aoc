__all__ = ['timer_start', 'timer_lap', 'timer_stop', 'timer_stop_all']


import atexit
import sys
import time

from .io_helpers import log


def seconds_to_most_relevant_unit(s: float) -> str:
	s *= 1e6
	if s < 1000:
		return f'{s:.3f}µs'

	s /= 1000
	if s < 1000:
		return f'{s:.3f}ms'

	s /= 1000
	if s < 60:
		return f'{s:.3f}s'

	s /= 60
	return f'{int(s):d}m {(s / 60) % 60:.3f}s'

def timer_start(name: str=sys.argv[0]):
	now_wall, now_cpu = time.perf_counter(), time.process_time()
	timers[name] = (now_wall, now_cpu, now_wall, now_cpu, 1)

def timer_lap(name: str=sys.argv[0]):
	now_wall, now_cpu =  time.perf_counter(), time.process_time()
	*x, prev_wall, prev_cpu, lap = timers[name]

	dt_wall = seconds_to_most_relevant_unit(now_wall - prev_wall)
	dt_cpu  = seconds_to_most_relevant_unit(now_cpu  - prev_cpu )

	log(f'Timer {name} lap #{lap}: {dt_wall} wall, {dt_cpu} CPU\n')

	timers[name] = (*x,  time.perf_counter(), time.process_time(), lap + 1)

def timer_stop(name: str=sys.argv[0]):
	now_wall, now_cpu = time.perf_counter(), time.process_time()
	prev_wall, prev_cpu, *_ = timers.pop(name)

	dt_wall = seconds_to_most_relevant_unit(now_wall - prev_wall)
	dt_cpu  = seconds_to_most_relevant_unit(now_cpu  - prev_cpu )

	log(f'Timer {name}: {dt_wall} wall, {dt_cpu} CPU\n')

def timer_stop_all():
	now_wall, now_cpu = time.perf_counter(), time.process_time()

	while timers:
		k, v = timers.popitem()
		prev_wall, prev_cpu, *_ = v
		dt_wall = seconds_to_most_relevant_unit(now_wall - prev_wall)
		dt_cpu  = seconds_to_most_relevant_unit(now_cpu  - prev_cpu )

		log(f'Timer {k}: {dt_wall} wall, {dt_cpu} CPU\n')

################################################################################

timers = {}
atexit.register(timer_stop_all)
