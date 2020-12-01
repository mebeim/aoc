#!/usr/bin/env python3

from utils import advent
from collections import defaultdict

def get_hour(event):
	return int(event[1][:event[1].find(':')])

def get_minute(event):
	return int(event[1][event[1].find(':')+1:-1])

def sum_intervals(intervals):
	return sum(b-a for a, b in intervals)

def times_slept(guard_id, minute):
	return sum(a <= minute < b for a, b in guards[guard_id])


advent.setup(2018, 4)
fin = advent.get_input()

events = list(map(str.split, sorted(fin.readlines())))
assert 'begins' in events[0]

guards = defaultdict(list)

for e in events:
	if 'begins' in e:
		gid = int(e[3][1:])
		lastw = get_minute(e) if get_hour(e) == 0 else 0
	elif 'wakes' in e:
		lastw = get_minute(e)
		guards[gid].append((lasts, lastw))
	elif 'falls' in e:
		lasts = get_minute(e)

worst_guard = max(guards, key=lambda g: sum_intervals(guards[g]))
worst_guard_min = max(range(60), key=lambda m: times_slept(worst_guard, m))
ans = worst_guard * worst_guard_min

advent.print_answer(1, ans)


worst_guard = max(guards, key=lambda g: max(times_slept(g, m) for m in range(60)))
worst_guard_min = max(range(60), key=lambda m: times_slept(worst_guard, m))
ans2 = worst_guard * worst_guard_min

advent.print_answer(2, ans2)
