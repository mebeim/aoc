#!/usr/bin/env python3

from utils.all import *

def diamond(space, cx, cy, xx, yy, rr=2000000):
	dist = abs(cx - xx) + abs(cy - yy)

	w = cx - dist
	e = cx + dist
	s = cy + dist
	n = cy - dist

	if n <= rr <= s:
		d = abs(rr - cy)
		# eprint(cx, cy, 'n:', n, 's:', s, '| d:', d, 'range', w + d, e - d)
		rang = autorange(w + d, e - d)
		space.update(rang)

def diamond2(space, cx, cy, xx, yy, rr):
	dist = abs(cx - xx) + abs(cy - yy)

	w = cx - dist
	e = cx + dist
	s = cy + dist
	n = cy - dist

	if n <= rr <= s:
		d = abs(rr - cy)
		w = max(0, w + d)
		e = min(MAX, e - d)
		return (w, e)

	return None

def p2(sensors):
	for y in range(0, MAX+1):
		space = set()
		segments = []

		for sx, sy, bx, by in sensors:
			seg = diamond2(space, sx, sy, bx, by, y)
			if seg is None:
				continue

			segments.append(seg)

		segments.sort()
		it = iter(segments)
		curs, cure = next(it)

		for s, e in it:
			if s <= cure + 1:
				cure = max(cure, e)
			else:
				return s - 1, y

		# eprint(y, segments)
		# eprint(y, cur)


advent.setup(2022, 15)

DEBUG = 'debug' in map(str.lower, sys.argv)
fin = advent.get_input() if not DEBUG else io.StringIO('''\
Sensor at x=2, y=18: closest beacon is at x=-2, y=15
Sensor at x=9, y=16: closest beacon is at x=10, y=16
Sensor at x=13, y=2: closest beacon is at x=15, y=3
Sensor at x=12, y=14: closest beacon is at x=10, y=16
Sensor at x=10, y=20: closest beacon is at x=10, y=16
Sensor at x=14, y=17: closest beacon is at x=10, y=16
Sensor at x=8, y=7: closest beacon is at x=2, y=10
Sensor at x=2, y=0: closest beacon is at x=2, y=10
Sensor at x=0, y=11: closest beacon is at x=2, y=10
Sensor at x=20, y=14: closest beacon is at x=25, y=17
Sensor at x=17, y=20: closest beacon is at x=21, y=22
Sensor at x=16, y=7: closest beacon is at x=15, y=3
Sensor at x=14, y=3: closest beacon is at x=15, y=3
Sensor at x=20, y=1: closest beacon is at x=15, y=3
''')

intmat = read_int_matrix(fin)
timer_start()

space = set()
sensors = []

for line in intmat:
	sensors.append(line)

good_beacons = set()

TARGETY = 10 if DEBUG else 2000000
for sx, sy, bx, by in sensors:
	diamond(space, sx, sy, bx, by, rr=TARGETY)
	if by == TARGETY:
		good_beacons.add(bx)

space -= good_beacons
ans = len(space)

# 5652848 no
# 6697770 no
advent.print_answer(1, ans)


MIN = 0
MAX = 20 if DEBUG else 4000000

x, y = p2(sensors)
ans = x * 4000000 + y

advent.print_answer(2, ans)
