#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 22)
DEBUG = 'debug' in map(str.lower, sys.argv)
fin = advent.get_input() if not DEBUG else io.StringIO('''\
1,0,1~1,2,1
0,0,2~2,0,2
0,2,3~2,2,3
0,0,4~0,2,4
2,0,5~2,2,5
0,1,6~2,1,6
1,1,8~1,1,9
''')

def draw_xz(space):
	g = {}
	maxz = max(map(itemgetter(2), space))
	for x in range(10): g[maxz - 0 + 1, x] = '-'
	for (x, _, z), ident in space.items(): g[maxz - z + 1, x] = ident
	dump_sparse_matrix(g)

def draw_yz(space):
	g = {}
	maxz = max(map(itemgetter(1), space))
	for y in range(10): g[maxz - 0 + 1, y] = '-'
	for (_, y, z), ident in space.items(): g[maxz - z + 1, y] = ident
	dump_sparse_matrix(g)

def fall_one(space, ident, ax, ay, az, bx, by, bz):
	assert (az != bz) + (ax != bx) + (ay != by) <= 1
	# eprint('brick', ident, (ax, ay, az, bx, by, bz), 'falls')

	below = set()

	if ax != bx:
		# Find first z (from az down) for which x,ay,z is occupied
		for minz in range(az, -1, -1):
			for x in autorange(ax, bx):
				# eprint('>', (x, ay, minz))
				if (x, ay, minz) in space:
					# eprint('> obstacle', (x, ay, minz))
					below.add(space[x, ay, minz])

			if below:
				break

		minz += 1
		# eprint(minz)
		for x in autorange(ax, bx):
			space[x, ay, minz] = ident
	elif ay != by:
		# Find first z (from az down) for which ax,y,z is occupied
		for minz in range(az, -1, -1):
			for y in autorange(ay, by):
				# eprint('>', (ax, y, minz))
				if (ax, y, minz) in space:
					# eprint('> obstacle', (ax, y, minz))
					below.add(space[ax, y, minz])

			if below:
				break

		minz += 1
		# eprint(minz)
		for y in autorange(ay, by):
			space[ax, y, minz] = ident
	else:
		zlo = min(az, bz)

		# Find first z (from z down) for which ax,ay,z is occupied
		for minz in range(zlo, -1, -1):
			# eprint('>', (ax, ay, minz))
			if (ax, ay, minz) in space:
				# eprint('> obstacle', (ax, ay, minz))
				below = {space[ax, ay, minz]}
				break

		minz += 1
		# eprint(minz)

		delta = zlo - minz
		az -= delta
		bz -= delta

		for z in autorange(az, bz):
			space[ax, ay, z] = ident

	return below


def fall():
	bricks.sort(key=lambda b: min(b[2], b[5]))
	space = {}
	supports = {}

	for identifier, b in enumerate(bricks):
		below = fall_one(space, identifier, *b)
		supports[identifier] = below
		# draw_xz(space)
		# draw_yz(space)

	# for x in sorted(supports):
	# 	print(x, bricks[x], 'supported by', supports[x])

	deletable = set(range(len(bricks)))

	# I cannot delete a brick if it's the only one supporting some other brick
	for below in supports.values():
		if len(below) == 1:
			deletable.discard(next(iter(below)))

	return deletable, supports


lines = read_lines(fin)
bricks = []

for line in lines:
	coords = extract_ints(line)
	bricks.append(coords)

deletable, supports = fall()

ans1 = len(deletable)
advent.print_answer(1, ans1)


def find_falling(supported_by, supports, root):
	falling = {root}
	q = deque([root])

	while q:
		brick = q.popleft()

		for a in supported_by[brick]:
			if all(s in falling for s in supports[a]):
				falling.add(a)
				q.append(a)

	falling.discard(root)
	return falling

not_deletable = set(range(len(bricks))) - deletable
assert len(deletable) + len(not_deletable) == len(bricks)

#   33333
#   2   4
# 111   4
# 0     4
# not_deletable = {0, 1}
# supports = {
# 	0: set(),
# 	1: {0},
# 	2: {1},
# 	3: {2,4},
# 	4: set(),
# }

supported_by = defaultdict(set)
for brick, below in supports.items():
	for b in below:
		supported_by[b].add(brick)

tot = 0
for brick in not_deletable:
	falling = find_falling(supported_by, supports, brick)
	# print('deleting', brick, 'would make these fall:', falling)
	tot += len(falling)

advent.print_answer(2, tot)
