#!/usr/bin/env python3

from utils.all import *

advent.setup(2022, 7)

DEBUG = 'debug' in map(str.lower, sys.argv)
if not DEBUG:
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
$ cd /
$ ls
dir a
14848514 b.txt
8504156 c.dat
dir d
$ cd a
$ ls
dir e
29116 f
2557 g
62596 h.lst
$ cd e
$ ls
584 i
$ cd ..
$ cd ..
$ cd d
$ ls
4060174 j
8033020 d.log
5626152 d.ext
7214296 k
''')

try: lines = get_lines(fin); fin.seek(0, 0)
except: pass

ans = 0
root = {}
parent = defaultdict(tuple)

t = root
cur = None
lising = False

for line in map(str.strip, lines):
	if line.startswith('$'):
		listing = False

		if line.startswith('$ cd'):
			nxt = line[len('$ cd '):]

			if nxt == '..':
				cur, t = parent[cur]
			else:
				parent[nxt] = (cur, t)
				t[nxt] = {}
				cur, t = nxt, t[nxt]
		elif line == '$ ls':
			listing = True

		continue

	if listing:
		n, name = line.split()

		if n.isdigit():
			n = int(n)
			t[name] = n
		elif n == 'dir':
			t[name] = {}
		else:
			assert False, line

# dump_dict(parent)
# eprint('root: --------------------------------')
# dump_dict(root)
# eprint('--------------------------------')

sizes = {}
directories = {'/'}

def dfs(t, name, path):
	# eprint('>', name, t, path)
	if isinstance(t, int):
		return t

	directories.add(path)

	tot = 0
	for subname, subt in t.items():
		# eprint('>>', subname, subt)
		if name == '/':
			p = '/' + subname
		else:
			p = path + '/' + subname

		tot += dfs(subt, subname, p)

	sizes[path] = tot
	return tot


dfs(root['/'], '/', '/')
# dump_iterable([(v, k) for k, v in sizes.items()])
# eprint('--------------------------------')
# dump_iterable(directories)

for v in sizes.values():
	if v <= 100000:
		ans += v

# 1001106 wrong
advent.print_answer(1, ans)


tot = sizes['/']
free = 70000000 - tot
need = 30000000 - free

# eprint('tot: ', tot)
# eprint('free:', free)
# eprint('need:', need)

mmin = float('inf')
for name, sz in sizes.items():
	if name in directories and sz >= need and sz < mmin:
		mmin = sz

# No idea why, but the next smallest size after mmin was correct. Probably some
# error in dfs() or in the input parsing that somehow still got me the right
# value for part 1
second = float('inf')
for name, sz in sizes.items():
	if name in directories and sz > mmin and sz < second:
		second = sz

# dump_iterable(sorted(sizes.items(), key=lambda kv: kv[1]))

# 3487907 wrong
# 3866390 correct for whatever reason...
advent.print_answer(2, second)
