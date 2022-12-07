#!/usr/bin/env python3

from utils import advent
from functools import lru_cache
from collections import deque, defaultdict

def parse_filesystem(fin):
	lines = deque(fin)
	fs    = defaultdict(list)
	path  = ()

	while lines:
		_, command, *args = lines.popleft().split()

		if command == 'ls':
			while lines and not lines[0].startswith('$'):
				size = lines.popleft().split()[0]
				if size != 'dir':
					fs[path].append(int(size))
		else:
			if args[0] == '..':
				path = path[:-1]
			else:
				new_path = path + (args[0],)
				fs[path].append(new_path)
				path = new_path

	return fs

@lru_cache(maxsize=None)
def directory_size(path):
	size = 0

	for subdir_or_size in fs[path]:
		if isinstance(subdir_or_size, int):
			size += subdir_or_size
		else:
			size += directory_size(subdir_or_size)

	return size


advent.setup(2022, 7)

with advent.get_input() as fin:
	fs = parse_filesystem(fin)

used = directory_size(('/',))
free = 70000000 - used
need = 30000000 - free

small_dir_total  = 0
min_size_to_free = used

for path in fs:
	sz = directory_size(path)

	if sz <= 100000:
		small_dir_total += sz
	if sz >= need and sz < min_size_to_free:
		min_size_to_free = sz

# Alternatively:
# small_dir_total  = sum(filter(lambda s: s <= 100000, map(directory_size, fs)))
# min_size_to_free = min(filter(lambda s: s >= need, map(directory_size, fs)))

advent.print_answer(1, small_dir_total)
advent.print_answer(2, min_size_to_free)
