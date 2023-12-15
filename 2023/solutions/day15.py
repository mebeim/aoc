#!/usr/bin/env python3

import sys
from collections import defaultdict

def aoc_hash(s):
	h = 0
	for c in s:
		h = ((h + c) * 17) % 256
	return h

class HashMap:
	__slots__ = 'backing_store'

	def __init__(self):
		self.backing_store = defaultdict(list)

	def _find_and_pop(self, key):
		slot = self.backing_store[aoc_hash(key)]

		for i, (k, _) in enumerate(slot):
			if k == key:
				slot.pop(i)
				return slot, i

		return slot, -1

	def remove(self, key):
		self._find_and_pop(key)

	def insert(self, key, value):
		slot, i = self._find_and_pop(key)

		if i != -1:
			slot.insert(i, (key, value))
		else:
			slot.append((key, value))

	def power(self):
		total = 0

		for i, lst in self.backing_store.items():
			for j, (_, v) in enumerate(lst, 1):
				total += (i + 1) * j * v

		return total


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1], 'rb') if len(sys.argv) > 1 else sys.stdin.buffer

strings = fin.read().strip().split(b',')
total1 = sum(map(aoc_hash, strings))
print('Part 1:', total1)


hashmap = HashMap()

for s in strings:
	if b'-' in s:
		hashmap.remove(s[:-1])
	elif b'=' in s:
		k, v = s.split(b'=')
		hashmap.insert(k, int(v))

total2 = hashmap.power()
print('Part 2:', total2)
