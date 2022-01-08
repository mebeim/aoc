#!/usr/bin/env python3
#
# Day 22 (part 2 only) using an octree.
# Time and space complexity are way too much, almost as bad as a brute force
# approach (keeping track of all points in space). Not a feasible solution at
# all, but fun enough to implement that I decided to keep the code.
#

import re
import resource

# Limit memory usage to 8GB... we will nonetheless exceed this limit and our
# script will be killed.
resource.setrlimit(resource.RLIMIT_AS, (8 * 2**30,) * 2)

class Octree:
	def __init__(self, cuboid):
		self.cuboid = cuboid
		self.value = 0
		self.leaf = True
		self._children = None

	@property
	def children(self):
		if self._children:
			return self._children

		x0, y0, z0, x1, y1, z1 = self.cuboid
		dx = (x1 - x0) // 2
		dy = (y1 - y0) // 2
		dz = (z1 - z0) // 2

		self._children = [
			Octree((x0     , y0     , z0     , x0 + dx, y0 + dy, z0 + dz)), # front sw
			Octree((x0 + dx, y0     , z0     , x1     , y0 + dy, z0 + dz)), # front se
			Octree((x0     , y0 + dy, z0     , x0 + dx, y1     , z0 + dz)), # front nw
			Octree((x0 + dx, y0 + dy, z0     , x1     , y1     , z0 + dz)), # front ne
			Octree((x0     , y0     , z0 + dz, x0 + dx, y0 + dy, z1     )), # back sw
			Octree((x0 + dx, y0     , z0 + dz, x1     , y0 + dy, z1     )), # back se
			Octree((x0     , y0 + dy, z0 + dz, x0 + dx, y1     , z1     )), # back nw
			Octree((x0 + dx, y0 + dy, z0 + dz, x1     , y1     , z1     )), # back ne
		]

		return self._children

	@children.deleter
	def children(self):
		self._children = None

	def set(self, cuboid, value, depth=0):
		x0, y0, z0, x1, y1, z1 = self.cuboid
		a0, b0, c0, a1, b1, c1 = cuboid

		# Am I completely inside this range? If so I can set the value on me,
		# become a leaf, and all my children become irrelevant.
		if x0 >= a0 and y0 >= b0 and z0 >= c0 and x1 <= a1 and y1 <= b1 and z1 <= c1:
			self.leaf = True
			self.value = value
			del self.children
			return

		# Am I completely outside this range? If so I am not interested and
		# neither are my children.
		if x1 <= a0 or y1 <= b0 or z1 <= c0 or x0 >= a1 or y0 >= b1 or z0 >= c1:
			return

		self.leaf = False

		for child in self.children:
			child.set(cuboid, value, depth + 1)

	def total(self):
		if self.leaf:
			return self.value
		return sum(c.total() for c in self.children)

	def __repr__(self):
		return f'<{self.cuboid} leaf={self.leaf} v={self.value}>'


commands = []

with open('input.txt') as fin:
	for line in fin:
		value = int(line.startswith('on'))
		x0, x1, y0, y1, z0, z1 = map(int, re.findall(r'-?\d+', line))
		x0 += 100000
		x1 += 100001
		y0 += 100000
		y1 += 100001
		z0 += 100000
		z1 += 100001

		commands.append(((x0, y0, z0, x1, y1, z1), value))

O = Octree((0, 0, 0, 2**19, 2**19, 2**19))

for cuboid, value in commands:
	print(cuboid, value)
	O.set(cuboid, value)

print(O.total())
