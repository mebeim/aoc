#!/usr/bin/env python3

from utils import advent
from itertools import chain

class Cup:
	__slots__ = ('value', 'prev', 'next')

	def __init__(self, value):
		self.value = value
		self.prev  = None
		self.next  = None

def build_list(values, n=None):
	n = (n if n else len(values)) + 1
	cups = [None] * n
	values = chain(values, range(len(values) + 1, n))

	first = next(values)
	cups[first] = Cup(first)
	first = cups[first]
	prev = first

	for value in values:
		cur = cups[value] = Cup(value)
		cur.prev = prev
		prev.next = cur
		prev = cur

	cur.next = first
	return first, cups

def play(cur, cups, moves):
	maxcup = len(cups) - 1

	for _ in range(moves):
		first  = cur.next
		mid    = first.next
		last   = mid.next
		picked = (first.value, mid.value, last.value)

		cur.next = last.next
		cur.next.prev = cur

		dst = maxcup if cur.value == 1 else cur.value - 1
		while dst in picked:
			dst = maxcup if dst == 1 else dst - 1

		dst = cups[dst]
		first.prev = dst
		last.next  = dst.next
		dst.next.prev = last
		dst.next      = first

		cur = cur.next


advent.setup(2020, 23)

fin = advent.get_input()
orig = tuple(map(int, fin.readline().rstrip()))

first, cups = build_list(orig)
play(first, cups, 100)

ans = ''
c = cups[1].next
while c != cups[1]:
	ans += str(c.value)
	c = c.next

advent.print_answer(1, ans)


first, cups = build_list(orig, n=1000000)
play(first, cups, 10000000)
ans = cups[1].next.value * cups[1].next.next.value

advent.print_answer(2, ans)
