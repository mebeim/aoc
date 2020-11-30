#!/usr/bin/env python3

from utils import advent
from collections import namedtuple

Node = namedtuple('Node', ['length', 'children', 'metadata'])

def build_tree(flat):
	nchilds  = flat[0]
	nmeta    = flat[1]
	length   = 2
	children = []

	for _ in range(nchilds):
		child = build_tree(flat[length:])
		children.append(child)
		length += child.length

	return Node(length + nmeta, children, flat[length:length + nmeta])

def sum_meta(node):
	return sum(node.metadata) + sum(sum_meta(c) for c in node.children)

def node_value(node):
	if not node.children:
		return sum(node.metadata)

	value = 0
	for i in node.metadata:
		if 1 <= i <= len(node.children):
			value += node_value(node.children[i - 1])

	return value


advent.setup(2018, 8, dry_run=True)
fin = advent.get_input()

nums = list(map(int, fin.read().split()))
root = build_tree(nums)

meta_sum = sum_meta(root)

assert meta_sum == 46962
advent.submit_answer(1, meta_sum)

value = node_value(root)

assert value == 22633
advent.submit_answer(2, value)
