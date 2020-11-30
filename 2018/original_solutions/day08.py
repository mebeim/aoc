#!/usr/bin/env python3

from utils import advent

advent.setup(2018, 8)
fin = advent.get_input()

##################################################

def scan(n, cur_id):
	nchilds = n[0]
	nmeta = n[1]

	if nchilds == 0:
		tree[cur_id] = ([], n[2:2+nmeta])
		return sum(tree[cur_id][1]), 2 + nmeta

	cur_len = 2
	meta_sum = 0
	childs = []

	for _ in range(nchilds):
		child_id = cur_id + cur_len
		childs.append(child_id)

		child_meta_sum, child_len = scan(n[cur_len:], child_id)
		meta_sum += child_meta_sum
		cur_len += child_len

	tree[cur_id] = (childs, n[cur_len:cur_len+nmeta])

	return meta_sum + sum(tree[cur_id][1]), cur_len + nmeta

def tree_value(root):
	me = tree[root]
	nchilds = len(me[0])

	if nchilds:
		tot = 0
		for child_index in me[1]:
			if 1 <= child_index <= nchilds:
				tot += tree_value(me[0][child_index - 1])

		return tot

	return sum(me[1])

tree = {}
nums = list(map(int, fin.read().split()))

ans, _ = scan(nums, 0)
advent.submit_answer(1, ans)

# for k, v in tree.items():
# 	print(k, ':', v)

value = tree_value(0)
advent.submit_answer(2, value)
