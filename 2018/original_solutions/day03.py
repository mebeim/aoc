#!/usr/bin/env python3

from utils import advent

advent.setup(2018, 3)

fin = advent.get_input()
ans = 0
ans2 = 0

##################################################

canvas = []
for i in range(1000):
	canvas.append([])
	for j in range(1000):
		canvas[i].append({'ids': set(), 'tot': 0})

claims = {}
for line in fin:
	cid, claim = line.strip().replace(' ', '').split('@')
	cid = int(cid[1:])
	start, size = claim.split(':')
	x, y = map(int, start.split(','))
	w, h = map(int, size.split('x'))
	claims[cid] = (x, y, w, h)

for cid, c in claims.items():
	for i in range(c[0], c[0]+c[2]):
		for j in range(c[1], c[1]+c[3]):
			canvas[i][j]['tot'] += 1
			canvas[i][j]['ids'].add(cid)

for row in canvas:
	ans += sum(map(lambda x: x['tot'] > 1, row))

advent.submit_answer(1, ans)

ok = set(claims.keys())
for row in canvas:
	for cell in row:
		if len(cell['ids']) > 1:
			for cid in cell['ids']:
				if cid in ok:
					ok.remove(cid)

assert len(ok) == 1

ans2 = ok.pop()
advent.submit_answer(2, ans2)
