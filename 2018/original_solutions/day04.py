#!/usr/bin/env python3

from utils import advent

advent.setup(2018, 4)

fin = advent.get_input()
ans = 0
ans2 = 0

arr = []
for l in fin:
	gid = -1

	if 'wakes up' in l:
		action = 'w'
	elif 'falls asleep' in l:
		action = 's'
	elif 'begins shift' in l:
		action = 'b'
		gid = l[l.find('#')+1:]
		gid = int(gid[:gid.find(' ')])

	date, time = l[1:17].split(' ')
	y, m, d = map(int, date.split('-'))
	h, mm = map(int, time.split(':'))

	arr.append({'date': (y, m, d), 'time': (h, mm), 'action': action, 'id': gid})

arr.sort(key=lambda x: x['date'] + x['time'])

# for g in arr[:20]:
# 	print(g)

days = {}

lastid = arr[0]['id']
lastw = arr[0]['time'][1]
lasts = lastw
days[arr[0]['date']] = {'min': [0] * 60, 'id': lastid}

for g in arr[1:]:
	if g['id'] != -1:
		lastid = g['id']

		if g['time'][0] == 0:
			days[g['date']] = {'min': [0] * 60, 'id': lastid}

		lastw = g['time'][1]
		lasts = lastw
	else:
		g['id'] = lastid

		if g['action'] in 'sw':
			if g['date'] not in days:
				days[g['date']] = {'min': [0] * 60, 'id': lastid}

		if g['action'] == 's':
			lasts = g['time'][1]
		elif g['action'] == 'w':
			lastw = g['time'][1]

			for i in range(lasts, lastw):
				days[g['date']]['min'][i] = 1

allids = set()
for d in arr:
	allids.add(d['id'])

minsofsleep = {}

for d in days.values():
	if d['id'] not in minsofsleep:
		minsofsleep[d['id']] = 0

	minsofsleep[d['id']] += sum(d['min'])

mostsleepid = -1
mostsleepmins = -1

for gid, mins in minsofsleep.items():
	if mins > mostsleepmins:
		mostsleepmins = mins
		mostsleepid = gid

minsmap = [0] * 60
for d in filter(lambda x: x['id'] == mostsleepid, days.values()):
	for i in range(60):
		minsmap[i] += d['min'][i]

mostsleepedminute = 0
for i in range(60):
	if minsmap[i] > minsmap[mostsleepedminute]:
		mostsleepedminute = i

print(mostsleepid, minsofsleep[mostsleepid], mostsleepedminute)
ans = mostsleepid * mostsleepedminute
advent.submit_answer(1, ans)

globalminsmap = {}
for gid in minsofsleep:
	minsmap = [0] * 60
	for d in filter(lambda x: x['id'] == gid, days.values()):
		for i in range(60):
			minsmap[i] += d['min'][i]

	mostsleepedminute = 0
	for i in range(60):
		if minsmap[i] > minsmap[mostsleepedminute]:
			mostsleepedminute = i

	globalminsmap[gid] = (mostsleepedminute, minsmap[mostsleepedminute])

for k in globalminsmap:
	bestsleeper = k
	break

mostsleepedminute = 0
for gid in globalminsmap:
	if globalminsmap[gid][1] > globalminsmap[bestsleeper][1]:
		bestsleeper = gid

ans2 = bestsleeper * globalminsmap[bestsleeper][0]
print(bestsleeper, globalminsmap[bestsleeper][0])
print('ans2:', ans2)

advent.submit_answer(2, ans2)
