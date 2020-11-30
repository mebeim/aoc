#!/usr/bin/env python3

from utils import advent
import heapq

advent.setup(2018, 12)
fin = advent.get_input()

##################################################

def simulate(days=20):
	seen = set()
	sseen = False
	pseen = False

	for d in range(1, days+1):
		alive = set()

		for i in range(2, len(pots)-2):
			k =  ''.join(pots[i-2:i+3])

			# print(i-offset, k, end='')

			if k in info:
				# print(':', info[k] + ':', end=' ')
				# print(pots[i], '->', end=' ')
				if info[k] == '#':
					alive.add(i)
				# print(pots[i], end='')
			# print()

		for i in range(len(pots)):
			if i in alive:
				pots[i] = '#'
			else:
				pots[i] = '.'

		state = ''.join(pots)
		idx = state.find('#')
		state = state[idx:]
		state = state[:state.rfind('#')+1]

		# print(''.join(pots[offset-10:offset+200]))

		if state in seen:
			print('SEEN', d, idx)
			print(state)
			sseen = True

			if pseen:
				break

		pseen = sseen

		seen.add(state)

		# print(d, ':', ''.join(pots))
		# break

	return d, state

offset = 1000
pots = list(fin.readline().replace('initial state:', '').strip())

print(''.join(pots))
pots = ['.'] * offset + pots + ['.'] * offset
fin.readline()
strings = list(map(str.strip, fin))

info = {}
for s in strings:
	k, v = s.replace(' ', '').split('=>')
	info[k] = v

print(info)

## Part 1:

# endsim, endstate = simulate()

# print('sim ended on day:', endsim)
# print(endstate)

# alive = sum(c == '#' for c in pots)
# print('alive:', alive)

# ans = 0
# for i in range(len(pots)):
# 	if pots[i] == '#':
# 		ans += i - offset

# advent.submit_answer(1, ans)

# day 91 ans 2391
# day 92 ans 2412

## Part 2 (only works if part 1 is commented)

endsim, endstate = simulate(50000000000)
print('sim ended on day:', endsim)
print(endstate)

alive = sum(c == '#' for c in pots)
print('alive:', alive)

remaining = 50000000000 - endsim
print(remaining, 'days left to sim')

ans = 0
for i in range(len(pots)):
	if pots[i] == '#':
		ans += i - offset

ans += alive*remaining

advent.submit_answer(2, ans)
