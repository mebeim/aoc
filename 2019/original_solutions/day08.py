#!/usr/bin/env python3

from utils.all import *

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

chars = fin.readline().strip()

layers = []
w = 25
h = 6
k = 0
sz = w * h

for layer in range(len(chars) // sz):
	layers.append(chars[k:k + sz])
	k += sz

leasti = 0
least = 9999

for i, l in enumerate(layers):
	zeroes = sum(x == '0' for x in l)

	if zeroes < least:
		least = zeroes
		leasti = i

n1 = zeroes = sum(x == '1' for x in layers[leasti])
n2 = zeroes = sum(x == '2' for x in layers[leasti])

advent.submit_answer(1, n1 * n2)

img = ['2'] * sz

for l in layers:
	for i, v in enumerate(l):
		if img[i] == '2':
			img[i] = v

for i, v in enumerate(img):
	sys.stdout.write(' ' if v == '0' else 'x')
	if (i+1) % w == 0:
		sys.stdout.write('\n')

