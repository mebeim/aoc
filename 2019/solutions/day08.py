#!/usr/bin/env python3

from utils import advent

WIDTH, HEIGHT = 25, 6
SIZE = WIDTH * HEIGHT

advent.setup(2019, 8)
fin = advent.get_input()

chars = fin.readline().strip()
layers = [chars[i:i + SIZE] for i in range(0, len(chars), SIZE)]

best = min(layers, key=lambda l: l.count('0'))
checksum = best.count('1') * best.count('2')

advent.print_answer(1, checksum)

image = ['2'] * SIZE

for i in range(SIZE):
	for l in layers:
		if l[i] != '2':
			image[i] = l[i]
			break

conv = {'0': ' ', '1': '#'}
decoded = ''

for i in range(0, SIZE, WIDTH):
	decoded += ''.join(map(conv.get, image[i:i + WIDTH])) + '\n'

# Can't really print this nicely, but whatever
advent.print_answer(2, '\n' + decoded)
