#!/usr/bin/env python3

from utils import advent
from lib.intcode import IntcodeVM

EMPTY, SCAFFOLD = '.#'
NORTH, SOUTH, WEST, EAST = range(4)
LEFT = (WEST, EAST, SOUTH, NORTH)
RIGHT = (EAST, WEST, NORTH, SOUTH)
MOVE_DELTA = ((-1, 0), (+1, 0), (0, -1), (0, +1))

def get_moves(grid, startpos, startdir):
	columns = len(grid[0])
	grid = [EMPTY * columns] + grid + [EMPTY * columns]

	for i in range(len(grid)):
		grid[i] = EMPTY + grid[i] + EMPTY

	r, c = startpos
	curdir = startdir
	moves = []
	steps = 0
	r += 1
	c += 1

	while 1:
		dr, dc = MOVE_DELTA[curdir]
		newr, newc = r + dr, c + dc

		if grid[newr][newc] == SCAFFOLD:
			steps += 1
			r, c = newr, newc
			continue

		newdir = LEFT[curdir]
		dr, dc = MOVE_DELTA[newdir]
		newr, newc = r + dr, c + dc

		if grid[newr][newc] == SCAFFOLD:
			turn = 'L'
		else:
			newdir = RIGHT[curdir]
			dr, dc = MOVE_DELTA[newdir]
			newr, newc = r + dr, c + dc

			if grid[newr][newc] == SCAFFOLD:
				turn = 'R'
			else:
				moves.append(str(steps))
				break

		if steps > 0:
			moves.append(str(steps))
		moves.append(turn)

		r, c = newr, newc
		curdir = newdir
		steps = 1

	return moves

def find_functions(moves):
	for la in range(2, 11):
		func_a = moves[:la]
		sb = la

		while moves[sb:][:la] == func_a:
			sb += la

		for lb in range(2, 11):
			func_b = moves[sb:sb + lb]
			sc = sb + lb

			while 1:
				if moves[sc:][:la] == func_a:
					sc += la
				elif moves[sc:][:lb] == func_b:
					sc += lb
				else:
					break

			for lc in range(2, 11):
				func_c = moves[sc:sc + lc]
				ok = True
				i = sc

				while i < len(moves):
					if moves[i:][:la] == func_a:
						i += la
					elif moves[i:][:lb] == func_b:
						i += lb
					elif moves[i:][:lc] == func_c:
						i += lc
					else:
						ok = False
						break

				if ok:
					A = ','.join(func_a)
					B = ','.join(func_b)
					C = ','.join(func_c)

					if len(A) <= 20 and len(B) <= 20 and len(C) <= 20:
						return A, B, C


advent.setup(2019, 17)
fin = advent.get_input()

program = list(map(int, fin.read().split(',')))
vm = IntcodeVM(program)

out = vm.run()
grid = ''.join(map(chr, out)).strip().splitlines()
rows, columns = len(grid), len(grid[0])
answer = 0

for r in range(1, rows - 1):
	for c in range(1, columns - 1):
		if grid[r][c] == SCAFFOLD:
			n = sum((grid[rr][cc] == SCAFFOLD for rr, cc in ((r+1, c), (r-1, c), (r, c+1), (r, c-1))))

			if n == 4:
				answer += r * c
		elif grid[r][c] in '^v<>':
			startpos = (r, c)
			startdir = '^v<>'.index(grid[r][c])

advent.print_answer(1, answer)


moves = get_moves(grid, startpos, startdir)
A, B, C = find_functions(moves)
main = ','.join(moves).replace(A, 'A').replace(B, 'B').replace(C, 'C')
robot_prog = list(map(ord, '{}\n{}\n{}\n{}\nn\n'.format(main, A, B, C)))

vm.reset()
vm.code[0] = 2
answer = vm.run(robot_prog)[-1]

advent.print_answer(2, answer)
