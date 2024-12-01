#!/usr/bin/env python3

from utils.all import *

# advent.setup(2024, )
DEBUG = 'debug' in map(str.lower, sys.argv)
fin = advent.get_input() if not DEBUG else io.StringIO('''\

''')
eprint(*fin, sep='', end='----- end of input -----\n\n'); fin.seek(0, 0)

try: data = fin.read(); fin.seek(0, 0)
except: pass
try: ints = extract_ints(data)
except: pass
try: intmat = read_int_matrix(fin); fin.seek(0, 0)
except: pass
try: lines = read_lines(fin); fin.seek(0, 0)
except: pass
try: grid = read_char_matrix(fin); fin.seek(0, 0)
except: pass
try: intgrid = read_digit_matrix(fin); fin.seek(0, 0)
except: pass
try: g = graph_from_grid(grid, find='QWERTYUIOPASDFGHJKLZXCVBNM', avoid='#', coords=False, get_neighbors=neighbors4)
except: pass
timer_start()

ans1 = ans2 = 0
# g = defaultdict(list)

# for r, row in enumerate(grid):
# 	for c, char in enumerate(row):
# 		pass

# for r, row in enumerate(intgrid):
# 	for c, num in enumerate(row):
# 		pass

# for line in lines:






advent.print_and_submit(1, ans1)
# advent.print_answer(1, ans1)






advent.print_and_submit(2, ans2)
# advent.print_answer(2, ans2)


# - Can you memoize some state for which the solution will always be the same?
# - Can you batch operations together instead of doing them singularly?
# - Too many points? Coordinate compression? Shoelace formula?
# - Can you go blind with Z3 (or GCC+IDA+Z3) instead of reverse engineering?
