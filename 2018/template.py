#!/usr/bin/env python3

import advent

import re
import sys
import copy
import heapq
from string import *
from collections import defaultdict, deque, namedtuple, Counter

def log(s, *a):
	sys.stderr.write(s.format(*a))
	sys.stderr.flush()

advent.setup(2018, 20, dry_run=True)
fin = advent.get_input()
print(*fin)

##################################################

# nums = list(map(int, fin))
# strings = list(map(str.strip, fin))
# matrix = list(map(lambda l: list(map(int, l.split())), fin))



# advent.submit_answer(1, ans)



# advent.submit_answer(2, ans2)
