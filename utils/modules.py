import heapq
import io
import re
import string
import sys

from collections import Counter, defaultdict, deque, namedtuple
from copy import deepcopy
from functools import cache, lru_cache, partial, reduce
from itertools import combinations, count, filterfalse, permutations, product, starmap
from math import pi as PI, inf as INFINITY
from math import floor, ceil, sqrt, sin, cos, tan, asin, acos, atan, factorial
from math import comb, gcd, isqrt, lcm, perm, prod
from operator import attrgetter, itemgetter, methodcaller

try:
	import z3
except ImportError:
	pass

try:
	import blist
except ImportError:
	pass

try:
	import sortedcontainers
except ImportError:
	pass

try:
	import numpy as np
except ImportError:
	pass

try:
	import networkx as nx
except ImportError:
	pass
