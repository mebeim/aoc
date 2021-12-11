import re
import io
import sys
import heapq
import string

from importlib import find_loader
from copy import deepcopy
from functools import lru_cache, reduce, partial
from collections import defaultdict, deque, namedtuple, Counter
from operator import itemgetter, attrgetter, methodcaller
from itertools import product, permutations, combinations, filterfalse, starmap, count
from math import pi as PI, inf as INFINITY
from math import floor, ceil, sqrt, sin, cos, tan, asin, acos, atan, factorial

from .polyfill import *

if find_loader('z3') is not None:
	import z3

if find_loader('blist') is not None:
	try:
		import blist
	except ImportError:
		pass

if find_loader('sortedcontainers') is not None:
	import sortedcontainers

if find_loader('numpy') is not None:
	try:
		import numpy as np
	except ImportError:
		pass

if find_loader('networkx') is not None:
	import networkx as nx
